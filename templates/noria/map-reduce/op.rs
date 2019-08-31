use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::HashMap;

use super::att3::Typed;
use nom_sql::SqlType;

use crate::ops::grouped::get_group_values;
use crate::state::click_ana::{iseq, ClickAnaState, Computer};
//use crate::state::cstate::{MemoElem};
use prelude::*;

#[derive(Debug)]
pub enum FreeGroup<A> {
    One(A),
    And(Box<FreeGroup<A>>, Box<FreeGroup<A>>),
    Not(Box<FreeGroup<A>>),
    Empty,
}

// Defined replacements
//   udf-name, map, reduce, node-properties

type Timestamp = i32;
type Category = i32;

#[derive(Serialize, Deserialize,Clone)]
pub struct
    // <begin(udf-name)>
    ClickAna
    // <end(udf-name)>
{
    // Function arguments
    // start_cat: DataType,
    // end_cat: DataType,

    // cat_index: usize,
    // ts_index: usize,

    // <insert(node-properties)>

    // Index for the input
    // Perhaps at some point this should allow multiple ancestors?
    src: IndexPair,

    // This *should* be `Option<usize>`
    cols: usize,

    // Index into the cache
    local_index: Option<IndexPair>,

    // Precomputed data structures, copied from `dataflow::ops::grouped`
    group_by: Vec<usize>,
    out_key: Vec<usize>,
    colfix: Vec<usize>,
}

impl Typed for ClickAna {
    type Type = SqlType;
    fn typ(&self) -> Self::Type {
        // <insert(sql-type)>
    }
}

impl ClickAna {
    fn run(&self, row: &[DataType]) -> iseq::Action<i32> {
        use self::iseq::Action;
        let cat = &row[self.cat_index];
        let ts = row[self.ts_index].clone().into();

        if cat == &self.start_cat {
            Action::Open(ts)
        } else if cat == &self.end_cat {
            Action::Close(ts)
        } else {
            Action::Insert(ts)
        }
    }

    pub fn new(
        src: NodeIndex,
        start_cat: Category,
        end_cat: Category,
        cat_index: usize,
        ts_index: usize,
        mut group_by: Vec<usize>,
    ) -> ClickAna {
        group_by.sort();
        let out_key = (0..group_by.len()).collect();
        ClickAna {
            src: src.into(),

            start_cat: start_cat.into(),
            end_cat: end_cat.into(),

            cat_index,
            ts_index,

            local_index: None,
            cols: 0, // Actually initialized in `on_connected`

            group_by: group_by,
            out_key: out_key,
            colfix: Vec::new(),
        }
    }

    fn on_input_mut(
        &mut self,
        from: LocalNodeIndex,
        rs: Records,
        replay_key_cols: &Option<&[usize]>,
        state: &mut StateMap,
    ) -> ProcessingResult {
        let idx = self.local_index.unwrap();
        println!("{} Received input of size {}", idx, rs.len());
        debug_assert_eq!(from, *self.src);

        if rs.is_empty() {
            return ProcessingResult {
                results: rs,
                ..Default::default()
            };
        }

        let group_by = &self.group_by;
        let cmp = |a: &Record, b: &Record| {
            group_by
                .iter()
                .map(|&col| &a[col])
                .cmp(group_by.iter().map(|&col| &b[col]))
        };

        // First, we want to be smart about multiple added/removed rows with same group.
        // For example, if we get a -, then a +, for the same group, we don't want to
        // execute two queries. We'll do this by sorting the batch by our group by.
        let mut rs: Vec<_> = rs.into();
        rs.sort_by(&cmp);

        // find the current value for this group
        let us = self.local_index.unwrap();
        let db = &mut state
            .get_mut(*us)
            .expect("grouped operators must have their own state materialized")
            .as_click_ana_state()
            .expect("This operator need a special state type")
            .0;

        println!("{} Fetched database", idx);

        let mut misses = Vec::new();
        let mut lookups = Vec::new();
        let mut out = Vec::new();
        {
            let out_key = &self.out_key;
            let mut handle_group =
                |group_rs: ::std::vec::Drain<Record>, diffs: ::std::vec::Drain<_>| {
                    let mut group_rs = group_rs.peekable();

                    let group = get_group_values(group_by, group_rs.peek().unwrap());

                    println!("{} Handling group {:?}", idx, &group);

                    let mut mrs = db.lookup_leaf_mut(&out_key[..], &KeyType::from(&group[..]));
                    let rs = match mrs {
                        Option::Some(ref mut rs) => {
                            if replay_key_cols.is_some() {
                                lookups.push(Lookup {
                                    on: *us,
                                    cols: out_key.clone(),
                                    key: group.clone(),
                                });
                            }
                            rs
                        }
                        _ => {
                            misses.extend(group_rs.map(|r| Miss {
                                on: *us,
                                lookup_idx: out_key.clone(),
                                lookup_cols: group_by.clone(),
                                replay_cols: replay_key_cols.map(Vec::from),
                                record: r.extract().0,
                            }));
                            return;
                        }
                    };

                    // Double check that `Computing(None, _)` should actually be caught here
                    // new is the result of applying all diffs and computing a new value
                    let new = {
                        let computer = rs.get_or_init_compute_mut();
                        for (ac, pos) in diffs {
                            println!("Applying action {:?}", &ac);
                            computer.apply(ac, pos);
                        }
                        //let v = computer.compute_new_value().into();
                        // <insert(reduce)>
                        println!("{} Computed {}", idx, v);
                        v
                    };

                    let old = rs.value_may();
                    // current value is in the last output column
                    // or "" if there is no current group
                    let current = old.map(|r| &r[r.len() - 1]);

                    match current {
                        Some(ref current) if new == **current => {
                            println!("Value did not change");
                            // no change
                        }
                        _ => {
                            if let Some(old) = old {
                                // revoke old value
                                debug_assert!(current.is_some());
                                // TODO this used to be `old.to_owned()` check that that also did a clone!
                                out.push(Record::Negative((**old).clone()));
                            }

                            // emit positive, which is group + new.
                            let mut rec = group;
                            rec.push(new);
                            out.push(Record::Positive(rec));
                        }
                    }
                };

            let mut diffs = Vec::new();
            let mut group_rs = Vec::new();
            for r in rs {
                if !group_rs.is_empty() && cmp(&group_rs[0], &r) != Ordering::Equal {
                    handle_group(group_rs.drain(..), diffs.drain(..));
                }

                {
                    let
                        // <begin(row-name)>
                        r0
                        // <end(row-name)>
                        = r;

                    // <insert(map)>
                }

                //diffs.push((self.run(&r[..]), r.is_positive()));
                group_rs.push(r);
            }
            assert!(!diffs.is_empty());
            handle_group(group_rs.drain(..), diffs.drain(..));
        }

        println!("{} Finished processing", idx);

        ProcessingResult {
            results: out.into(),
            lookups,
            misses,
        }
    }
}

impl Ingredient for ClickAna {
    fn take(&mut self) -> NodeOperator {
        Clone::clone(self).into()
    }

    fn ancestors(&self) -> Vec<NodeIndex> {
        vec![self.src.as_global()]
    }

    /// TODO check this is can be copied like this
    fn on_connected(&mut self, g: &Graph) {
        let srcn = &g[self.src.as_global()];

        // group by all columns
        self.cols = srcn.fields().len();

        // build a translation mechanism for going from output columns to input columns
        let colfix: Vec<_> = (0..self.cols)
            .filter(|col| {
                // since the generated value goes at the end,
                // this is the n'th output value
                // otherwise this column does not appear in output
                self.group_by.iter().any(|c| c == col)
            })
            .collect();
        self.colfix.extend(colfix.into_iter());
    }

    fn on_commit(&mut self, us: NodeIndex, remap: &HashMap<NodeIndex, IndexPair>) {

        println!("Being added to graph");
        // who's our parent really?
        self.src.remap(remap);

        // who are we?
        self.local_index = Some(remap[&us]);
    }

    fn on_input(
        &mut self,
        _: &mut dyn Executor,
        _: LocalNodeIndex,
        _: Records,
        _: &mut Tracer,
        _: Option<&[usize]>,
        _: &DomainNodes,
        _: &StateMap,
    ) -> ProcessingResult {
        unreachable!()
    }

    fn on_input_raw_mut(
        &mut self,
        _: &mut dyn Executor,
        from: LocalNodeIndex,
        rs: Records,
        _: &mut Tracer,
        replay_key_cols: &ReplayContext,
        _: &DomainNodes,
        state: &mut StateMap,
    ) -> RawProcessingResult {
        RawProcessingResult::Regular(self.on_input_mut(from, rs, &replay_key_cols.key(), state))
    }

    fn suggest_indexes(&self, this: NodeIndex) -> HashMap<NodeIndex, Vec<usize>> {
        // index by our primary key
        Some((this, self.out_key.clone())).into_iter().collect()
    }

    fn resolve(&self, col: usize) -> Option<Vec<(NodeIndex, usize)>> {
        if col == self.colfix.len() {
            return None;
        }
        Some(vec![(self.src.as_global(), self.colfix[col])])
    }

    fn description(&self, detailed: bool) -> String {
        "click-ana".to_string()
    }

    fn parent_columns(&self, column: usize) -> Vec<(NodeIndex, Option<usize>)> {
        if column == self.colfix.len() {
            return vec![(self.src.as_global(), None)];
        }
        vec![(self.src.as_global(), Some(self.colfix[column]))]
    }

    fn is_selective(&self) -> bool {
        true
    }

    fn make_special_state(&self) -> Option<Box<dyn State>> {
        Option::Some(Box::new(
            // <insert(make-special-state)>
        ))
    }
}

// pub mod itree {
//     enum Direction {
//         Left,
//         Right,
//     }
//     enum Span<T> {
//         Closed {
//             span: (T, T),
//         },
//         HalfOpen {
//             direction: Direction,
//             bound: T,
//         },
//         Open,
//     }
//     pub struct Tree<T,E>(Box<Node<T,E>>);
//     struct Node<T,E>
//         {
//             span: Span<T,E>,
//             elems: Vec<(T,E)>,
//             left: Tree<T,E>,
//             right: Tree<T,E>,
//         }
//     pub enum Action<T,E> {
//         Open(T),
//         Close(T),
//         Record(T,E),
//     }

//     impl <T,E> Node {
//         fn new(span: Span<T,E>) -> Node<T,E> {
//             Node::new_with_elems(span, Vec::empty())
//         }
//         fn new_with_elems(span: Span<T,E>, elems: Vec<(T,E)>) -> Node<T,E> {
//             Node { span: span, elems: elems }
//         }
//         fn empty() -> Node<T,E> {
//             Node::Empty
//         }
//         fn new_open(elems: Vec<(T,E)>) {
//             Node::Node{ span: Open, elems: elems }
//         }
//     }

//     use std::cmp::Ordering;

//     impl <T> Span {

//         fn contains(&self, e: &T) -> bool {
//             match *self {
//                 Open => true,
//                 HalfOpen { direction: Left, bound } => e <= bound,
//                 HalfOpen { direction: Right, bound} => bound < e,
//                 Closed { span: (lower, upper) } => lower <= e && e < upper,
//             }
//         }

//         fn is_open(&self) {
//             match *self {
//                 Closed{} => false,
//                 _ => true,
//             }
//         }
//     }

//     fn split_vec<F: Fn(T) -> bool, T>(predicate: F, v: Vec<T>) -> (Vec<T>, Vec<T>) {
//         let v1 = Vec::new();
//         let v2 = Vec::new();

//         for i in v.drain(..) {
//             if predicate(i) {
//                 v1.push(i)
//             } else {
//                 v2.push(i)
//             }
//         }
//         (v1, v2)
//     }

//     impl <T : std::cmp::Ord,E> Tree {
//         fn new_node(node: Node<T,E>) -> Tree<T,E> {
//             Tree(Box::new(node))
//         }
//         fn new_half_open(direction: Direction, bound: T) -> Tree<T,E> {
//             Tree::new_node(
//                 Node::new(HalfOpen { direction: direction,
//                                      bound: bound,
//                                      child: Tree::empty(),
//                 }))
//         }
//         fn empty() -> Tree<T,E> {
//             Tree::new_node(Node { span: Open, elems: Vec::new()})
//         }
//         fn new_open(elems: Vec<(T,E)>) -> Tree<T,E> {
//             Tree::new_node(Node::new_open(elems))
//         }
//         pub fn open_interval(&mut self, bound: T) {
//             let ref mut elem = self;
//             loop {
//                 let node@Node{span, ..} = *elem.0;
//                 match span {

//                     Option::None => {
//                         let new_node = match span {
//                             HalfOpen{ direction: Left, bound: bound0, child } => {
//                                 let (smaller, larger) = split_vec(|a| a.0 < bound, elems);
//                                 Tree:new_node(
//                                     Node::new_with_elems(
//                                         Span::Closed {
//                                             span: (bound, bound0),
//                                             right: child,
//                                             left: Tree::new_open(smaller),
//                                         },
//                                         larger,
//                                     )
//                                 );
//                             },
//                             HalfOpen { direction: Right, ..} => {
//                                 let (smaller, larger) = split_vec(|a| a.0 < bound, elems);

//                             },
//                             Open => {
//                                 let (smaller, larger) = split_vec(|a| a.0 < bound, elems);
//                                 Tree::new_node(
//                                     Node::new_with_elems(
//                                         HalfOpen {
//                                             direction: Right,
//                                             bound: bound,
//                                             child: Tree::new_open(smaller),
//                                         },
//                                         larger,
//                                     )
//                                 )
//                             }
//                             elem.0 = new_node;
//                             return;
//                         },
//                         Option::Some(child) => {
//                             elem = child;
//                         }
//                     }
//                 }
//             }

//         }
//     }
// }
