use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::HashMap;

use super::super::att3::Typed;
use nom_sql::SqlType;

use crate::ops::grouped::get_group_values;
use crate::state::cstate::{ SpecialStateWrapper, MemoElem };

//use crate::state::cstate::{MemoElem};
use prelude::*;

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

    // <insert(udf-args-sigs)>

    // <insert(node-properties)>

    // Index for the input
    // Perhaps at some point this should allow multiple ancestors?
    src: IndexPair,

    // the first `n` columns are moved to the output unchanged, to make sure scope is
    // preserved. `n+1` is the computed result
    carry: usize,
}

impl Typed for
    // <begin(udf-name)>
    ClickAna
    // <end(udf-name)>
{
    type Type = SqlType;
    fn typ_static() -> Self::Type {
        // <insert(udf-state-type)>
            ::typ_static()
    }
}

impl
    // <begin(udf-name)>
    ClickAna
    // <end(udf-name)>
{
    pub fn new(
        src: NodeIndex,
        // <insert(udf-args-sigs)>
        // <insert(node-properties)>
    ) -> Self {
        // <begin(udf-name)>
        Self
        // <end(udf-name)>
            {
            src: src.into(),

            // <insert(udf-args)>

            // <insert(node-property-args)>

            carry:
                // <insert(carry)>
                ,
        }
    }
}
impl Ingredient for
    // <begin(udf-name)>
    ClickAna
    // <end(udf-name)>
{
    fn take(&mut self) -> NodeOperator {
        Clone::clone(self).into()
    }

    fn ancestors(&self) -> Vec<NodeIndex> {
        vec![self.src.as_global()]
    }

    /// TODO check this is can be copied like this
    fn on_connected(&mut self, g: &Graph) {}

    fn on_commit(&mut self, us: NodeIndex, remap: &HashMap<NodeIndex, IndexPair>) {
        self.src.remap(remap);
    }

    fn on_input(
        &mut self,
        _: &mut dyn Executor,
        _: LocalNodeIndex,
        mut rs: Records,
        _: &mut Tracer,
        _: Option<&[usize]>,
        _: &DomainNodes,
        _: &StateMap,
    ) -> ProcessingResult {
        for mut r in rs {
            // This could also support multiple returns by pushing more than one arg.
            let computed = {
                // <insert(function)>
            };
            r.truncate(self.carry);
            r.push(computed);
        }
        ProcessingResult {
            results: rs,
            ..Default::default()
        }
    }

    fn suggest_indexes(&self, this: NodeIndex) -> HashMap<NodeIndex, Vec<usize>> {
        HashMap::new()
    }

    fn resolve(&self, col: usize) -> Option<Vec<(NodeIndex, usize)>> {
        if col == self.carry {
            return None;
        }
        Some(vec![(self.src.as_global(), col)])
    }

    fn description(&self, detailed: bool) -> String {
        // <insert(udf-name-str)>
          .to_string()
    }

    fn parent_columns(&self, column: usize) -> Vec<(NodeIndex, Option<usize>)> {
        if column == self.carry {
            return vec![(self.src.as_global(), None)];
        }
        vec![(self.src.as_global(), Some(column))]
    }

    fn is_selective(&self) -> bool {
        false
    }
}
