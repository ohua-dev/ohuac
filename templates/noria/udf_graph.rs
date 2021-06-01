use crate::node::{ MirNodeType };
use column::Column;
use super::{ExecutionType, UDFGraph};
use nom_sql::Operator;
use dataflow::ops::filter::{Value, FilterCondition };
use common::DataType;

pub fn mk_graph(tables : &[String]) -> UDFGraph {
    // <begin(graph)>
    super::UDFGraph {
        adjacency_list: vec![],
        sink: (0, vec![]),
    }
    // <end(graph)>
}
