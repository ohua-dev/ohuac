use crate::node::MirNodeType;
use column::Column;
use super::{ExecutionType, UDFGraph};

pub fn mk_graph() -> UDFGraph {
    // <begin(graph)>
    super::UDFGraph {
        adjacency_list: vec![],
        sink: (0, vec![]),
    }
    // <end(graph)>
}
