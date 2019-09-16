use crate::node::MirNodeType;

pub fn mk_graph() -> super::UDFGraph {
    // <begin(graph)>
    super::UDFGraph {
        adjacency_list: vec![],
        sink: (0, vec![]),
    }
    // <end(graph)>
}
