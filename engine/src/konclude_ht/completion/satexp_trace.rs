//! `KM_HT_SATEXP_TRACE=1` (diagnostic): one line per satisfiable expander
//! cache write and per satisfiable cache hit, with the node's label, flags,
//! ancestor depth and links. Used to isolate the cache entries of
//! docs/HYBRID-CB-HT.md section 23. Production never sets the variable.

use super::super::model::ontology::OntologyArenas;
use super::super::process::context::ProcessContext;
use super::super::process::{ConDescId, NodeId};

/// A compact description of `node`: id, nominal flag, ancestor depth, flags,
/// label (concept tags, `-` for negated) and links (`role:src->dst`).
pub(crate) fn describe_node(pc: &ProcessContext, onto: &OntologyArenas, node: NodeId) -> String {
    if node.is_none() {
        return "node <none>".to_string();
    }
    let n = pc.node(node);
    let mut labels: Vec<String> = Vec::new();
    let ls = n.use_reapply_con_label_set;
    if ls.is_some() {
        let mut it = pc.label_set(ls).get_concept_label_set_iterator(true, false, false);
        while it.has_next() {
            let cd: ConDescId = it.next(true, pc);
            if cd.is_none() {
                break;
            }
            let des = pc.con_desc(cd);
            labels.push(format!(
                "{}{}",
                if des.is_negated() { "-" } else { "" },
                onto.concept(des.get_concept()).get_concept_tag()
            ));
        }
    }
    let sid = |x: NodeId| if x.is_some() { pc.node(x).individual_node_id() } else { i64::MIN };
    let mut links: Vec<String> = Vec::new();
    let mut keys = Vec::new();
    let mut it = pc.node_successor_iterator(node);
    while it.has_next() {
        let link = it.next_link(false);
        let other = it.next_individual_id(true);
        if link.is_some() {
            keys.push(other);
        }
    }
    keys.sort_unstable();
    keys.dedup();
    for other in keys {
        let mut rit = pc.node_successor_role_iterator(node, other);
        while rit.has_next() {
            let link = rit.next(true);
            if link.is_some() {
                let e = pc.edge(link);
                links.push(format!(
                    "[{}:{}->{}]",
                    onto.role(e.get_link_role()).get_role_tag(),
                    sid(e.get_source_individual()),
                    sid(e.get_destination_individual())
                ));
            }
        }
    }
    format!(
        "node {} nom={} depth={} flags={:#x} L=[{}] links={}",
        n.individual_node_id(),
        n.is_nominal_individual_node(),
        n.individual_ancestor_depth(),
        n.processing_restriction_flags,
        labels.join(","),
        links.join("")
    )
}
