//! Anonymous-individual occurrence and forest restrictions (OWL 2, 11.2).
//! Named-neighbor admission follows the formal condition in section 11.2,
//! including for isolated anonymous vertices. The following named-star example
//! in that specification contradicts the condition; it is not an exception here.
use std::collections::{BTreeMap, BTreeSet};
use super::{expand, Node};

fn anonymous(node: &Node<'_>) -> Option<String> {
    node.as_atom().filter(|s| s.starts_with("_:")).map(str::to_owned)
}

fn forbidden_occurrence(node: &Node<'_>) -> Option<String> {
    match node {
        Node::Atom(_) => anonymous(node),
        Node::List("Annotation", _) => None,
        Node::List(_, args) => args.iter().find_map(forbidden_occurrence),
    }
}

fn role(node: &Node<'_>, prefixes: &BTreeMap<String, String>) -> String {
    match node {
        Node::Atom(name) => expand(name, prefixes),
        Node::List(head, args) => format!("{head}({})",
            args.iter().map(|n| role(n, prefixes)).collect::<Vec<_>>().join(" ")),
    }
}

#[derive(Default)]
struct Graph {
    vertices: BTreeSet<String>,
    named_edges: BTreeMap<String, BTreeSet<(String, String, String)>>,
    // One source assertion per undirected anonymous pair. Repeated occurrences
    // of the same assertion do not add another axiom to the ontology's set.
    edges: BTreeMap<(String, String), (String, String, String)>,
}
impl Graph {
    fn observe(&mut self, node: &Node<'_>, prefixes: &BTreeMap<String, String>) -> Result<(), String> {
        let Node::List(head, children) = node else {
            if let Some(id) = anonymous(node) { self.vertices.insert(id); }
            return Ok(());
        };
        if matches!(*head, "Annotation" | "AnnotationAssertion") { return Ok(()); }
        if matches!(*head, "SameIndividual" | "DifferentIndividuals"
            | "NegativeObjectPropertyAssertion" | "NegativeDataPropertyAssertion"
            | "ObjectOneOf" | "ObjectHasValue") {
            if let Some(id) = forbidden_occurrence(node) {
                return Err(format!("invalid OWL 2 DL input: anonymous individual {id} is forbidden in {head}"));
            }
        }
        if *head == "ObjectPropertyAssertion" {
            let args: Vec<_> = children.iter().filter(|n| n.head() != Some("Annotation")).collect();
            if let [property, from, to] = args.as_slice() {
                if let (Some(from), Some(to)) = (anonymous(from), anonymous(to)) {
                    if from == to {
                        return Err(format!("invalid OWL 2 DL input: anonymous individual {from} has a self-loop; anonymous object-property assertions must form a forest"));
                    }
                    let pair = if from < to { (from.clone(), to.clone()) } else { (to.clone(), from.clone()) };
                    let assertion = (role(property, prefixes), from, to);
                    if let Some(previous) = self.edges.get(&pair) {
                        if previous != &assertion {
                            return Err(format!("invalid OWL 2 DL input: multiple object-property assertions connect anonymous individuals {} and {}", pair.0, pair.1));
                        }
                    } else {
                        self.edges.insert(pair, assertion);
                    }
                } else if let Some(id) = anonymous(from).or_else(|| anonymous(to)) {
                    self.named_edges.entry(id).or_default().insert((
                        role(property, prefixes), role(from, prefixes), role(to, prefixes),
                    ));
                }
            }
        }
        for child in children { self.observe(child, prefixes)?; }
        Ok(())
    }

    fn finish(self) -> Result<(), String> {
        let mut neighbors = BTreeMap::<String, Vec<String>>::new();
        for vertex in self.vertices { neighbors.entry(vertex).or_default(); }
        for ((a,b),_) in self.edges {
            neighbors.entry(a.clone()).or_default().push(b.clone());
            neighbors.entry(b).or_default().push(a);
        }
        let mut seen = BTreeSet::new();
        for root in neighbors.keys() {
            if seen.contains(root) { continue; }
            let mut stack = vec![(root.clone(), None)];
            let mut has_permitted_root = false;
            while let Some((vertex, parent)) = stack.pop() {
                if !seen.insert(vertex.clone()) {
                    return Err(format!("invalid OWL 2 DL input: object-property assertions contain an anonymous-individual cycle through {vertex}; the graph must be a forest"));
                }
                has_permitted_root |= self.named_edges.get(&vertex)
                    .map_or(true, |assertions| assertions.len() <= 1);
                for next in &neighbors[&vertex] {
                    if Some(next) != parent.as_ref() {
                        stack.push((next.clone(), Some(vertex.clone())));
                    }
                }
            }
            if !has_permitted_root {
                return Err(format!("invalid OWL 2 DL input: anonymous-individual tree containing {root} has no node with at most one object-property assertion to a named individual (formal restriction in OWL 2 section 11.2)"));
            }
        }
        Ok(())
    }
}

pub(super) fn check(text: &str, prefixes: &BTreeMap<String, String>) -> Result<(), String> {
    let mut graph = Graph::default();
    crate::frontend::parse::for_each_ontology_child(text, |node|
        graph.observe(node, prefixes).map_err(crate::frontend::parse::OutOfFragment)).map_err(|e| e.0)?;
    graph.finish()
}

#[cfg(test)]
mod tests {
    use super::super::check_source;
    #[test]
    fn anonymous_individuals_are_rejected_in_forbidden_logical_positions() {
        for axiom in [
            "SameIndividual(_:a :b)", "DifferentIndividuals(:b _:a)",
            "NegativeObjectPropertyAssertion(:r :b _:a)",
            "NegativeDataPropertyAssertion(:p _:a \"value\")",
            "SubClassOf(:A ObjectOneOf(_:a))",
            "SubClassOf(:A ObjectSomeValuesFrom(:r ObjectHasValue(:s _:a)))",
        ] {
            let error = check_source(&format!("Ontology({axiom})")).unwrap_err();
            assert!(error.contains("anonymous individual") && error.contains("forbidden"), "{error}");
        }
        check_source("Ontology(Annotation(rdfs:comment _:a) SameIndividual(Annotation(rdfs:comment _:b) :a :b))").unwrap();
    }
    #[test]
    fn anonymous_object_graphs_reject_cycles_parallel_edges_and_self_loops() {
        for axioms in [
            "ObjectPropertyAssertion(:r _:a _:a)",
            "ObjectPropertyAssertion(:r _:a _:b) ObjectPropertyAssertion(:s _:a _:b)",
            "ObjectPropertyAssertion(:r _:a _:b) ObjectPropertyAssertion(:r _:b _:a)",
            "ObjectPropertyAssertion(:r _:a _:b) ObjectPropertyAssertion(:r _:b _:c) ObjectPropertyAssertion(:r _:c _:a)",
        ] {
            assert!(check_source(&format!("Ontology({axioms})")).unwrap_err().contains("anonymous"), "{axioms}");
        }
    }
    #[test]
    fn forests_duplicates_and_isolated_anonymous_individuals_remain_valid() {
        for axioms in [
            "ObjectPropertyAssertion(:r _:a _:b) ObjectPropertyAssertion(:r _:a _:b)",
            "ObjectPropertyAssertion(:r _:a _:b) ObjectPropertyAssertion(ObjectInverseOf(:s) _:c _:b)",
            "ObjectPropertyAssertion(:r _:a _:b) ObjectPropertyAssertion(:r _:c _:d)",
            "ClassAssertion(:A _:a) DataPropertyAssertion(:p _:a \"value\")",
        ] { check_source(&format!("Ontology({axioms})")).unwrap(); }
    }

    #[test]
    fn each_anonymous_tree_needs_one_node_with_at_most_one_named_assertion() {
        for axioms in [
            // Follow the formal condition, not the contradictory named-star example.
            "ObjectPropertyAssertion(:r :francis _:a) ObjectPropertyAssertion(:r _:a :meg) ObjectPropertyAssertion(:r _:a :chris)",
            // Count assertions, not distinct named neighbors.
            "ObjectPropertyAssertion(:r _:a :one) ObjectPropertyAssertion(:s _:a :one)",
            "ObjectPropertyAssertion(:r _:a :one) ObjectPropertyAssertion(:r :one _:a)",
            // Every vertex in this component has two named assertions.
            "ObjectPropertyAssertion(:r _:a _:b) ObjectPropertyAssertion(:r _:a :one) ObjectPropertyAssertion(:r _:a :two) ObjectPropertyAssertion(:r _:b :one) ObjectPropertyAssertion(ObjectInverseOf(:s) :two _:b)",
            // An isolated vertex in another component cannot repair the first.
            "ObjectPropertyAssertion(:r _:a :one) ObjectPropertyAssertion(:r _:a :two) ClassAssertion(:A _:b)",
        ] {
            let error = check_source(&format!("Ontology({axioms})")).unwrap_err();
            assert!(error.contains("at most one") && error.contains("section 11.2"), "{error}");
        }
        for axioms in [
            "ObjectPropertyAssertion(:r _:a :one)",
            "ObjectPropertyAssertion(ObjectInverseOf(:r) :one _:a)",
            "ObjectPropertyAssertion(:r _:a :one) ObjectPropertyAssertion(:r _:a :one)",
            // Only one suitable vertex is required in a component, not every vertex.
            "ObjectPropertyAssertion(:r _:a _:b) ObjectPropertyAssertion(:r _:a :one) ObjectPropertyAssertion(:r _:a :two)",
            "ObjectPropertyAssertion(:r _:a :one) AnnotationAssertion(:note _:a _:b)",
        ] { check_source(&format!("Ontology({axioms})")).unwrap(); }
        check_source("Prefix(:=<urn:>) Ontology(ObjectPropertyAssertion(:r _:a :one) ObjectPropertyAssertion(<urn:r> _:a <urn:one>))").unwrap();
    }
}
