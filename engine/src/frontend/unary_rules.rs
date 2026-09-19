//! Exact OWL lowering of one-variable class rules over source individual names.
//! Non-unary or unrepresented rules prevent the whole transformation. The
//! original rule counts remain in the profile alongside a normalization count.
use super::iri::IriRegistry;
use super::sexpr::Node;
use super::syntax::{mk_and, mk_or, Axiom, Concept, Ontology, RuleAtom, RuleTerm};

#[derive(Default)]
pub(super) struct Scan {
    count: u64,
    invalid: bool,
    non_pointwise_source: bool,
}

// In this source fragment, every TBox constraint is pointwise over class
// membership. An arbitrary fresh unnamed point satisfying the TBox can be
// adjoined without changing any source individual or DL-safe rule instance.
// Keep the retained rule backend for this certified-separable fragment.
// Raw-node coverage matters: an unrepresented axiom must not disappear from
// the eligibility check. Anonymous source individuals also stay out because
// the legacy consistency certificate does not distinguish them from names.
fn pointwise_source(node: &Node<'_>) -> bool {
    fn named(node: &Node<'_>) -> bool {
        matches!(node, Node::Atom(s) if !s.starts_with("_:") && !s.starts_with('"'))
    }
    fn class(node: &Node<'_>) -> bool {
        match node {
            Node::Atom(_) => named(node),
            Node::List("ObjectIntersectionOf" | "ObjectUnionOf", args) =>
                !args.is_empty() && args.iter().all(class),
            Node::List("ObjectComplementOf", args) => args.len() == 1 && class(&args[0]),
            _ => false,
        }
    }
    let Node::List(kind, args) = node else { return false };
    let args = super::parse::strip_annotations(args);
    match *kind {
        "Annotation" | "DLSafeRule" => true,
        "Declaration" => matches!(args.as_slice(), [Node::List("Class" | "NamedIndividual", inner)]
            if inner.len() == 1 && named(&inner[0])),
        "SubClassOf" => args.len() == 2 && args.iter().all(|node| class(node)),
        "EquivalentClasses" | "DisjointClasses" => args.len() >= 2 && args.iter().all(|node| class(node)),
        "ClassAssertion" => args.len() == 2 && class(&args[0]) && named(&args[1]),
        _ => false,
    }
}

impl Scan {
    pub(super) fn observe(&mut self, node: &Node<'_>) {
        self.non_pointwise_source |= !pointwise_source(node);
        let Node::List("DLSafeRule", arguments) = node else { return };
        self.count += 1;
        let arguments = super::parse::strip_annotations(arguments);
        let valid = (|| {
            let [Node::List("Body", body), Node::List("Head", head)] = arguments.as_slice() else {
                return false;
            };
            if head.is_empty() { return false; }
            let mut variable = None;
            for atom in body.iter().chain(head.iter()) {
                let Node::List("ClassAtom", args) = atom else { return false };
                let [Node::Atom(class), Node::List("Variable", vars)] = args.as_slice() else {
                    return false;
                };
                let [Node::Atom(name)] = vars.as_slice() else { return false };
                if class.starts_with('"') || name.starts_with('"') { return false; }
                if variable.is_some_and(|previous| previous != *name) { return false; }
                variable = Some(*name);
            }
            variable.is_some()
        })();
        self.invalid |= !valid;
    }

    pub(super) fn lower(
        &self, ontology: &mut Ontology, registry: &mut IriRegistry,
        source_individuals: &[&str], source_rule_count: u64,
    ) -> u64 {
        if self.invalid || self.count == 0 || self.count != source_rule_count {
            return 0;
        }
        let rules: Vec<_> = ontology.rules().collect();
        if rules.len() as u64 != self.count { return 0; }
        // Recheck the parsed view independently of the raw-node certificate.
        for rule in &rules {
            let Axiom::Rule(body, head) = rule else { return 0 };
            if head.is_empty() { return 0; }
            let mut variable = None;
            for atom in body.iter().chain(head) {
                let RuleAtom::Class(Concept::Name(_), RuleTerm::Var(name)) = atom else {
                    return 0;
                };
                if variable.is_some_and(|previous| previous != name) { return 0; }
                variable = Some(name);
            }
        }
        if !self.non_pointwise_source {
            return 0;
        }
        // The profiler includes declarations, assertions and nominal uses.
        // It excludes rule variables and never sees a synthetic query witness.
        let guard = mk_or(source_individuals.iter()
            .map(|name| Concept::Nominal(registry.short(name))));
        let mut normalized = Vec::new();
        for rule in rules {
            let Axiom::Rule(body, head) = rule else { unreachable!() };
            let antecedent = mk_and(std::iter::once(guard.clone()).chain(body.iter().map(|atom| {
                let RuleAtom::Class(concept, _) = atom else { unreachable!() };
                concept.clone()
            })));
            for atom in head {
                let RuleAtom::Class(concept, _) = atom else { unreachable!() };
                normalized.push(Axiom::SubClassOf(antecedent.clone(), concept.clone()));
            }
        }
        ontology.retain_axioms(|axiom| !matches!(axiom, Axiom::Rule(..)));
        for axiom in normalized { ontology.add(axiom); }
        self.count
    }
}
