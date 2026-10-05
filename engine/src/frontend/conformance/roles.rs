//! OWL 2 Structural Specification 11.1 and 11.2: simple object properties.
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use super::{expand, Node};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Role(String, bool);
impl Role { fn inverse(&self) -> Self { Self(self.0.clone(), !self.1) } }

fn role(node: &Node<'_>, prefixes: &BTreeMap<String, String>) -> Option<Role> {
    match node {
        Node::Atom(s) => Some(Role(expand(s, prefixes), false)),
        Node::List("ObjectInverseOf", args) if args.len() == 1 =>
            role(&args[0], prefixes).map(|r| r.inverse()),
        _ => None,
    }
}

#[derive(Default)]
struct Hierarchy {
    supers: BTreeMap<Role, BTreeSet<Role>>,
    composite: BTreeSet<Role>,
    required_simple: Vec<(Role, String)>,
    chains: Vec<(Vec<Role>, Role)>,
}
impl Hierarchy {
    fn inclusion(&mut self, sub: Role, sup: Role) {
        self.supers.entry(sub.inverse()).or_default().insert(sup.inverse());
        self.supers.entry(sub).or_default().insert(sup);
    }
    fn composite(&mut self, r: Role) {
        self.composite.insert(r.inverse());
        self.composite.insert(r);
    }
    fn observe(&mut self, node: &Node<'_>, prefixes: &BTreeMap<String, String>) {
        let Node::List(kind, children) = node else { return };
        if matches!(*kind, "Annotation" | "AnnotationAssertion") { return; }
        let args: Vec<_> = children.iter().filter(|n| n.head() != Some("Annotation")).collect();
        match (*kind, args.as_slice()) {
            ("SubObjectPropertyOf", [left, right]) => {
                if let Some(sup) = role(right, prefixes) {
                    if let Node::List("ObjectPropertyChain", chain) = left {
                        if chain.len() > 1 {
                            self.composite(sup.clone());
                            if let Some(chain) = chain.iter().map(|r| role(r, prefixes)).collect() {
                                self.chains.push((chain, sup));
                            }
                        }
                    } else if let Some(sub) = role(left, prefixes) { self.inclusion(sub, sup); }
                }
            }
            ("EquivalentObjectProperties", _) => {
                let roles: Vec<_> = args.iter().filter_map(|n| role(n, prefixes)).collect();
                if let Some(first) = roles.first() {
                    for r in roles.iter().skip(1) {
                        self.inclusion(first.clone(), r.clone());
                        self.inclusion(r.clone(), first.clone());
                    }
                }
            }
            ("InverseObjectProperties", [a,b]) => {
                if let (Some(a), Some(b)) = (role(a,prefixes), role(b,prefixes)) {
                    self.inclusion(a.clone(), b.inverse());
                    self.inclusion(b.inverse(), a);
                }
            }
            ("SymmetricObjectProperty", [r]) => {
                if let Some(r) = role(r,prefixes) { self.inclusion(r.clone(), r.inverse()); }
            }
            ("TransitiveObjectProperty", [r]) => {
                if let Some(r) = role(r,prefixes) { self.composite(r); }
            }
            ("ObjectMinCardinality" | "ObjectMaxCardinality" | "ObjectExactCardinality", [_,r,..]) => {
                if let Some(r) = role(r,prefixes) { self.required_simple.push((r, kind.to_string())); }
            }
            ("ObjectHasSelf" | "FunctionalObjectProperty" | "InverseFunctionalObjectProperty"
                | "IrreflexiveObjectProperty" | "AsymmetricObjectProperty" | "DisjointObjectProperties", _) => {
                for r in &args {
                    if let Some(r) = role(r,prefixes) { self.required_simple.push((r, kind.to_string())); }
                }
            }
            _ => {}
        }
        for child in children { self.observe(child, prefixes); }
    }
    fn finish(mut self) -> Result<(), String> {
        self.check_regularity()?;
        for name in ["topObjectProperty", "bottomObjectProperty"] {
            self.composite(Role(format!("http://www.w3.org/2002/07/owl#{name}"), false));
        }
        let mut pending: VecDeque<_> = self.composite.iter().cloned().collect();
        while let Some(r) = pending.pop_front() {
            if let Some(supers) = self.supers.get(&r) {
                for sup in supers {
                    if self.composite.insert(sup.clone()) { pending.push_back(sup.clone()); }
                }
            }
        }
        for (r, construct) in self.required_simple {
            if self.composite.contains(&r) {
                return Err(format!("invalid OWL 2 DL input: {construct} requires a simple object property, but {}<{}>{} is non-simple (transitive, a property-chain target, a superproperty of one, or a top/bottom property)",
                    if r.1 { "ObjectInverseOf(" } else { "" }, r.0, if r.1 { ")" } else { "" }));
            }
        }
        Ok(())
    }

    /// Construct the least strict ordering required by the chains. The allowed
    /// recursive end occurrence and the transitivity case add no self edge.
    /// Closure under inverse on the left is required by section 11.2. A strict
    /// ordering may not contradict the ordinary subproperty hierarchy.
    fn check_regularity(&self) -> Result<(), String> {
        let mut strict: BTreeMap<Role, BTreeSet<Role>> = BTreeMap::new();
        for (chain, target) in &self.chains {
            if target.0 == "http://www.w3.org/2002/07/owl#topObjectProperty" { continue; }
            if chain.len() == 2 && chain.iter().all(|r| r == target) { continue; }
            let skip = if chain.first() == Some(target) { Some(0) }
                else if chain.last() == Some(target) { Some(chain.len() - 1) }
                else { None };
            for (i, operand) in chain.iter().enumerate() {
                if skip == Some(i) { continue; }
                strict.entry(operand.clone()).or_default().insert(target.clone());
                strict.entry(operand.inverse()).or_default().insert(target.clone());
            }
        }
        for start in strict.keys() {
            let mut visited = BTreeSet::new();
            let mut pending: Vec<_> = strict[start].iter().cloned().collect();
            while let Some(end) = pending.pop() {
                if !visited.insert(end.clone()) { continue; }
                if reaches(&self.supers, &end, start) {
                    return Err(format!("invalid OWL 2 DL input: irregular object-property chain hierarchy; required strict order from <{}> to <{}> conflicts with the subproperty hierarchy or creates a cycle", start.0, end.0));
                }
                if let Some(next) = strict.get(&end) { pending.extend(next.iter().cloned()); }
            }
        }
        Ok(())
    }
}

fn reaches(graph: &BTreeMap<Role, BTreeSet<Role>>, start: &Role, target: &Role) -> bool {
    let mut pending = vec![start.clone()];
    let mut visited = BTreeSet::new();
    while let Some(node) = pending.pop() {
        if node == *target { return true; }
        if !visited.insert(node.clone()) { continue; }
        if let Some(next) = graph.get(&node) { pending.extend(next.iter().cloned()); }
    }
    false
}

pub(super) fn check(text: &str, prefixes: &BTreeMap<String, String>) -> Result<(), String> {
    let mut hierarchy = Hierarchy::default();
    crate::frontend::parse::for_each_ontology_child(text, |node| {
        hierarchy.observe(node, prefixes);
        Ok(())
    }).map_err(|error| error.0)?;
    hierarchy.finish()
}

#[cfg(test)]
mod tests {
    use super::super::check_source;
    #[test]
    fn non_simple_roles_propagate_through_inverses_and_superproperties() {
        for restriction in ["ObjectMinCardinality(1 :s)", "ObjectMaxCardinality(2 ObjectInverseOf(:s))", "ObjectExactCardinality(0 :s)", "ObjectHasSelf(:s)"] {
            let source = format!("Prefix(:=<urn:test:>) Ontology(TransitiveObjectProperty(:r) InverseObjectProperties(:r :i) SubObjectPropertyOf(:i :s) SubClassOf(:A {restriction}))");
            assert!(check_source(&source).unwrap_err().contains("non-simple"));
        }
    }
    #[test]
    fn chain_targets_are_non_simple_but_operands_can_be_simple() {
        let base = "Prefix(:=<urn:test:>) Ontology(SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:p) :q) :r) ";
        assert!(check_source(&format!("{base} FunctionalObjectProperty(:r))")).is_err());
        assert!(check_source(&format!("{base} FunctionalObjectProperty(:p) FunctionalObjectProperty(:q))")).is_ok());
    }
    #[test]
    fn equivalent_roles_and_builtin_top_are_checked() {
        assert!(check_source("Ontology(TransitiveObjectProperty(:r) EquivalentObjectProperties(:r :s :t) DisjointObjectProperties(:t :p))").is_err());
        assert!(check_source("Ontology(SubClassOf(:A ObjectHasSelf(owl:topObjectProperty)))").is_err());
        assert!(check_source("Ontology(TransitiveObjectProperty(:r) SubClassOf(:A ObjectSomeValuesFrom(:r :B)))").is_ok());
    }
    #[test]
    fn regular_chains_allow_transitivity_and_end_recursion() {
        for chain in [":r :r", ":r :p", ":p :r", "ObjectInverseOf(:p) :q", ":p :q :r"] {
            assert!(check_source(&format!("Ontology(SubObjectPropertyOf(ObjectPropertyChain({chain}) :r))")).is_ok(), "{chain}");
        }
        assert!(check_source("Ontology(SubObjectPropertyOf(ObjectPropertyChain(:r :p :r) owl:topObjectProperty))").is_ok());
    }
    #[test]
    fn irregular_chains_reject_middle_recursion_and_dependency_cycles() {
        for axioms in [
            "SubObjectPropertyOf(ObjectPropertyChain(:p :r :q) :r)",
            "SubObjectPropertyOf(ObjectPropertyChain(:r :p :r) :r)",
            "SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r) SubObjectPropertyOf(:r :p)",
            "SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r) SubObjectPropertyOf(ObjectPropertyChain(:r :q) :p)",
            "SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:r) :q) :r)",
        ] {
            let error = check_source(&format!("Ontology({axioms})")).unwrap_err();
            assert!(error.contains("irregular"), "{axioms}: {error}");
        }
    }
}
