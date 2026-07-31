//! Fail-closed certificates for source SWRL rules that need no worker rule.

use std::collections::{HashMap, HashSet, VecDeque};

use super::sexpr::Node;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Term {
    Var(String),
    Ind(String),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Atom {
    Class(String, Term),
    Role(String, Term, Term),
    Data(String, Term, Term),
    Builtin(String, Vec<Term>),
    Same(Term, Term),
    Diff(Term, Term),
}

#[derive(Clone, Debug)]
struct Rule {
    body: Vec<Atom>,
    head: Vec<Atom>,
}

#[derive(Default)]
pub(super) struct RuleCertificateScan {
    class_assertions: Vec<(String, String)>,
    role_assertions: Vec<(String, String, String)>,
    disjoint_classes: HashSet<(String, String)>,
    different_individuals: HashSet<(String, String)>,
    exact_one_roles: HashSet<(String, String)>,
    named_subclasses: Vec<(String, String)>,
    rules: Vec<Rule>,
    data_assertions: u64,
    data_property_inclusions: u64,
    data_value_constructor: bool,
}

fn term(node: &Node<'_>) -> Option<Term> {
    match node {
        Node::List("Variable", args) => Some(Term::Var(args.first()?.as_atom()?.to_string())),
        Node::Atom(value) if !value.starts_with('"') => Some(Term::Ind((*value).to_string())),
        _ => None,
    }
}

fn atoms(node: &Node<'_>) -> Option<Vec<Atom>> {
    let Node::List(_, values) = node else {
        return None;
    };
    values
        .iter()
        .filter(|a| a.head() != Some("Annotation"))
        .map(|atom| {
            let Node::List(kind, args) = atom else {
                return None;
            };
            Some(match *kind {
                "ClassAtom" => {
                    Atom::Class(args.first()?.as_atom()?.to_string(), term(args.get(1)?)?)
                }
                "ObjectPropertyAtom" => Atom::Role(
                    args.first()?.as_atom()?.to_string(),
                    term(args.get(1)?)?,
                    term(args.get(2)?)?,
                ),
                "DataPropertyAtom" => Atom::Data(
                    args.first()?.as_atom()?.to_string(),
                    term(args.get(1)?)?,
                    term(args.get(2)?)?,
                ),
                "BuiltInAtom" => Atom::Builtin(
                    args.first()?.as_atom()?.to_string(),
                    args.iter().skip(1).map(term).collect::<Option<Vec<_>>>()?,
                ),
                "SameIndividualAtom" => Atom::Same(term(args.first()?)?, term(args.get(1)?)?),
                "DifferentIndividualsAtom" => Atom::Diff(term(args.first()?)?, term(args.get(1)?)?),
                _ => return None,
            })
        })
        .collect()
}

impl RuleCertificateScan {
    pub(super) fn observe(&mut self, node: &Node<'_>) {
        fn contains_data_value(node: &Node<'_>) -> bool {
            matches!(node.head(), Some("DataHasValue"))
                || match node {
                    Node::List(_, args) => args.iter().any(contains_data_value),
                    Node::Atom(_) => false,
                }
        }
        self.data_value_constructor |= contains_data_value(node);
        let Node::List(kind, args) = node else { return };
        match *kind {
            "ClassAssertion" => {
                if let (Some(c), Some(i)) = (
                    args.first().and_then(Node::as_atom),
                    args.get(1).and_then(Node::as_atom),
                ) {
                    self.class_assertions.push((i.to_string(), c.to_string()));
                } else if let (Some(Node::List("ObjectExactCardinality", card)), Some(individual)) =
                    (args.first(), args.get(1).and_then(Node::as_atom))
                {
                    // Only unqualified =1 R limits every R successor. A
                    // qualified =1 R.C permits additional R successors outside
                    // C and cannot support this clash certificate.
                    if card.len() == 2 && card.first().and_then(Node::as_atom) == Some("1") {
                        if let Some(role) = card.get(1).and_then(Node::as_atom) {
                            self.exact_one_roles
                                .insert((individual.to_string(), role.to_string()));
                        }
                    }
                }
            }
            "ObjectPropertyAssertion" => {
                if let (Some(r), Some(s), Some(t)) = (
                    args.first().and_then(Node::as_atom),
                    args.get(1).and_then(Node::as_atom),
                    args.get(2).and_then(Node::as_atom),
                ) {
                    self.role_assertions
                        .push((r.to_string(), s.to_string(), t.to_string()));
                }
            }
            "SubClassOf" => {
                if let (Some(sub), Some(sup)) = (
                    args.first().and_then(Node::as_atom),
                    args.get(1).and_then(Node::as_atom),
                ) {
                    self.named_subclasses
                        .push((sub.to_string(), sup.to_string()));
                }
            }
            "DisjointClasses" => {
                let names: Vec<_> = args.iter().filter_map(Node::as_atom).collect();
                for (i, left) in names.iter().enumerate() {
                    for right in names.iter().skip(i + 1) {
                        self.disjoint_classes.insert(ordered_pair(left, right));
                    }
                }
            }
            "DifferentIndividuals" => {
                let names: Vec<_> = args.iter().filter_map(Node::as_atom).collect();
                for (i, left) in names.iter().enumerate() {
                    for right in names.iter().skip(i + 1) {
                        self.different_individuals.insert(ordered_pair(left, right));
                    }
                }
            }
            "DataPropertyAssertion" | "NegativeDataPropertyAssertion" => self.data_assertions += 1,
            "SubDataPropertyOf" | "EquivalentDataProperties" => self.data_property_inclusions += 1,
            "DLSafeRule" => {
                let body = args
                    .iter()
                    .find(|n| n.head() == Some("Body"))
                    .and_then(atoms);
                let head = args
                    .iter()
                    .find(|n| n.head() == Some("Head"))
                    .and_then(atoms);
                if let (Some(body), Some(head)) = (body, head) {
                    self.rules.push(Rule { body, head });
                }
            }
            _ => {}
        }
    }

    pub(super) fn certified_unsupported_rules(&self) -> u64 {
        let no_data_facts = self.data_assertions == 0
            && self.data_property_inclusions == 0
            && !self.data_value_constructor
            && self
                .rules
                .iter()
                .all(|r| !r.head.iter().any(|a| matches!(a, Atom::Data(..))));
        self.rules
            .iter()
            .filter(|r| {
                (no_data_facts && r.body.iter().any(|a| matches!(a, Atom::Data(..))))
                    || self.legacy_meta_rule_is_subsumed(r)
            })
            .count() as u64
    }

    /// Certify an inconsistency using only explicit named-ABox facts, explicit
    /// distinctness (or disjoint asserted types), one exact-cardinality axiom,
    /// and one parsed DL-safe rule. This is a one-sided certificate: unsupported
    /// body atoms or unbound equality tests simply produce no witness.
    pub(super) fn certified_inconsistent(&self) -> bool {
        if self.rules.is_empty()
            || self.exact_one_roles.is_empty()
            || self.role_assertions.is_empty()
        {
            return false;
        }
        for rule in &self.rules {
            // A rule body is a conjunction. Match sparse role assertions first
            // so they bind both endpoints before broad class scans; evaluate
            // equality and difference guards next, then named classes. This
            // changes only enumeration order, not the accepted substitutions.
            let mut body: Vec<&Atom> = rule.body.iter().collect();
            body.sort_by_key(|atom| match atom {
                Atom::Role(..) => 0,
                Atom::Same(..) | Atom::Diff(..) => 1,
                Atom::Class(..) => 2,
                Atom::Data(..) | Atom::Builtin(..) => 3,
            });
            for atom in &rule.head {
                let Atom::Role(role, source_term, target_term) = atom else {
                    continue;
                };
                // Work backwards from the only heads that could violate an
                // asserted =1 restriction. Pre-binding the head source avoids
                // enumerating the rule's unrelated named-ABox matches.
                for (source, exact_role) in &self.exact_one_roles {
                    if exact_role != role {
                        continue;
                    }
                    let mut seed = HashMap::new();
                    if !bind(source_term, source, &mut seed) {
                        continue;
                    }
                    let mut substitutions = vec![seed];
                    for body_atom in &body {
                        let mut next = Vec::new();
                        for subst in substitutions {
                            self.extend_match(body_atom, &subst, &mut next);
                        }
                        substitutions = next;
                        if substitutions.is_empty() {
                            break;
                        }
                    }
                    for subst in substitutions {
                        let Some(target) = resolve(target_term, &subst) else {
                            continue;
                        };
                        if self.role_assertions.iter().any(|(r, s, old_target)| {
                            r == role && s == source && self.known_different(old_target, target)
                        }) {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    fn extend_match(
        &self,
        atom: &Atom,
        subst: &HashMap<String, String>,
        out: &mut Vec<HashMap<String, String>>,
    ) {
        match atom {
            Atom::Class(concept, term) => {
                for (individual, asserted) in &self.class_assertions {
                    if asserted == concept {
                        let mut candidate = subst.clone();
                        if bind(term, individual, &mut candidate) {
                            out.push(candidate);
                        }
                    }
                }
            }
            Atom::Role(role, source, target) => {
                for (asserted, left, right) in &self.role_assertions {
                    if asserted == role {
                        let mut candidate = subst.clone();
                        if bind(source, left, &mut candidate) && bind(target, right, &mut candidate)
                        {
                            out.push(candidate);
                        }
                    }
                }
            }
            Atom::Same(left, right) => {
                if let (Some(left), Some(right)) = (resolve(left, subst), resolve(right, subst)) {
                    if left == right {
                        out.push(subst.clone());
                    }
                }
            }
            Atom::Diff(left, right) => {
                if let (Some(left), Some(right)) = (resolve(left, subst), resolve(right, subst)) {
                    if self.known_different(left, right) {
                        out.push(subst.clone());
                    }
                }
            }
            Atom::Data(..) | Atom::Builtin(..) => {}
        }
    }

    fn known_different(&self, left: &str, right: &str) -> bool {
        if left == right {
            return false;
        }
        if self
            .different_individuals
            .contains(&ordered_pair(left, right))
        {
            return true;
        }
        let left_types: Vec<_> = self
            .class_assertions
            .iter()
            .filter(|(individual, _)| individual == left)
            .map(|(_, class)| class.as_str())
            .collect();
        let right_types: Vec<_> = self
            .class_assertions
            .iter()
            .filter(|(individual, _)| individual == right)
            .map(|(_, class)| class.as_str())
            .collect();
        left_types.iter().any(|left_class| {
            right_types.iter().any(|right_class| {
                self.disjoint_classes
                    .contains(&ordered_pair(left_class, right_class))
            })
        })
    }

    fn legacy_meta_rule_is_subsumed(&self, rule: &Rule) -> bool {
        const HAS_CLASS: &str =
            "<http://swrl.stanford.edu/ontologies/built-ins/3.3/abox.owl#hasClass>";
        const IS_SUBCLASS: &str =
            "<http://swrl.stanford.edu/ontologies/built-ins/3.3/tbox.owl#isSubClassOf>";
        let mut has_class = Vec::new();
        let mut subclass = None;
        for atom in &rule.body {
            match atom {
                Atom::Builtin(name, args) if name == HAS_CLASS && args.len() == 2 => {
                    has_class.push((args[0].clone(), args[1].clone()))
                }
                Atom::Builtin(name, args) if name == IS_SUBCLASS && args.len() == 2 => {
                    if subclass
                        .replace((args[0].clone(), args[1].clone()))
                        .is_some()
                    {
                        return false;
                    }
                }
                Atom::Builtin(..) => return false,
                _ => {}
            }
        }
        if has_class.len() != 2 {
            return false;
        }
        let Some((sub_var, sup_var)) = subclass else {
            return false;
        };
        let Some((left, _)) = has_class.iter().find(|(_, c)| *c == sub_var) else {
            return false;
        };
        let Some((right, _)) = has_class.iter().find(|(_, c)| *c == sup_var) else {
            return false;
        };
        if !matches!(left, Term::Var(_)) || !matches!(right, Term::Var(_)) {
            return false;
        }
        let left_targets = self.role_targets(rule, left);
        let right_targets = self.role_targets(rule, right);
        if left_targets.is_empty() || right_targets.is_empty() {
            return false;
        }

        let mut types: HashMap<&str, Vec<&str>> = HashMap::new();
        for (i, c) in &self.class_assertions {
            types.entry(i).or_default().push(c);
        }
        let supers = self.superclass_closure();
        let mut witnessed = false;
        for l in &left_targets {
            for r in &right_targets {
                for lc in types.get(l.as_str()).into_iter().flatten() {
                    for rc in types.get(r.as_str()).into_iter().flatten() {
                        if supers.get(*lc).is_some_and(|s| s.contains(*rc)) {
                            witnessed = true;
                            if l != r {
                                return false;
                            }
                        }
                    }
                }
            }
        }
        if !witnessed {
            return true;
        }
        self.rules.iter().any(|candidate| {
            !candidate
                .body
                .iter()
                .any(|a| matches!(a, Atom::Builtin(..) | Atom::Data(..)))
                && same_rule_after_identifying(rule, candidate, left, right)
        })
    }

    fn role_targets(&self, rule: &Rule, wanted: &Term) -> HashSet<String> {
        let roles: HashSet<&str> = rule
            .body
            .iter()
            .filter_map(|a| match a {
                Atom::Role(role, _, target) if target == wanted => Some(role.as_str()),
                _ => None,
            })
            .collect();
        self.role_assertions
            .iter()
            .filter(|(r, _, _)| roles.contains(r.as_str()))
            .map(|(_, _, t)| t.clone())
            .collect()
    }

    fn superclass_closure(&self) -> HashMap<&str, HashSet<&str>> {
        let mut direct: HashMap<&str, Vec<&str>> = HashMap::new();
        for (sub, sup) in &self.named_subclasses {
            direct.entry(sub).or_default().push(sup);
        }
        let mut result = HashMap::new();
        for start in direct.keys().copied() {
            let mut seen = HashSet::new();
            let mut queue: VecDeque<_> = direct.get(start).into_iter().flatten().copied().collect();
            while let Some(next) = queue.pop_front() {
                if seen.insert(next) {
                    queue.extend(direct.get(next).into_iter().flatten().copied());
                }
            }
            result.insert(start, seen);
        }
        result
    }
}

fn ordered_pair(left: &str, right: &str) -> (String, String) {
    if left <= right {
        (left.to_string(), right.to_string())
    } else {
        (right.to_string(), left.to_string())
    }
}

fn resolve<'a>(term: &'a Term, subst: &'a HashMap<String, String>) -> Option<&'a str> {
    match term {
        Term::Ind(individual) => Some(individual),
        Term::Var(variable) => subst.get(variable).map(String::as_str),
    }
}

fn bind(term: &Term, value: &str, subst: &mut HashMap<String, String>) -> bool {
    match term {
        Term::Ind(individual) => individual == value,
        Term::Var(variable) => match subst.get(variable) {
            Some(bound) => bound == value,
            None => {
                subst.insert(variable.clone(), value.to_string());
                true
            }
        },
    }
}

fn same_rule_after_identifying(source: &Rule, candidate: &Rule, left: &Term, right: &Term) -> bool {
    fn rw(t: &Term, l: &Term, r: &Term) -> Term {
        if t == l || t == r {
            Term::Var("__KM_IDENTIFIED__".into())
        } else {
            t.clone()
        }
    }
    fn atom(a: &Atom, l: &Term, r: &Term) -> Option<Atom> {
        Some(match a {
            Atom::Class(c, t) => Atom::Class(c.clone(), rw(t, l, r)),
            Atom::Role(p, s, t) => Atom::Role(p.clone(), rw(s, l, r), rw(t, l, r)),
            Atom::Same(x, y) => Atom::Same(rw(x, l, r), rw(y, l, r)),
            Atom::Diff(x, y) => Atom::Diff(rw(x, l, r), rw(y, l, r)),
            Atom::Data(..) | Atom::Builtin(..) => return None,
        })
    }
    fn set(v: &[Atom], l: &Term, r: &Term) -> Option<HashSet<Atom>> {
        let mut out = HashSet::new();
        for value in v {
            if matches!(value, Atom::Builtin(..)) {
                continue;
            }
            out.insert(atom(value, l, r)?);
        }
        Some(out)
    }
    let join = candidate
        .body
        .iter()
        .filter_map(|a| match a {
            Atom::Role(_, _, t) => Some(t),
            _ => None,
        })
        .find(|t| {
            candidate
                .body
                .iter()
                .filter(|a| matches!(a, Atom::Role(_, _, x) if x == *t))
                .count()
                >= 2
        })
        .cloned();
    let Some(join) = join else { return false };
    set(&source.body, left, right) == set(&candidate.body, &join, &join)
        && set(&source.head, left, right) == set(&candidate.head, &join, &join)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::{iri::IriRegistry, parse};

    fn certified(text: &str) -> u64 {
        let mut scan = RuleCertificateScan::default();
        let mut registry = IriRegistry::new();
        parse::parse_axioms_observed(&mut registry, text, |node| scan.observe(node))
            .expect("synthetic functional syntax");
        scan.certified_unsupported_rules()
    }

    fn inconsistent(text: &str) -> bool {
        let mut scan = RuleCertificateScan::default();
        let mut registry = IriRegistry::new();
        parse::parse_axioms_observed(&mut registry, text, |node| scan.observe(node))
            .expect("synthetic functional syntax");
        scan.certified_inconsistent()
    }

    const RULE_CLASH: &str = r#"
        ClassAssertion(ObjectExactCardinality(1 <r>) <s>)
        ObjectPropertyAssertion(<r> <s> <old>)
        DifferentIndividuals(<old> <new>)
        ClassAssertion(<Situation> <s>)
        ObjectPropertyAssertion(<requestor> <s> <d>)
        ClassAssertion(<Requestor> <d>)
        ObjectPropertyAssertion(<department> <d> <w1>)
        ClassAssertion(<Hospital> <w1>)
        ObjectPropertyAssertion(<patient> <s> <p>)
        ClassAssertion(<Patient> <p>)
        ObjectPropertyAssertion(<clinic> <p> <w2>)
        ClassAssertion(<Clinic> <w2>)
        DisjointClasses(<Hospital> <Clinic>)
        DLSafeRule(
          Body(
            ClassAtom(<Situation> Variable(<s>))
            ObjectPropertyAtom(<requestor> Variable(<s>) Variable(<d>))
            ClassAtom(<Requestor> Variable(<d>))
            ObjectPropertyAtom(<department> Variable(<d>) Variable(<w1>))
            ClassAtom(<Hospital> Variable(<w1>))
            ObjectPropertyAtom(<patient> Variable(<s>) Variable(<p>))
            ClassAtom(<Patient> Variable(<p>))
            ObjectPropertyAtom(<clinic> Variable(<p>) Variable(<w2>))
            ClassAtom(<Clinic> Variable(<w2>))
            DifferentIndividualsAtom(Variable(<w1>) Variable(<w2>))
          )
          Head(ObjectPropertyAtom(<r> Variable(<s>) <new>))
        )
    "#;

    #[test]
    fn exact_one_rule_witness_certifies_inconsistency() {
        assert!(inconsistent(&format!("Ontology({RULE_CLASH})")));
    }

    #[test]
    fn exact_one_rule_witness_fails_closed_when_any_essential_part_is_absent() {
        let controls = [
            RULE_CLASH.replace(
                "ObjectExactCardinality(1 <r>)",
                "ObjectExactCardinality(2 <r>)",
            ),
            RULE_CLASH.replace(
                "ObjectExactCardinality(1 <r>)",
                "ObjectExactCardinality(1 <r> <Filler>)",
            ),
            RULE_CLASH.replace("DifferentIndividuals(<old> <new>)", ""),
            RULE_CLASH.replace("DisjointClasses(<Hospital> <Clinic>)", ""),
            RULE_CLASH.replace("ClassAssertion(<Patient> <p>)", ""),
            RULE_CLASH.replace(
                "Head(ObjectPropertyAtom(<r> Variable(<s>) <new>))",
                "Head(ClassAtom(<Situation> Variable(<s>)))",
            ),
        ];
        for control in controls {
            assert!(!inconsistent(&format!("Ontology({control})")));
        }
    }

    #[test]
    fn empty_data_relation_certifies_rule_but_assertion_revokes_it() {
        let rule = "DLSafeRule(Body(DataPropertyAtom(<p> Variable(<x>) Variable(<v>))) Head(ClassAtom(<C> Variable(<x>))))";
        assert_eq!(certified(&format!("Ontology({rule})")), 1);
        assert_eq!(
            certified(&format!(
                "Ontology(DataPropertyAssertion(<p> <a> \"1\") {rule})"
            )),
            0
        );
    }

    #[test]
    fn legacy_type_join_requires_a_subsuming_same_individual_rule() {
        let meta = "DLSafeRule(Body(ObjectPropertyAtom(<left> Variable(<t>) Variable(<e1>)) ObjectPropertyAtom(<right> Variable(<l>) Variable(<e2>)) BuiltInAtom(<http://swrl.stanford.edu/ontologies/built-ins/3.3/abox.owl#hasClass> Variable(<e1>) Variable(<h1>)) BuiltInAtom(<http://swrl.stanford.edu/ontologies/built-ins/3.3/abox.owl#hasClass> Variable(<e2>) Variable(<h2>)) BuiltInAtom(<http://swrl.stanford.edu/ontologies/built-ins/3.3/tbox.owl#isSubClassOf> Variable(<h1>) Variable(<h2>))) Head(ObjectPropertyAtom(<out> Variable(<t>) <answer>)))";
        let ordinary = "DLSafeRule(Body(ObjectPropertyAtom(<left> Variable(<t>) Variable(<e>)) ObjectPropertyAtom(<right> Variable(<l>) Variable(<e>))) Head(ObjectPropertyAtom(<out> Variable(<t>) <answer>)))";
        let shared = "ClassAssertion(<A> <section>) ClassAssertion(<B> <section>) SubClassOf(<A> <B>) ObjectPropertyAssertion(<left> <task> <section>) ObjectPropertyAssertion(<right> <auth> <section>)";
        assert_eq!(
            certified(&format!("Ontology({shared} {meta} {ordinary})")),
            1
        );

        let split = "ClassAssertion(<A> <section1>) ClassAssertion(<B> <section2>) SubClassOf(<A> <B>) ObjectPropertyAssertion(<left> <task> <section1>) ObjectPropertyAssertion(<right> <auth> <section2>)";
        assert_eq!(
            certified(&format!("Ontology({split} {meta} {ordinary})")),
            0
        );
    }
}
