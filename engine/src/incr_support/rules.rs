//! Bounded source-support proposals for a single explicit rule/role clash.
//!
//! This is not a rule engine or an inconsistency certificate. The caller must
//! classify the exact proposed source subset before retaining any support.
use std::collections::{BTreeMap, BTreeSet};

use crate::frontend::sexpr::{Node, Parser};
use crate::source_locality::{fingerprint, Scan};

const MAX_STATEMENTS: usize = 100_000;
const MAX_SOURCE_BYTES: usize = 8 << 20;
const MAX_RECORDS: usize = 50_000;
const MAX_RULES: usize = 128;
const MAX_BODY: usize = 24;
const MAX_STATES: usize = 4_096;
const MAX_WORK: usize = 250_000;
const MAX_NODE_BYTES: usize = 32_768;
const MAX_LISTS: usize = 256;

type Support = BTreeSet<u128>;

#[derive(Clone, Debug)]
enum Term {
    Variable(String),
    Individual(String),
}

#[derive(Clone, Debug)]
enum Atom {
    Class(String, Term),
    Role(String, Term, Term),
    Different(Term, Term),
}

impl Atom {
    fn terms(&self) -> Vec<&Term> {
        match self {
            Self::Class(_, a) => vec![a],
            Self::Role(_, a, b) | Self::Different(a, b) => vec![a, b],
        }
    }
}

struct Rule {
    body: Vec<Atom>,
    head: Atom,
    hash: u128,
}

#[derive(Default)]
struct Facts {
    classes: BTreeMap<String, Vec<(String, u128)>>,
    types: BTreeMap<String, Vec<(String, u128)>>,
    roles: BTreeMap<String, Vec<(String, String, u128)>>,
    different: BTreeMap<(String, String), u128>,
    disjoint: BTreeMap<(String, String), u128>,
    at_most_one: BTreeMap<(String, String), u128>,
    functional: BTreeMap<String, u128>,
    rules: Vec<Rule>,
    records: usize,
}

fn pair(a: &str, b: &str) -> (String, String) {
    if a <= b { (a.into(), b.into()) } else { (b.into(), a.into()) }
}

fn iri(raw: &str, prefixes: &BTreeMap<String, String>) -> Option<String> {
    // Optional proposal only: do not reinterpret blank labels, literals,
    // escaped local names or unsupported relative names.
    if raw.starts_with("_:") || raw.contains('\\') || raw.starts_with('"') {
        return None;
    }
    if let Some(full) = raw.strip_prefix('<').and_then(|x| x.strip_suffix('>')) {
        return (!full.is_empty() && full.contains(':')).then(|| full.to_owned());
    }
    let (prefix, local) = raw.split_once(':')?;
    let base = prefixes.get(&format!("{prefix}:"))?;
    (!local.is_empty()).then(|| format!("{base}{local}"))
}

fn named(node: &Node<'_>, prefixes: &BTreeMap<String, String>) -> Option<String> {
    iri(node.as_atom()?, prefixes)
}

fn term(node: &Node<'_>, prefixes: &BTreeMap<String, String>) -> Option<Term> {
    match node {
        Node::Atom(_) => Some(Term::Individual(named(node, prefixes)?)),
        Node::List("Variable", args) if args.len() == 1 =>
            Some(Term::Variable(named(&args[0], prefixes)?)),
        _ => None,
    }
}

fn atom(node: &Node<'_>, prefixes: &BTreeMap<String, String>) -> Option<Atom> {
    match node {
        Node::List("ClassAtom", args) if args.len() == 2 =>
            Some(Atom::Class(named(&args[0], prefixes)?, term(&args[1], prefixes)?)),
        Node::List("ObjectPropertyAtom", args) if args.len() == 3 =>
            Some(Atom::Role(named(&args[0], prefixes)?, term(&args[1], prefixes)?, term(&args[2], prefixes)?)),
        Node::List("DifferentIndividualsAtom", args) if args.len() == 2 =>
            Some(Atom::Different(term(&args[0], prefixes)?, term(&args[1], prefixes)?)),
        _ => None,
    }
}

fn args_without_annotations<'n, 's>(args: &'n [Node<'s>]) -> Vec<&'n Node<'s>> {
    args.iter().filter(|arg| arg.head() != Some("Annotation")).collect()
}

impl Facts {
    fn collect(&mut self, node: &Node<'_>, hash: u128,
               prefixes: &BTreeMap<String, String>) -> Option<()> {
        let Node::List(head, children) = node else { return Some(()) };
        let args = args_without_annotations(children);
        match (*head, args.as_slice()) {
            ("ClassAssertion", [class, individual]) => {
                let Some(individual) = named(individual, prefixes) else { return Some(()) };
                if let Some(class) = named(class, prefixes) {
                    self.classes.entry(class.clone()).or_default().push((individual.clone(), hash));
                    self.types.entry(individual).or_default().push((class, hash));
                    self.records += 1;
                } else if let Node::List("ObjectMaxCardinality" | "ObjectExactCardinality", fields) = class {
                    // Qualified restrictions would need separate filler facts,
                    // except when the filler is owl:Thing.
                    let unqual_role = match fields.as_slice() {
                        [Node::Atom("1"), role] => Some(role),
                        [Node::Atom("1"), role, filler]
                            if named(filler, prefixes).as_deref()
                                == Some("http://www.w3.org/2002/07/owl#Thing") =>
                        {
                            Some(role)
                        }
                        _ => None,
                    };
                    if let Some(role) = unqual_role.and_then(|role| named(role, prefixes)) {
                        self.at_most_one.entry((role, individual)).or_insert(hash);
                        self.records += 1;
                    }
                }
            }
            ("ObjectPropertyAssertion", [role, subject, object]) => {
                if let (Some(role), Some(subject), Some(object)) =
                    (named(role, prefixes), named(subject, prefixes), named(object, prefixes)) {
                    self.roles.entry(role).or_default().push((subject, object, hash));
                    self.records += 1;
                }
            }
            ("FunctionalObjectProperty", [role]) => {
                if let Some(role) = named(role, prefixes) {
                    self.functional.entry(role).or_insert(hash);
                    self.records += 1;
                }
            }
            ("DifferentIndividuals" | "DisjointClasses", items) if (2..=64).contains(&items.len()) => {
                let names: Option<Vec<_>> = items.iter().map(|node| named(node, prefixes)).collect();
                if let Some(names) = names {
                    let table = if *head == "DifferentIndividuals" { &mut self.different } else { &mut self.disjoint };
                    for i in 0..names.len() {
                        for j in i + 1..names.len() {
                            table.entry(pair(&names[i], &names[j])).or_insert(hash);
                            self.records += 1;
                        }
                    }
                }
            }
            ("DLSafeRule", [Node::List("Body", body), Node::List("Head", head)])
                if !body.is_empty() && body.len() <= MAX_BODY && head.len() == 1 => {
                let body: Option<Vec<_>> = body.iter().map(|node| atom(node, prefixes)).collect();
                let head = atom(&head[0], prefixes);
                if let (Some(body), Some(head @ Atom::Role(..))) = (body, head) {
                    if self.rules.len() >= MAX_RULES { return None; }
                    self.rules.push(Rule { body, head, hash });
                }
            }
            _ => {}
        }
        (self.records <= MAX_RECORDS).then_some(())
    }

    fn count(&self, atom: &Atom) -> usize {
        match atom {
            Atom::Class(class, _) => self.classes.get(class).map_or(0, Vec::len),
            Atom::Role(role, _, _) => self.roles.get(role).map_or(0, Vec::len),
            Atom::Different(..) => 0,
        }
    }

    fn difference(&self, left: &str, right: &str, work: &mut usize) -> Option<Support> {
        if let Some(hash) = self.different.get(&pair(left, right)) {
            return Some([*hash].into_iter().collect());
        }
        for (a, ah) in self.types.get(left)? {
            for (b, bh) in self.types.get(right)? {
                spend(work)?;
                if let Some(disjoint) = self.disjoint.get(&pair(a, b)) {
                    return Some([*ah, *bh, *disjoint].into_iter().collect());
                }
            }
        }
        None
    }
}

#[derive(Clone, Default)]
struct State {
    bindings: BTreeMap<String, String>,
    support: Support,
}

fn spend(work: &mut usize) -> Option<()> {
    *work = work.checked_sub(1)?;
    Some(())
}

fn value<'s>(term: &'s Term, state: &'s State) -> Option<&'s str> {
    match term {
        Term::Individual(name) => Some(name),
        Term::Variable(name) => state.bindings.get(name).map(String::as_str),
    }
}

fn bind(term: &Term, individual: &str, state: &mut State) -> bool {
    match term {
        Term::Individual(name) => name == individual,
        Term::Variable(name) => match state.bindings.get(name) {
            Some(bound) => bound == individual,
            None => { state.bindings.insert(name.clone(), individual.to_owned()); true }
        },
    }
}

fn joins(facts: &Facts, rule: &Rule, work: &mut usize) -> Option<Vec<State>> {
    let mut pending: Vec<_> = rule.body.iter().enumerate()
        .filter(|(_, atom)| !matches!(atom, Atom::Different(..))).collect();
    if pending.is_empty() { return None; }
    let mut states = vec![State::default()];
    while !pending.is_empty() {
        // Prefer atoms already constrained by constants/bindings, then the
        // smallest indexed fact list. Avoid a blind class Cartesian product.
        let choice = pending.iter().enumerate().min_by_key(|(_, (i, atom))| {
            let bound = atom.terms().iter().filter(|term| value(term, &states[0]).is_some()).count();
            (std::cmp::Reverse(bound), facts.count(atom), *i)
        })?.0;
        let (_, atom) = pending.remove(choice);
        let mut next = Vec::new();
        for state in &states {
            match atom {
                Atom::Class(class, arg) => {
                    for (individual, hash) in facts.classes.get(class)? {
                        spend(work)?;
                        let mut matched = state.clone();
                        if bind(arg, individual, &mut matched) {
                            matched.support.insert(*hash);
                            next.push(matched);
                            if next.len() > MAX_STATES { return None; }
                        }
                    }
                }
                Atom::Role(role, left, right) => {
                    for (a, b, hash) in facts.roles.get(role)? {
                        spend(work)?;
                        let mut matched = state.clone();
                        if bind(left, a, &mut matched) && bind(right, b, &mut matched) {
                            matched.support.insert(*hash);
                            next.push(matched);
                            if next.len() > MAX_STATES { return None; }
                        }
                    }
                }
                Atom::Different(..) => unreachable!(),
            }
        }
        if next.is_empty() { return Some(next); }
        states = next;
    }
    let mut matched = Vec::new();
    for mut state in states {
        let mut valid = true;
        for atom in &rule.body {
            if let Atom::Different(a, b) = atom {
                let proof = value(a, &state).zip(value(b, &state))
                    .and_then(|(a, b)| facts.difference(a, b, work));
                if let Some(proof) = proof { state.support.extend(proof); }
                else { valid = false; break; }
            }
        }
        if *work == 0 { return None; }
        if valid { matched.push(state); }
    }
    Some(matched)
}

/// Candidate hashes only. Caller must independently verify the exact subset.
pub(super) fn propose(text: &str, scan: &Scan) -> Option<Vec<u128>> {
    if text.len() > MAX_SOURCE_BYTES || scan.statements.len() > MAX_STATEMENTS { return None; }
    let mut prefixes: BTreeMap<String, String> = [
        ("owl:", "http://www.w3.org/2002/07/owl#"),
        ("rdf:", "http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
        ("rdfs:", "http://www.w3.org/2000/01/rdf-schema#"),
        ("xsd:", "http://www.w3.org/2001/XMLSchema#"),
    ].into_iter().map(|(a, b)| (a.to_owned(), b.to_owned())).collect();
    let mut declared_prefixes = BTreeSet::new();
    for (name, iri) in &scan.prefixes {
        if !declared_prefixes.insert(name) { return None; }
        prefixes.insert(name.clone(), iri.clone());
    }
    let mut facts = Facts::default();
    let mut source = BTreeMap::new();
    for statement in &scan.statements {
        let slice = text.get(statement.start..statement.end)?;
        if fingerprint(slice.as_bytes()) != statement.hash { return None; }
        if source.insert(statement.hash, slice).is_some_and(|old| old != slice) { return None; }
        // This optional source proposal declines unsupported Unicode tokens
        // rather than risking the legacy byte-based sexpr token boundary.
        if !slice.is_ascii() || slice.len() > MAX_NODE_BYTES
            || slice.bytes().filter(|b| *b == b'(').count() > MAX_LISTS { continue; }
        let mut parser = Parser::new(slice);
        let head = parser.peek()?;
        if !matches!(head, "ClassAssertion" | "ObjectPropertyAssertion" | "DifferentIndividuals"
            | "DisjointClasses" | "FunctionalObjectProperty" | "DLSafeRule") { continue; }
        let node = parser.parse().ok()?;
        if parser.peek().is_some() { return None; }
        facts.collect(&node, statement.hash, &prefixes)?;
    }
    let mut work = MAX_WORK;
    for rule in &facts.rules {
        let Some(states) = joins(&facts, rule, &mut work) else {
            if work == 0 { return None; }
            continue;
        };
        let Atom::Role(role, subject, object) = &rule.head else { continue };
        for state in states {
            let (Some(subject), Some(object)) = (value(subject, &state), value(object, &state)) else { continue };
            let Some(bound) = facts.at_most_one.get(&(role.clone(), subject.to_owned()))
                .or_else(|| facts.functional.get(role)) else { continue };
            for (source, existing, edge) in facts.roles.get(role).into_iter().flatten() {
                spend(&mut work)?;
                if source != subject { continue; }
                // The head conflict requires asserted inequality. Distinct
                // source spellings alone never imply distinct individuals.
                let Some(difference) = facts.different.get(&pair(existing, object)) else { continue };
                let mut support = state.support.clone();
                support.extend([rule.hash, *bound, *edge, *difference]);
                let mut seen = BTreeSet::new();
                return Some(scan.statements.iter().filter_map(|st|
                    (support.contains(&st.hash) && seen.insert(st.hash)).then_some(st.hash)).collect());
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source_locality::scan;

    fn fixture(extra: &str, body_difference: bool, functional: bool) -> String {
        let difference = if body_difference {
            "DifferentIndividualsAtom(Variable(:x) Variable(:y))"
        } else { "" };
        let bound = if functional { "FunctionalObjectProperty(:result)" }
            else { "ClassAssertion(ObjectExactCardinality(1 :result) :s)" };
        format!("Prefix(:=<urn:renamed#>) Ontology(\n\
            ClassAssertion(:Left :a)\nClassAssertion(:Right :b)\n\
            ObjectPropertyAssertion(:input :s :a)\nObjectPropertyAssertion(:other :s :b)\n\
            DisjointClasses(:Left :Right)\n\
            ObjectPropertyAssertion(:result :s :first)\n{bound}\n{extra}\n\
            DLSafeRule(Body(ObjectPropertyAtom(:input Variable(:s) Variable(:x))\n\
                ObjectPropertyAtom(:other Variable(:s) Variable(:y)) {difference})\n\
                Head(ObjectPropertyAtom(:result Variable(:s) :second)))\n)")
    }

    fn candidate(text: &str) -> Option<Vec<u128>> {
        propose(text, &scan(text).ok()?)
    }

    #[test]
    fn renamed_rule_role_conflict_collects_exact_disjointness_support() {
        let text = fixture("DifferentIndividuals(:first :second)", true, false);
        let hashes = candidate(&text).expect("bounded explicit join");
        let scanned = scan(&text).unwrap();
        let selected: Vec<_> = scanned.statements.iter().filter(|s| hashes.contains(&s.hash))
            .map(|s| &text[s.start..s.end]).collect();
        assert_eq!(selected.len(), 9);
        assert!(selected.iter().any(|s| s.starts_with("DisjointClasses")));
        assert!(selected.iter().any(|s| s.starts_with("ClassAssertion(:Left")));
        assert!(selected.iter().any(|s| s.starts_with("DLSafeRule")));
    }

    #[test]
    fn explicit_body_difference_and_functionality_are_supported() {
        let text = fixture("DifferentIndividuals(:a :b)\nDifferentIndividuals(:first :second)", true, true)
            .replace("DisjointClasses(:Left :Right)", "");
        assert!(candidate(&text).is_some());
    }

    #[test]
    fn absent_premise_and_no_unique_name_assumption_decline() {
        let text = fixture("DifferentIndividuals(:first :second)", true, false);
        assert!(candidate(&text.replace("ObjectPropertyAssertion(:other :s :b)", "")).is_none());
        assert!(candidate(&fixture("", true, false)).is_none());
        assert!(candidate(&text.replace("DisjointClasses(:Left :Right)", "")).is_none());
    }

    #[test]
    fn unsupported_qualified_cardinality_atoms_and_unbound_head_decline() {
        let text = fixture("DifferentIndividuals(:first :second)", false, false);
        assert!(candidate(&text.replace("ObjectExactCardinality(1 :result)", "ObjectExactCardinality(1 :result :Type)")).is_none());
        assert!(candidate(&text.replace("ObjectPropertyAtom(:other Variable(:s) Variable(:y))", "BuiltInAtom(:unknown Variable(:s))")).is_none());
        assert!(candidate(&text.replace("Head(ObjectPropertyAtom(:result Variable(:s) :second))", "Head(ObjectPropertyAtom(:result Variable(:unknown) :second))")).is_none());
        assert!(candidate("Ontology(ClassAssertion(:A))").is_none());
        assert!(candidate("Ontology(DLSafeRule(Body(").is_none());
    }
}
