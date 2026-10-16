//! Stateless global named-class consequences of exact NEW role axioms.
//! This is a narrow proof preparer, not source admission or classification.
use std::collections::{BTreeMap, BTreeSet};
use crate::frontend::sexpr::{Node, Parser};
use crate::source_locality::{fingerprint, Scan};

const MAX_SOURCE_BYTES: usize = 4 << 20;
const MAX_STATEMENTS: usize = 100_000;
const MAX_NODE_BYTES: usize = 32_768;
const MAX_LISTS: usize = 256;
const MAX_IRI_BYTES: usize = 4_096;
const MAX_ROLES: usize = 4_096;
const MAX_EDGES: usize = 16_384;
const MAX_GLOBALS: usize = 4_096;
const MAX_WORK: usize = 250_000;

fn named(node: &Node<'_>, prefixes: &BTreeMap<String, String>) -> Option<String> {
    let raw = node.as_atom()?;
    if raw.len() > MAX_IRI_BYTES || raw.starts_with("_:") || raw.starts_with('"') || raw.contains('\\') {
        return None;
    }
    if let Some(full) = raw.strip_prefix('<').and_then(|s| s.strip_suffix('>')) {
        return (!full.is_empty() && full.contains(':')).then(|| full.to_owned());
    }
    let (prefix, local) = raw.split_once(':')?;
    let base = prefixes.get(&format!("{prefix}:"))?;
    if local.is_empty() || base.len().checked_add(local.len())? > MAX_IRI_BYTES { return None; }
    Some(format!("{base}{local}"))
}

/// Every returned IRI denotes the whole class domain in actual NEW:
/// reflexivity propagates to named superroles, and either named domain or
/// range of such a role contains every element. Unsupported expressions skip.
/// Bounds/collisions return None, leaving ordinary classification available.
pub(crate) fn global_named_classes(text: &str, scan: &Scan) -> Option<Vec<String>> {
    if text.len() > MAX_SOURCE_BYTES || scan.statements.len() > MAX_STATEMENTS { return None; }
    let mut prefixes: BTreeMap<String, String> = [
        ("owl:", "http://www.w3.org/2002/07/owl#"), ("rdf:", "http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
        ("rdfs:", "http://www.w3.org/2000/01/rdf-schema#"), ("xsd:", "http://www.w3.org/2001/XMLSchema#"),
    ].into_iter().map(|(a,b)| (a.into(), b.into())).collect();
    let mut seen_prefixes = BTreeSet::new();
    for (prefix, iri) in &scan.prefixes {
        if !seen_prefixes.insert(prefix) { return None; }
        prefixes.insert(prefix.clone(), iri.clone());
    }
    let mut originals = BTreeMap::new();
    let mut roles = BTreeSet::new();
    let mut reflexive = BTreeSet::new();
    let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut constraints = Vec::new();
    let mut records = 0;
    for statement in &scan.statements {
        let slice = text.get(statement.start..statement.end)?;
        if fingerprint(slice.as_bytes()) != statement.hash { return None; }
        if originals.insert(statement.hash, slice).is_some_and(|old| old != slice) { return None; }
        // Binding checks above are linear in already-owned source bytes;
        // only bounded ASCII statements enter the legacy byte parser.
        if !slice.is_ascii() || slice.len() > MAX_NODE_BYTES
            || slice.bytes().filter(|b| *b == b'(').count() > MAX_LISTS { continue; }
        let mut parser = Parser::new(slice);
        if !matches!(parser.peek(), Some("ReflexiveObjectProperty" | "SubObjectPropertyOf"
            | "ObjectPropertyDomain" | "ObjectPropertyRange")) { continue; }
        let Ok(Node::List(head, args)) = parser.parse() else { continue; };
        if parser.peek().is_some() { continue; }
        match (head, args.as_slice()) {
            ("ReflexiveObjectProperty", [role]) => {
                if let Some(role) = named(role, &prefixes) {
                    roles.insert(role.clone()); reflexive.insert(role); records += 1;
                }
            },
            ("SubObjectPropertyOf", [left, right]) => {
                if let (Some(left), Some(right)) = (named(left, &prefixes), named(right, &prefixes)) {
                    roles.insert(left.clone()); roles.insert(right.clone());
                    edges.entry(left).or_default().insert(right); records += 1;
                }
            },
            ("ObjectPropertyDomain" | "ObjectPropertyRange", [role, class]) => {
                if let (Some(role), Some(class)) = (named(role, &prefixes), named(class, &prefixes)) {
                    roles.insert(role.clone()); constraints.push((role, class)); records += 1;
                }
            },
            _ => {},
        }
        if roles.len() > MAX_ROLES || records > MAX_EDGES { return None; }
    }
    let mut work = MAX_WORK;
    let mut queue: Vec<_> = reflexive.iter().cloned().collect();
    while let Some(role) = queue.pop() {
        work = work.checked_sub(1)?;
        for next in edges.get(&role).into_iter().flatten() {
            work = work.checked_sub(1)?;
            if reflexive.insert(next.clone()) { queue.push(next.clone()); }
        }
    }
    let mut globals = BTreeSet::new();
    for (role, class) in constraints {
        work = work.checked_sub(1)?;
        if reflexive.contains(&role) { globals.insert(class); }
        if globals.len() > MAX_GLOBALS { return None; }
    }
    Some(globals.into_iter().collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn globals(body: &str) -> Option<Vec<String>> {
        let text = format!("Prefix(:=<urn:global#>) Ontology({body})");
        let scan = crate::source_locality::scan(&text).unwrap();
        global_named_classes(&text, &scan)
    }
    #[test] fn reflexive_hierarchy_named_domain_and_range_follow_actual_new() {
        let source="ReflexiveObjectProperty(:r) SubObjectPropertyOf(:r :s) SubObjectPropertyOf(:s :t) ObjectPropertyRange(:r :A) ObjectPropertyDomain(:s :B) ObjectPropertyRange(:t :C)";
        assert_eq!(globals(source).unwrap(), vec!["urn:global#A", "urn:global#B", "urn:global#C"]);
        assert!(globals(&source.replace("ReflexiveObjectProperty(:r)", "")).unwrap().is_empty());
        assert_eq!(globals(&source.replace("SubObjectPropertyOf(:r :s)", "")).unwrap(), vec!["urn:global#A"]);
        assert_eq!(globals(&source.replace("ObjectPropertyRange(:t :C)", "")).unwrap(), vec!["urn:global#A", "urn:global#B"]);
    }
    #[test] fn aliases_and_cycles_resolve_without_spelling_identity_assumptions() {
        assert_eq!(globals("ReflexiveObjectProperty(:r) SubObjectPropertyOf(<urn:global#r> :s) SubObjectPropertyOf(:s :r) ObjectPropertyDomain(<urn:global#s> :A)").unwrap(),vec!["urn:global#A"]);
        assert!(globals("ReflexiveObjectProperty(:r) ObjectPropertyRange(:other :A)").unwrap().is_empty());
    }
    #[test] fn assertions_una_unions_inverses_and_data_do_not_supply_global_seeds() {
        for body in [
            "ObjectPropertyAssertion(:r :a :b) ObjectPropertyRange(:r :A)",
            "DifferentIndividuals(:a :b) ObjectPropertyDomain(:r :A)",
            "ReflexiveObjectProperty(:r) ObjectPropertyDomain(:r ObjectUnionOf(:A :B))",
            "ReflexiveObjectProperty(:r) ObjectPropertyRange(:r ObjectIntersectionOf(:A :B))",
            "ReflexiveObjectProperty(ObjectInverseOf(:r)) ObjectPropertyDomain(:r :A)",
            "ReflexiveObjectProperty(:r) SubObjectPropertyOf(ObjectPropertyChain(:r :r) :s) ObjectPropertyDomain(:s :A)",
            "ReflexiveObjectProperty(:r) DataPropertyRange(:r :A)",
        ] { assert!(globals(body).unwrap().is_empty(),"{body}"); }
    }
    #[test] fn source_collision_prefix_ambiguity_and_parser_bounds_decline() {
        let text="Prefix(:=<urn:global#>) Ontology(ReflexiveObjectProperty(:r) ObjectPropertyRange(:r :A))";
        let mut scan=crate::source_locality::scan(text).unwrap();
        scan.statements[0].hash=scan.statements[1].hash;
        assert!(global_named_classes(text,&scan).is_none());
        let duplicate="Prefix(:=<urn:a#>) Prefix(:=<urn:b#>) Ontology(ReflexiveObjectProperty(:r) ObjectPropertyRange(:r :A))";
        assert!(global_named_classes(duplicate,&crate::source_locality::scan(duplicate).unwrap()).is_none());
        assert!(globals("ReflexiveObjectProperty(:\u{120}) ObjectPropertyRange(:r :A)").unwrap().is_empty());
        let deep=format!("ReflexiveObjectProperty(:r) ObjectPropertyRange(:r {}:A{})","ObjectIntersectionOf(:A ".repeat(300),")".repeat(300));
        assert!(globals(&deep).unwrap().is_empty());
        let oversized=format!("ObjectPropertyRange(:r :{})","A".repeat(MAX_NODE_BYTES));
        assert!(globals(&oversized).unwrap().is_empty());
        let many=(0..=MAX_ROLES).map(|i|format!("ReflexiveObjectProperty(:r{i})")).collect::<String>();
        assert!(globals(&many).is_none());
    }
    #[test] fn aggregate_source_cap_declines_before_optional_preparation() {
        let text = format!("Ontology({})", " ".repeat(MAX_SOURCE_BYTES));
        let scan = crate::source_locality::scan(&text).unwrap();
        assert!(global_named_classes(&text, &scan).is_none());
    }
}
