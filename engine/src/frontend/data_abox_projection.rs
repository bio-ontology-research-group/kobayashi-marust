//! Exact elimination of an independent, positive data ABox.
//!
//! The object reduct retains every asserted value's inherited domain types and
//! every owner inequality forced by functionality. Conversely, extend any model
//! of this reduct with the asserted data edges and their superproperty closure.
//! Ranges hold by checked value membership; functionality holds because owners
//! carrying unequal values cannot coincide. No unique-name assumption is used.
use std::collections::{BTreeMap, BTreeSet};
use super::{datatypes, parse, sexpr::{Node, Parser}};

fn render(n: &Node<'_>) -> String {
    match n { Node::Atom(s) => s.to_string(), Node::List(h, a) =>
        format!("{h}({})", a.iter().map(render).collect::<Vec<_>>().join(" ")) }
}
fn iri(n: &Node<'_>) -> Result<String, String> {
    let s = n.as_atom().ok_or("expected named IRI")?;
    if !s.starts_with('<') || !s.ends_with('>') { return Err("projection requires expanded entity IRIs".into()); }
    if s == "<http://www.w3.org/2002/07/owl#topDataProperty>"
        || s == "<http://www.w3.org/2002/07/owl#bottomDataProperty>" {
        return Err("builtin data property cannot be projected".into());
    }
    Ok(s.into())
}
fn independent(n: &Node<'_>) -> bool {
    match n {
        Node::Atom(_) => true,
        Node::List("Annotation" | "AnnotationAssertion" | "Declaration", _) => true,
        Node::List(h, a) => !h.contains("Data") && !matches!(*h, "HasKey" | "DLSafeRule" | "Import")
            && a.iter().all(independent),
    }
}
fn range(n: &Node<'_>) -> Result<String, String> {
    match n {
        Node::Atom(s) => Ok(format!("__dt__{}", datatypes::datatype_concept_key(s))),
        Node::List("DataOneOf", _) => {
            let key = format!("__dt__c__{}", render(n));
            datatypes::bridge_exact_finite_values(&key).ok_or("finite range has an inexact literal")?;
            Ok(key)
        },
        _ => Err("data range has no projection membership checker".into()),
    }
}

pub fn project(text: &str) -> Result<String, String> {
    if text.len() > 4 * 1024 * 1024 { return Err("data ABox projection size bound".into()); }
    let mut parser = Parser::new(text);
    let mut prefixes = Vec::new();
    let mut children = None;
    while parser.peek().is_some() {
        let node = parser.parse()?;
        match node {
            Node::List("Prefix", ref args) => {
                // Datatype helpers recognize standard abbreviations. A source
                // must never rebind those abbreviations to a custom datatype.
                let body = args.iter().map(render).collect::<String>();
                for (prefix, ns) in [("xsd:", "http://www.w3.org/2001/XMLSchema#"),
                    ("rdf:", "http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
                    ("rdfs:", "http://www.w3.org/2000/01/rdf-schema#")] {
                    if body.starts_with(prefix) && body != format!("{prefix}=<{ns}>") {
                        return Err("rebound standard datatype prefix".into());
                    }
                }
                prefixes.push(render(&node));
            }
            Node::List("Ontology", args) if children.is_none() => children = Some(args),
            _ => return Err("expected one ontology with prefix declarations".into()),
        }
    }
    let children = children.ok_or("missing ontology")?;
    let mut retained = Vec::new();
    let mut already_asserted = BTreeSet::new();
    let mut supers: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut domains: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut ranges: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut functional = BTreeSet::new();
    let mut assertions = Vec::new();
    for n in &children {
        let Node::List(head, args) = n else { retained.push(render(n)); continue; };
        let a = parse::strip_annotations(args);
        if *head == "ClassAssertion" && a.len() == 2 {
            already_asserted.insert(format!("ClassAssertion({} {})", render(&a[0]), render(&a[1])));
        }
        if *head == "DifferentIndividuals" {
            for (i, left) in a.iter().enumerate() {
                for right in &a[i+1..] {
                    let (left, right) = (render(left), render(right));
                    let (left, right) = if left <= right { (left,right) } else { (right,left) };
                    already_asserted.insert(format!("DifferentIndividuals({left} {right})"));
                }
            }
        }
        match *head {
            "DataPropertyAssertion" => {
                if a.len() < 3 { return Err("malformed data assertion".into()); }
                let (literal, used) = parse::glue_literal(&a, 2).ok_or("missing data value")?;
                if a.len() != 2 + used || !datatypes::bridge_exact_atomic_name(&format!("__dt__val__{literal}")) {
                    return Err("data value has no exact projection interpretation".into());
                }
                assertions.push((iri(&a[0])?, iri(&a[1])?, literal));
            }
            "DataPropertyDomain" if a.len() == 2 => domains.entry(iri(&a[0])?).or_default().push(iri(&a[1])?),
            "DataPropertyRange" if a.len() == 2 => ranges.entry(iri(&a[0])?).or_default().push(range(&a[1])?),
            "SubDataPropertyOf" if a.len() == 2 => supers.entry(iri(&a[0])?).or_default().push(iri(&a[1])?),
            "FunctionalDataProperty" if a.len() == 1 => { functional.insert(iri(&a[0])?); }
            _ if independent(n) => retained.push(render(n)),
            _ => return Err(format!("data ABox is coupled through {head}")),
        }
    }
    if assertions.is_empty() || assertions.len() > 256 { return Err("projection assertion bound".into()); }
    let mut generated = BTreeSet::new();
    let mut values: BTreeMap<String, Vec<(String, String)>> = BTreeMap::new();
    for (property, owner, literal) in assertions {
        let mut pending = vec![property];
        let mut seen = BTreeSet::new();
        while let Some(property) = pending.pop() {
            if !seen.insert(property.clone()) { continue; }
            if let Some(parents) = supers.get(&property) { pending.extend(parents.iter().cloned()); }
            for domain in domains.get(&property).into_iter().flatten() {
                generated.insert(format!("ClassAssertion({domain} {owner})"));
            }
            for range in ranges.get(&property).into_iter().flatten() {
                let truth = datatypes::finite_literal_datatype_truth(&literal, &[range.clone()])
                    .ok_or("undecided data range membership")?;
                if !truth[0] { generated.insert(format!("ClassAssertion(<http://www.w3.org/2002/07/owl#Nothing> {owner})")); }
            }
            if functional.contains(&property) {
                values.entry(property).or_default().push((owner.clone(), literal.clone()));
            }
        }
    }
    for group in values.values() {
        for (i, (a, left)) in group.iter().enumerate() {
            for (b, right) in &group[i+1..] {
                match datatypes::bridge_exact_value_equal(&format!("__dt__val__{left}"), &format!("__dt__val__{right}")) {
                    Some(true) => {},
                    Some(false) => { let (a,b) = if a <= b { (a,b) } else { (b,a) };
                        generated.insert(format!("DifferentIndividuals({a} {b})")); },
                    None => return Err("undecided functional value equality".into()),
                }
            }
        }
    }
    retained.extend(generated.into_iter().filter(|axiom| !already_asserted.contains(axiom)));
    Ok(format!("{}\nOntology(\n{}\n)\n", prefixes.join("\n"), retained.join("\n")))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn inherited_domains_and_functional_owner_inequalities() {
        let result = project(r#"Ontology(
            SubDataPropertyOf(<urn:p> <urn:q>) SubDataPropertyOf(<urn:q> <urn:p>)
            FunctionalDataProperty(<urn:q>) DataPropertyDomain(<urn:q> <urn:C>)
            DataPropertyRange(<urn:q> DataOneOf("1"^^xsd:int "2"^^xsd:int))
            DataPropertyAssertion(<urn:p> <urn:a> "1"^^xsd:integer)
            DataPropertyAssertion(<urn:p> <urn:b> "01"^^xsd:int)
            DataPropertyAssertion(<urn:q> <urn:c> "2"^^xsd:int))"#).unwrap();
        for owner in ["a", "b", "c"] { assert!(result.contains(&format!("ClassAssertion(<urn:C> <urn:{owner}>)"))); }
        assert!(result.contains("DifferentIndividuals(<urn:a> <urn:c>)"));
        assert!(result.contains("DifferentIndividuals(<urn:b> <urn:c>)"));
        assert!(!result.contains("DifferentIndividuals(<urn:a> <urn:b>)"));
        assert!(!result.contains("DataPropertyAssertion"));
    }
    #[test]
    fn inherited_assertions_do_not_duplicate_retained_source_facts() {
        let result = project(r#"Ontology(
            ClassAssertion(Annotation(<urn:note> "retained") <urn:C> <urn:a>)
            DifferentIndividuals(<urn:b> <urn:a>)
            DataPropertyDomain(<urn:p> <urn:C>) FunctionalDataProperty(<urn:p>)
            DataPropertyAssertion(<urn:p> <urn:a> "red"^^xsd:string)
            DataPropertyAssertion(<urn:p> <urn:b> "blue"^^xsd:string))"#).unwrap();
        assert_eq!(result.matches("ClassAssertion(").count(), 2);
        assert_eq!(result.matches("DifferentIndividuals(").count(), 1);
        assert!(result.contains("Annotation(<urn:note> \"retained\")"));
    }
    #[test]
    fn range_violation_is_retained_as_contradiction() {
        let result = project(r#"Ontology(DataPropertyRange(<urn:p> DataOneOf("red"^^xsd:string))
            DataPropertyAssertion(<urn:p> <urn:a> "blue"^^xsd:string))"#).unwrap();
        assert!(result.contains("ClassAssertion(<http://www.w3.org/2002/07/owl#Nothing> <urn:a>)"));
    }
    #[test]
    fn coupled_or_unknown_data_semantics_defer() {
        let assertion = r#"DataPropertyAssertion(<urn:p> <urn:a> "1"^^xsd:int)"#;
        for axiom in ["SubClassOf(<urn:C> DataMinCardinality(1 <urn:p>))",
            "HasKey(<urn:C> () (<urn:p>))", "Import(<urn:other>)",
            "DataPropertyRange(<urn:p> <urn:custom>)",
            "DLSafeRule(Body() Head())"] {
            assert!(project(&format!("Ontology({assertion} {axiom})")).is_err(), "{axiom}");
        }
        assert!(project(&format!("Prefix(xsd:=<urn:custom#>) Ontology({assertion})")).is_err());
    }
}
