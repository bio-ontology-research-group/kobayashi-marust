//! Optional admission-independent shape guard for common nominal modules.
//! The complete source must already have passed public admission. This guard
//! supplies no model or answer: both actual revisions must be consistent.
use crate::frontend::sexpr::{Node, Parser};
use crate::source_locality::{Scan, StmtKind};
use crate::fxhash::FxHashSet;

pub(crate) struct Eligibility { pub data_tbox: FxHashSet<u128>, pub object_only: bool }

/// Exact spellings recognized by the locality resolver, including partial-base
/// aliases and default prefixes. Last bindings win; unresolved inputs decline
/// at the existing public boundary, never acquire new admission here.
fn universal_spellings(scan: &Scan) -> FxHashSet<String> {
    let mut result = FxHashSet::default();
    // The data boundary models ordinary properties; fixed-empty bottomData
    // needs a separate semantic constructor and is conservatively excluded.
    for local in ["topObjectProperty", "topDataProperty", "bottomDataProperty"] {
        let iri = format!("http://www.w3.org/2002/07/owl#{local}");
        result.insert(format!("<{iri}>"));
        result.insert(iri.clone());
        let mut seen = FxHashSet::default();
        for (prefix, base) in scan.prefixes.iter().rev() {
            if !seen.insert(prefix.as_str()) { continue; }
            if let Some(suffix) = iri.strip_prefix(base) {
                result.insert(format!("{prefix}{suffix}"));
            }
        }
        if !seen.contains("owl:") { result.insert(format!("owl:{local}")); }
    }
    result
}

fn forbidden(node: &Node<'_>, universals: &FxHashSet<String>) -> bool {
    match node {
        Node::Atom(atom) => universals.contains(*atom),
        Node::List("Annotation", _) => false,
        Node::List(head, args) => matches!(*head,
            "DataSomeValuesFrom" | "DataAllValuesFrom" | "DataHasValue"
            | "DataMinCardinality" | "DataMaxCardinality" | "DataExactCardinality")
            || args.iter().any(|arg| forbidden(arg, universals)),
    }
}
fn atom(node: &Node<'_>) -> bool { node.as_atom().is_some() }
fn role(node: &Node<'_>) -> bool {
    atom(node) || matches!(node, Node::List("ObjectInverseOf", a) if a.len()==1 && atom(&a[0]))
}
fn class(node: &Node<'_>) -> bool {
    match node {
        Node::Atom(_) => true,
        Node::List("ObjectIntersectionOf" | "ObjectUnionOf", a) => a.len()>=2 && a.iter().all(class),
        Node::List("ObjectComplementOf", a) => a.len()==1 && class(&a[0]),
        Node::List("ObjectSomeValuesFrom" | "ObjectAllValuesFrom", a) => a.len()==2 && role(&a[0]) && class(&a[1]),
        Node::List("ObjectHasValue", a) => a.len()==2 && role(&a[0]) && atom(&a[1]),
        Node::List("ObjectHasSelf", a) => a.len()==1 && role(&a[0]),
        Node::List("ObjectOneOf", a) => !a.is_empty() && a.iter().all(atom),
        Node::List("ObjectMinCardinality" | "ObjectMaxCardinality" | "ObjectExactCardinality", a) =>
            (a.len()==2 || a.len()==3) && atom(&a[0]) && role(&a[1]) && (a.len()==2 || class(&a[2])),
        _ => false,
    }
}
fn range(node: &Node<'_>) -> bool {
    match node {
        Node::Atom(_) => true,
        Node::List("DataIntersectionOf" | "DataUnionOf", a) => a.len()>=2 && a.iter().all(range),
        Node::List("DataComplementOf", a) => a.len()==1 && range(&a[0]),
        Node::List("DataOneOf", a) => !a.is_empty() && a.iter().all(atom),
        Node::List("DatatypeRestriction", a) => a.len()>=3 && a.iter().all(atom),
        _ => false,
    }
}
/// Some(true): a data TBox axiom which must be marked dirty; Some(false):
/// object axiom or assertion. Unknown forms are never silently projected.
fn axiom(head: &str, args: &[&Node<'_>]) -> Option<bool> {
    let all = |f: fn(&Node<'_>)->bool| args.iter().all(|a| f(a));
    let allowed = match head {
        "SubClassOf" => args.len()==2 && all(class),
        "EquivalentClasses" | "DisjointClasses" | "DisjointUnion" => args.len()>=2 && all(class),
        "SubObjectPropertyOf" if args.len()==2 => {
            let sub = role(args[0]) || matches!(args[0], Node::List("ObjectPropertyChain", a) if !a.is_empty() && a.iter().all(role));
            sub && role(args[1])
        }
        "EquivalentObjectProperties" | "DisjointObjectProperties" | "InverseObjectProperties" => args.len()>=2 && all(role),
        "ObjectPropertyDomain" | "ObjectPropertyRange" => args.len()==2 && role(args[0]) && class(args[1]),
        "FunctionalObjectProperty" | "InverseFunctionalObjectProperty" | "ReflexiveObjectProperty"
        | "IrreflexiveObjectProperty" | "SymmetricObjectProperty" | "AsymmetricObjectProperty"
        | "TransitiveObjectProperty" => args.len()==1 && role(args[0]),
        "ClassAssertion" => args.len()==2 && class(args[0]) && atom(args[1]),
        "ObjectPropertyAssertion" | "NegativeObjectPropertyAssertion" => args.len()==3 && role(args[0]) && atom(args[1]) && atom(args[2]),
        "SameIndividual" | "DifferentIndividuals" => args.len()>=2 && all(atom),
        "DataPropertyAssertion" | "NegativeDataPropertyAssertion" => args.len()>=3 && all(atom),
        "DataPropertyDomain" => return (args.len()==2 && atom(args[0]) && class(args[1])).then_some(true),
        "DataPropertyRange" => return (args.len()==2 && atom(args[0]) && range(args[1])).then_some(true),
        "FunctionalDataProperty" => return (args.len()==1 && atom(args[0])).then_some(true),
        "SubDataPropertyOf" => return (args.len()==2 && all(atom)).then_some(true),
        "DisjointDataProperties" => return (args.len()>=2 && all(atom)).then_some(true),
        _ => false,
    };
    allowed.then_some(false)
}

pub(crate) fn eligible(text: &str, scan: &Scan) -> Option<Eligibility> {
    // This optional optimization may decline without rejecting valid input.
    // Bound the legacy byte parser before it sees Unicode or deep trees.
    if !text.is_ascii() { return None; }
    let universals = universal_spellings(scan);
    let mut data_tbox = FxHashSet::default();
    let mut object_only = true;
    for statement in &scan.statements {
        if statement.kind==StmtKind::Annotation { continue; }
        if statement.kind==StmtKind::Import { return None; }
        let slice = text.get(statement.start..statement.end)?;
        if slice.len()>32_768 || slice.bytes().filter(|b|*b==b'(').count()>256 { return None; }
        let mut parser = Parser::new(slice);
        let node = parser.parse().ok()?;
        if parser.peek().is_some() || forbidden(&node, &universals) { return None; }
        let Node::List(head, args) = &node else { return None; };
        let args: Vec<_> = args.iter().filter(|a|a.head()!=Some("Annotation")).collect();
        if statement.kind==StmtKind::Declaration {
            if args.len()!=1 || !matches!(args[0], Node::List("Class"|"ObjectProperty"|"DataProperty"|"NamedIndividual"|"Datatype"|"AnnotationProperty", a) if a.len()==1 && atom(&a[0])) { return None; }
            if matches!(args[0].head(), Some("DataProperty" | "Datatype")) { object_only = false; }
            continue;
        }
        let data = axiom(head, &args)?;
        if data { data_tbox.insert(statement.hash); }
        if data || matches!(*head, "DataPropertyAssertion" | "NegativeDataPropertyAssertion") { object_only = false; }
    }
    Some(Eligibility { data_tbox, object_only })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source_locality::{scan, fingerprint};
    fn source(body: &str) -> String { format!("Prefix(:=<urn:envelope#>) Ontology({body})") }
    fn check(body: &str) -> Option<Eligibility> {
        let text=source(body); eligible(&text,&scan(&text).unwrap())
    }
    #[test]
    fn exact_allowed_data_owners_are_returned_and_assertions_stay_on_right() {
        let axioms=["DataPropertyDomain(:p ObjectUnionOf(:A :B))", "DataPropertyRange(:p xsd:string)",
            "FunctionalDataProperty(:p)", "SubDataPropertyOf(:p :q)", "DisjointDataProperties(:p :q)"];
        let text=source(&format!("{} DataPropertyAssertion(:p :a \"x\"^^xsd:string) NegativeDataPropertyAssertion(:q :a \"x\") ClassAssertion(ObjectHasValue(:r :a) :b)",axioms.join(" ")));
        let result=eligible(&text,&scan(&text).unwrap()).unwrap();
        assert!(!result.object_only);
        assert!(check("SubClassOf(:A :B) ClassAssertion(:A :a)").unwrap().object_only);
        assert!(!check("Declaration(DataProperty(:p))").unwrap().object_only);
        assert_eq!(result.data_tbox,axioms.iter().map(|a|fingerprint(a.as_bytes())).collect());
    }
    #[test]
    fn all_data_class_constructors_decline_even_when_only_in_assertions() {
        for class in ["DataSomeValuesFrom(:p xsd:string)","DataAllValuesFrom(:p xsd:string)",
            "DataHasValue(:p \"x\")","DataMinCardinality(1 :p)","DataMaxCardinality(1 :p)","DataExactCardinality(1 :p)"] {
            assert!(check(&format!("SubClassOf(:A {class})")).is_none());
            assert!(check(&format!("ClassAssertion({class} :a)")).is_none());
            assert!(check(&format!("DataPropertyDomain(:p {class})")).is_none());
        }
        for axiom in ["HasKey(:A () (:p))","DLSafeRule(Body(ClassAtom(:A Variable(:x))) Head(ClassAtom(:B Variable(:x))))",
            "DatatypeDefinition(:D xsd:string)","EquivalentDataProperties(:p :q)","UnknownAxiom(:A)"] {
            assert!(check(axiom).is_none(),"{axiom}");
        }
    }
    #[test]
    fn resolved_universal_roles_decline_including_assertions_and_partial_aliases() {
        for role in ["topObjectProperty","topDataProperty","bottomDataProperty"] {
            let full=format!("http://www.w3.org/2002/07/owl#{role}");
            for spelling in [format!("owl:{role}"),format!("<{full}>")] {
                assert!(check(&format!("ObjectPropertyAssertion({spelling} :a :b)")).is_none());
                assert!(check(&format!("DataPropertyAssertion({spelling} :a \"x\")")).is_none());
            }
            let split=role.len()-8;
            let text=format!("Prefix(t:=<http://www.w3.org/2002/07/owl#{}>) Ontology(ObjectPropertyAssertion(t:{} :a :b))",&role[..split],&role[split..]);
            assert!(eligible(&text,&scan(&text).unwrap()).is_none());
            let text=format!("Prefix(t:=<{full}>) Ontology(DataPropertyAssertion(t: :a \"x\"))");
            assert!(eligible(&text,&scan(&text).unwrap()).is_none());
            // Token spellings, not substring matches in literals/annotations.
            assert!(check(&format!("DataPropertyAssertion(:p :a \"owl:{role}\") AnnotationAssertion(:note :A <{full}>)")).is_some());
        }
        // Guard resolution follows the last binding. Public validation is a
        // separate requirement and rejects a rebound standard owl prefix.
        let shadow="Prefix(owl:=<urn:ordinary#>) Ontology(SubDataPropertyOf(owl:topDataProperty :p))";
        assert!(eligible(shadow,&scan(shadow).unwrap()).is_some());
        let text="Prefix(t:=<http://www.w3.org/2002/07/owl#>) Prefix(t:=<urn:ordinary#>) Ontology(SubDataPropertyOf(t:topDataProperty :p))";
        assert!(eligible(text,&scan(text).unwrap()).is_some());
        let text="Prefix(t:=<urn:ordinary#>) Prefix(t:=<http://www.w3.org/2002/07/owl#>) Ontology(SubDataPropertyOf(t:topDataProperty :p))";
        assert!(eligible(text,&scan(text).unwrap()).is_none());
    }
    #[test]
    fn optional_parser_bounds_decline_without_rejecting_source_globally() {
        assert!(check("DataPropertyAssertion(:p :a \"\u{120}\")").is_none());
        let nested=format!("SubClassOf(:A {}:B{})","ObjectComplementOf(".repeat(257),")".repeat(257));
        assert!(check(&nested).is_none());
    }
}
