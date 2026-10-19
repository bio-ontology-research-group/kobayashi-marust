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
fn builtin_spellings(scan: &Scan, locals: &[&str]) -> FxHashSet<String> {
    let mut result = FxHashSet::default();
    // The data boundary models ordinary properties; fixed-empty bottomData
    // needs a separate semantic constructor and is conservatively excluded.
    for local in locals {
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
// The only data class constructor exception is an entire top-level axiom.
// Public admission supplies entity typing; this guard additionally requires
// named tokens and excludes fixed builtins under every effective prefix alias.
fn named_atom(node: &Node<'_>) -> bool {
    node.as_atom().is_some_and(|token| {
        (token.starts_with('<') && token.ends_with('>'))
            || (!matches!(token.as_bytes().first(), Some(b'"' | b'^' | b'@'))
                && !token.starts_with("_:") && token.contains(':'))
    })
}
fn cardinality_axiom(head: &str, args: &[&Node<'_>],
    builtin_classes: &FxHashSet<String>, universals: &FxHashSet<String>) -> bool
{
    if head != "SubClassOf" || args.len() != 2 || !named_atom(args[0])
        || forbidden(args[0], universals)
        || args[0].as_atom().is_some_and(|c| builtin_classes.contains(c)) { return false; }
    let Node::List("DataMinCardinality" | "DataExactCardinality", a) = args[1] else { return false; };
    a.len() == 2 && a[0].as_atom() == Some("1") && named_atom(&a[1])
        && !forbidden(&a[1], universals)
}
// Literal values stay in the fixed native datatype/literal interpretation.
// This recognizes token shape only; public source admission remains required.
fn literal_tokens(args: &[Node<'_>]) -> bool {
    let [Node::Atom(lexical), suffix @ ..] = args else { return false; };
    if !lexical.starts_with('"') || !lexical.ends_with('"') || lexical.len() < 2 {
        return false;
    }
    match suffix {
        [] => true,
        [Node::Atom(suffix)] => {
            if let Some(datatype) = suffix.strip_prefix("^^") {
                named_atom(&Node::Atom(datatype))
            } else if let Some(language) = suffix.strip_prefix('@') {
                !language.is_empty() && language.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
            } else { false }
        }
        _ => false,
    }
}

fn has_value_axiom(head: &str, args: &[&Node<'_>],
    builtin_classes: &FxHashSet<String>, universals: &FxHashSet<String>) -> bool
{
    if head != "SubClassOf" || args.len() != 2 || !named_atom(args[0])
        || forbidden(args[0], universals)
        || args[0].as_atom().is_some_and(|c| builtin_classes.contains(c)) { return false; }
    let Node::List("DataHasValue", values) = args[1] else { return false; };
    let Some(property) = values.first() else { return false; };
    named_atom(property) && !forbidden(property, universals) && literal_tokens(&values[1..])
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

/// The legacy tokenizer is byte based outside strings. Permit UTF-8 only
/// in quoted literal tokens, whose scanner ends at an ASCII quote boundary.
/// Match token starts exactly: quotes embedded in atoms, IRIs, or comments
/// cannot open a literal. This is a parser-safety check, not source admission.
fn unicode_only_in_literal_bodies(text: &str) -> bool {
    if text.is_ascii() { return true; }
    let bytes = text.as_bytes();
    let mut i = 0;
    let end_atom = |byte| matches!(byte, b'\t'..=b'\r' | b' ' | b'(' | b')');
    while i < bytes.len() {
        if !bytes[i].is_ascii() { return false; }
        match bytes[i] {
            byte if end_atom(byte) => i += 1,
            b'<' => {
                i += 1;
                while i < bytes.len() && bytes[i] != b'>' {
                    if !bytes[i].is_ascii() { return false; }
                    i += 1;
                }
                if i == bytes.len() { return false; }
                i += 1;
            }
            b'#' => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    if !bytes[i].is_ascii() { return false; }
                    i += 1;
                }
            }
            b'"' => {
                i += 1;
                loop {
                    if i == bytes.len() { return false; }
                    match bytes[i] {
                        b'\\' => {
                            if i + 1 >= bytes.len() { return false; }
                            i += 2;
                        }
                        b'"' => { i += 1; break; }
                        _ => i += 1,
                    }
                }
            }
            _ => {
                while i < bytes.len() && !end_atom(bytes[i]) {
                    if !bytes[i].is_ascii() { return false; }
                    i += 1;
                }
            }
        }
    }
    true
}

pub(crate) fn eligible(text: &str, scan: &Scan) -> Option<Eligibility> {
    // This optional optimization may decline without rejecting valid input.
    // Bound the legacy byte parser before unsafe Unicode atom boundaries or
    // deep trees. Literal bodies keep their exact values and public admission.
    if !unicode_only_in_literal_bodies(text) { return None; }
    let universals = builtin_spellings(scan,
        &["topObjectProperty", "topDataProperty", "bottomDataProperty"]);
    let top_roles = builtin_spellings(scan, &["topObjectProperty"]);
    let builtin_classes = builtin_spellings(scan, &["Thing", "Nothing"]);
    let mut data_tbox = FxHashSet::default();
    let mut object_only = true;
    for statement in &scan.statements {
        if statement.kind==StmtKind::Annotation { continue; }
        if statement.kind==StmtKind::Import { return None; }
        let slice = text.get(statement.start..statement.end)?;
        if slice.len()>32_768 || slice.bytes().filter(|b|*b==b'(').count()>256 { return None; }
        let mut parser = Parser::new(slice);
        let node = parser.parse().ok()?;
        if parser.peek().is_some() { return None; }
        let Node::List(head, args) = &node else { return None; };
        let args: Vec<_> = args.iter().filter(|a|a.head()!=Some("Annotation")).collect();
        if cardinality_axiom(head, &args, &builtin_classes, &universals)
            || has_value_axiom(head, &args, &builtin_classes, &universals) {
            // Mark even unchanged positive data-value/cardinality owners.
            // Retained object modules must omit these axioms and their class
            // owners from the closed logical signature, before declarations.
            data_tbox.insert(statement.hash);
            object_only = false;
            continue;
        }
        // `SubObjectPropertyOf(R owl:topObjectProperty)` (a role or role chain
        // on the left) holds in every interpretation, so it is a vacuous
        // axiom. The frontend already elides it exactly when the builtin has
        // no other occurrence (`frontend::top_role`), and KM classifies the
        // retained ontology. Here the bare builtin in that super-role slot is
        // skipped, while every other position of every statement, including
        // the left side of this one, is still checked: any other occurrence
        // declines as before. The index compiles the axiom as never
        // non-local, so no module contains it.
        let vacuous_super = *head == "SubObjectPropertyOf" && args.len() == 2
            && args[1].as_atom().is_some_and(|token| top_roles.contains(token));
        if vacuous_super {
            if forbidden(args[0], &universals) { return None; }
        } else if forbidden(&node, &universals) { return None; }
        if *head == "EquivalentDataProperties" {
            if args.len() != 2 || !args.iter().all(|arg| named_atom(arg)) { return None; }
            // One original source owner represents both directed subproperty
            // obligations; every such owner stays dirty in object queries.
            data_tbox.insert(statement.hash);
            object_only = false;
            continue;
        }
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
    fn unsupported_data_class_positions_and_constructors_decline() {
        for class in ["DataSomeValuesFrom(:p xsd:string)","DataAllValuesFrom(:p xsd:string)",
            "DataHasValue(:p \"x\")","DataMinCardinality(1 :p)","DataMaxCardinality(1 :p)","DataExactCardinality(1 :p)"] {
            if !class.starts_with("DataMinCardinality(1 ") && !class.starts_with("DataExactCardinality(1 ") {
                if !class.starts_with("DataHasValue(") {
                    assert!(check(&format!("SubClassOf(:A {class})")).is_none());
                }
            }
            assert!(check(&format!("ClassAssertion({class} :a)")).is_none());
            assert!(check(&format!("DataPropertyDomain(:p {class})")).is_none());
        }
        for axiom in ["HasKey(:A () (:p))","DLSafeRule(Body(ClassAtom(:A Variable(:x))) Head(ClassAtom(:B Variable(:x))))",
            "DatatypeDefinition(:D xsd:string)","UnknownAxiom(:A)"] {
            assert!(check(axiom).is_none(),"{axiom}");
        }
    }
    #[test]
    fn named_has_value_and_binary_equivalence_mark_exact_original_owners() {
        let axioms = ["SubClassOf(:A DataHasValue(:p \"01\"^^xsd:integer))",
            "SubClassOf(:B DataHasValue(:q \"1\"^^<http://www.w3.org/2001/XMLSchema#int>))",
            "SubClassOf(:C DataHasValue(:p \"è \\\"quoted\\\"\"@en))",
            "SubClassOf(:D DataHasValue(:q \"plain\"))", "EquivalentDataProperties(:p :q)"];
        let text = source(&axioms.join(" "));
        let admitted = eligible(&text, &scan(&text).unwrap()).unwrap();
        assert!(!admitted.object_only);
        assert_eq!(admitted.data_tbox, axioms.iter().map(|a| fingerprint(a.as_bytes())).collect());
        for axiom in ["SubClassOf(ObjectIntersectionOf(:A :B) DataHasValue(:p \"x\"))",
            "SubClassOf(:A ObjectIntersectionOf(:B DataHasValue(:p \"x\")))",
            "SubClassOf(DataHasValue(:p \"x\") :A)",
            "EquivalentClasses(:A DataHasValue(:p \"x\"))",
            "SubClassOf(:A DataHasValue(ObjectInverseOf(:r) \"x\"))",
            "SubClassOf(:A DataHasValue(:p :notALiteral))",
            "SubClassOf(:A DataHasValue(:p \"x\" junk))",
            "SubClassOf(:A DataHasValue(:p \"x\" ^^))",
            "SubClassOf(:A DataHasValue(:p \"x\" @))",
            "SubClassOf(:A DataHasValue(:p \"x\"^^xsd:string \"extra\"))",
            "EquivalentDataProperties(:p)", "EquivalentDataProperties(:p :q :r)",
            "EquivalentDataProperties(:p ObjectInverseOf(:r))"] {
            assert!(check(axiom).is_none(), "{axiom}");
        }
    }
    #[test]
    fn has_value_and_equivalent_data_respect_resolved_builtin_aliases() {
        for class in ["owl:Thing", "owl:Nothing", "<http://www.w3.org/2002/07/owl#Thing>"] {
            assert!(check(&format!("SubClassOf({class} DataHasValue(:p \"x\"))")).is_none());
        }
        for local in ["topDataProperty", "bottomDataProperty"] {
            let text = format!("Prefix(t:=<http://www.w3.org/2002/07/owl#{local}>) Ontology(SubClassOf(<urn:A> DataHasValue(t: \"x\")))");
            assert!(eligible(&text, &scan(&text).unwrap()).is_none());
            let text = format!("Prefix(t:=<http://www.w3.org/2002/07/owl#{local}>) Ontology(EquivalentDataProperties(<urn:p> t:))");
            assert!(eligible(&text, &scan(&text).unwrap()).is_none());
        }
        let text = "Prefix(t:=<http://www.w3.org/2002/07/owl#>) Prefix(t:=<urn:ordinary#>) Ontology(SubClassOf(t:Thing DataHasValue(t:topDataProperty \"x\")))";
        assert!(eligible(text, &scan(text).unwrap()).is_some());
    }
    #[test]
    fn cardinality_one_is_top_level_named_and_marks_exact_owner_hashes() {
        let cards=["SubClassOf(:A DataMinCardinality(1 :p))",
            "SubClassOf(:B DataExactCardinality(1 :q))"];
        let text=source(&format!("{} SubClassOf(:E :F)",cards.join(" ")));
        let result=eligible(&text,&scan(&text).unwrap()).unwrap();
        assert!(!result.object_only);
        assert_eq!(result.data_tbox,cards.iter().map(|a|fingerprint(a.as_bytes())).collect());
        for axiom in [
            "SubClassOf(ObjectIntersectionOf(:A :B) DataMinCardinality(1 :p))",
            "SubClassOf(:A DataMinCardinality(1 :p xsd:string))",
            "SubClassOf(:A DataExactCardinality(1 :p rdfs:Literal))",
            "SubClassOf(:A DataMinCardinality(0 :p))",
            "SubClassOf(:A DataExactCardinality(2 :p))",
            "SubClassOf(:A DataMaxCardinality(1 :p))",
            "SubClassOf(:A ObjectIntersectionOf(:B DataMinCardinality(1 :p)))",
            "SubClassOf(DataMinCardinality(1 :p) :A)",
            "EquivalentClasses(:A DataExactCardinality(1 :p))",
            "SubClassOf(owl:topObjectProperty DataMinCardinality(1 :p))",
            "SubClassOf(:A DataMinCardinality(1 _:p))",
            "SubClassOf(:A DataMinCardinality(1 \"literal\"))",
        ] { assert!(check(axiom).is_none(),"{axiom}"); }
    }
    #[test]
    fn cardinality_builtin_aliases_decline_and_last_prefix_binding_wins() {
        for local in ["Thing","Nothing"] {
            let iri=format!("http://www.w3.org/2002/07/owl#{local}");
            for token in [format!("owl:{local}"),format!("<{iri}>")] {
                assert!(check(&format!("SubClassOf({token} DataMinCardinality(1 :p))")).is_none());
            }
            for (prefix,base,suffix) in [("t:","http://www.w3.org/2002/07/owl#",local),
                (":","http://www.w3.org/2002/07/owl#",local),
                ("t:",if local == "Thing" {"http://www.w3.org/2002/07/owl#Th"}
                    else {"http://www.w3.org/2002/07/owl#No"},if local == "Thing" {"ing"} else {"thing"}),
                ("t:",iri.as_str(),"")] {
                let text=format!("Prefix({prefix}=<{base}>) Ontology(SubClassOf({prefix}{suffix} DataMinCardinality(1 <urn:p>)))");
                assert!(eligible(&text,&scan(&text).unwrap()).is_none(),"{text}");
            }
        }
        for local in ["topDataProperty","bottomDataProperty"] {
            for token in [format!("owl:{local}"),format!("<http://www.w3.org/2002/07/owl#{local}>")] {
                assert!(check(&format!("SubClassOf(:A DataExactCardinality(1 {token}))")).is_none());
            }
            let text=format!("Prefix(t:=<http://www.w3.org/2002/07/owl#{local}>) Ontology(SubClassOf(<urn:A> DataExactCardinality(1 t:)))");
            assert!(eligible(&text,&scan(&text).unwrap()).is_none());
        }
        for (first,last,accepted) in [("http://www.w3.org/2002/07/owl#","urn:ordinary#",true),
            ("urn:ordinary#","http://www.w3.org/2002/07/owl#",false)] {
            let text=format!("Prefix(t:=<{first}>) Prefix(t:=<{last}>) Ontology(SubClassOf(t:Thing DataMinCardinality(1 <urn:p>)))");
            assert_eq!(eligible(&text,&scan(&text).unwrap()).is_some(),accepted);
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
    fn vacuous_top_object_super_role_is_skipped_only_in_that_slot() {
        // The tautology R <= U (role or chain on the left) does not decline.
        for axiom in [
            "SubObjectPropertyOf(:r owl:topObjectProperty)",
            "SubObjectPropertyOf(:r <http://www.w3.org/2002/07/owl#topObjectProperty>)",
            "SubObjectPropertyOf(ObjectInverseOf(:r) owl:topObjectProperty)",
            "SubObjectPropertyOf(ObjectPropertyChain(:r :s) owl:topObjectProperty)",
        ] {
            let text = source(&format!("{axiom} SubClassOf(:A :B) ClassAssertion(:A :a)"));
            let result = eligible(&text, &scan(&text).unwrap());
            assert!(result.as_ref().is_some_and(|e| e.object_only && e.data_tbox.is_empty()), "{axiom}");
        }
        let text = "Prefix(t:=<http://www.w3.org/2002/07/owl#>) Ontology(SubObjectPropertyOf(<urn:r> t:topObjectProperty))";
        assert!(eligible(text, &scan(text).unwrap()).is_some());
        let split = "Prefix(t:=<http://www.w3.org/2002/07/owl#top>) Ontology(SubObjectPropertyOf(<urn:r> t:ObjectProperty))";
        assert!(eligible(split, &scan(split).unwrap()).is_some());
        // Last binding wins: a rebound prefix that no longer spells the builtin
        // is an ordinary role, and one that now does is still the vacuous slot.
        let rebound = "Prefix(t:=<http://www.w3.org/2002/07/owl#>) Prefix(t:=<urn:ordinary#>) Ontology(SubObjectPropertyOf(<urn:r> t:topObjectProperty))";
        assert!(eligible(rebound, &scan(rebound).unwrap()).is_some());
        // Every other occurrence of any universal builtin declines, even next
        // to a vacuous inclusion.
        let vacuous = "SubObjectPropertyOf(:r owl:topObjectProperty)";
        for other in [
            "SubObjectPropertyOf(owl:topObjectProperty :s)",
            "SubObjectPropertyOf(ObjectPropertyChain(owl:topObjectProperty :s) :t)",
            "SubObjectPropertyOf(ObjectPropertyChain(:s owl:topObjectProperty) owl:topObjectProperty)",
            "SubObjectPropertyOf(ObjectInverseOf(owl:topObjectProperty) owl:topObjectProperty)",
            "SubObjectPropertyOf(:s ObjectInverseOf(owl:topObjectProperty))",
            "SubObjectPropertyOf(:s owl:topDataProperty)",
            "SubObjectPropertyOf(:s owl:bottomDataProperty)",
            "SubDataPropertyOf(:d owl:topDataProperty)",
            "ObjectPropertyDomain(owl:topObjectProperty :A)",
            "ObjectPropertyRange(owl:topObjectProperty :A)",
            "TransitiveObjectProperty(owl:topObjectProperty)",
            "SubClassOf(:A ObjectSomeValuesFrom(owl:topObjectProperty :B))",
            "SubClassOf(:A ObjectAllValuesFrom(owl:topObjectProperty :B))",
            "ClassAssertion(ObjectSomeValuesFrom(owl:topObjectProperty :B) :a)",
            "ObjectPropertyAssertion(owl:topObjectProperty :a :b)",
        ] {
            let text = source(&format!("{vacuous} {other}"));
            assert!(eligible(&text, &scan(&text).unwrap()).is_none(), "{other}");
        }
        // Three arguments are never the two-sided inclusion shape.
        let text = source("SubObjectPropertyOf(:r owl:topObjectProperty :s)");
        assert!(eligible(&text, &scan(&text).unwrap()).is_none());
    }
    #[test]
    fn unicode_literals_preserve_safe_token_boundaries_only() {
        // These code points have UTF-8 continuation bytes 0x85 or 0xA0,
        // which the legacy tokenizer mistakes for whitespace in bare atoms.
        let literal = "è l’altra \u{85}\u{a0}\u{105}\u{120}";
        assert!(check(&format!("DataPropertyAssertion(:p :a \"{literal}\")")).is_some());
        assert!(check(r#"DataPropertyAssertion(:p :a "è \"quoted\" and \\ tail")"#).is_some());
        assert!(unicode_only_in_literal_bodies("# ASCII quote \" ignored\n Ontology(DataPropertyAssertion(:p :a \"è\"))"));
        for source in [
            "Ontology(SubClassOf(:A :\u{120}))",
            "Ontology(\u{85}SubClassOf(:A :B))",
            "Ontology(\u{a0}SubClassOf(:A :B))",
            "Ontology(abc\"\u{120}\")",
            "Prefix(:=<urn:\u{105}>) Ontology()",
            "Ontology(SubClassOf(<urn:\u{120}> :B))",
            "# quote \" does not open literal: \u{120}\nOntology()",
            "<urn:quote\"> \u{120}",
            "Ontology(DataPropertyAssertion(:p :a \"è))",
            "<urn:unterminated \"è\"",
        ] {
            assert!(!unicode_only_in_literal_bodies(source), "{source:?}");
        }
    }

    #[test]
    fn optional_parser_bounds_decline_without_rejecting_source_globally() {
        assert!(check("DataPropertyAssertion(:p :a \"\u{120}\")").is_some());
        let nested=format!("SubClassOf(:A {}:B{})","ObjectComplementOf(".repeat(257),")".repeat(257));
        assert!(check(&nested).is_none());
    }
}
