//! Exact elimination of admitted ground data-property ABoxes.
//! The projected object ontology retains every entailed property-domain fact.
//! A model extends by giving each data property exactly its asserted pairs,
//! closed under the source subproperty relation. Functional values receive
//! private bit labels on owners. No literal becomes an object.
use std::collections::{BTreeMap, HashMap, HashSet};
use std::borrow::Cow;
use super::{parse, sexpr::Node};

#[derive(Default)]
pub(super) struct Scan<'a> {
    domains: HashMap<&'a str, Vec<Node<'a>>>,
    ranges: HashMap<&'a str, Vec<Node<'a>>>,
    supers: HashMap<&'a str, Vec<&'a str>>,
    facts: Vec<(&'a str, &'a str, Value<'a>)>,
    functional: HashSet<&'a str>,
    object_mentions: HashSet<&'a str>,
    refused: bool,
}

pub(super) fn ordinary_iri(s: &str) -> bool {
    s.starts_with('<') && s.ends_with('>') && !s.contains('\\')
        && s[1..s.len()-1].contains(':')
        && !s.starts_with("<http://www.w3.org/2002/07/owl#")
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Value<'a> {
    String(Cow<'a, str>), Integer(i128), Boolean(bool),
    // OWL uses value identity, not host floating-point equality. Signed
    // zeroes stay distinct; each floating-point datatype has its own space.
    Float(u32), Double(u64),
}

pub(super) struct Projection<'a> {
    /// Two distinct canonical values of one functional property at the same owner.
    pub inconsistent: bool,
    pub domains: Vec<Node<'a>>,
    pub bits: Vec<(&'a str, String, bool)>,
}

fn quoted_value(token: &str) -> Option<Cow<'_, str>> {
    let value = token.strip_prefix('"')?.strip_suffix('"')?;
    if !value.contains(['\\', '"']) { return Some(Cow::Borrowed(value)); }
    let mut out = String::new();
    let mut chars = value.chars();
    while let Some(c) = chars.next() {
        match c {
            '\\' => match chars.next()? {
                escaped @ ('\\' | '"') => out.push(escaped),
                _ => return None,
            },
            '"' => return None,
            _ => out.push(c),
        }
    }
    Some(Cow::Owned(out))
}
fn datatype(s: &str) -> Option<&str> {
    s.strip_prefix("xsd:").or_else(|| s.strip_prefix("<http://www.w3.org/2001/XMLSchema#")?.strip_suffix('>'))
}
fn integer_member(value: i128, kind: &str) -> bool {
    match kind {
        "integer" => true,
        "int" => i32::try_from(value).is_ok(),
        "long" => i64::try_from(value).is_ok(),
        "short" => i16::try_from(value).is_ok(),
        "byte" => i8::try_from(value).is_ok(),
        "unsignedInt" => u32::try_from(value).is_ok(),
        "unsignedLong" => u64::try_from(value).is_ok(),
        "unsignedShort" => u16::try_from(value).is_ok(),
        "unsignedByte" => u8::try_from(value).is_ok(),
        "nonNegativeInteger" => value >= 0,
        "nonPositiveInteger" => value <= 0,
        "positiveInteger" => value > 0,
        "negativeInteger" => value < 0,
        _ => false,
    }
}
// XML Schema's decimal floating-point lexical grammar, before rounding.
// Do not let Rust's extra spellings (inf, infinity, signed NaN) widen admission.
fn decimal_float_lexical(text: &str) -> bool {
    let bytes = text.as_bytes();
    let mut i = usize::from(matches!(bytes.first(), Some(b'+' | b'-')));
    let mut digits = 0;
    while bytes.get(i).is_some_and(u8::is_ascii_digit) { i += 1; digits += 1; }
    if bytes.get(i) == Some(&b'.') {
        i += 1;
        while bytes.get(i).is_some_and(u8::is_ascii_digit) { i += 1; digits += 1; }
    }
    if digits == 0 { return false; }
    if matches!(bytes.get(i), Some(b'e' | b'E')) {
        i += 1;
        if matches!(bytes.get(i), Some(b'+' | b'-')) { i += 1; }
        let start = i;
        while bytes.get(i).is_some_and(u8::is_ascii_digit) { i += 1; }
        if i == start { return false; }
    }
    i == bytes.len()
}
fn floating_value(text: &str, double: bool) -> Option<Value<'static>> {
    let text = text.trim_matches([' ', '\t', '\n', '\r']);
    if double {
        let value = match text {
            "INF" | "+INF" => f64::INFINITY,
            "-INF" => f64::NEG_INFINITY,
            "NaN" => return Some(Value::Double(0x7ff8_0000_0000_0000)),
            _ if decimal_float_lexical(text) => text.parse::<f64>().ok()?,
            _ => return None,
        };
        Some(Value::Double(value.to_bits()))
    } else {
        let value = match text {
            "INF" | "+INF" => f32::INFINITY,
            "-INF" => f32::NEG_INFINITY,
            "NaN" => return Some(Value::Float(0x7fc0_0000)),
            _ if decimal_float_lexical(text) => text.parse::<f32>().ok()?,
            _ => return None,
        };
        Some(Value::Float(value.to_bits()))
    }
}
pub(super) fn literal_value<'a>(args: &[&Node<'a>]) -> Option<Value<'a>> {
    let text = quoted_value(args.first()?.as_atom()?)?;
    let kind = match args.get(1).map(|n| n.as_atom()) {
        None if args.len() == 1 => "string",
        Some(Some(suffix)) if args.len() == 2 => datatype(suffix.strip_prefix("^^")?)?,
        _ => return None,
    };
    if kind == "string" { return Some(Value::String(text)); }
    if matches!(kind, "float" | "double") { return floating_value(&text, kind == "double"); }
    if kind == "boolean" {
        return match text.as_ref() { "true" | "1" => Some(Value::Boolean(true)),
            "false" | "0" => Some(Value::Boolean(false)), _ => None };
    }
    let digits = text.strip_prefix(['+', '-']).unwrap_or(&text);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) { return None; }
    let value = text.parse::<i128>().ok()?;
    integer_member(value, kind).then_some(Value::Integer(value))
}
// None means that the range is outside this exact decoder. Some(false)
// is a proved non-membership, and therefore a ground assertion clash.
pub(super) fn in_range(value: &Value<'_>, range: &Node<'_>) -> Option<bool> {
    match range {
        Node::Atom("rdfs:Literal" | "<http://www.w3.org/2000/01/rdf-schema#Literal>") => Some(true),
        Node::Atom(atom) => {
            let kind = datatype(atom)?;
            if !matches!(kind, "string" | "boolean" | "float" | "double"
                | "integer" | "int" | "long" | "short" | "byte"
                | "unsignedInt" | "unsignedLong" | "unsignedShort" | "unsignedByte"
                | "nonNegativeInteger" | "nonPositiveInteger" | "positiveInteger" | "negativeInteger") {
                return None;
            }
            Some(match (kind, value) {
                ("string", Value::String(_)) | ("boolean", Value::Boolean(_))
                    | ("float", Value::Float(_)) | ("double", Value::Double(_)) => true,
                (_, Value::Integer(n)) => integer_member(*n, kind),
                _ => false,
            })
        }
        Node::List("DataOneOf", values) if !values.is_empty() => {
            let mut i = 0;
            let mut found = false;
            while i < values.len() {
                let n = if values.get(i + 1).and_then(Node::as_atom)
                    .is_some_and(|s| s.starts_with("^^") || s.starts_with('@')) { 2 } else { 1 };
                let refs: Vec<_> = values[i..i+n].iter().collect();
                let candidate = literal_value(&refs)?;
                found |= &candidate == value;
                i += n;
            }
            Some(found)
        }
        _ => None,
    }
}
fn has_data_use(node: &Node<'_>) -> bool {
    match node {
        Node::Atom(_) => false,
        Node::List(head, args) => head.starts_with("Data")
            || matches!(*head, "HasKey" | "DLSafeRule" | "FunctionalDataProperty"
                | "NegativeDataPropertyAssertion" | "EquivalentDataProperties"
                | "DisjointDataProperties" | "SubDataPropertyOf")
            || args.iter().any(has_data_use),
    }
}
fn collect_atoms<'a>(node: &Node<'a>, atoms: &mut HashSet<&'a str>) {
    match node {
        Node::Atom(atom) => { atoms.insert(atom); }
        Node::List("Annotation", _) => {},
        Node::List(_, args) => { for arg in args { collect_atoms(arg, atoms); } }
    }
}
impl<'a> Scan<'a> {
    pub fn observe(&mut self, node: &Node<'a>) {
        if self.refused { return; }
        let Node::List(head, children) = node else { return; };
        let args = parse::strip_annotations(children);
        match *head {
            "Declaration" if args.first().is_some_and(|n| n.head() == Some("DataProperty")) => {},
            "DataPropertyDomain" | "DataPropertyRange" => {
                if args.len() != 2 { self.refused = true; return; }
                let Some(p) = args[0].as_atom().filter(|p| ordinary_iri(p)) else {
                    self.refused = true; return;
                };
                if *head == "DataPropertyDomain" {
                    self.refused |= has_data_use(args[1]);
                    collect_atoms(args[1], &mut self.object_mentions);
                    self.domains.entry(p).or_default().push(args[1].clone());
                } else {
                    self.ranges.entry(p).or_default().push(args[1].clone());
                }
            }
            "FunctionalDataProperty" => {
                if args.len() != 1 { self.refused = true; return; }
                match args[0].as_atom() {
                    Some(p) if ordinary_iri(p) => { self.functional.insert(p); }
                    _ => self.refused = true,
                }
            }
            "SubDataPropertyOf" => {
                if args.len() != 2 { self.refused = true; return; }
                match (args[0].as_atom(), args[1].as_atom()) {
                    (Some(p), Some(q)) if ordinary_iri(p) && ordinary_iri(q) => {
                        self.supers.entry(p).or_default().push(q);
                    }
                    _ => self.refused = true,
                }
            }
            "DataPropertyAssertion" => {
                if args.len() < 3 { self.refused = true; return; }
                match (args[0].as_atom(), args[1].as_atom(), literal_value(&args[2..])) {
                    (Some(p), Some(i), Some(v)) if ordinary_iri(p) && ordinary_iri(i) => {
                        self.facts.push((p, i, v));
                    }
                    _ => self.refused = true,
                }
            }
            // Annotation values cannot constrain the data-property extension.
            "AnnotationAssertion" | "Annotation" => {},
            "Import" => self.refused = true,
            _ => {
                self.refused |= has_data_use(node);
                collect_atoms(node, &mut self.object_mentions);
            }
        }
    }

    pub fn project(&self, source: &str, expected: u64) -> Option<Projection<'a>> {
        if self.refused || expected == 0 || self.facts.len() as u64 != expected {
            return None;
        }
        // Builtin abbreviated datatype tokens may not have been rebound.
        let mut tokens = super::sexpr::tokens(source);
        while let Some(token) = tokens.next() {
            if token != "Prefix" { continue; }
            let mut binding = String::new();
            for part in tokens.by_ref() {
                binding.push_str(part);
                if part == ")" { break; }
            }
            for (prefix, iri) in [("xsd", "http://www.w3.org/2001/XMLSchema#"),
                ("rdfs", "http://www.w3.org/2000/01/rdf-schema#"),
                ("owl", "http://www.w3.org/2002/07/owl#")] {
                if binding.starts_with(&format!("({prefix}:"))
                    && binding != format!("({prefix}:=<{iri}>)") { return None; }
            }
        }
        // Source object/data names must not alias through an unexpanded
        // custom prefix. The existing registry uses raw tokens, so admit only
        // full IRIs and the standard OWL builtins in object-side expressions.
        if self.object_mentions.iter().any(|atom| atom.contains(':')
            && !atom.starts_with('<') && !atom.starts_with('"')
            && !matches!(*atom, "owl:Thing" | "owl:Nothing"
                | "owl:topObjectProperty" | "owl:bottomObjectProperty")) {
            return None;
        }
        if self.facts.iter().any(|(p, _, _)| self.object_mentions.contains(p))
            || self.domains.keys().chain(self.ranges.keys()).chain(self.supers.keys())
                .chain(self.supers.values().flatten()).chain(self.functional.iter()).any(|p| self.object_mentions.contains(p)) {
            return None;
        }
        let mut assertions = Vec::new();
        let mut inconsistent = false;
        let mut functional_values: BTreeMap<&str, BTreeMap<Value<'a>, Vec<&'a str>>> = BTreeMap::new();
        for (property, individual, value) in &self.facts {
            let (property, individual) = (*property, *individual);
            let mut todo = vec![property];
            let mut seen = HashSet::new();
            while let Some(p) = todo.pop() {
                if !seen.insert(p) { continue; }
                if self.functional.contains(p) {
                    functional_values.entry(p).or_default().entry(value.clone()).or_default().push(individual);
                }
                if let Some(ranges) = self.ranges.get(p) {
                    for range in ranges {
                        inconsistent |= !in_range(value, range)?;
                    }
                }
                if let Some(domains) = self.domains.get(p) {
                    for domain in domains {
                        assertions.push(Node::List("ClassAssertion",
                            vec![domain.clone(), Node::Atom(individual)]));
                    }
                }
                if let Some(supers) = self.supers.get(p) { todo.extend(supers.iter().copied()); }
            }
        }
        let mut bits = Vec::new();
        for (property_id, (_property, values)) in functional_values.into_iter().enumerate() {
            let width = (usize::BITS - (values.len() - 1).leading_zeros()) as usize;
            let capacity = 1usize.checked_shl(width as u32)?;
            if values.len() > capacity { return None; }
            let mut owner_values = HashMap::new();
            for (value_id, (_value, owners)) in values.into_iter().enumerate() {
                for individual in owners {
                    if owner_values.insert(individual, value_id).is_some_and(|old| old != value_id) {
                        inconsistent = true;
                    }
                    for bit in 0..width {
                        bits.push((individual, format!("__km_ground_data_p{property_id}_b{bit}"),
                            (value_id >> bit) & 1 != 0));
                    }
                }
            }
        }
        Some(Projection { domains: assertions, bits, inconsistent })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn project(source: &str, expected: u64) -> Option<Projection<'_>> {
        let mut scan = Scan::default();
        parse::for_each_ontology_child(source, |node| { scan.observe(node); Ok(()) }).ok()?;
        scan.project(source, expected)
    }
    #[test]
    fn ground_data_inherits_union_domains_and_finite_string_ranges() {
        let source = r#"Ontology(
          DataPropertyAssertion(<http://e/p> <http://e/a> "yes")
          SubDataPropertyOf(<http://e/p> <http://e/q>)
          SubDataPropertyOf(<http://e/q> <http://e/p>)
          DataPropertyRange(<http://e/q> DataOneOf("yes"^^xsd:string "no"))
          DataPropertyDomain(<http://e/q> ObjectUnionOf(<http://e/A> <http://e/B>)))"#;
        let assertions = project(source, 1).unwrap();
        assert_eq!(assertions.domains.len(), 1);
        assert_eq!(assertions.domains[0].head(), Some("ClassAssertion"));
        assert!(project(source, 2).is_none());
        assert!(project(&source.replace("\"yes\")", "\"other\")"), 1).unwrap().inconsistent);
    }
    #[test]
    fn range_clashes_distinguish_non_membership_from_unknown_ranges() {
        let make = |range: &str| format!("Ontology(DataPropertyRange(<http://e/p> {range}) DataPropertyAssertion(<http://e/p> <http://e/a> \"0\"^^xsd:integer))");
        for range in ["xsd:positiveInteger", "xsd:string", "xsd:float", "DataOneOf(\"1\"^^xsd:int)"] {
            assert!(project(&make(range), 1).unwrap().inconsistent, "{range}");
        }
        for range in ["xsd:integer", "xsd:nonNegativeInteger", "DataOneOf(\"+00\"^^xsd:int)"] {
            assert!(!project(&make(range), 1).unwrap().inconsistent, "{range}");
        }
        for range in ["xsd:decimal", "<http://e/unknown>", "DataOneOf(\"0\"^^xsd:integer \"unknown\"^^<http://e/unknown>)"] {
            assert!(project(&make(range), 1).is_none(), "{range}");
        }
    }

    #[test]
    fn same_owner_functionality_clash_uses_closed_canonical_values() {
        let source = r#"Ontology(
          FunctionalDataProperty(<http://e/p>)
          SubDataPropertyOf(<http://e/q> <http://e/p>)
          DataPropertyAssertion(<http://e/q> <http://e/a> "0"^^xsd:double)
          DataPropertyAssertion(<http://e/p> <http://e/a> "-0"^^xsd:double))"#;
        assert!(project(source, 2).unwrap().inconsistent);
        assert!(!project(&source.replace("\"-0\"", "\"0.0\""), 2).unwrap().inconsistent);
        assert!(!project(&source.replace("<http://e/p> <http://e/a>", "<http://e/p> <http://e/b>"), 2).unwrap().inconsistent);
        assert!(!project(&source.replace("FunctionalDataProperty(<http://e/p>)", ""), 2).unwrap().inconsistent);
    }

    #[test]
    fn functional_values_use_canonical_values_and_logarithmic_bit_labels() {
        let source = r#"Ontology(
          FunctionalDataProperty(<http://e/p>)
          DataPropertyAssertion(<http://e/p> <http://e/a> "+01"^^xsd:int)
          DataPropertyAssertion(<http://e/p> <http://e/b> "1"^^xsd:integer)
          DataPropertyAssertion(<http://e/p> <http://e/c> "2"^^xsd:int))"#;
        let result = project(source, 3).unwrap();
        assert_eq!(result.bits.len(), 3);
        assert_eq!(result.bits[0].1, result.bits[1].1);
        assert_eq!(result.bits[0].2, result.bits[1].2);
        assert_ne!(result.bits[0].2, result.bits[2].2);
        let mut large = String::from("Ontology(FunctionalDataProperty(<http://e/p>)");
        for i in 0..257 {
            large.push_str(&format!("DataPropertyAssertion(<http://e/p> <http://e/i{i}> \"{i}\"^^xsd:int)"));
        }
        large.push(')');
        assert_eq!(project(&large, 257).unwrap().bits.len(), 257 * 9);
    }

    #[test]
    fn literal_values_validate_types_and_decode_only_owl_quoted_escapes() {
        let lit = |text, ty| literal_value(&[&Node::Atom(text), &Node::Atom(ty)]);
        assert_eq!(lit("\"+001\"", "^^xsd:int"), lit("\"1\"", "^^xsd:integer"));
        assert_ne!(lit("\"1\"", "^^xsd:string"), lit("\"1\"", "^^xsd:integer"));
        assert_eq!(lit("\"1\"", "^^xsd:boolean"), lit("\"true\"", "^^xsd:boolean"));
        for bad in ["\"1.0\"", "\"1e0\"", "\"2147483648\"", "\"--1\""] {
            assert!(lit(bad, "^^xsd:int").is_none());
        }
        assert_eq!(quoted_value(r#""a\"b\\c""#).as_deref(), Some("a\"b\\c"));
        assert!(quoted_value(r#""a\nb""#).is_none());
    }

    #[test]
    fn floating_identity_preserves_signed_zero_nan_and_disjoint_value_spaces() {
        assert_eq!(floating_value("1.0", false), floating_value("+1e0", false));
        assert_eq!(floating_value(" 1.0 ", true), floating_value("1", true));
        assert_ne!(floating_value("0", false), floating_value("-0", false));
        assert_ne!(floating_value("0", true), floating_value("-0", true));
        assert_ne!(floating_value("1", false), floating_value("1", true));
        assert_ne!(floating_value("1", true), Some(Value::Integer(1)));
        assert_eq!(floating_value("NaN", false), Some(Value::Float(0x7fc0_0000)));
        assert_eq!(floating_value("NaN", true), Some(Value::Double(0x7ff8_0000_0000_0000)));
        assert_eq!(floating_value("INF", false), floating_value("+INF", false));
        assert_ne!(floating_value("INF", true), floating_value("-INF", true));
        assert_eq!(floating_value("16777217", false), floating_value("16777216", false));
        assert_ne!(floating_value("16777217", true), floating_value("16777216", true));
        for bad in ["", ".", "+", "1e", "1e+", "1 2", "inf", "nan", "Infinity", "-NaN", "0x1p0"] {
            assert!(floating_value(bad, false).is_none(), "{bad}");
        }
        assert_eq!(in_range(&Value::Float(0), &Node::Atom("xsd:float")), Some(true));
        assert_eq!(in_range(&Value::Float(0), &Node::Atom("xsd:double")), Some(false));
        assert_eq!(in_range(&Value::Double(0), &Node::Atom("xsd:integer")), Some(false));
    }

    #[test]
    fn ground_data_rejects_every_unrepresented_interaction() {
        let base = r#"DataPropertyAssertion(<http://e/p> <http://e/a> "v")"#;
        for extra in [
            "NegativeDataPropertyAssertion(<http://e/p> <http://e/a> \"v\")",
            "SubClassOf(<http://e/A> DataSomeValuesFrom(<http://e/p> xsd:string))",
            "HasKey(<http://e/A> () (<http://e/p>))",
            "DLSafeRule(Body() Head())",
            "Import(<http://e/other>)",
            "ClassAssertion(e:Alias <http://e/a>)",
            "ObjectPropertyAssertion(<http://e/p> <http://e/a> <http://e/b>)",
        ] {
            assert!(project(&format!("Ontology({base} {extra})"), 1).is_none(), "{extra}");
        }
        assert!(project(&format!("Prefix(xsd:=<http://wrong/>) Ontology({base})"), 1).is_none());
        assert!(project(&format!("Ontology({})", base.replace("<http://e/p>", "<http://www.w3.org/2002/07/owl#topDataProperty>")), 1).is_none());
    }
}
