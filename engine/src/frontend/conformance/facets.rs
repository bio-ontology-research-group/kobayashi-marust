//! Bound, length, and language-range facet conformance (OWL 2 Structural Specification 4 and 7.5).
//! Non-normative facet extensions remain subject to a separate support audit.
use std::collections::BTreeMap;
use super::{expand, Node};

pub(super) const XSD: &str = "http://www.w3.org/2001/XMLSchema#";
const OWL: &str = "http://www.w3.org/2002/07/owl#";

#[derive(PartialEq, Eq)]
enum OrderedSpace { Real, Float, Double, DateTime }

fn ordered_space(iri: &str) -> Option<OrderedSpace> {
    if matches!(iri.strip_prefix(OWL), Some("real" | "rational")) {
        return Some(OrderedSpace::Real);
    }
    match iri.strip_prefix(XSD)? {
        "decimal" | "integer" | "nonNegativeInteger" | "nonPositiveInteger"
        | "positiveInteger" | "negativeInteger" | "long" | "int" | "short" | "byte"
        | "unsignedLong" | "unsignedInt" | "unsignedShort" | "unsignedByte" => Some(OrderedSpace::Real),
        "float" => Some(OrderedSpace::Float),
        "double" => Some(OrderedSpace::Double),
        "dateTime" | "dateTimeStamp" => Some(OrderedSpace::DateTime),
        _ => None,
    }
}

fn supports_length(iri: &str) -> bool {
    iri == "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral"
        || matches!(iri.strip_prefix(XSD), Some("string" | "normalizedString" | "token"
            | "language" | "Name" | "NCName" | "NMTOKEN" | "hexBinary" | "base64Binary" | "anyURI"))
}

// Decimal long division uses at most nine subtractions per input digit.
// Numeric size is limited only by the source, never by machine integers.
fn division(numerator: &str, denominator: &str) -> Option<(String, bool)> {
    let divisor: Vec<u8> = denominator.trim_start_matches('0').bytes().map(|b| b-b'0').collect();
    if divisor.is_empty() { return None; }
    let mut quotient = String::new();
    let mut remainder = Vec::<u8>::new();
    for digit in numerator.bytes() {
        remainder.push(digit-b'0');
        let leading = remainder.iter().take_while(|&&b| b==0).count();
        remainder.drain(..leading);
        let mut digit_quotient = 0u8;
        while remainder.len() > divisor.len()
            || (remainder.len() == divisor.len() && remainder.as_slice() >= divisor.as_slice()) {
            digit_quotient += 1;
            let mut borrow = 0i16;
            for offset in 0..remainder.len() {
                let i = remainder.len()-1-offset;
                let sub = if offset < divisor.len() { i16::from(divisor[divisor.len()-1-offset]) } else { 0 };
                let difference = i16::from(remainder[i])-sub-borrow;
                remainder[i] = difference.rem_euclid(10) as u8;
                borrow = i16::from(difference < 0);
            }
            let leading = remainder.iter().take_while(|&&b| b==0).count();
            remainder.drain(..leading);
        }
        if digit_quotient != 0 || !quotient.is_empty() {
            quotient.push(char::from(b'0' + digit_quotient));
        }
    }
    if quotient.is_empty() { quotient.push('0'); }
    Some((quotient, remainder.is_empty()))
}

fn divisible(numerator: &str, denominator: &str) -> bool {
    division(numerator, denominator).is_some_and(|(_, exact)| exact)
}

// XML Schema bound facets require a value in the base datatype's value space.
// Membership is about values, so 6/3 and 2.0 can both bound xsd:integer.
fn bound_value_member(base: &str, quoted: &str, datatype: &str) -> bool {
    let Some(kind) = base.strip_prefix(XSD) else { return true };
    let text = quoted.trim_matches('"').trim_matches([' ', '\t', '\r', '\n']);
    if kind == "dateTimeStamp" {
        return super::lexical::check(quoted, base).is_ok();
    }
    if ordered_space(base) != Some(OrderedSpace::Real) { return true; }
    let negative = text.starts_with('-');
    let unsigned = text.strip_prefix(['+', '-']).unwrap_or(text);
    let integer = if datatype == format!("{OWL}rational") {
        let Some((num, den)) = unsigned.split_once('/') else { return false };
        if kind == "decimal" {
            // A rational has a finite decimal expansion exactly when, after
            // removing powers of 2 and 5, the denominator divides its numerator.
            let mut residual = den.to_owned();
            for factor in ["2", "5"] {
                loop {
                    let Some((quotient, true)) = division(&residual, factor) else { break };
                    residual = quotient;
                }
            }
            return divisible(num, &residual);
        }
        let Some((quotient, true)) = division(num, den) else { return false };
        quotient
    } else {
        if kind == "decimal" { return true; }
        let (whole, fraction) = unsigned.split_once('.').unwrap_or((unsigned, ""));
        if fraction.bytes().any(|b| b != b'0') { return false; }
        if whole.is_empty() { "0".to_owned() } else { whole.to_owned() }
    };
    let signed = if negative { format!("-{integer}") } else { integer };
    super::lexical::integer(&signed, kind)
}

// Source lexical validation has already succeeded. Membership concerns the
// value: decimal 2.0 and rational 6/3 are nonnegative integers too.
fn nonnegative_integer(quoted: &str, datatype: &str) -> bool {
    if ordered_space(datatype) != Some(OrderedSpace::Real) { return false; }
    let text = quoted.trim_matches('"').trim_matches([' ', '\t', '\r', '\n']);
    let negative = text.starts_with('-');
    let unsigned = text.strip_prefix(['+', '-']).unwrap_or(text);
    if datatype == format!("{OWL}rational") {
        let Some((num, den)) = unsigned.split_once('/') else { return false };
        if negative && num.bytes().any(|b| b!=b'0') { return false; }
        divisible(num, den)
    } else {
        let (whole, fraction) = unsigned.split_once('.').unwrap_or((unsigned, ""));
        (!negative || whole.bytes().chain(fraction.bytes()).all(|b| b==b'0'))
            && fraction.bytes().all(|b| b==b'0')
    }
}

fn string_value_type(quoted: &str, datatype: &str, language_tagged: bool) -> bool {
    if language_tagged { return false; }
    if datatype == "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral" {
        return quoted.strip_prefix('"').and_then(|s| s.strip_suffix('"'))
            .is_some_and(|s| s.ends_with('@'));
    }
    matches!(datatype.strip_prefix(XSD), Some("string" | "normalizedString" | "token"
        | "language" | "Name" | "NCName" | "NMTOKEN"))
}

// Language ranges are strings, not language-tagged pairs. Basic ranges use
// RFC 4647 section 2.1, deliberately not the stricter language-tag grammar.
fn basic_language_range(quoted: &str, datatype: &str, language_tagged: bool) -> bool {
    if language_tagged { return false; }
    let Some(mut text) = quoted.strip_prefix('"').and_then(|s| s.strip_suffix('"')) else { return false };
    if datatype == "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral" {
        let Some(value) = text.strip_suffix('@') else { return false };
        text = value;
    } else {
        match datatype.strip_prefix(XSD) {
            Some("string" | "normalizedString") => {}
            Some("token" | "language" | "Name" | "NCName" | "NMTOKEN") => {
                text = text.trim_matches([' ', '\t', '\r', '\n']);
            }
            _ => return false,
        }
    }
    text == "*" || text.split('-').enumerate().all(|(i, subtag)| {
        !subtag.is_empty() && subtag.len() <= 8
            && subtag.bytes().all(|b| if i == 0 { b.is_ascii_alphabetic() } else { b.is_ascii_alphanumeric() })
    })
}

/// Literal spelling/lexical validity is checked before this walk. Consume its
/// suffix here as well so a datatype IRI cannot be mistaken for the next facet.
fn literal_datatype(args: &[Node<'_>], index: &mut usize, prefixes: &BTreeMap<String, String>) -> Option<String> {
    let literal = args.get(*index)?.as_atom()?;
    if !literal.starts_with('"') { return None; }
    *index += 1;
    let suffix = args.get(*index).and_then(Node::as_atom);
    if let Some(datatype) = suffix.and_then(|s| s.strip_prefix("^^")) {
        *index += 1;
        let datatype = if datatype.is_empty() {
            let datatype = args.get(*index)?.as_atom()?;
            *index += 1;
            datatype
        } else { datatype };
        Some(expand(datatype, prefixes))
    } else if suffix.is_some_and(|s| s.starts_with('@')) {
        *index += 1;
        Some("http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral".into())
    } else {
        Some(format!("{XSD}string"))
    }
}

pub(super) fn check(node: &Node<'_>, prefixes: &BTreeMap<String, String>) -> Result<(), String> {
    let Node::List(head, args) = node else { return Ok(()) };
    if *head == "DatatypeRestriction" {
        let base = args.first().and_then(Node::as_atom).map(|s| expand(s, prefixes))
            .ok_or("invalid OWL 2 DL input: missing datatype restriction base")?;
        let mut index = 1;
        while index < args.len() {
            let facet = args[index].as_atom().map(|s| expand(s, prefixes))
                .ok_or("invalid OWL 2 DL input: missing datatype restriction facet")?;
            index += 1;
            // These XML Schema extensions are outside the normative OWL facet
            // set. Do not certify or silently ignore a restriction whose
            // extension-specific value semantics KM has not validated.
            if matches!(facet.strip_prefix(XSD), Some("totalDigits" | "fractionDigits"
                | "whiteSpace" | "enumeration" | "explicitTimezone" | "assertion"
                | "maxScale" | "minScale")) {
                return Err(format!("OWL 2 DL validation unsupported: facet <{facet}> on <{base}> requires an XML Schema facet extension that KM does not validate; no conformance verdict was produced"));
            }
            if !matches!(facet.strip_prefix(XSD), Some("length" | "minLength" | "maxLength"
                | "pattern" | "minInclusive" | "maxInclusive" | "minExclusive" | "maxExclusive"))
                && facet != "http://www.w3.org/1999/02/22-rdf-syntax-ns#langRange" {
                return Err(format!("invalid OWL 2 DL input: facet <{facet}> is not defined in the OWL 2 datatype map"));
            }
            let quoted = args.get(index).and_then(Node::as_atom).unwrap_or("");
            let language_tagged = args.get(index+1).and_then(Node::as_atom).is_some_and(|s| s.starts_with('@'));
            let value_type = literal_datatype(args, &mut index, prefixes)
                .ok_or("invalid OWL 2 DL input: missing datatype restriction value")?;
            if facet == format!("{XSD}pattern") {
                // XSD supplies pattern even for types where OWL does not make
                // it normative (e.g. integer and boolean). OWL's own numeric
                // types and the RDF XML/top literal types have no such facet.
                if super::datatypes::builtin(&base) && !base.starts_with(XSD)
                    && base != "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral" {
                    return Err(format!("invalid OWL 2 DL input: xsd:pattern is not defined for datatype <{base}>"));
                }
                if !string_value_type(quoted, &value_type, language_tagged) {
                    return Err(format!("invalid OWL 2 DL input: xsd:pattern requires a string value; found {quoted}^^<{value_type}>"));
                }
                super::pattern::check(quoted, &value_type)?;
            }
            if facet == "http://www.w3.org/1999/02/22-rdf-syntax-ns#langRange" {
                if super::datatypes::builtin(&base) && base != "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral" {
                    return Err(format!("invalid OWL 2 DL input: rdf:langRange is not defined for datatype <{base}>"));
                }
                if !basic_language_range(quoted, &value_type, language_tagged) {
                    return Err(format!("invalid OWL 2 DL input: rdf:langRange requires a string value containing a basic language range; found {quoted}^^<{value_type}>"));
                }
            }
            if matches!(facet.strip_prefix(XSD), Some("length" | "minLength" | "maxLength")) {
                if super::datatypes::builtin(&base) && !supports_length(&base) {
                    return Err(format!("invalid OWL 2 DL input: length facet <{facet}> is not defined for datatype <{base}>"));
                }
                if !nonnegative_integer(quoted, &value_type) {
                    return Err(format!("invalid OWL 2 DL input: length facet <{facet}> requires a nonnegative integer value; found {quoted}^^<{value_type}>"));
                }
            }
            if matches!(facet.strip_prefix(XSD), Some("minInclusive" | "maxInclusive" | "minExclusive" | "maxExclusive")) {
                // Custom definitions are diagnosed by datatypes::Definitions.
                // Built-in unordered spaces cannot use any of these facets.
                if super::datatypes::builtin(&base) {
                    let space = ordered_space(&base).ok_or_else(|| format!(
                        "invalid OWL 2 DL input: bound facet <{facet}> is not defined for datatype <{base}>"))?;
                    if ordered_space(&value_type).as_ref() != Some(&space)
                        || !bound_value_member(&base, quoted, &value_type) {
                        return Err(format!(
                            "invalid OWL 2 DL input: bound facet <{facet}> on <{base}> has a value of datatype <{value_type}> outside its ordered value space"));
                    }
                }
            }
        }
    }
    for arg in args { check(arg, prefixes)?; }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::super::check_source;
    fn source(base: &str, value: &str) -> String {
        format!("Ontology(DataPropertyRange(:p DatatypeRestriction({base} xsd:minInclusive {value})))")
    }

    #[test]
    fn unknown_facets_and_patterns_on_facetless_datatypes_are_rejected() {
        for base in ["owl:real", "owl:rational", "rdf:XMLLiteral", "rdfs:Literal"] {
            let input = format!(r#"Ontology(DataPropertyRange(:p DatatypeRestriction({base} xsd:pattern "a")))"#);
            assert!(check_source(&input).unwrap_err().contains("not defined"), "{input}");
        }
        for facet in ["xsd:unknownFacet", "<urn:custom:pattern>"] {
            let input = format!(r#"Ontology(DataPropertyRange(:p DatatypeRestriction(xsd:string {facet} "a")))"#);
            assert!(check_source(&input).unwrap_err().contains("not defined"), "{input}");
        }
        // These are specified by XSD, even though not normative OWL facets.
        for base in ["xsd:integer", "xsd:boolean", "xsd:base64Binary"] {
            check_source(&format!(r#"Ontology(DataPropertyRange(:p DatatypeRestriction({base} xsd:pattern "a")))"#)).unwrap();
        }
    }

    #[test]
    fn unvalidated_facet_extensions_are_explicit_refusals_not_invalid_verdicts() {
        for facet in ["totalDigits", "fractionDigits", "whiteSpace", "enumeration", "explicitTimezone"] {
            let input = format!(r#"Ontology(DataPropertyRange(:p DatatypeRestriction(xsd:decimal xsd:{facet} "2"^^xsd:integer)))"#);
            let error = check_source(&input).unwrap_err();
            assert!(error.starts_with("OWL 2 DL validation unsupported:"), "{error}");
            assert!(error.contains("no conformance verdict"), "{error}");
        }
    }

    #[test]
    fn pattern_values_must_be_strings_including_plain_literal_string_values() {
        for value in [r#""[a-z]+""#, r#""[a-z]+@"^^rdf:PlainLiteral"#,
            r#""abc"^^xsd:token"#, r#""a{999999999999999999999999999999999999}""#,
            r#""[a-z-[aeiou]]+""#, r#""\\i\\c*""#] {
            check_source(&format!("Ontology(DataPropertyRange(:p DatatypeRestriction(xsd:string xsd:pattern {value})))")).unwrap();
        }
        for value in [r#""123"^^xsd:integer"#, r#""abc"@en"#, r#""abc@en"^^rdf:PlainLiteral"#,
            r#""abc"^^xsd:anyURI"#, r#""abc@"@en"#] {
            let source = format!("Ontology(DataPropertyRange(:p DatatypeRestriction(xsd:string xsd:pattern {value})))");
            assert!(check_source(&source).unwrap_err().contains("pattern requires a string"), "{source}");
        }
    }

    #[test]
    fn language_ranges_use_basic_range_syntax_and_string_values() {
        for value in [r#""*""#, r#""en-GB""#, r#""a-0""#, r#""en-a""#,
            r#""en@"^^rdf:PlainLiteral"#, r#"" en "^^xsd:token"#, r#""en"^^xsd:language"#] {
            check_source(&format!("Ontology(DataPropertyRange(:p DatatypeRestriction(rdf:PlainLiteral rdf:langRange {value})))")).unwrap();
        }
        for value in [r#""""#, r#""en-*""#, r#""*-GB""#, r#""en--GB""#, r#""123""#,
            r#""abcdefghi""#, r#"" en ""#, r#""en"@en"#, r#""en@"@en"#,
            r#""en@en"^^rdf:PlainLiteral"#, r#""1"^^xsd:integer"#, r#""en"^^xsd:anyURI"#] {
            let source = format!("Ontology(DataPropertyRange(:p DatatypeRestriction(rdf:PlainLiteral rdf:langRange {value})))");
            assert!(check_source(&source).unwrap_err().contains("basic language range"), "{source}");
        }
        assert!(check_source(r#"Ontology(DataPropertyRange(:p DatatypeRestriction(xsd:string rdf:langRange "en")))"#).unwrap_err().contains("not defined"));
        check_source(r#"Prefix(r:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)
Ontology(DLSafeRule(Body(DataRangeAtom(DatatypeRestriction(r:PlainLiteral r:langRange "*") Variable(:x))) Head(ClassAtom(:A :a))))"#).unwrap();
    }

    #[test]
    fn length_facets_require_nonnegative_integer_values_without_numeric_limits() {
        for facet in ["length", "minLength", "maxLength"] {
            for value in [r#""-1"^^xsd:integer"#, r#""1.5"^^xsd:decimal"#,
                r#""1/3"^^owl:rational"#, r#""1"^^xsd:float"#, r#""1""#,
                r#""-6/3"^^owl:rational"#] {
                let source = format!("Ontology(DataPropertyRange(:p DatatypeRestriction(xsd:string xsd:{facet} {value})))");
                assert!(check_source(&source).unwrap_err().contains("nonnegative integer"), "{source}");
            }
            for value in [r#""999999999999999999999999999999999999"^^xsd:integer"#,
                r#""-0"^^xsd:integer"#, r#""2.000"^^xsd:decimal"#, r#""-0.0"^^xsd:decimal"#,
                r#""6/3"^^owl:rational"#, r#""-0/7"^^owl:rational"#,
                r#""200000000000000000000000000000000000000/100000000000000000000000000000000000000"^^owl:rational"#] {
                for base in ["xsd:string", "rdf:PlainLiteral", "xsd:base64Binary", "xsd:anyURI"] {
                    check_source(&format!("Ontology(DataPropertyRange(:p DatatypeRestriction({base} xsd:{facet} {value})))")).unwrap();
                }
            }
        }
        assert!(check_source(r#"Ontology(DataPropertyRange(:p DatatypeRestriction(xsd:boolean xsd:length "1"^^xsd:integer)))"#).unwrap_err().contains("not defined"));
    }

    #[test]
    fn arbitrary_precision_divisibility_matches_small_integer_oracle() {
        for numerator in 0..250 {
            for denominator in 1..50 {
                assert_eq!(super::divisible(&numerator.to_string(), &denominator.to_string()),
                    numerator % denominator == 0, "{numerator}/{denominator}");
            }
        }
        assert!(super::divisible("000006", "00003"));
        assert!(!super::divisible("1", "999999999999999999999999999999999"));
        assert!(!super::divisible("123", "0"));
    }

    #[test]
    fn bound_values_belong_to_the_derived_base_by_value() {
        for (base, value, valid) in [
            ("xsd:byte", r#""128"^^xsd:integer"#, false),
            ("xsd:byte", r#""-128.0"^^xsd:decimal"#, true),
            ("xsd:byte", r#""-129"^^xsd:integer"#, false),
            ("xsd:unsignedByte", r#""510/2"^^owl:rational"#, true),
            ("xsd:unsignedByte", r#""512/2"^^owl:rational"#, false),
            ("xsd:positiveInteger", r#""-0.0"^^xsd:decimal"#, false),
            ("xsd:nonNegativeInteger", r#""-0/7"^^owl:rational"#, true),
            ("xsd:integer", r#""1.5"^^xsd:decimal"#, false),
            ("xsd:integer", r#""6/3"^^owl:rational"#, true),
            ("xsd:integer", r#""7/3"^^owl:rational"#, false),
            ("xsd:integer", r#""999999999999999999999999999999999999000/1000"^^owl:rational"#, true),
            ("xsd:long", r#""999999999999999999999999999999999999000/1000"^^owl:rational"#, false),
            ("xsd:decimal", r#""1/3"^^owl:rational"#, false),
            ("xsd:decimal", r#""3/6"^^owl:rational"#, true),
            ("xsd:decimal", r#""7/280"^^owl:rational"#, true),
            ("xsd:decimal", r#""1/280"^^owl:rational"#, false),
            ("owl:rational", r#""1/3"^^owl:rational"#, true),
            ("xsd:dateTimeStamp", r#""2000-01-01T00:00:00"^^xsd:dateTime"#, false),
            ("xsd:dateTimeStamp", r#""2000-01-01T00:00:00Z"^^xsd:dateTime"#, true),
        ] {
            for facet in ["minInclusive", "maxInclusive", "minExclusive", "maxExclusive"] {
                let input = source(base, value).replace("minInclusive", facet);
                let result = check_source(&input);
                assert_eq!(result.is_ok(), valid, "{input}: {result:?}");
            }
        }
    }

    #[test]
    fn arbitrary_precision_quotients_match_small_integer_oracle() {
        for numerator in 0..250 {
            for denominator in 1..50 {
                let (quotient, exact) = super::division(&numerator.to_string(), &denominator.to_string()).unwrap();
                assert_eq!(quotient, (numerator / denominator).to_string());
                assert_eq!(exact, numerator % denominator == 0);
            }
        }
    }

    #[test]
    fn bounds_reject_unordered_and_disjoint_value_spaces() {
        for (base, value) in [
            ("xsd:integer", r#""text"^^xsd:string"#),
            ("xsd:decimal", r#""1"^^xsd:double"#),
            ("owl:rational", r#""1"^^xsd:float"#),
            ("xsd:float", r#""1"^^xsd:double"#),
            ("xsd:double", r#""1"^^xsd:integer"#),
            ("xsd:dateTime", r#""2000-01-01T00:00:00Z""#),
            ("xsd:boolean", r#""true"^^xsd:boolean"#),
            ("xsd:string", r#""a""#),
        ] {
            assert!(check_source(&source(base, value)).unwrap_err().contains("bound facet"), "{base} {value}");
        }
    }

    #[test]
    fn bounds_preserve_arbitrary_precision_and_prefix_aliases() {
        for (base, value) in [
            ("xsd:integer", r#""999999999999999999999999999999999999"^^xsd:integer"#),
            ("owl:real", r#""1/3"^^owl:rational"#),
            ("xsd:double", r#""INF"^^ xsd:double"#),
            ("xsd:float", r#""1.25"^^<http://www.w3.org/2001/XMLSchema#float>"#),
            ("xsd:dateTime", r#""2000-01-01T00:00:00Z"^^xsd:dateTimeStamp"#),
        ] { check_source(&source(base, value)).unwrap(); }
        check_source(r#"Prefix(t:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(DataPropertyRange(:p DatatypeRestriction(t:integer t:minInclusive "1"^^t:int t:maxExclusive "5"^^t:integer)))"#).unwrap();
    }

    #[test]
    fn rule_ranges_receive_bound_validation_without_rejecting_other_facets() {
        let rule = r#"Ontology(DLSafeRule(Body(DataRangeAtom(DatatypeRestriction(xsd:integer xsd:minInclusive "text") Variable(:x))) Head(ClassAtom(:A :a))))"#;
        assert!(check_source(rule).unwrap_err().contains("bound facet"));
        check_source(r#"Ontology(DataPropertyRange(:p DatatypeRestriction(xsd:string xsd:pattern "[a-z]+" xsd:minLength "1"^^xsd:integer)))"#).unwrap();
    }
}
