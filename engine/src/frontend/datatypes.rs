//! Datatype (concrete-domain) reasoning for the `__dt__` abstraction.
//!
//! The frontend abstracts data expressions to concepts: `__dt__<name>` for a
//! named datatype, `__dt__val__<literal>` for a literal value
//! (`DataHasValue`), and `__dt__c__<canonical text>` for a complex range
//! (facet restriction, `DataOneOf`, boolean combinations).  Those concepts
//! carry no semantics by themselves — this module decides the OWL 2 datatype
//! map relations between the ones that actually occur in the clause set and
//! emits ordinary DL clauses for them:
//!
//!   * membership      `v ∈ D`        ⇝  `__dt__val__v(x) → __dt__D(x)`
//!   * non-membership  `v ∉ D`        ⇝  `__dt__val__v(x) ∧ __dt__D(x) → ⊥`
//!   * value equality  `v = w`        ⇝  inclusions both ways
//!   * value clash     `v ≠ w`        ⇝  `__dt__val__v(x) ∧ __dt__val__w(x) → ⊥`
//!     (a data node denotes one value, so distinct values are disjoint)
//!   * range subsumption / disjointness between named/complex ranges
//!   * finite covers   `|D| ≤ cap`    ⇝  `__dt__D(x) → ⋁ __dt__val__vᵢ(x)`
//!     (with the value clashes this gives finite-range counting through the
//!     engine's standard equality reasoning, e.g. `≥3 p.xsd:boolean ⊑ ⊥`)
//!
//! Every decision procedure returns `Option<bool>`; `None` (unknown) emits
//! nothing, so unsupported corners (patterns, dateTime arithmetic, …) degrade
//! to the old sound-but-incomplete abstraction, never to a wrong clause.

use std::collections::BTreeSet;

use super::clauses::{clause, Atom, DLClause, Term};
use super::sexpr::{Node, Parser};

/// Exact rational value (normalised, den > 0).  Numerics in the OWL 2 map
/// (`owl:real` and below, plus finite float/double values) are rationals.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Rat {
    num: i128,
    den: i128,
}

impl Rat {
    fn new(num: i128, den: i128) -> Option<Rat> {
        if den == 0 {
            return None;
        }
        let (mut n, mut d) = if den < 0 { (-num, -den) } else { (num, den) };
        let g = gcd(n.unsigned_abs(), d.unsigned_abs()) as i128;
        if g > 1 {
            n /= g;
            d /= g;
        }
        Some(Rat { num: n, den: d })
    }
    fn from_int(n: i128) -> Rat {
        Rat { num: n, den: 1 }
    }
    fn is_integer(&self) -> bool {
        self.den == 1
    }
    /// `self < other` (cross-multiplication; checked to avoid overflow).
    fn lt(&self, other: &Rat) -> Option<bool> {
        let a = self.num.checked_mul(other.den)?;
        let b = other.num.checked_mul(self.den)?;
        Some(a < b)
    }
    fn le(&self, other: &Rat) -> Option<bool> {
        let a = self.num.checked_mul(other.den)?;
        let b = other.num.checked_mul(self.den)?;
        Some(a <= b)
    }
}

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    if a == 0 {
        1
    } else {
        a
    }
}

pub(super) fn swrl_math_has_non_numeric_argument(iri: &str, literals: &[&str]) -> bool {
    let iri = iri.strip_prefix('<').and_then(|s| s.strip_suffix('>')).unwrap_or(iri);
    matches!(iri.strip_prefix("http://www.w3.org/2003/11/swrlb#"), Some("add" | "subtract"))
        && literals.iter().any(|literal| matches!(parse_literal(literal),
            Some((Val::Bool(_) | Val::Str(..) | Val::DateTime(_), _))))
}

/// Evaluate a fully bound SWRL numeric relation using datatype-specific arithmetic.
/// `None` is an unsupported or unrepresentable obligation, never a false body.
/// This helper does not license dropping a rule or assuming its data properties
/// are closed: the rule backend must still consider all model bindings.
pub fn swrl_numeric_relation(iri: &str, literals: &[&str]) -> Option<bool> {
    let iri = if iri.starts_with('<') { iri.strip_prefix('<')?.strip_suffix('>')? } else { iri };
    let operator = iri.strip_prefix("http://www.w3.org/2003/11/swrlb#")?;
    fn numeric(token: &str) -> Option<Rat> {
        let close = token.rfind('"')?;
        if !token.starts_with('"') || close == 0 { return None; }
        let datatype = builtin_datatype_key(token[close + 1..].strip_prefix("^^")?)?;
        let domain = named_dt_kind(datatype)?;
        // IEEE values need their own arithmetic/promotion implementation.
        // Decimal and integer-derived literals share exact rational values,
        // but each integer datatype's lexical and value bounds must be checked.
        if datatype != "decimal" && !domain.integral { return None; }
        let lex = token[1..close].trim();
        if lex.contains(['e', 'E']) || (domain.integral && lex.contains('.')) {
            return None;
        }
        let digits = lex.strip_prefix(['+', '-']).unwrap_or(lex);
        if !digits.chars().any(|c| c.is_ascii_digit())
            || digits.chars().any(|c| !c.is_ascii_digit() && c != '.') {
            return None;
        }
        let value = parse_decimal(lex)?;
        if domain.min.is_some_and(|bound| value.num < bound)
            || domain.max.is_some_and(|bound| value.num > bound) {
            return None;
        }
        Some(value)
    }
    if swrl_math_has_non_numeric_argument(iri, literals) {
        return Some(false);
    }
    if literals.iter().any(|literal| exact_ieee_literal(literal)) {
        return swrl_ieee_relation(operator, literals);
    }
    let values: Vec<Rat> = literals.iter().map(|value| numeric(value)).collect::<Option<_>>()?;
    fn sum(left: Rat, right: Rat, subtract: bool) -> Option<Rat> {
        let left_num = left.num.checked_mul(right.den)?;
        let right_num = right.num.checked_mul(left.den)?;
        let numerator = if subtract { left_num.checked_sub(right_num)? }
            else { left_num.checked_add(right_num)? };
        Rat::new(numerator, left.den.checked_mul(right.den)?)
    }
    match (operator, values.as_slice()) {
        ("equal", [a, b]) => Some(a == b),
        ("notEqual", [a, b]) => Some(a != b),
        ("lessThan", [a, b]) => a.lt(b),
        ("lessThanOrEqual", [a, b]) => a.le(b),
        ("greaterThan", [a, b]) => b.lt(a),
        ("greaterThanOrEqual", [a, b]) => b.le(a),
        ("subtract", [result, a, b]) => Some(*result == sum(*a, *b, true)?),
        ("add", [result, a, rest @ ..]) if !rest.is_empty() => {
            let mut value = *a;
            for operand in rest { value = sum(value, *operand, false)?; }
            Some(*result == value)
        }
        _ => None,
    }
}

// IEEE operators preserve the selected width. OWL literal identity remains
// separate from numeric comparison (notably signed zero and NaN).
fn swrl_ieee_relation(operator: &str, literals: &[&str]) -> Option<bool> {
    let values: Vec<_> = literals.iter().map(|literal| parse_literal(literal).map(|v| v.0)).collect::<Option<_>>()?;
    let wide = values.iter().any(|value| matches!(value, Val::Float64(_)));
    if matches!(operator, "add" | "subtract") && wide
        && values.iter().any(|value| matches!(value, Val::Float32(_))) {
        // Arithmetic promotion depends on operands, not the result slot.
        // Mixed-width arithmetic is deferred until that distinction is modeled.
        return None;
    }
    macro_rules! evaluate {
        ($ty:ty, $variant:ident) => {{
            let mut numbers: Vec<$ty> = Vec::new();
            for (value, literal) in values.iter().zip(literals) {
                let number = match value {
                    Val::$variant(bits) => <$ty>::from_bits(*bits),
                    Val::Float32(bits) if wide => f32::from_bits(*bits) as $ty,
                    // Zero promotes exactly at either IEEE width. Other decimal
                    // promotions await a correctly rounded conversion backend.
                    Val::Num(value) if value.num == 0 &&
                        swrl_numeric_relation("http://www.w3.org/2003/11/swrlb#equal", &[literal, literal]) == Some(true) => 0.0,
                    _ => return None,
                };
                numbers.push(number);
            }
            match (operator, numbers.as_slice()) {
                ("equal", [a, b]) => Some(a == b),
                ("notEqual", [a, b]) => Some(a != b),
                ("lessThan", [a, b]) => Some(a < b),
                ("lessThanOrEqual", [a, b]) => Some(a <= b),
                ("greaterThan", [a, b]) => Some(a > b),
                ("greaterThanOrEqual", [a, b]) => Some(a >= b),
                ("subtract", [result, a, b]) => Some(*result == *a - *b),
                ("add", [result, a, rest @ ..]) if !rest.is_empty() => {
                    Some(*result == rest.iter().fold(*a, |sum, value| sum + *value))
                }
                _ => None,
            }
        }};
    }
    if wide { evaluate!(f64, Float64) } else { evaluate!(f32, Float32) }
}

/// Bind known numeric operands, preserving IEEE width or exact decimal value.
/// This does not assert completeness of any data-property extension.
pub fn swrl_numeric_output(iri: &str, operands: &[&str]) -> Option<String> {
    let operator = iri.trim_start_matches('<').trim_end_matches('>')
        .strip_prefix("http://www.w3.org/2003/11/swrlb#")?;
    if !matches!((operator, operands.len()), ("add", 2..) | ("subtract", 2)) {
        return None;
    }
    if operands.iter().any(|operand| exact_ieee_literal(operand)) {
        let values: Vec<_> = operands.iter().map(|operand| parse_literal(operand).map(|v| v.0)).collect::<Option<_>>()?;
        macro_rules! output {
            ($ty:ty, $variant:ident, $datatype:literal) => {{
                let numbers: Vec<$ty> = values.iter().map(|value| match value {
                    Val::$variant(bits) => Some(<$ty>::from_bits(*bits)),
                    _ => None,
                }).collect::<Option<_>>()?;
                let value = numbers[1..].iter().fold(numbers[0], |value, operand|
                    if operator == "subtract" { value - *operand } else { value + *operand });
                let lexical = if value.is_nan() { "NaN".to_string() }
                    else if value == <$ty>::INFINITY { "INF".to_string() }
                    else if value == <$ty>::NEG_INFINITY { "-INF".to_string() }
                    else { value.to_string() };
                let result = format!("\"{lexical}\"^^<http://www.w3.org/2001/XMLSchema#{}>", $datatype);
                let mut args = vec![result.as_str()];
                args.extend_from_slice(operands);
                return (swrl_numeric_relation(iri, &args) == Some(true)).then_some(result);
            }};
        }
        if matches!(values[0], Val::Float32(_)) { output!(f32, Float32, "float"); }
        else { output!(f64, Float64, "double"); }
    }
    let mut values = Vec::with_capacity(operands.len());
    for operand in operands {
        // Reuse the strict lexical, datatype and derived-bound checks.
        if swrl_numeric_relation("http://www.w3.org/2003/11/swrlb#equal",
            &[operand, operand]) != Some(true) { return None }
        let (Val::Num(value), _) = parse_literal(operand)? else { return None };
        values.push(value);
    }
    let mut result = values[0];
    for value in &values[1..] {
        let left = result.num.checked_mul(value.den)?;
        let right = value.num.checked_mul(result.den)?;
        let numerator = if operator == "subtract" { left.checked_sub(right)? }
            else { left.checked_add(right)? };
        result = Rat::new(numerator, result.den.checked_mul(value.den)?)?;
    }
    let magnitude = result.num.unsigned_abs();
    let denominator = result.den as u128;
    let mut lexical = format!("{}{}", if result.num < 0 { "-" } else { "" },
        magnitude / denominator);
    let mut remainder = magnitude % denominator;
    if remainder != 0 {
        lexical.push('.');
        while remainder != 0 {
            remainder = remainder.checked_mul(10)?;
            lexical.push(char::from(b'0' + (remainder / denominator) as u8));
            remainder %= denominator;
        }
    }
    let output = format!("\"{lexical}\"^^<http://www.w3.org/2001/XMLSchema#decimal>");
    let mut args = vec![output.as_str()];
    args.extend_from_slice(operands);
    (swrl_numeric_relation(iri, &args) == Some(true)).then_some(output)
}

#[cfg(test)]
mod swrl_numeric_tests {
    use super::swrl_numeric_relation;
    fn relation(operator: &str, args: &[&str]) -> Option<bool> {
        swrl_numeric_relation(&format!("<http://www.w3.org/2003/11/swrlb#{operator}>"), args)
    }
    #[test]
    fn arithmetic_output_binds_exact_values_and_defers_invalid_operands() {
        let output = |op: &str, args: &[&str]| super::swrl_numeric_output(
            &format!("http://www.w3.org/2003/11/swrlb#{op}"), args);
        let a = "\"0.1\"^^xsd:decimal";
        let b = "\"0.2\"^^xsd:decimal";
        let value = output("add", &[a, b]).unwrap();
        assert_eq!(relation("equal", &[&value, "\"0.3\"^^xsd:decimal"]), Some(true));
        let value = output("subtract", &[a, b]).unwrap();
        assert_eq!(relation("equal", &[&value, "\"-0.1\"^^xsd:decimal"]), Some(true));
        let value = output("add", &["\"9007199254740993\"^^xsd:integer", "\"1\"^^xsd:integer"]).unwrap();
        assert_eq!(relation("equal", &[&value, "\"9007199254740994\"^^xsd:integer"]), Some(true));
        assert!(output("add", &["\"256\"^^xsd:unsignedByte", a]).is_none());
        assert!(output("add", &["\"0.1\"^^xsd:double", b]).is_none());
        assert!(output("add", &[a]).is_none());
        assert!(output("subtract", &[a, b, a]).is_none());
    }
    #[test]
    fn ieee_graph_subtraction_preserves_width_and_numeric_comparison() {
        let a = "\"102.92\"^^xsd:float";
        let b = "\"100.89\"^^xsd:float";
        let result = super::swrl_numeric_output("http://www.w3.org/2003/11/swrlb#subtract", &[a, b]).unwrap();
        assert!(result.ends_with("#float>"));
        assert_eq!(relation("subtract", &[&result, a, b]), Some(true));
        assert_eq!(relation("greaterThan", &[&result, "\"0\"^^xsd:int"]), Some(true));
        assert_eq!(relation("equal", &["\"-0\"^^xsd:float", "\"0\"^^xsd:float"]), Some(true));
        assert_eq!(relation("greaterThan", &["\"NaN\"^^xsd:float", "\"0\"^^xsd:int"]), Some(false));
        assert_eq!(relation("equal", &["\"16777217\"^^xsd:float", "\"16777216\"^^xsd:double"]), Some(true));
        assert_eq!(relation("equal", &[a, "\"102.92\"^^xsd:decimal"]), None);
        assert_eq!(relation("add", &["\"16777216\"^^xsd:float", "\"16777216\"^^xsd:float", "\"1\"^^xsd:float"]), Some(true));
        assert_eq!(relation("add", &["\"16777217\"^^xsd:double", "\"16777216\"^^xsd:double", "\"1\"^^xsd:double"]), Some(true));
        assert_eq!(relation("subtract", &["\"2.03\"^^xsd:double", a, b]), None);
        assert_eq!(relation("greaterThan", &["\"INF\"^^xsd:float", "\"0\"^^xsd:int"]), Some(true));
        assert!(super::swrl_numeric_output("http://www.w3.org/2003/11/swrlb#subtract", &["\"INF\"^^xsd:float", "\"INF\"^^xsd:float"]).is_none());
    }

    #[test]
    fn decimal_arithmetic_and_result_position_are_exact() {
        assert_eq!(relation("add", &["\"0.3\"^^xsd:decimal", "\"0.1\"^^xsd:decimal", "\"0.2\"^^xsd:decimal"]), Some(true));
        assert_eq!(relation("subtract", &["\"-2\"^^xsd:integer", "\"1\"^^xsd:integer", "\"3\"^^xsd:integer"]), Some(true));
        assert_eq!(relation("subtract", &["\"2\"^^xsd:integer", "\"1\"^^xsd:integer", "\"3\"^^xsd:integer"]), Some(false));
        assert_eq!(relation("greaterThan", &["\"9007199254740993\"^^xsd:integer", "\"9007199254740992\"^^xsd:integer"]), Some(true));
        assert_eq!(relation("equal", &["\"1\"^^xsd:integer", "\"1.00\"^^xsd:decimal"]), Some(true));
    }
    #[test]
    fn unsupported_or_invalid_values_are_obligations_not_false() {
        assert_eq!(relation("add", &["\"1\"^^xsd:integer"]), None);
        assert_eq!(relation("equal", &["\"1.1\"^^xsd:integer", "\"1.1\"^^xsd:decimal"]), None);
        assert_eq!(relation("equal", &["\"--1\"^^xsd:integer", "\"-1\"^^xsd:integer"]), None);
        assert_eq!(relation("equal", &["\"1E2\"^^xsd:decimal", "\"100\"^^xsd:integer"]), None);
        assert_eq!(relation("equal", &["\"NaN\"^^xsd:double", "\"NaN\"^^xsd:double"]), Some(false));
        assert_eq!(swrl_numeric_relation("http://example.org/swrlb#equal", &["\"1\"^^xsd:integer", "\"1\"^^xsd:integer"]), None);
    }
    #[test]
    fn integer_derived_literals_validate_their_value_bounds() {
        assert_eq!(relation("greaterThan", &["\"18\"^^xsd:int", "\"17\"^^xsd:long"]), Some(true));
        assert_eq!(relation("equal", &["\"255\"^^xsd:unsignedByte", "\"255\"^^xsd:integer"]), Some(true));
        assert_eq!(relation("equal", &["\"256\"^^xsd:unsignedByte", "\"256\"^^xsd:integer"]), None);
        assert_eq!(relation("equal", &["\"0\"^^xsd:positiveInteger", "\"0\"^^xsd:integer"]), None);
        assert_eq!(relation("equal", &["\"1.0\"^^xsd:int", "\"1\"^^xsd:integer"]), None);
    }
}

/// A parsed literal value in the OWL 2 datatype map.
#[derive(Clone, PartialEq, Debug)]
enum Val {
    Num(Rat),
    Float32(u32),
    Float64(u64),
    DateTime(super::datetime_value::DateTimeValue),
    Bool(bool),
    /// string with optional language tag
    Str(String, Option<String>),
    /// `xsd:anyURI` value: the IRI denoted by the whitespace-collapsed lexical
    /// form (XSD 1.1 `whiteSpace=collapse`; OWL 2 parses relative IRIs as-is).
    Uri(String),
    /// recognised datatype but value not represented exactly (e.g. enormous
    /// exponents) — comparable only for identity of the raw token
    Opaque(String),
}

/// Top-level value-space partition of the OWL 2 datatype map.  Values from
/// different partitions are always distinct; named datatypes from different
/// partitions are disjoint.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Partition {
    Numeric,
    Float32,
    Float64,
    Strings,
    Boolean,
    Uri,
    Binary,
    Time,
    Other,
}

/// A recognised named datatype.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct NamedDt {
    /// Exact OWL datatype identity. Structural fields alone are lossy:
    /// `real`/`rational`/`decimal`, the XML name family, and the temporal
    /// datatypes can share all fields while denoting different value spaces.
    kind: &'static str,
    part: Partition,
    /// numeric bounds for the integer-derived types (inclusive), if any
    min: Option<i128>,
    max: Option<i128>,
    /// values must be integers
    integral: bool,
    /// position in the string-family tower (smaller = more specific); the
    /// tower is `string ⊒ normalizedString ⊒ token ⊒ {language, Name ⊒ NCName,
    /// NMTOKEN}` — we model only the linear prefix we can order soundly
    str_level: Option<u8>,
    /// the type is exactly the two boolean values / exactly the float or
    /// double specials+finites — used for finite covers
    finite_bool: bool,
}

const XSD_NS: &str = "http://www.w3.org/2001/XMLSchema#";
const RDF_PLAIN_LITERAL_IRI: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral";
const RDFS_LITERAL_IRI: &str = "http://www.w3.org/2000/01/rdf-schema#Literal";
const RDF_XML_LITERAL_IRI: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral";
const OWL_REAL_IRI: &str = "http://www.w3.org/2002/07/owl#real";
const OWL_RATIONAL_IRI: &str = "http://www.w3.org/2002/07/owl#rational";

fn unwrapped_iri(name: &str) -> &str {
    let raw = name.trim();
    raw.strip_prefix('<')
        .and_then(|value| value.strip_suffix('>'))
        .unwrap_or(raw)
}

/// Return the canonical key of a datatype only when the complete source IRI
/// is one of the standard spellings understood by this module.  Matching a
/// local name is unsound: `ex:boolean` is a legal user datatype and does not
/// acquire the value space of `xsd:boolean` merely by sharing its suffix.
fn builtin_datatype_key(name: &str) -> Option<&str> {
    let raw = unwrapped_iri(name);
    let xsd_local = raw
        .strip_prefix("xsd:")
        .or_else(|| raw.strip_prefix(XSD_NS));
    if let Some(local) = xsd_local {
        return matches!(
            local,
            "decimal"
                | "float"
                | "double"
                | "integer"
                | "nonNegativeInteger"
                | "positiveInteger"
                | "nonPositiveInteger"
                | "negativeInteger"
                | "long"
                | "int"
                | "short"
                | "byte"
                | "unsignedLong"
                | "unsignedInt"
                | "unsignedShort"
                | "unsignedByte"
                | "string"
                | "normalizedString"
                | "token"
                | "language"
                | "Name"
                | "NCName"
                | "NMTOKEN"
                | "boolean"
                | "anyURI"
                | "hexBinary"
                | "base64Binary"
                | "dateTime"
                | "dateTimeStamp"
                | "date"
                | "time"
                | "gYear"
                | "gMonth"
                | "gDay"
                | "gYearMonth"
                | "gMonthDay"
                | "duration"
        )
        .then_some(local);
    }
    match raw {
        "owl:real" | OWL_REAL_IRI => Some("real"),
        "owl:rational" | OWL_RATIONAL_IRI => Some("rational"),
        "rdfs:Literal" | RDFS_LITERAL_IRI => Some("rdfs:Literal"),
        "rdf:PlainLiteral" | RDF_PLAIN_LITERAL_IRI => Some("rdf:PlainLiteral"),
        "rdf:XMLLiteral" | RDF_XML_LITERAL_IRI => Some("XMLLiteral"),
        _ => None,
    }
}

/// Whether a source datatype token is `rdfs:Literal`, the top data range
/// whose value space contains every data value.
pub(crate) fn is_top_data_range(name: &str) -> bool {
    builtin_datatype_key(name) == Some("rdfs:Literal")
}

/// Canonical, collision-free key for a named data range in the internal
/// `__dt__` symbol space.  Known builtins retain the historical compact key;
/// every other source token is encoded byte-for-byte instead of losing its
/// namespace through `short_base`.
pub(crate) fn datatype_concept_key(name: &str) -> String {
    if let Some(key) = builtin_datatype_key(name) {
        return match key {
            "rdfs:Literal" => "Literal".to_string(),
            "rdf:PlainLiteral" => "PlainLiteral".to_string(),
            other => other.to_string(),
        };
    }
    let raw = unwrapped_iri(name);
    let mut encoded = String::with_capacity(raw.len() * 2);
    for byte in raw.as_bytes() {
        use std::fmt::Write;
        let _ = write!(encoded, "{byte:02x}");
    }
    format!("iri__{}_{}", raw.len(), encoded)
}

fn builtin_facet_key(name: &str) -> Option<&str> {
    let raw = unwrapped_iri(name);
    let local = raw
        .strip_prefix("xsd:")
        .or_else(|| raw.strip_prefix(XSD_NS))?;
    matches!(
        local,
        "minInclusive" | "minExclusive" | "maxInclusive" | "maxExclusive"
    )
    .then_some(local)
}

fn named_dt(name: &str) -> Option<NamedDt> {
    let local = builtin_datatype_key(name)?;
    named_dt_kind(local)
}

fn named_dt_kind(local: &str) -> Option<NamedDt> {
    let n = |kind: &'static str, min: Option<i128>, max: Option<i128>| NamedDt {
        kind,
        part: Partition::Numeric,
        min,
        max,
        integral: true,
        str_level: None,
        finite_bool: false,
    };
    let s = |kind: &'static str, lvl: u8| NamedDt {
        kind,
        part: Partition::Strings,
        min: None,
        max: None,
        integral: false,
        str_level: Some(lvl),
        finite_bool: false,
    };
    Some(match local {
        // owl:real / owl:rational / xsd:decimal: unbounded, non-integral
        "real" | "rational" | "decimal" => NamedDt {
            kind: match local {
                "real" => "real",
                "rational" => "rational",
                _ => "decimal",
            },
            part: Partition::Numeric,
            min: None,
            max: None,
            integral: false,
            str_level: None,
            finite_bool: false,
        },
        // OWL gives each IEEE width its own disjoint value space.
        "float" | "double" => NamedDt {
            kind: if local == "float" { "float" } else { "double" },
            part: if local == "float" { Partition::Float32 } else { Partition::Float64 },
            min: None,
            max: None,
            integral: false,
            str_level: None,
            finite_bool: false,
        },
        "integer" => n("integer", None, None),
        "nonNegativeInteger" => n("nonNegativeInteger", Some(0), None),
        "positiveInteger" => n("positiveInteger", Some(1), None),
        "nonPositiveInteger" => n("nonPositiveInteger", None, Some(0)),
        "negativeInteger" => n("negativeInteger", None, Some(-1)),
        "long" => n("long", Some(i64::MIN as i128), Some(i64::MAX as i128)),
        "int" => n("int", Some(i32::MIN as i128), Some(i32::MAX as i128)),
        "short" => n("short", Some(i16::MIN as i128), Some(i16::MAX as i128)),
        "byte" => n("byte", Some(i8::MIN as i128), Some(i8::MAX as i128)),
        "unsignedLong" => n("unsignedLong", Some(0), Some(u64::MAX as i128)),
        "unsignedInt" => n("unsignedInt", Some(0), Some(u32::MAX as i128)),
        "unsignedShort" => n("unsignedShort", Some(0), Some(u16::MAX as i128)),
        "unsignedByte" => n("unsignedByte", Some(0), Some(u8::MAX as i128)),
        "string" => s("string", 3),
        "normalizedString" => s("normalizedString", 2),
        "token" => s("token", 1),
        "language" => s("language", 0),
        "Name" => s("Name", 0),
        "NCName" => s("NCName", 0),
        "NMTOKEN" => s("NMTOKEN", 0),
        "boolean" => NamedDt {
            kind: "boolean",
            part: Partition::Boolean,
            min: None,
            max: None,
            integral: false,
            str_level: None,
            finite_bool: true,
        },
        // RDF Concepts: the XML-value space of rdf:XMLLiteral is disjoint from
        // the value space of every other datatype of the map.
        "XMLLiteral" => NamedDt {
            kind: "XMLLiteral",
            part: Partition::Other,
            min: None,
            max: None,
            integral: false,
            str_level: None,
            finite_bool: false,
        },
        "anyURI" => NamedDt {
            kind: "anyURI",
            part: Partition::Uri,
            min: None,
            max: None,
            integral: false,
            str_level: None,
            finite_bool: false,
        },
        "hexBinary" | "base64Binary" => NamedDt {
            kind: if local == "hexBinary" {
                "hexBinary"
            } else {
                "base64Binary"
            },
            part: Partition::Binary,
            min: None,
            max: None,
            integral: false,
            str_level: None,
            finite_bool: false,
        },
        "dateTime" | "dateTimeStamp" | "date" | "time" | "gYear" | "gMonth" | "gDay"
        | "gYearMonth" | "gMonthDay" | "duration" => NamedDt {
            kind: match local {
                "dateTime" => "dateTime",
                "dateTimeStamp" => "dateTimeStamp",
                "date" => "date",
                "time" => "time",
                "gYear" => "gYear",
                "gMonth" => "gMonth",
                "gDay" => "gDay",
                "gYearMonth" => "gYearMonth",
                "gMonthDay" => "gMonthDay",
                _ => "duration",
            },
            part: Partition::Time,
            min: None,
            max: None,
            integral: false,
            str_level: None,
            finite_bool: false,
        },
        _ => return None,
    })
}

/// Parse a literal token: `"lex"`, `"lex"@lang`, `"lex"^^dt`.
/// Returns the value and the datatype name (None = plain literal).
fn parse_literal(tok: &str) -> Option<(Val, Option<String>)> {
    let tok = tok.trim();
    if !tok.starts_with('"') {
        return None;
    }
    let close = tok.rfind('"')?;
    if close == 0 {
        return None;
    }
    let lex = &tok[1..close];
    let rest = &tok[close + 1..];
    if rest.is_empty() {
        return Some((Val::Str(lex.to_string(), None), None));
    }
    if let Some(lang) = rest.strip_prefix('@') {
        return Some((
            Val::Str(lex.to_string(), Some(lang.to_ascii_lowercase())),
            None,
        ));
    }
    let dt = rest.strip_prefix("^^")?.to_string();
    let builtin = builtin_datatype_key(&dt);
    let val = match builtin {
        Some("boolean") => match lex.trim() {
            "true" | "1" => Val::Bool(true),
            "false" | "0" => Val::Bool(false),
            _ => return Some((Val::Opaque(tok.to_string()), Some(dt))),
        },
        Some("string") => Val::Str(lex.to_string(), None),
        Some("anyURI") => Val::Uri(lex.split([' ', '\t', '\n', '\r'])
            .filter(|part| !part.is_empty()).collect::<Vec<_>>().join(" ")),
        Some("dateTime" | "dateTimeStamp") => super::datetime_value::parse(
            lex, builtin == Some("dateTimeStamp"),
        ).map(Val::DateTime).unwrap_or_else(|| Val::Opaque(tok.to_string())),
        // XML Schema's derived string types apply whitespace replacement or
        // collapse before entering the value space.  Until that canonical
        // mapping is represented exactly, preserve the token opaquely: raw
        // lexical inequality is not a proof of value inequality.
        Some("normalizedString" | "token" | "language" | "Name" | "NCName" | "NMTOKEN") => {
            Val::Opaque(tok.to_string())
        }
        // OWL uses IEEE binary32/binary64 value spaces.  Parsing a decimal
        // lexical form as an exact rational (or directly as f64 for xsd:float)
        // can distinguish two spellings that round to the same value. Parse
        // directly at the declared width and retain its exact identity bits.
        Some("float" | "double") => {
            let text = lex.trim_matches([' ', '\t', '\r', '\n']);
            let numeric = text.bytes().all(|byte| byte.is_ascii_digit()
                || matches!(byte, b'+' | b'-' | b'.' | b'e' | b'E'));
            if !numeric && !matches!(text, "INF" | "-INF" | "NaN") {
                Val::Opaque(tok.to_string())
            } else if builtin == Some("float") {
                let value = match text {
                    "INF" => Some(f32::INFINITY), "-INF" => Some(f32::NEG_INFINITY),
                    "NaN" => Some(f32::NAN), _ => text.parse::<f32>().ok(),
                };
                value.map(|value| Val::Float32(value.to_bits()))
                    .unwrap_or_else(|| Val::Opaque(tok.to_string()))
            } else {
                let value = match text {
                    "INF" => Some(f64::INFINITY), "-INF" => Some(f64::NEG_INFINITY),
                    "NaN" => Some(f64::NAN), _ => text.parse::<f64>().ok(),
                };
                value.map(|value| Val::Float64(value.to_bits()))
                    .unwrap_or_else(|| Val::Opaque(tok.to_string()))
            }
        },
        Some(kind) if named_dt_kind(kind).is_some_and(|d| d.part == Partition::Numeric) => {
            match parse_decimal(lex.trim()) {
                Some(r) => Val::Num(r),
                None => Val::Opaque(tok.to_string()),
            }
        }
        _ => Val::Opaque(tok.to_string()),
    };
    Some((val, Some(dt)))
}

/// Exact decimal/integer lexical → rational (handles sign, fraction, and
/// exponent forms `1.5E2`; `None` on overflow or junk).
fn parse_decimal(s: &str) -> Option<Rat> {
    let (mant, exp) = match s.find(['e', 'E']) {
        Some(i) => (&s[..i], s[i + 1..].parse::<i32>().ok()?),
        None => (s, 0),
    };
    let (int_part, frac_part) = match mant.find('.') {
        Some(i) => (&mant[..i], &mant[i + 1..]),
        None => (mant, ""),
    };
    let neg = int_part.starts_with('-');
    let int_digits = int_part.trim_start_matches(['+', '-']);
    if int_digits.is_empty() && frac_part.is_empty() {
        return None;
    }
    if !int_digits.chars().all(|c| c.is_ascii_digit())
        || !frac_part.chars().all(|c| c.is_ascii_digit())
    {
        return None;
    }
    let mut num: i128 = 0;
    for c in int_digits.chars().chain(frac_part.chars()) {
        num = num.checked_mul(10)?.checked_add((c as u8 - b'0') as i128)?;
    }
    if neg {
        num = -num;
    }
    let mut den: i128 = 1;
    for _ in 0..frac_part.len() {
        den = den.checked_mul(10)?;
    }
    // apply the exponent
    let mut e = exp;
    while e > 0 {
        num = num.checked_mul(10)?;
        e -= 1;
    }
    while e < 0 {
        den = den.checked_mul(10)?;
        e += 1;
    }
    Rat::new(num, den)
}

/// Decode an exactly validated integral SWRL numeric value.
pub(crate) fn exact_swrl_integer(token: &str) -> Option<i128> {
    if swrl_numeric_relation("http://www.w3.org/2003/11/swrlb#equal", &[token, token]) != Some(true) {
        return None;
    }
    let (Val::Num(value), _) = parse_literal(token)? else { return None };
    value.is_integer().then_some(value.num)
}

pub(crate) fn integer_datatype_bounds(name: &str) -> Option<(Option<i128>, Option<i128>)> {
    let datatype = named_dt_kind(builtin_datatype_key(name)?)?;
    datatype.integral.then_some((datatype.min, datatype.max))
}

pub(crate) enum IntegerPredicate {
    Minimum(i128), Maximum(i128), Equal(i128), NotEqual(i128), Always, Never,
}

/// Exact restriction of a numeric comparison to mathematical integers.
/// Fractional decimal thresholds use floor/ceiling, including negative values.
pub(crate) fn swrl_integer_predicate(operator: &str, token: &str) -> Option<IntegerPredicate> {
    if swrl_numeric_relation("http://www.w3.org/2003/11/swrlb#equal", &[token, token]) != Some(true) {
        return None;
    }
    let (Val::Num(value), _) = parse_literal(token)? else { return None };
    let floor = value.num.div_euclid(value.den);
    let integral = value.is_integer();
    let ceiling = || if integral { Some(floor) } else { floor.checked_add(1) };
    Some(match operator {
        "lessThan" => IntegerPredicate::Maximum(ceiling()?.checked_sub(1)?),
        "lessThanOrEqual" => IntegerPredicate::Maximum(floor),
        "greaterThan" => IntegerPredicate::Minimum(floor.checked_add(1)?),
        "greaterThanOrEqual" => IntegerPredicate::Minimum(ceiling()?),
        "equal" if integral => IntegerPredicate::Equal(value.num),
        "equal" => IntegerPredicate::Never,
        "notEqual" if integral => IntegerPredicate::NotEqual(value.num),
        "notEqual" => IntegerPredicate::Always,
        _ => return None,
    })
}

/// A facet-restricted numeric interval (the decidable core of
/// `DatatypeRestriction` over numeric base types).
#[derive(Clone, Debug)]
struct NumRange {
    /// Base datatype of the restriction. Bounds alone cannot distinguish a
    /// decimal interval from a rational/real interval with the same endpoints.
    base_kind: &'static str,
    integral: bool,
    min: Option<(Rat, bool)>, // (bound, inclusive)
    max: Option<(Rat, bool)>,
}

/// Closed interval of representable IEEE values, ordered by bit rank.
/// Signed zeros have adjacent ranks but compare equal for bounding facets.
/// NaN is separate and is excluded by every bounding facet (XSD 1.1 §3.3.4).
#[derive(Clone, Debug)]
struct FloatRange {
    part: Partition,
    lo: u64,
    hi: u64,
    nan: bool,
}

impl FloatRange {
    fn sign(part: Partition) -> u64 {
        if part == Partition::Float32 { 1 << 31 } else { 1 << 63 }
    }
    fn rank(bits: u64, part: Partition) -> u64 {
        let sign = Self::sign(part);
        if bits & sign != 0 { (!bits) & (sign | (sign - 1)) } else { bits | sign }
    }
    fn full(part: Partition) -> Self {
        let inf = if part == Partition::Float32 { 0x7f800000 } else { 0x7ff0000000000000 };
        Self { part, lo: Self::rank(inf | Self::sign(part), part),
            hi: Self::rank(inf, part), nan: true }
    }
    fn empty(&self) -> bool { self.lo > self.hi && !self.nan }
    fn value_bits(&self, value: &Val) -> Option<(u64, bool)> {
        match value {
            Val::Float32(bits) if self.part == Partition::Float32 =>
                Some((*bits as u64, f32::from_bits(*bits).is_nan())),
            Val::Float64(bits) if self.part == Partition::Float64 =>
                Some((*bits, f64::from_bits(*bits).is_nan())),
            _ => None,
        }
    }
    fn restrict(&mut self, facet: &str, value: &Val) -> Option<()> {
        if !matches!(facet, "minInclusive" | "minExclusive" | "maxInclusive" | "maxExclusive") {
            return None;
        }
        let (bits, nan) = self.value_bits(value)?;
        self.nan = false;
        if nan { self.lo = 1; self.hi = 0; return Some(()); }
        let rank = Self::rank(bits, self.part);
        let sign = Self::sign(self.part);
        let zero = bits & (sign - 1) == 0;
        let lower = if zero { sign - 1 } else { rank };
        let upper = if zero { sign } else { rank };
        match facet {
            "minInclusive" => self.lo = self.lo.max(lower),
            "minExclusive" => self.lo = self.lo.max(upper + 1),
            "maxInclusive" => self.hi = self.hi.min(upper),
            "maxExclusive" => self.hi = self.hi.min(lower - 1),
            _ => unreachable!(),
        }
        Some(())
    }
    fn contains(&self, value: &Val) -> Option<bool> {
        if let Some((bits, nan)) = self.value_bits(value) {
            let rank = Self::rank(bits, self.part);
            Some(if nan { self.nan } else { self.lo <= rank && rank <= self.hi })
        } else { val_partition(value).map(|_| false) }
    }
    fn subset(&self, other: &Self) -> bool {
        self.empty() || (self.part == other.part && (!self.nan || other.nan)
            && (self.lo > self.hi || (other.lo <= self.lo && self.hi <= other.hi)))
    }
    fn disjoint(&self, other: &Self) -> bool {
        self.part != other.part || (!(self.nan && other.nan)
            && (self.lo > self.hi || other.lo > other.hi || self.hi < other.lo || other.hi < self.lo))
    }
}

/// A parsed data range.
#[derive(Clone, Debug)]
enum DRange {
    /// a recognised named datatype
    Named(NamedDt),
    /// one of the ⊤ data ranges (`rdfs:Literal`)
    Top,
    /// numeric interval (facet restriction over a numeric base)
    Num(NumRange),
    /// IEEE interval, separate from the real/decimal value space.
    Float(FloatRange),
    /// explicit enumeration
    OneOf(Vec<Val>),
    /// Complement in the data-value universe, with unknown decisions retained.
    Complement(Box<DRange>),
    /// `DataUnionOf`: a value is in the union iff it is in some member.
    Union(Vec<DRange>),
    /// recognised structure but no decision support — emit nothing
    Unknown,
}

fn range_of_named(name: &str) -> DRange {
    if builtin_datatype_key(name) == Some("rdfs:Literal") {
        return DRange::Top;
    }
    match named_dt(name) {
        Some(d) => DRange::Named(d),
        None => DRange::Unknown,
    }
}

/// Interpret a key that has already passed through `datatype_concept_key`.
/// Exact standard source spellings are also accepted for compatibility with
/// clause streams produced by older frontends.  Arbitrary prefixed names are
/// never reduced to their local suffix.
fn range_of_internal_name(name: &str) -> DRange {
    if matches!(name, "Literal" | "rdfs:Literal") {
        return DRange::Top;
    }
    if matches!(name, "PlainLiteral" | "rdf:PlainLiteral") || name.starts_with("iri__") {
        return DRange::Unknown;
    }
    if let Some(datatype) = named_dt_kind(name).or_else(|| named_dt(name)) {
        DRange::Named(datatype)
    } else {
        DRange::Unknown
    }
}

/// Parse the canonical text of a complex range (`__dt__c__…`) back into a
/// structured `DRange`.  The text is the s-expression the frontend serialised.
fn parse_complex(text: &str) -> DRange {
    let mut p = Parser::new(text);
    match p.parse() {
        Ok(node) => range_from_node(&node),
        Err(_) => DRange::Unknown,
    }
}

/// Walk a node's arguments, re-gluing the string-atom + `^^dt`/`@lang`
/// sibling pairs the tokeniser splits, into plain atom tokens.  `None` when a
/// non-atomic argument appears.
fn glued_atoms(args: &[Node]) -> Option<Vec<String>> {
    let refs: Vec<&Node> = args.iter().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < refs.len() {
        if let Some((lit, used)) = super::parse::glue_literal(&refs, i) {
            out.push(lit);
            i += used;
        } else {
            out.push(refs[i].as_atom()?.to_string());
            i += 1;
        }
    }
    Some(out)
}

fn range_from_node(node: &Node) -> DRange {
    match node {
        Node::Atom(s) => range_of_named(s),
        Node::List(h, args) => match *h {
            // Intersection of facet intervals of one base: the conjunction of
            // their facets (exact for IEEE ranks and for decimal intervals).
            "DataIntersectionOf" if args.len() >= 2 => {
                let members: Vec<DRange> = args.iter().map(range_from_node).collect();
                match &members[0] {
                    DRange::Float(first) => {
                        let mut range = first.clone();
                        for member in &members[1..] {
                            let DRange::Float(other) = member else { return DRange::Unknown };
                            if other.part != range.part { return DRange::Unknown; }
                            range.lo = range.lo.max(other.lo);
                            range.hi = range.hi.min(other.hi);
                            range.nan = range.nan && other.nan;
                        }
                        DRange::Float(range)
                    }
                    DRange::Num(first) => {
                        let mut range = first.clone();
                        for member in &members[1..] {
                            let DRange::Num(other) = member else { return DRange::Unknown };
                            if other.base_kind != range.base_kind { return DRange::Unknown; }
                            let tighter_lo = match (&range.min, &other.min) {
                                (None, b) => b.clone(),
                                (a, None) => a.clone(),
                                (Some(a), Some(b)) => match rat_cmp(&a.0, &b.0) {
                                    Some(std::cmp::Ordering::Less) => Some(*b),
                                    Some(std::cmp::Ordering::Greater) => Some(*a),
                                    Some(std::cmp::Ordering::Equal) => Some((a.0, a.1 && b.1)),
                                    None => return DRange::Unknown,
                                },
                            };
                            let tighter_hi = match (&range.max, &other.max) {
                                (None, b) => b.clone(),
                                (a, None) => a.clone(),
                                (Some(a), Some(b)) => match rat_cmp(&a.0, &b.0) {
                                    Some(std::cmp::Ordering::Less) => Some(*a),
                                    Some(std::cmp::Ordering::Greater) => Some(*b),
                                    Some(std::cmp::Ordering::Equal) => Some((a.0, a.1 && b.1)),
                                    None => return DRange::Unknown,
                                },
                            };
                            range.min = tighter_lo;
                            range.max = tighter_hi;
                        }
                        DRange::Num(range)
                    }
                    _ => DRange::Unknown,
                }
            }
            "DataUnionOf" if args.len() >= 2 =>
                DRange::Union(args.iter().map(range_from_node).collect()),
            "DataComplementOf" if args.len() == 1 =>
                DRange::Complement(Box::new(range_from_node(&args[0]))),
            "DataOneOf" => {
                let toks = match glued_atoms(args) {
                    Some(t) => t,
                    None => return DRange::Unknown,
                };
                let mut vals = Vec::new();
                for t in &toks {
                    match parse_literal(t) {
                        Some((v, _)) => vals.push(v),
                        None => return DRange::Unknown,
                    }
                }
                DRange::OneOf(vals)
            }
            "DatatypeRestriction" => {
                let toks = match glued_atoms(args) {
                    Some(t) => t,
                    None => return DRange::Unknown,
                };
                let base = match toks.first() {
                    Some(b) => b.as_str(),
                    None => return DRange::Unknown,
                };
                if let Some(bd) = named_dt(base).filter(|d| matches!(d.part, Partition::Float32 | Partition::Float64)) {
                    let mut range = FloatRange::full(bd.part);
                    if (toks.len() - 1) % 2 != 0 { return DRange::Unknown; }
                    for pair in toks[1..].chunks_exact(2) {
                        let Some(facet) = builtin_facet_key(&pair[0]) else { return DRange::Unknown; };
                        let Some((value, _)) = parse_literal(&pair[1]) else { return DRange::Unknown; };
                        if range.restrict(facet, &value).is_none() { return DRange::Unknown; }
                    }
                    return DRange::Float(range);
                }
                let bd = match named_dt(base) {
                    // Facet restrictions over IEEE float/double need a
                    // representability-aware interval domain; `NumRange` is a
                    // mathematical-rational interval and cannot encode them.
                    Some(d)
                        if d.part == Partition::Numeric
                            && !matches!(d.kind, "float" | "double") =>
                    {
                        d
                    }
                    _ => return DRange::Unknown,
                };
                let mut r = NumRange {
                    base_kind: bd.kind,
                    integral: bd.integral,
                    min: bd.min.map(|m| (Rat::from_int(m), true)),
                    max: bd.max.map(|m| (Rat::from_int(m), true)),
                };
                let mut i = 1;
                while i < toks.len() {
                    let facet = match builtin_facet_key(&toks[i]) {
                        Some(facet) => facet,
                        None => return DRange::Unknown,
                    };
                    let lit = match toks.get(i + 1) {
                        Some(l) => l.as_str(),
                        None => return DRange::Unknown,
                    };
                    let v = match parse_literal(lit) {
                        Some((Val::Num(rv), _)) => rv,
                        _ => return DRange::Unknown,
                    };
                    // At equal endpoints an exclusive bound is the tighter one
                    // (e.g. `nonNegativeInteger minExclusive 0` excludes 0).
                    let tighter_min = |cur: &Option<(Rat, bool)>, nb: (Rat, bool)| match cur {
                        None => Some(nb),
                        Some((c, incl)) => {
                            if c.lt(&nb.0).unwrap_or(false) || (*c == nb.0 && *incl && !nb.1) {
                                Some(nb)
                            } else {
                                *cur
                            }
                        }
                    };
                    let tighter_max = |cur: &Option<(Rat, bool)>, nb: (Rat, bool)| match cur {
                        None => Some(nb),
                        Some((c, incl)) => {
                            if nb.0.lt(c).unwrap_or(false) || (*c == nb.0 && *incl && !nb.1) {
                                Some(nb)
                            } else {
                                *cur
                            }
                        }
                    };
                    match facet {
                        "minInclusive" => r.min = tighter_min(&r.min, (v, true)),
                        "minExclusive" => r.min = tighter_min(&r.min, (v, false)),
                        "maxInclusive" => r.max = tighter_max(&r.max, (v, true)),
                        "maxExclusive" => r.max = tighter_max(&r.max, (v, false)),
                        _ => return DRange::Unknown, // pattern/length/…: opaque
                    }
                    i += 2;
                }
                DRange::Num(r)
            }
            _ => DRange::Unknown, // complement / unions: opaque (sound)
        },
    }
}

/// `v = w`? `None` when not comparable.
fn val_eq(v: &Val, w: &Val) -> Option<bool> {
    match (v, w) {
        (Val::Num(a), Val::Num(b)) => Some(a == b),
        (Val::Float32(a), Val::Float32(b)) => Some(a == b),
        (Val::Float64(a), Val::Float64(b)) => Some(a == b),
        (Val::DateTime(a), Val::DateTime(b)) => Some(a == b),
        (Val::Bool(a), Val::Bool(b)) => Some(a == b),
        (Val::Str(a, la), Val::Str(b, lb)) => Some(a == b && la == lb),
        (Val::Uri(a), Val::Uri(b)) => Some(a == b),
        // cross-partition values are always distinct
        (Val::Num(_), Val::Bool(_) | Val::Str(..))
        | (Val::Bool(_), Val::Num(_) | Val::Str(..))
        | (Val::Str(..), Val::Num(_) | Val::Bool(_)) => Some(false),
        (Val::Opaque(a), Val::Opaque(b)) if a == b => Some(true),
        _ => match (val_partition(v), val_partition(w)) {
            (Some(a), Some(b)) if a != b => Some(false),
            _ => None,
        },
    }
}

fn val_partition(v: &Val) -> Option<Partition> {
    match v {
        Val::Num(_) => Some(Partition::Numeric),
        Val::Float32(_) => Some(Partition::Float32),
        Val::Float64(_) => Some(Partition::Float64),
        Val::DateTime(_) => Some(Partition::Time),
        Val::Bool(_) => Some(Partition::Boolean),
        Val::Str(..) => Some(Partition::Strings),
        Val::Uri(_) => Some(Partition::Uri),
        Val::Opaque(_) => None,
    }
}

fn numeric_base_subsumed(
    sub_kind: &str,
    sub_integral: bool,
    super_kind: &str,
    super_integral: bool,
) -> bool {
    if sub_kind == super_kind {
        return true;
    }
    if matches!(sub_kind, "float" | "double") || matches!(super_kind, "float" | "double") {
        return false;
    }
    if sub_integral {
        return super_integral || matches!(super_kind, "decimal" | "rational" | "real");
    }
    matches!(
        (sub_kind, super_kind),
        ("decimal", "rational" | "real") | ("rational", "real")
    )
}

fn in_num_range(v: &Rat, r: &NumRange) -> Option<bool> {
    if r.integral && !v.is_integer() {
        return Some(false);
    }
    if let Some((m, incl)) = &r.min {
        let ok = if *incl { m.le(v)? } else { m.lt(v)? };
        if !ok {
            return Some(false);
        }
    }
    if let Some((m, incl)) = &r.max {
        let ok = if *incl { v.le(m)? } else { v.lt(m)? };
        if !ok {
            return Some(false);
        }
    }
    Some(true)
}

/// `v ∈ D`?
fn val_in_range(v: &Val, d: &DRange) -> Option<bool> {
    match d {
        DRange::Union(members) => {
            let mut unknown = false;
            for member in members {
                match val_in_range(v, member) {
                    Some(true) => return Some(true),
                    Some(false) => {}
                    None => unknown = true,
                }
            }
            if unknown { None } else { Some(false) }
        }
        DRange::Float(r) => r.contains(v),
        DRange::Top => Some(true),
        DRange::Unknown => None,
        DRange::Complement(inner) => val_in_range(v, inner).map(|member| !member),
        DRange::OneOf(vals) => {
            let mut any_unknown = false;
            for w in vals {
                match val_eq(v, w) {
                    Some(true) => return Some(true),
                    Some(false) => {}
                    None => any_unknown = true,
                }
            }
            if any_unknown {
                None
            } else {
                Some(false)
            }
        }
        DRange::Num(r) => match v {
            Val::Num(rv) => in_num_range(rv, r),
            Val::Bool(_) | Val::Str(..) | Val::Uri(_) | Val::Float32(_) | Val::Float64(_) | Val::DateTime(_) => Some(false),
            Val::Opaque(_) => None,
        },
        DRange::Named(nd) => match v {
            Val::Float32(_) => Some(nd.part == Partition::Float32),
            Val::Float64(_) => Some(nd.part == Partition::Float64),
            Val::DateTime(value) => Some(nd.kind == "dateTime"
                || (nd.kind == "dateTimeStamp" && value.offset.is_some())),
            Val::Num(rv) => {
                if nd.part != Partition::Numeric {
                    return Some(false);
                }
                // `Val::Num` records the exact mathematical value but not a
                // proof that it is representable by IEEE binary32/binary64.
                // Treat float/double membership as unknown.
                if matches!(nd.kind, "float" | "double") {
                    return None;
                }
                if nd.integral && !rv.is_integer() {
                    return Some(false);
                }
                if let Some(min) = nd.min {
                    if !Rat::from_int(min).le(rv)? {
                        return Some(false);
                    }
                }
                if let Some(max) = nd.max {
                    if !rv.le(&Rat::from_int(max))? {
                        return Some(false);
                    }
                }
                // a plain rational is a decimal/real value; float/double
                // value spaces contain only dyadic-representable values, so
                // membership there is unknown unless dyadic — keep it simple
                // and sound: report membership only for the decimal tower.
                Some(true)
            }
            Val::Bool(_) => Some(nd.part == Partition::Boolean),
            Val::Uri(_) => Some(nd.part == Partition::Uri),
            Val::Str(_, lang) => {
                if nd.part != Partition::Strings {
                    return Some(false);
                }
                // language-tagged literals are rdf:PlainLiteral values, not
                // xsd:string-family values
                if lang.is_some() {
                    return Some(false);
                }
                // membership below xsd:string needs lexical checks we do not
                // model: only xsd:string itself is decided
                if nd.str_level == Some(3) {
                    Some(true)
                } else {
                    None
                }
            }
            Val::Opaque(_) => None,
        },
    }
}

/// `D1 ⊑ D2`?
fn range_subsumed(d1: &DRange, d2: &DRange) -> Option<bool> {
    match (d1, d2) {
        (DRange::Float(a), _) if a.empty() => Some(true),
        (DRange::Float(a), DRange::Float(b)) => Some(a.subset(b)),
        (DRange::Float(a), DRange::Named(b)) => Some(a.part == b.part),
        (DRange::Named(a), DRange::Float(b)) => Some(
            matches!(a.part, Partition::Float32 | Partition::Float64)
                && FloatRange::full(a.part).subset(b)),
        (DRange::Float(_), DRange::Num(_)) => Some(false),
        (DRange::Num(_), DRange::Float(_)) => None,

        (_, DRange::Top) => Some(true),
        // A union is below `d2` iff every member is; a member decided
        // outside `d2` refutes it only when that member is non-empty, which
        // we do not track, so only the positive direction is decided.
        (DRange::Union(members), _) => {
            let mut all = true;
            for member in members {
                match range_subsumed(member, d2) {
                    Some(true) => {}
                    _ => all = false,
                }
            }
            all.then_some(true)
        }
        // `d1` is below a union when it is below one member (sufficient).
        (_, DRange::Union(members)) => members
            .iter()
            .any(|member| range_subsumed(d1, member) == Some(true))
            .then_some(true),
        (DRange::Unknown, _) | (_, DRange::Unknown) => None,
        (DRange::OneOf(vals), _) => {
            // every enumerated value in d2
            let mut all = true;
            for v in vals {
                match val_in_range(v, d2) {
                    Some(true) => {}
                    Some(false) => return Some(false),
                    None => all = false,
                }
            }
            if all {
                Some(true)
            } else {
                None
            }
        }
        // subsumption INTO an enumeration: only decidable by enumerating the
        // left side, which the cover machinery handles separately — unknown
        (_, DRange::OneOf(_)) => None,
        (DRange::Complement(_), _) | (_, DRange::Complement(_)) => None,
        (DRange::Named(a), DRange::Named(b)) => {
            if a.kind == b.kind { return Some(true); }
            if a.part != b.part {
                // distinct partitions are disjoint, so subsumption only for
                // empty ranges, which named types are not
                return Some(false);
            }
            match a.part {
                Partition::Numeric => {
                    if a.kind == b.kind {
                        return Some(true);
                    }
                    // IEEE float/double are not the unbounded mathematical
                    // real/decimal value space. Except for reflexivity above,
                    // leave cross-type inclusions unknown.
                    if matches!(a.kind, "float" | "double") || matches!(b.kind, "float" | "double")
                    {
                        return None;
                    }
                    if a.integral && b.integral {
                        let lo_ok = match (a.min, b.min) {
                            (_, None) => true,
                            (Some(am), Some(bm)) => am >= bm,
                            (None, Some(_)) => false,
                        };
                        let hi_ok = match (a.max, b.max) {
                            (_, None) => true,
                            (Some(am), Some(bm)) => am <= bm,
                            (None, Some(_)) => false,
                        };
                        return (lo_ok && hi_ok).then_some(true);
                    }
                    // OWL 2 numeric tower: every integer is a decimal, every
                    // decimal is rational, and every rational is real.
                    if a.integral && matches!(b.kind, "decimal" | "rational" | "real") {
                        return Some(true);
                    }
                    match (a.kind, b.kind) {
                        ("decimal", "rational" | "real") | ("rational", "real") => Some(true),
                        _ => None,
                    }
                }
                Partition::Strings => match (a.kind, b.kind) {
                    (x, y) if x == y => Some(true),
                    ("normalizedString", "string")
                    | ("token", "normalizedString" | "string")
                    | ("language" | "Name" | "NMTOKEN", "token" | "normalizedString" | "string")
                    | ("NCName", "Name" | "token" | "normalizedString" | "string") => Some(true),
                    _ => None,
                },
                _ => (a.kind == b.kind).then_some(true),
            }
        }
        (DRange::Num(r), DRange::Named(b)) => {
            if b.part != Partition::Numeric {
                return Some(false);
            }
            if matches!(b.kind, "float" | "double") {
                return None;
            }
            if !numeric_base_subsumed(r.base_kind, r.integral, b.kind, b.integral) {
                return None;
            }
            if b.integral && !r.integral {
                return None; // interval may still contain non-integers — and bounds unknown side
            }
            let lo_ok = match b.min {
                None => true,
                Some(bm) => match &r.min {
                    Some((m, _)) => Rat::from_int(bm).le(m)?,
                    None => false,
                },
            };
            let hi_ok = match b.max {
                None => true,
                Some(bm) => match &r.max {
                    Some((m, _)) => m.le(&Rat::from_int(bm))?,
                    None => false,
                },
            };
            if lo_ok && hi_ok && (!b.integral || r.integral) {
                Some(true)
            } else {
                None // bounds violated does not refute subsumption of the *value sets* conclusively for exclusive bounds; stay safe
            }
        }
        (DRange::Named(a), DRange::Num(r)) => {
            if a.part != Partition::Numeric {
                return Some(false);
            }
            if matches!(a.kind, "float" | "double") {
                return None;
            }
            if !numeric_base_subsumed(a.kind, a.integral, r.base_kind, r.integral) {
                return None;
            }
            // named ⊑ interval: need the named type's bounds inside r
            let lo_ok = match &r.min {
                None => true,
                Some((m, incl)) => match a.min {
                    Some(am) => {
                        let av = Rat::from_int(am);
                        if *incl {
                            m.le(&av)?
                        } else {
                            m.lt(&av)?
                        }
                    }
                    None => false,
                },
            };
            let hi_ok = match &r.max {
                None => true,
                Some((m, incl)) => match a.max {
                    Some(am) => {
                        let av = Rat::from_int(am);
                        if *incl {
                            av.le(m)?
                        } else {
                            av.lt(m)?
                        }
                    }
                    None => false,
                },
            };
            let int_ok = !r.integral || a.integral;
            if lo_ok && hi_ok && int_ok {
                Some(true)
            } else {
                None
            }
        }
        (DRange::Num(a), DRange::Num(b)) => {
            if !numeric_base_subsumed(a.base_kind, a.integral, b.base_kind, b.integral) {
                return None;
            }
            let lo_ok = match &b.min {
                None => true,
                Some((bm, bincl)) => match &a.min {
                    Some((am, aincl)) => {
                        if bm.lt(am)? {
                            true
                        } else if am == bm {
                            *bincl || !*aincl
                        } else {
                            false
                        }
                    }
                    None => false,
                },
            };
            let hi_ok = match &b.max {
                None => true,
                Some((bm, bincl)) => match &a.max {
                    Some((am, aincl)) => {
                        if am.lt(bm)? {
                            true
                        } else if am == bm {
                            *bincl || !*aincl
                        } else {
                            false
                        }
                    }
                    None => false,
                },
            };
            let int_ok = !b.integral || a.integral;
            if lo_ok && hi_ok && int_ok {
                Some(true)
            } else {
                None
            }
        }
        (DRange::Top, _) => None,
    }
}

/// `D1 ∩ D2 = ∅`?
fn range_disjoint(d1: &DRange, d2: &DRange) -> Option<bool> {
    match (d1, d2) {
        (DRange::Float(a), _) | (_, DRange::Float(a)) if a.empty() => Some(true),
        (DRange::Float(a), DRange::Float(b)) => Some(a.disjoint(b)),
        (DRange::Float(a), DRange::Named(b)) | (DRange::Named(b), DRange::Float(a)) =>
            Some(a.part != b.part),
        (DRange::Float(_), DRange::Num(_)) | (DRange::Num(_), DRange::Float(_)) => Some(true),

        (DRange::Union(members), other) | (other, DRange::Union(members)) => {
            let mut all = true;
            for member in members {
                match range_disjoint(member, other) {
                    Some(true) => {}
                    Some(false) => return Some(false),
                    None => all = false,
                }
            }
            all.then_some(true)
        }
        (DRange::Unknown, _) | (_, DRange::Unknown) => None,
        (DRange::Top, _) | (_, DRange::Top) => Some(false), // named ranges are non-empty
        (DRange::OneOf(vals), other) | (other, DRange::OneOf(vals)) => {
            let mut all_out = true;
            for v in vals {
                match val_in_range(v, other) {
                    Some(true) => return Some(false),
                    Some(false) => {}
                    None => all_out = false,
                }
            }
            if all_out {
                Some(true)
            } else {
                None
            }
        }
        (DRange::Complement(_), _) | (_, DRange::Complement(_)) => None,
        (DRange::Named(a), DRange::Named(b)) => {
            if a.part != b.part {
                return Some(true);
            }
            match a.part {
                Partition::Numeric => {
                    // disjoint iff the integer bounds separate
                    match (a.max, b.min) {
                        (Some(amax), Some(bmin)) if amax < bmin => return Some(true),
                        _ => {}
                    }
                    match (b.max, a.min) {
                        (Some(bmax), Some(amin)) if bmax < amin => return Some(true),
                        _ => {}
                    }
                    Some(false) // numeric named types always share values otherwise (0 or overlap)
                }
                _ => Some(false),
            }
        }
        (DRange::Num(r), DRange::Named(b)) | (DRange::Named(b), DRange::Num(r)) => {
            if b.part != Partition::Numeric {
                return Some(true);
            }
            // separated bounds?
            if let (Some((rmax, rincl)), Some(bmin)) = (&r.max, b.min) {
                let bv = Rat::from_int(bmin);
                let sep = if *rincl { rmax.lt(&bv)? } else { rmax.le(&bv)? };
                if sep {
                    return Some(true);
                }
            }
            if let (Some((rmin, rincl)), Some(bmax)) = (&r.min, b.max) {
                let bv = Rat::from_int(bmax);
                let sep = if *rincl { bv.lt(rmin)? } else { bv.le(rmin)? };
                if sep {
                    return Some(true);
                }
            }
            // an integral-empty interval is handled by emptiness elsewhere
            None
        }
        (DRange::Num(a), DRange::Num(b)) => {
            if let (Some((amax, aincl)), Some((bmin, bincl))) = (&a.max, &b.min) {
                let sep = if *aincl && *bincl {
                    amax.lt(bmin)?
                } else {
                    amax.le(bmin)?
                };
                if sep {
                    return Some(true);
                }
            }
            if let (Some((bmax, bincl)), Some((amin, aincl))) = (&b.max, &a.min) {
                let sep = if *bincl && *aincl {
                    bmax.lt(amin)?
                } else {
                    bmax.le(amin)?
                };
                if sep {
                    return Some(true);
                }
            }
            None
        }
    }
}

/// Enumerate a finite range up to `cap` values (for the covering clause).
fn enumerate_range(d: &DRange, cap: usize) -> Option<Vec<String>> {
    match d {
        DRange::Float(r) if r.empty() => Some(vec![]),
        DRange::OneOf(_) => None, // handled via the serialized literals directly
        DRange::Named(nd) if nd.finite_bool => Some(vec![
            "\"true\"^^xsd:boolean".to_string(),
            "\"false\"^^xsd:boolean".to_string(),
        ]),
        DRange::Num(r) if r.integral => {
            let (min, mincl) = r.min.as_ref()?;
            let (max, maxcl) = r.max.as_ref()?;
            if !min.is_integer() || !max.is_integer() {
                // round inward
            }
            // smallest integer ≥ min (respecting exclusivity)
            let mut lo = div_ceil_rat(min)?;
            if !mincl && Rat::from_int(lo) == *min {
                lo += 1;
            }
            let mut hi = div_floor_rat(max)?;
            if !maxcl && Rat::from_int(hi) == *max {
                hi -= 1;
            }
            if lo > hi {
                return Some(vec![]);
            }
            let n = (hi - lo) as u128 + 1;
            if n > cap as u128 {
                return None;
            }
            Some(
                (lo..=hi)
                    .map(|v| format!("\"{}\"^^xsd:integer", v))
                    .collect(),
            )
        }
        _ => None,
    }
}

fn div_ceil_rat(r: &Rat) -> Option<i128> {
    let q = r.num.div_euclid(r.den);
    if r.num.rem_euclid(r.den) == 0 {
        Some(q)
    } else {
        q.checked_add(1)
    }
}
fn div_floor_rat(r: &Rat) -> Option<i128> {
    Some(r.num.div_euclid(r.den))
}

/// A `__dt__` concept occurring in the clause set, classified.
enum DtEntry {
    Range(String, DRange),
    Value(String, Val),
}

fn classify_name(name: &str) -> Option<DtEntry> {
    let rest = name.strip_prefix("__dt__")?;
    if let Some(lit) = rest.strip_prefix("val__") {
        if lit == "opaque" {
            return None;
        }
        let (v, _) = parse_literal(lit)?;
        return Some(DtEntry::Value(name.to_string(), v));
    }
    if let Some(text) = rest.strip_prefix("c__") {
        return Some(DtEntry::Range(name.to_string(), parse_complex(text)));
    }
    if rest == "opaque" || rest == "val" {
        return None;
    }
    Some(DtEntry::Range(
        name.to_string(),
        range_of_internal_name(rest),
    ))
}

/// Atomic datatype symbols for which the native completion bridge has a
/// complete model in its deliberately narrow `Exists`/`Forall` data fragment.
/// This is not a claim that the whole datatype module is complete. The bridge
/// separately checks source-axiom shape, role-local ranges, cardinalities, and
/// that every generated relation clause is encoded.
pub(crate) fn bridge_exact_atomic_family(name: &str) -> Option<&'static str> {
    let Some(rest) = name.strip_prefix("__dt__") else {
        return None;
    };
    if let Some(literal) = rest.strip_prefix("val__") {
        let Some((value, datatype)) = parse_literal(literal) else {
            return None;
        };
        let builtin = datatype.as_deref().and_then(builtin_datatype_key);
        return match (value, builtin) {
            (Val::Bool(_), Some("boolean")) => Some("boolean"),
            // Integral decimal spellings denote the same values as integer
            // literals. Keep the exact lexical/value check; fractional decimal
            // values remain outside this atomic bridge admission boundary.
            (Val::Num(value), Some("decimal" | "integer" | "int" | "nonNegativeInteger" | "positiveInteger"))
                if value.is_integer() && exact_swrl_integer(literal).is_some() => Some("integer"),
            (Val::Str(_, None), Some("string")) => Some("string"),
            (Val::Str(_, None), None) if datatype.is_none() => Some("string"),
            (Val::Float32(_), Some("float")) => Some("float"),
            (Val::DateTime(_), Some("dateTime")) => Some("dateTime"),
            _ => None,
        };
    }
    if let Some(text) = rest.strip_prefix("c__") {
        // `DataOneOf(false,true)` is extensionally exactly xsd:boolean, not
        // merely a finite subset of it.  Treat either source ordering as the
        // atomic boolean family so the bridge can consume OWL ontologies that
        // spell a data-property range as the explicit two-value enumeration.
        // Every other complex range remains fail-closed.
        let DRange::OneOf(values) = parse_complex(text) else {
            return None;
        };
        if values.len() == 2
            && values.iter().any(|value| matches!(value, Val::Bool(false)))
            && values.iter().any(|value| matches!(value, Val::Bool(true)))
        {
            return Some("boolean");
        }
        return bridge_exact_finite_values(name).map(|_| "finite");
    }
    if matches!(rest, "opaque" | "val") {
        return None;
    }
    match range_of_internal_name(rest) {
        DRange::Named(datatype)
            if matches!(
                datatype.kind,
                "boolean"
                    | "dateTime"
                    | "decimal"
                    | "int"
                    | "integer"
                    | "nonNegativeInteger"
                    | "positiveInteger"
                    | "string"
                    | "float"
            ) =>
        {
            Some(match datatype.kind {
                // Keep the exact range identity in `range_of_internal_name`;
                // this return value is only the disjoint value-space family.
                // The bridge uses `bridge_exact_atomic_subsumed` below for
                // direction-sensitive range checks.
                "decimal" | "int" | "integer" | "nonNegativeInteger" | "positiveInteger" => {
                    "decimal"
                }
                other => other,
            })
        }
        _ => None,
    }
}

/// Explicit finite ranges whose literals all have validated exact values.
/// The bridge must additionally verify an exhaustive cover in its own input.
pub(crate) fn bridge_exact_finite_values(name: &str) -> Option<Vec<String>> {
    let text = name.strip_prefix("__dt__c__")?;
    let mut parser = Parser::new(text);
    let Node::List("DataOneOf", args) = parser.parse().ok()? else { return None };
    let literals = glued_atoms(&args)?;
    if literals.is_empty() { return None; }
    literals.into_iter().map(|literal| {
        let name = format!("__dt__val__{literal}");
        bridge_exact_atomic_name(&name).then_some(name)
    }).collect()
}

/// `true` when `range` is an admitted integral decimal-tower range and every
/// integer it contains lies in one of the admitted integral ranges or integer
/// values named in `head` (the frontend's finite-difference cover).
pub(crate) fn bridge_exact_integral_cover(range: &str, head: &[&str]) -> bool {
    if !bridge_tbox_atomic_name(range) || range.starts_with("__dt__val__") {
        return false;
    }
    let Some(DtEntry::Range(_, outer)) = classify_name(range) else { return false };
    let Some(outer) = integral_interval(&outer) else { return false };
    let mut parts = Vec::new();
    for name in head {
        if !bridge_tbox_atomic_name(name) {
            return false;
        }
        match classify_name(name) {
            Some(DtEntry::Range(_, inner)) => match integral_interval(&inner) {
                Some(interval) => parts.push(interval),
                None => return false,
            },
            Some(DtEntry::Value(_, Val::Num(value))) if value.is_integer() =>
                parts.push((Some(value.num), Some(value.num))),
            _ => return false,
        }
    }
    integral_difference(outer, &parts, 0).is_some_and(|missing| missing.is_empty())
}

/// Bridge-TBox variant of [`bridge_exact_finite_values`]: the enumerated
/// literals may be any value of the bridge-TBox map (e.g. xsd:double,
/// xsd:decimal, xsd:anyURI). The narrow function stays unchanged for the data
/// ABox projection.
pub(crate) fn bridge_tbox_finite_values(name: &str) -> Option<Vec<String>> {
    let text = name.strip_prefix("__dt__c__")?;
    let mut parser = Parser::new(text);
    let Node::List("DataOneOf", args) = parser.parse().ok()? else { return None };
    let literals = glued_atoms(&args)?;
    if literals.is_empty() { return None; }
    literals.into_iter().map(|literal| {
        let name = format!("__dt__val__{literal}");
        bridge_tbox_atomic_name(&name).then_some(name)
    }).collect()
}

/// Bridge-TBox variant of [`bridge_exact_finite_cover`].
pub(crate) fn bridge_tbox_finite_cover(range: &str, head: &[&str]) -> bool {
    let Some(values) = bridge_tbox_finite_values(range) else { return false };
    values.iter().all(|value| head.iter().any(|other|
        bridge_exact_value_equal(value, other) == Some(true)))
        && head.iter().all(|value| values.iter().any(|other|
            bridge_exact_value_equal(value, other) == Some(true)))
}

/// Compare a finite range with a proposed value-concept cover extensionally.
/// Lexical aliases can repeat a value, but cannot omit or add a value.
pub(crate) fn bridge_exact_finite_cover(range: &str, head: &[&str]) -> bool {
    let Some(values) = bridge_exact_finite_values(range) else { return false };
    values.iter().all(|value| head.iter().any(|other|
        bridge_exact_value_equal(value, other) == Some(true)))
        && head.iter().all(|value| values.iter().any(|other|
            bridge_exact_value_equal(value, other) == Some(true)))
}

pub(crate) fn bridge_exact_atomic_name(name: &str) -> bool {
    bridge_exact_atomic_family(name).is_some()
}

/// `true` for a literal whose lexical form is in the xsd:decimal lexical
/// space `(\+|-)?([0-9]+(\.[0-9]*)?|\.[0-9]+)` (no exponent, no padding).
fn exact_decimal_lexical(literal: &str) -> bool {
    let Some(close) = literal.rfind('"') else { return false };
    if !literal.starts_with('"') || close == 0 {
        return false;
    }
    let lex = &literal[1..close];
    let digits = lex.strip_prefix(['+', '-']).unwrap_or(lex);
    let (whole, fraction) = match digits.split_once('.') {
        Some((whole, fraction)) => (whole, Some(fraction)),
        None => (digits, None),
    };
    let all_digits = |text: &str| text.bytes().all(|byte| byte.is_ascii_digit());
    all_digits(whole) && fraction.is_none_or(all_digits)
        && (!whole.is_empty() || fraction.is_some_and(|fraction| !fraction.is_empty()))
}

/// Bridge-TBox extension of [`bridge_exact_atomic_family`]. It is consumed
/// only by the native completion bridge's TBox datatype certificate
/// (`konclude_ht::bridge`), which additionally checks relation-clause
/// evidence, body sensitivity, and exact IEEE cell sizes for the members
/// added here. The data-ABox projection and tableau callers keep the narrower
/// map. The additional members are:
///
/// * `xsd:anyURI` as a named range. OWL 2 (Structural Specification,
///   section 4.6) gives it the set of all IRIs as value space, disjoint from
///   `xsd:string` and from every other datatype of the map except
///   `rdfs:Literal`. Its literal values remain opaque and are not admitted.
/// * `xsd:double` as a named range and its literal values, parsed at binary64
///   width (XSD 1.1 round-half-to-even lexical mapping) and compared by
///   identity: `+0` and `-0` are distinct, `NaN` is one value equal to itself.
/// * Facet intervals `minInclusive/minExclusive/maxInclusive/maxExclusive`
///   over `xsd:double` or `xsd:float` with same-width facet values. Facets
///   compare by IEEE equality (both zeros satisfy a zero bound) and exclude
///   `NaN` (OWL 2 section 4.2, XSD 1.1 section 3.3.4).
/// * `rdfs:Literal`, the top data range ("any set of data values that
///   contains the union of the value spaces of all datatypes").
pub(crate) fn bridge_tbox_atomic_family(name: &str) -> Option<&'static str> {
    if let Some(family) = bridge_exact_atomic_family(name) {
        return Some(family);
    }
    let rest = name.strip_prefix("__dt__")?;
    if let Some(literal) = rest.strip_prefix("val__") {
        let (value, datatype) = parse_literal(literal)?;
        return match (value, datatype.as_deref().and_then(builtin_datatype_key)) {
            (Val::Float64(_), Some("double")) => Some("double"),
            (Val::Uri(_), Some("anyURI")) => Some("anyURI"),
            // xsd:decimal values are exact rationals; the decimal lexical space
            // has no exponent (XSD 1.1 decimalLexicalRep), so require it.
            (Val::Num(_), Some("decimal")) if exact_decimal_lexical(literal) => Some("decimal"),
            _ => None,
        };
    }
    if let Some(text) = rest.strip_prefix("c__") {
        return match parse_complex(text) {
            DRange::Float(range) if range.part == Partition::Float32 => Some("float"),
            DRange::Float(range) if range.part == Partition::Float64 => Some("double"),
            // Facet intervals over the decimal tower (decimal or an integer
            // datatype base). Their realizability is certified by
            // `bridge_decimal_cells_realizable`.
            DRange::Num(range) if !matches!(range.base_kind, "real" | "rational") => Some("decimal"),
            // A union of named datatypes from the exact map. Its semantics
            // reaches the bridge through the member inclusions and the union
            // cover clause, both checked by the bridge.
            DRange::OneOf(_) => bridge_tbox_finite_values(name).map(|_| "finite"),
            DRange::Union(_) => union_member_names(name)
                .filter(|members| members.iter().all(|member| {
                    !member.starts_with("__dt__c__") && bridge_tbox_atomic_name(member)
                }))
                .map(|_| "union"),
            _ => None,
        };
    }
    if matches!(rest, "opaque" | "val") {
        return None;
    }
    match range_of_internal_name(rest) {
        DRange::Top => Some("literal"),
        DRange::Named(datatype) if datatype.kind == "anyURI" => Some("anyURI"),
        DRange::Named(datatype) if datatype.kind == "XMLLiteral" => Some("XMLLiteral"),
        DRange::Named(datatype) if datatype.kind == "double" => Some("double"),
        // Every bounded/unbounded integer datatype of the map (`long`, `short`,
        // `unsignedInt`, `negativeInteger`, ...): an integral interval, decided
        // by `bridge_decimal_cells_realizable` like the narrow members.
        DRange::Named(datatype) if datatype.part == Partition::Numeric && datatype.integral => Some("decimal"),
        _ => None,
    }
}

pub(crate) fn bridge_tbox_atomic_name(name: &str) -> bool {
    bridge_tbox_atomic_family(name).is_some()
}

/// `true` for an admitted IEEE facet interval (`__dt__c__DatatypeRestriction`
/// over float/double), as opposed to a named range or a literal value.
pub(crate) fn bridge_ieee_facet_range(name: &str) -> bool {
    name.strip_prefix("__dt__c__")
        .is_some_and(|text| matches!(parse_complex(text), DRange::Float(_)))
}

/// `true` for an admitted facet interval of any width or base: IEEE
/// (float/double) or decimal tower.
pub(crate) fn bridge_facet_range(name: &str) -> bool {
    bridge_tbox_atomic_name(name)
        && name.strip_prefix("__dt__c__")
            .is_some_and(|text| matches!(parse_complex(text), DRange::Float(_) | DRange::Num(_)))
}

/// `true` for an admitted named or facet decimal-tower range.
pub(crate) fn bridge_decimal_range(name: &str) -> bool {
    !name.starts_with("__dt__val__")
        && bridge_tbox_atomic_family(name) == Some("decimal")
        && DecimalInterval::of(name).is_some()
}

/// `true` for an admitted named or facet IEEE range (not a literal value).
pub(crate) fn bridge_ieee_range(name: &str) -> bool {
    if name.starts_with("__dt__val__") {
        return false;
    }
    matches!(bridge_tbox_atomic_family(name), Some("float" | "double"))
        && bridge_ieee_interval(name).is_some()
}

fn bridge_ieee_interval(name: &str) -> Option<FloatRange> {
    match bridge_exact_atomic_range(name)? {
        DRange::Float(range) => Some(range),
        DRange::Named(datatype) if matches!(datatype.part, Partition::Float32 | Partition::Float64) =>
            Some(FloatRange::full(datatype.part)),
        _ => None,
    }
}

/// An admitted decimal-tower range as an interval of the decimal value
/// space, optionally restricted to integers.
#[derive(Clone, Debug)]
struct DecimalInterval {
    integral: bool,
    lo: Option<(Rat, bool)>,
    hi: Option<(Rat, bool)>,
}

impl DecimalInterval {
    fn of(name: &str) -> Option<Self> {
        match bridge_exact_atomic_range(name)? {
            DRange::Named(datatype)
                if datatype.part == Partition::Numeric
                    && !matches!(datatype.kind, "float" | "double" | "real" | "rational") =>
            {
                Some(Self {
                    integral: datatype.integral,
                    lo: datatype.min.map(|bound| (Rat::from_int(bound), true)),
                    hi: datatype.max.map(|bound| (Rat::from_int(bound), true)),
                })
            }
            DRange::Num(range) if !matches!(range.base_kind, "real" | "rational") => Some(Self {
                integral: range.integral,
                lo: range.min,
                hi: range.max,
            }),
            _ => None,
        }
    }

    /// Interval membership of a decimal value, ignoring integrality.
    fn spans(&self, value: &Rat) -> Option<bool> {
        if let Some((bound, inclusive)) = &self.lo {
            if !(if *inclusive { bound.le(value)? } else { bound.lt(value)? }) {
                return Some(false);
            }
        }
        if let Some((bound, inclusive)) = &self.hi {
            if !(if *inclusive { value.le(bound)? } else { value.lt(bound)? }) {
                return Some(false);
            }
        }
        Some(true)
    }

    fn contains(&self, value: &Rat) -> Option<bool> {
        Some((!self.integral || value.is_integer()) && self.spans(value)?)
    }
}

fn rat_cmp(left: &Rat, right: &Rat) -> Option<std::cmp::Ordering> {
    let a = left.num.checked_mul(right.den)?;
    let b = right.num.checked_mul(left.den)?;
    Some(a.cmp(&b))
}

fn rat_midpoint(left: &Rat, right: &Rat) -> Option<Rat> {
    let num = left.num.checked_mul(right.den)?.checked_add(right.num.checked_mul(left.den)?)?;
    Rat::new(num, left.den.checked_mul(right.den)?.checked_mul(2)?)
}

/// Number of integers strictly between `lo` and `hi` (`None` bound is
/// unbounded); saturates at `u128::MAX`.
fn integers_strictly_between(lo: Option<&Rat>, hi: Option<&Rat>) -> Option<u128> {
    let (Some(lo), Some(hi)) = (lo, hi) else { return Some(u128::MAX) };
    let first = if lo.is_integer() { lo.num.checked_add(1)? } else { div_floor_rat(lo)?.checked_add(1)? };
    let last = if hi.is_integer() { hi.num.checked_sub(1)? } else { div_floor_rat(hi)? };
    Some(if last < first { 0 } else { (last - first) as u128 + 1 })
}

/// Number of values of `interval` (saturating; `u128::MAX` = infinite) and
/// how many of them are among `values`.
fn decimal_interval_capacity(interval: &DecimalInterval, values: &[Rat]) -> Option<(u128, u128)> {
    let occupied = values.iter().map(|value| interval.contains(value)).collect::<Option<Vec<bool>>>()?
        .into_iter().filter(|&inside| inside).count() as u128;
    let size: u128 = if interval.integral {
        let lo = match &interval.lo {
            None => None,
            Some((bound, inclusive)) => {
                let floor = div_floor_rat(bound)?;
                Some(if bound.is_integer() && *inclusive { floor } else { floor.checked_add(1)? })
            }
        };
        let hi = match &interval.hi {
            None => None,
            Some((bound, inclusive)) => {
                let floor = div_floor_rat(bound)?;
                Some(if bound.is_integer() && !inclusive { floor.checked_sub(1)? } else { floor })
            }
        };
        match (lo, hi) {
            (Some(lo), Some(hi)) if hi < lo => 0,
            (Some(lo), Some(hi)) => (hi - lo) as u128 + 1,
            _ => u128::MAX,
        }
    } else {
        match (&interval.lo, &interval.hi) {
            (Some((lo, li)), Some((hi, hi_inc))) => match rat_cmp(lo, hi)? {
                std::cmp::Ordering::Greater => 0,
                std::cmp::Ordering::Equal => u128::from(*li && *hi_inc),
                std::cmp::Ordering::Less => u128::MAX,
            },
            _ => u128::MAX,
        }
    };
    Some((size, occupied))
}

/// Values of the decimal-tower range `name` that are not among `literals`
/// (saturating; `u128::MAX` = infinite). `None` when undecided.
pub(crate) fn bridge_decimal_free_capacity(name: &str, literals: &[&str]) -> Option<u128> {
    let interval = DecimalInterval::of(name)?;
    let mut values: Vec<Rat> = Vec::new();
    for literal in literals {
        let Some(token) = literal.strip_prefix("__dt__val__") else { continue };
        match parse_literal(token) {
            Some((Val::Num(value), _)) => if !values.contains(&value) { values.push(value) },
            Some((Val::Opaque(_), datatype))
                if datatype.as_deref().and_then(builtin_datatype_key).and_then(named_dt_kind)
                    .is_some_and(|d| d.part == Partition::Numeric) => return None,
            _ => {}
        }
    }
    let (size, occupied) = decimal_interval_capacity(&interval, &values)?;
    Some(size.saturating_sub(occupied))
}

/// Fast exact path of [`bridge_decimal_cells_realizable`] for a cell-covered
/// vocabulary. A member is *atomic* when the present clauses relate it to
/// every other member by inclusion or disjointness. When every non-atomic
/// member has a present cover whose heads are all atomic, every admissible
/// label contains an atomic `C` and then equals the inclusion closure of `C`
/// (any other member is disjoint from `C`). Such a label is realized exactly
/// by the values of `C`, so it suffices that each atomic member holds
/// `required` values outside `literals`. `None` = not applicable.
fn decimal_cells_by_atoms(
    ranges: &[&str],
    intervals: &[DecimalInterval],
    inclusion: &dyn Fn(usize, usize) -> bool,
    disjoint: &dyn Fn(usize, usize) -> bool,
    literals: &[&str],
    required: u128,
    covers: &[(usize, Vec<usize>)],
) -> Option<bool> {
    let k = ranges.len();
    let atomic: Vec<bool> = (0..k)
        .map(|i| (0..k).all(|j| i == j || inclusion(i, j) || disjoint(i, j)))
        .collect();
    let covered = (0..k).all(|i| atomic[i] || covers.iter().any(|(body, heads)|
        *body == i && !heads.is_empty() && heads.iter().all(|&head| atomic[head])));
    if !covered {
        return None;
    }
    let mut values: Vec<Rat> = Vec::new();
    for literal in literals {
        let Some(token) = literal.strip_prefix("__dt__val__") else { continue };
        match parse_literal(token) {
            Some((Val::Num(value), _)) => if !values.contains(&value) { values.push(value) },
            Some((Val::Opaque(_), _)) => return None,
            _ => {}
        }
    }
    for (index, interval) in intervals.iter().enumerate() {
        if !atomic[index] {
            continue;
        }
        let (size, occupied) = decimal_interval_capacity(interval, &values)?;
        if size.saturating_sub(occupied) < required {
            if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
                eprintln!("BRIDGE-DECIMAL-CELL: atomic={} size={size} occupied={occupied} required={required}", ranges[index]);
            }
            return Some(false);
        }
    }
    Some(true)
}

/// Exact cell certificate for the decimal-tower ranges (`decimal`, the
/// admitted integer datatypes, and decimal/integer facet intervals); the
/// counterpart of [`bridge_ieee_cells_realizable`] with the same obligation:
/// every label set `S` closed under the present inclusions and free of
/// present disjoint pairs needs two values that lie in every range of `S`,
/// in no body-sensitive range outside `S`, and that are no present literal.
///
/// Values are counted exactly over the decimal line cut at every range
/// endpoint: an open piece holds infinitely many decimals (or the exact
/// number of integers when a member of `S` is integral); an endpoint piece
/// holds one value. For example, with `nonNegativeInteger` and a
/// body-sensitive `positiveInteger`, the label `{nonNegativeInteger}` is
/// realized only by `0`, so two forced-distinct successors fail the
/// certificate.
pub(crate) fn bridge_decimal_cells_realizable(
    ranges: &[&str],
    body_sensitive: &[bool],
    inclusion: &dyn Fn(usize, usize) -> bool,
    disjoint: &dyn Fn(usize, usize) -> bool,
    literals: &[&str],
    required: u128,
    covers: &[(usize, Vec<usize>)],
) -> Option<bool> {
    if ranges.is_empty() {
        return Some(true);
    }
    if body_sensitive.len() != ranges.len() {
        return None;
    }
    let intervals: Vec<DecimalInterval> =
        ranges.iter().map(|name| DecimalInterval::of(name)).collect::<Option<_>>()?;
    if let Some(decided) = decimal_cells_by_atoms(ranges, &intervals, inclusion, disjoint, literals, required, covers) {
        return Some(decided);
    }
    if ranges.len() > 20 {
        return None;
    }
    let mut values: Vec<Rat> = Vec::new();
    for literal in literals {
        let Some(token) = literal.strip_prefix("__dt__val__") else { continue };
        match parse_literal(token) {
            Some((Val::Num(value), _)) => values.push(value),
            Some((Val::Opaque(_), datatype))
                if datatype.as_deref().and_then(builtin_datatype_key)
                    .and_then(named_dt_kind).is_some_and(|d| d.part == Partition::Numeric
                        && !matches!(d.kind, "float" | "double")) => return None,
            _ => {}
        }
    }
    let mut unique: Vec<Rat> = Vec::new();
    for value in values {
        if !unique.contains(&value) {
            unique.push(value);
        }
    }
    let values = unique;
    // Cut points: every finite endpoint, sorted and deduplicated.
    let mut cuts: Vec<Rat> = Vec::new();
    for interval in &intervals {
        for (bound, _) in interval.lo.iter().chain(interval.hi.iter()) {
            cuts.push(*bound);
        }
    }
    let mut failed = false;
    cuts.sort_by(|a, b| rat_cmp(a, b).unwrap_or_else(|| { failed = true; std::cmp::Ordering::Equal }));
    if failed {
        return None;
    }
    cuts.dedup();
    enum Piece { Open(Option<Rat>, Option<Rat>), Point(Rat) }
    let mut pieces: Vec<Piece> = Vec::new();
    let mut previous: Option<Rat> = None;
    for cut in &cuts {
        pieces.push(Piece::Open(previous, Some(*cut)));
        pieces.push(Piece::Point(*cut));
        previous = Some(*cut);
    }
    pieces.push(Piece::Open(previous, None));
    let k = ranges.len();
    // Per piece: representative membership vector and per-domain capacity.
    struct Cell { spans: u32, point: Option<Rat>, lo: Option<Rat>, hi: Option<Rat> }
    let mut cells: Vec<Cell> = Vec::new();
    for piece in pieces {
        let (representative, point, lo, hi) = match piece {
            Piece::Point(value) => (value, Some(value), None, None),
            Piece::Open(None, None) => (Rat::from_int(0), None, None, None),
            Piece::Open(None, Some(hi)) => (Rat::new(hi.num.checked_sub(hi.den)?, hi.den)?, None, None, Some(hi)),
            Piece::Open(Some(lo), None) => (Rat::new(lo.num.checked_add(lo.den)?, lo.den)?, None, Some(lo), None),
            Piece::Open(Some(lo), Some(hi)) => (rat_midpoint(&lo, &hi)?, None, Some(lo), Some(hi)),
        };
        let mut spans = 0u32;
        for (index, interval) in intervals.iter().enumerate() {
            if interval.spans(&representative)? {
                spans |= 1 << index;
            }
        }
        cells.push(Cell { spans, point, lo, hi });
    }
    let sensitive = body_sensitive.iter().enumerate()
        .fold(0u32, |mask, (index, &flag)| if flag { mask | (1 << index) } else { mask });
    let integral_mask = intervals.iter().enumerate()
        .fold(0u32, |mask, (index, range)| if range.integral { mask | (1 << index) } else { mask });
    for set in 1u32..(1u32 << k) {
        let member = |index: usize| set & (1 << index) != 0;
        let closed = (0..k).all(|i| !member(i) || (0..k).all(|j| member(j) || !inclusion(i, j)));
        if !closed {
            continue;
        }
        if (0..k).any(|i| member(i) && (i..k).any(|j| member(j) && disjoint(i, j))) {
            continue;
        }
        // A present cover clause `A -> B1 ∨ … ∨ values` forces a non-value
        // node labelled `A` to carry one of the range heads.
        if covers.iter().any(|(body, heads)| member(*body) && !heads.iter().any(|&h| member(h))) {
            continue;
        }
        let integers_only = set & integral_mask != 0;
        let excluded = sensitive & !set;
        let mut available: u128 = 0;
        for cell in &cells {
            if cell.spans & set != set {
                continue;
            }
            let blocking = cell.spans & excluded;
            match &cell.point {
                Some(value) => {
                    if integers_only && !value.is_integer() {
                        continue;
                    }
                    // A non-integral excluded range removes the point; an
                    // integral one only when the point is an integer.
                    let removed = (0..k).any(|j| blocking & (1 << j) != 0
                        && (!intervals[j].integral || value.is_integer()));
                    if removed || values.iter().any(|literal| literal == value) {
                        continue;
                    }
                    available = available.saturating_add(1);
                }
                None => {
                    let removed_all = (0..k).any(|j| blocking & (1 << j) != 0
                        && (!intervals[j].integral || integers_only));
                    if removed_all {
                        continue;
                    }
                    if !integers_only {
                        // Infinitely many non-integer decimals remain; integral
                        // exclusions and finitely many literals cannot exhaust them.
                        available = u128::MAX;
                        continue;
                    }
                    let count = integers_strictly_between(cell.lo.as_ref(), cell.hi.as_ref())?;
                    let mut occupied = 0u128;
                    for literal in &values {
                        if !literal.is_integer() { continue; }
                        let above = match &cell.lo { Some(lo) => lo.lt(literal)?, None => true };
                        let below = match &cell.hi { Some(hi) => literal.lt(hi)?, None => true };
                        if above && below { occupied += 1; }
                    }
                    available = available.saturating_add(count.saturating_sub(occupied));
                }
            }
        }
        if available < required {
            if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
                let labels: Vec<&str> = (0..k).filter(|&index| member(index)).map(|index| ranges[index]).collect();
                eprintln!("BRIDGE-DECIMAL-CELL: label={labels:?} available={available} required={required}");
            }
            return Some(false);
        }
    }
    Some(true)
}

/// Exact cell certificate for the IEEE ranges of one width.
///
/// The completion bridge treats data ranges as atomic concepts related only
/// by the pairwise inclusion/disjointness clauses present in its input. A
/// completion graph can therefore label a data node with any set `S` of
/// ranges that is closed under the present inclusions and contains no
/// present disjoint pair. Translating that graph into an OWL model replaces
/// the node by a concrete value `v`; this is faithful when
///
/// * `v` lies in every range of `S` (positive/head occurrences), and
/// * `v` lies in no body-sensitive range outside `S` (a range with a
///   negative-polarity occurrence, i.e. an HT body occurrence other than a
///   pure relation clause), and
/// * `v` is none of the literal values present in the vocabulary (so value
///   concepts and singleton merges keep their abstract truth).
///
/// At most two sibling data nodes are ever forced distinct in the admitted
/// fragment (data cardinalities are bounded by two), so the caller requires
/// `required = 2` such values when the input can force two distinct data
/// successors, and `1` otherwise (then unforced data siblings may share a
/// value and only body-sensitive literals need to be avoided).
/// Values are counted exactly over binary32/binary64 ranks, with `NaN` as a
/// separate single value that only the unrestricted named range contains.
///
/// `None` means the certificate could not be evaluated (unknown range,
/// mixed widths, or more than 16 ranges); callers must fail closed.
pub(crate) fn bridge_ieee_cells_realizable(
    ranges: &[&str],
    body_sensitive: &[bool],
    inclusion: &dyn Fn(usize, usize) -> bool,
    disjoint: &dyn Fn(usize, usize) -> bool,
    literals: &[&str],
    required: u128,
) -> Option<bool> {
    if ranges.is_empty() {
        return Some(true);
    }
    if ranges.len() > 16 || body_sensitive.len() != ranges.len() {
        return None;
    }
    let intervals: Vec<FloatRange> = ranges.iter().map(|name| bridge_ieee_interval(name))
        .collect::<Option<_>>()?;
    let part = intervals[0].part;
    if intervals.iter().any(|range| range.part != part) {
        return None;
    }
    let full = FloatRange::full(part);
    // Literal values of this width, by rank (finite/infinite) or NaN.
    let mut literal_ranks: Vec<u64> = Vec::new();
    let mut literal_nan = false;
    for literal in literals {
        let Some(token) = literal.strip_prefix("__dt__val__") else { continue };
        let Some((value, _)) = parse_literal(token) else { continue };
        match full.value_bits(&value) {
            Some((_, true)) => literal_nan = true,
            Some((bits, false)) => literal_ranks.push(FloatRange::rank(bits, part)),
            None => {}
        }
    }
    literal_ranks.sort_unstable();
    literal_ranks.dedup();
    // Elementary segments of [full.lo, full.hi] on which every interval's
    // membership is constant.
    let mut cuts: Vec<u128> = vec![full.lo as u128, full.hi as u128 + 1];
    for range in &intervals {
        if range.lo <= range.hi {
            cuts.push((range.lo.max(full.lo)) as u128);
            cuts.push((range.hi.min(full.hi)) as u128 + 1);
        }
    }
    cuts.retain(|&cut| cut >= full.lo as u128 && cut <= full.hi as u128 + 1);
    cuts.sort_unstable();
    cuts.dedup();
    let mut counts: std::collections::HashMap<u32, u128> = std::collections::HashMap::new();
    for window in cuts.windows(2) {
        let (start, end) = (window[0], window[1]); // [start, end)
        let mask = intervals.iter().enumerate().fold(0u32, |mask, (index, range)| {
            if range.lo <= range.hi && range.lo as u128 <= start && start <= range.hi as u128 {
                mask | (1 << index)
            } else {
                mask
            }
        });
        let occupied = literal_ranks.iter()
            .filter(|&&rank| start <= rank as u128 && (rank as u128) < end).count() as u128;
        *counts.entry(mask).or_default() += (end - start) - occupied;
    }
    let nan_mask = intervals.iter().enumerate()
        .fold(0u32, |mask, (index, range)| if range.nan { mask | (1 << index) } else { mask });
    if !literal_nan {
        *counts.entry(nan_mask).or_default() += 1;
    }
    let sensitive = body_sensitive.iter().enumerate()
        .fold(0u32, |mask, (index, &flag)| if flag { mask | (1 << index) } else { mask });
    let k = ranges.len();
    for set in 1u32..(1u32 << k) {
        let member = |index: usize| set & (1 << index) != 0;
        let closed = (0..k).all(|i| !member(i) || (0..k).all(|j| member(j) || !inclusion(i, j)));
        if !closed {
            continue;
        }
        let clash = (0..k).any(|i| member(i) && (i..k).any(|j| member(j) && disjoint(i, j)));
        if clash {
            continue;
        }
        let available: u128 = counts.iter()
            .filter(|(&vector, _)| vector & set == set && (vector & !set & sensitive) == 0)
            .map(|(_, &count)| count)
            .sum();
        if available < required {
            return Some(false);
        }
    }
    Some(true)
}

fn bridge_exact_atomic_range(name: &str) -> Option<DRange> {
    match classify_name(name)? {
        DtEntry::Range(_, range) => Some(range),
        DtEntry::Value(_, value) => Some(DRange::OneOf(vec![value])),
    }
}

/// Exact subset relation between two atomic bridge datatype symbols.
///
/// Unlike [`bridge_exact_atomic_family`], this preserves direction in the
/// numeric tower (`positiveInteger <= nonNegativeInteger <= integer <=
/// decimal`) and checks literal membership through the same OWL 2 datatype
/// implementation that emits the frontend relation clauses.
pub(crate) fn bridge_exact_atomic_subsumed(sub: &str, sup: &str) -> Option<bool> {
    if !bridge_tbox_atomic_name(sub) || !bridge_tbox_atomic_name(sup) {
        return None;
    }
    if sub == sup {
        return Some(true);
    }
    range_subsumed(
        &bridge_exact_atomic_range(sub)?,
        &bridge_exact_atomic_range(sup)?,
    )
}

/// Exact disjointness relation for two admitted atomic bridge datatype
/// symbols. `None` remains a fail-closed unknown.
pub(crate) fn bridge_exact_atomic_disjoint(left: &str, right: &str) -> Option<bool> {
    if !bridge_tbox_atomic_name(left) || !bridge_tbox_atomic_name(right) {
        return None;
    }
    range_disjoint(
        &bridge_exact_atomic_range(left)?,
        &bridge_exact_atomic_range(right)?,
    )
}

/// Equality in the deliberately narrow literal value fragment used by exact
/// certificates.  `None` means that lexical-to-value canonicalisation is not
/// fully represented and callers must not infer either equality or
/// disjointness.  In particular this excludes XML whitespace-derived strings
/// and IEEE float/double values.
pub(crate) fn exact_literal_value_equal(left: &str, right: &str) -> Option<bool> {
    fn exact_value(literal: &str) -> Option<Val> {
        let (value, datatype) = parse_literal(literal)?;
        let builtin = datatype.as_deref().and_then(builtin_datatype_key);
        match (&value, builtin) {
            (Val::Bool(_), Some("boolean")) => Some(value),
            (Val::Num(number), Some("integer")) if number.is_integer() => Some(value),
            (Val::Str(_, None), Some("string")) => Some(value),
            // OWL functional syntax abbreviates xsd:string literals by
            // omitting the datatype; language-tagged literals stay separate.
            (Val::Str(_, None), None) if datatype.is_none() => Some(value),
            _ => None,
        }
    }

    let left = exact_value(left)?;
    let right = exact_value(right)?;
    val_eq(&left, &right)
}

pub(crate) fn exact_ieee_literal(literal: &str) -> bool {
    matches!(parse_literal(literal), Some((Val::Float32(_) | Val::Float64(_), _)))
}
pub(crate) fn exact_datetime_literal(literal: &str) -> bool {
    matches!(parse_literal(literal), Some((Val::DateTime(_), _)))
}

pub(crate) fn bridge_exact_value_equal(left: &str, right: &str) -> Option<bool> {
    if !bridge_tbox_atomic_name(left) || !bridge_tbox_atomic_name(right) {
        return None;
    }
    let left = left.strip_prefix("__dt__val__")?;
    let right = right.strip_prefix("__dt__val__")?;
    let left_value = parse_literal(left)?.0;
    let right_value = parse_literal(right)?.0;
    // Atomic admission above has checked integer lexical forms and subtype
    // bounds. Their exact rational values preserve cross-datatype identity.
    // IEEE values compare by identity of the parsed binary32/binary64 datum
    // (OWL 2 section 4.2: +0 and -0 are distinct data values, NaN is one
    // value identical to itself); the two widths are disjoint value spaces.
    if matches!(left_value, Val::Float32(_) | Val::Float64(_) | Val::Num(_) | Val::DateTime(_) | Val::Uri(_))
        || matches!(right_value, Val::Float32(_) | Val::Float64(_) | Val::Num(_) | Val::DateTime(_) | Val::Uri(_)) {
        return val_eq(&left_value, &right_value);
    }
    exact_literal_value_equal(left, right)
}

fn cx(name: &str) -> Atom {
    Atom::Concept(name.to_string(), Term::Var("x".to_string()))
}

/// Singleton clause for a value concept: a data node IS its value, so two
/// nodes carrying the same value concept are equal —
/// `__dt__val__v(z₁) ∧ __dt__val__v(z₂) → z₁ ≈ z₂`.  This is what makes
/// finite-range counting clash: a cover plus value disjointness pins each
/// node to a value, and the singleton clauses merge nodes sharing one,
/// contradicting the `≉` witnesses of a `≥ n` restriction.
fn singleton_clause(name: &str) -> DLClause {
    let z1 = Term::Var("y0".to_string());
    let z2 = Term::Var("y1".to_string());
    clause(
        [
            Atom::Concept(name.to_string(), z1.clone()),
            Atom::Concept(name.to_string(), z2.clone()),
        ],
        [Atom::Eq(z1, z2)],
    )
}

/// Check that the relation generator can decide every pair in this vocabulary.
/// This checks value equality, membership and range relations only. It does not
/// certify a concrete-domain model, source coverage, or worker admission.
pub fn datatype_relations_decidable(names: &BTreeSet<String>) -> Result<(), String> {
    let entries: Vec<_> = names.iter().map(|name| classify_name(name)
        .ok_or_else(|| format!("unrecognized datatype concept: {name}")))
        .collect::<Result<_, _>>()?;
    for (i, left) in entries.iter().enumerate() {
        for right in entries.iter().skip(i) {
            let decided = match (left, right) {
                (DtEntry::Value(_, a), DtEntry::Value(_, b)) => val_eq(a, b).is_some(),
                (DtEntry::Value(_, value), DtEntry::Range(_, range))
                | (DtEntry::Range(_, range), DtEntry::Value(_, value)) =>
                    val_in_range(value, range).is_some(),
                (DtEntry::Range(_, a), DtEntry::Range(_, b)) =>
                    range_subsumed(a, b).is_some() && range_subsumed(b, a).is_some()
                        && range_disjoint(a, b).is_some(),
            };
            if !decided {
                return Err(format!("undecided datatype relation at vocabulary indices {i}"));
            }
        }
    }
    Ok(())
}

/// Exact truth of this vocabulary at one concrete literal value. Restrict the
/// literal decoder to the bridge's exact value fragment; unknown membership
/// or an opaque vocabulary value yields no realization evidence.
pub(crate) fn finite_literal_datatype_truth(literal: &str, names: &[String]) -> Option<Vec<bool>> {
    if !bridge_exact_atomic_name(&format!("__dt__val__{literal}")) { return None; }
    let (value, _) = parse_literal(literal)?;
    names.iter().map(|name| match classify_name(name)? {
        DtEntry::Value(_, other) => {
            if !bridge_exact_atomic_name(name) { return None; }
            val_eq(&value, &other)
        }
        DtEntry::Range(_, range) => val_in_range(&value, &range),
    }).collect()
}

#[cfg(test)]
mod finite_literal_realization_tests {
    use super::*;
    #[test]
    fn concrete_profiles_preserve_rounding_signed_zero_and_range_membership() {
        let names = vec!["__dt__val__\"16777217\"^^xsd:float".into(),
            "__dt__val__\"0\"^^xsd:float".into(), "__dt__val__\"-0\"^^xsd:float".into(),
            "__dt__float".into(), "__dt__double".into(), "__dt__string".into()];
        assert_eq!(finite_literal_datatype_truth("\"16777216\"^^xsd:float", &names), Some(vec![true,false,false,true,false,false]));
        assert_eq!(finite_literal_datatype_truth("\"0\"^^xsd:float", &names), Some(vec![false,true,false,true,false,false]));
        assert_eq!(finite_literal_datatype_truth("\"-0\"^^xsd:float", &names), Some(vec![false,false,true,true,false,false]));
        assert_eq!(finite_literal_datatype_truth("\"text\"^^xsd:string", &names), Some(vec![false,false,false,false,false,true]));
    }
    #[test]
    fn opaque_values_and_unknown_ranges_do_not_produce_evidence() {
        assert!(finite_literal_datatype_truth("\"NULL\"^^rdfs:Literal", &[]).is_none());
        assert!(finite_literal_datatype_truth("\"x\"^^xsd:string", &["__dt__unknown".into()]).is_none());
        assert!(finite_literal_datatype_truth("\"x\"^^xsd:string", &["__dt__val__\"x\"^^rdfs:Literal".into()]).is_none());
    }
}

/// Member concept names of a `DataUnionOf` whose members are all named
/// datatypes; `None` for any other symbol.
pub(crate) fn union_member_names(name: &str) -> Option<Vec<String>> {
    let text = name.strip_prefix("__dt__c__")?;
    let mut parser = Parser::new(text);
    let Node::List("DataUnionOf", args) = parser.parse().ok()? else { return None };
    if args.len() < 2 {
        return None;
    }
    args.iter()
        .map(|arg| arg.as_atom().map(|atom| format!("__dt__{}", datatype_concept_key(atom))))
        .collect()
}

/// `true` when `range` is a `DataUnionOf` of named datatypes and `head`
/// names every member: then `range(x) -> head` is valid.
pub(crate) fn bridge_exact_union_cover(range: &str, head: &[&str]) -> bool {
    union_member_names(range).is_some_and(|members|
        members.iter().all(|member| head.contains(&member.as_str())))
}

/// Upper bound on the cells of one role group; larger groups keep the
/// pairwise relation clauses only (and the bridge's cell certificate defers).
const MAX_INTEGRAL_CELLS: usize = 64;

/// Name of the integral cell `[lo, hi]` (`None` = unbounded).
fn integral_cell_name(lo: Option<i128>, hi: Option<i128>) -> String {
    match (lo, hi) {
        (Some(lo), Some(hi)) if lo == hi => format!("__dt__val__\"{lo}\"^^xsd:integer"),
        (None, None) => "__dt__integer".to_string(),
        (Some(lo), None) => format!("__dt__c__DatatypeRestriction(xsd:integer xsd:minInclusive \"{lo}\"^^xsd:integer)"),
        (None, Some(hi)) => format!("__dt__c__DatatypeRestriction(xsd:integer xsd:maxInclusive \"{hi}\"^^xsd:integer)"),
        (Some(lo), Some(hi)) => format!(
            "__dt__c__DatatypeRestriction(xsd:integer xsd:minInclusive \"{lo}\"^^xsd:integer xsd:maxInclusive \"{hi}\"^^xsd:integer)"),
    }
}

/// Cell covers `(A, [C1..Cm])` for every integral range `A` of a role group
/// that another integral range of the group splits. Groups with fewer than
/// two integral ranges, or more than `MAX_INTEGRAL_CELLS` cells, get none.
fn integral_cell_covers(names: &BTreeSet<String>, groups: &[BTreeSet<String>]) -> Vec<(String, Vec<String>)> {
    let mut out: Vec<(String, Vec<String>)> = Vec::new();
    let mut seen: BTreeSet<(String, Vec<String>)> = BTreeSet::new();
    for group in groups {
        let ranges: Vec<(&String, (Option<i128>, Option<i128>))> = names.iter()
            .filter(|name| group.contains(*name) && !name.starts_with("__dt__val__"))
            .filter_map(|name| match classify_name(name)? {
                DtEntry::Range(_, range) => integral_interval(&range).map(|interval| (name, interval)),
                DtEntry::Value(..) => None,
            })
            .filter(|(_, interval)| !matches!(interval, (Some(lo), Some(hi)) if lo > hi))
            .collect();
        if ranges.len() < 2 {
            continue;
        }
        let mut cuts: Vec<i128> = Vec::new();
        let mut overflow = false;
        for (_, (lo, hi)) in &ranges {
            if let Some(lo) = lo { cuts.push(*lo); }
            if let Some(hi) = hi {
                match hi.checked_add(1) { Some(next) => cuts.push(next), None => overflow = true }
            }
        }
        if overflow {
            continue;
        }
        cuts.sort_unstable();
        cuts.dedup();
        let mut segments: Vec<(Option<i128>, Option<i128>)> = Vec::new();
        let mut previous: Option<i128> = None;
        for &cut in &cuts {
            segments.push((previous, Some(cut - 1)));
            previous = Some(cut);
        }
        segments.push((previous, None));
        let inside = |segment: &(Option<i128>, Option<i128>), range: &(Option<i128>, Option<i128>)| {
            let lower = match (range.0, segment.0) { (None, _) => true, (Some(_), None) => false, (Some(r), Some(s)) => r <= s };
            let upper = match (range.1, segment.1) { (None, _) => true, (Some(_), None) => false, (Some(r), Some(s)) => s <= r };
            lower && upper
        };
        let segments: Vec<_> = segments.into_iter()
            .filter(|segment| ranges.iter().any(|(_, range)| inside(segment, range)))
            .collect();
        if segments.len() > MAX_INTEGRAL_CELLS {
            continue;
        }
        let cell_names: Vec<String> = segments.iter().map(|segment| {
            ranges.iter().find(|(_, range)| range == segment)
                .map(|(name, _)| (*name).clone())
                .unwrap_or_else(|| integral_cell_name(segment.0, segment.1))
        }).collect();
        for (name, range) in &ranges {
            let heads: Vec<String> = segments.iter().zip(&cell_names)
                .filter(|(segment, _)| inside(segment, range))
                .map(|(_, cell)| cell.clone())
                .collect();
            if heads.len() == 1 && heads[0] == **name {
                continue; // the range is itself a cell
            }
            if seen.insert(((*name).clone(), heads.clone())) {
                out.push(((*name).clone(), heads));
            }
        }
    }
    out
}

/// The integer interval `[lo, hi]` (`None` = unbounded) of an integral
/// decimal-tower range; `None` for every other range.
fn integral_interval(range: &DRange) -> Option<(Option<i128>, Option<i128>)> {
    match range {
        DRange::Named(datatype)
            if datatype.part == Partition::Numeric && datatype.integral =>
            Some((datatype.min, datatype.max)),
        DRange::Num(range) if range.integral => {
            let lo = match &range.min {
                None => None,
                Some((bound, inclusive)) => {
                    let mut value = div_ceil_rat(bound)?;
                    if !inclusive && Rat::from_int(value) == *bound {
                        value = value.checked_add(1)?;
                    }
                    Some(value)
                }
            };
            let hi = match &range.max {
                None => None,
                Some((bound, inclusive)) => {
                    let mut value = div_floor_rat(bound)?;
                    if !inclusive && Rat::from_int(value) == *bound {
                        value = value.checked_sub(1)?;
                    }
                    Some(value)
                }
            };
            Some((lo, hi))
        }
        _ => None,
    }
}

/// The integers of `outer` outside every interval of `parts`, when that set
/// is finite with at most `cap` elements (sorted); `None` otherwise.
fn integral_difference(
    outer: (Option<i128>, Option<i128>),
    parts: &[(Option<i128>, Option<i128>)],
    cap: usize,
) -> Option<Vec<i128>> {
    // Sort the parts by lower end and sweep the outer interval.
    let mut parts: Vec<_> = parts.iter().copied()
        .filter(|(lo, hi)| match (lo, hi) { (Some(lo), Some(hi)) => lo <= hi, _ => true })
        .collect();
    parts.sort_by(|a, b| match (a.0, b.0) {
        (None, None) => std::cmp::Ordering::Equal,
        (None, _) => std::cmp::Ordering::Less,
        (_, None) => std::cmp::Ordering::Greater,
        (Some(x), Some(y)) => x.cmp(&y),
    });
    let mut missing: Vec<i128> = Vec::new();
    // `cursor` = smallest outer integer not yet covered (None = -infinity).
    let mut cursor: Option<i128> = outer.0;
    let mut push_range = |from: Option<i128>, to: Option<i128>, missing: &mut Vec<i128>| -> Option<()> {
        // integers in [from, to]; unbounded ends make the difference infinite
        let (from, to) = (from?, to?);
        if from > to {
            return Some(());
        }
        let width = to.checked_sub(from)?;
        if width >= cap as i128 || missing.len() + (width as usize) + 1 > cap {
            return None;
        }
        missing.extend(from..=to);
        Some(())
    };
    for (lo, hi) in parts {
        // gap [cursor, lo-1]
        match lo {
            None => {}
            Some(lo) => {
                let gap_end = lo.checked_sub(1)?;
                let gap_end = match outer.1 { Some(top) => gap_end.min(top), None => gap_end };
                if cursor.is_none_or(|c| c <= gap_end) {
                    push_range(cursor, Some(gap_end), &mut missing)?;
                }
            }
        }
        cursor = match hi {
            None => return Some(missing), // covered to +infinity
            Some(hi) => {
                let next = hi.checked_add(1)?;
                Some(match cursor { Some(c) => c.max(next), None => next })
            }
        };
        if let (Some(c), Some(top)) = (cursor, outer.1) {
            if c > top {
                return Some(missing);
            }
        }
    }
    // tail [cursor, outer.hi]
    if let (Some(c), Some(top)) = (cursor, outer.1) {
        if c > top {
            return Some(missing);
        }
    }
    push_range(cursor, outer.1, &mut missing)?;
    Some(missing)
}

/// The datatype-relation clauses for the `__dt__` concepts in `names`
/// (collected from the clause set). Every emitted clause is justified by the
/// OWL 2 datatype map; unknown relations emit nothing. `cap` bounds the
/// finite-cover enumeration width.
pub fn datatype_relation_clauses(names: &BTreeSet<String>, cap: usize) -> Vec<DLClause> {
    datatype_relation_clauses_grouped(names, cap, None)
}

/// Role groups of a clause set for the finite-difference covers: one set of
/// `__dt__` names per connected component of roles, where the roles of every
/// clause deriving a role atom (inclusions, inverses, chains, transitivity,
/// symmetry, role assertions) are connected. A name is in
/// a group when a clause places it on the target of a role atom of that
/// group. A datatype atom on a term that no role atom of its clause reaches
/// (outside the role-free relation clauses) joins every group.
pub fn datatype_role_groups(clauses: &[DLClause]) -> Vec<BTreeSet<String>> {
    datatype_role_groups_linked(clauses, &[])
}

/// As [`datatype_role_groups`], additionally connecting each listed role set
/// (RBox inclusions, inverses and chains carried outside the clause stream).
pub fn datatype_role_groups_linked(clauses: &[DLClause], linked: &[Vec<String>]) -> Vec<BTreeSet<String>> {
    use std::collections::BTreeMap;
    let mut parent: BTreeMap<String, String> = BTreeMap::new();
    fn find(parent: &mut BTreeMap<String, String>, role: &str) -> String {
        let mut current = role.to_string();
        loop {
            let next = parent.get(&current).cloned().unwrap_or_else(|| current.clone());
            if next == current { break; }
            current = next;
        }
        parent.insert(role.to_string(), current.clone());
        current
    }
    for roles in linked {
        for window in roles.windows(2) {
            let (a, b) = (find(&mut parent, &window[0]), find(&mut parent, &window[1]));
            if a != b { parent.insert(a, b); }
        }
    }
    let mut placements: Vec<(String, String)> = Vec::new();
    let mut universal: BTreeSet<String> = BTreeSet::new();
    // A Skolem successor `f(x)` is placed by role atoms of other clauses
    // (`A(x) -> r(x, f(x))` and `A(x) -> D(f(x))`): collect its roles first.
    fn skolem_name(term: &Term) -> Option<&str> {
        match term {
            Term::Fun(name, _) | Term::Aux(name, _) => Some(name.as_str()),
            _ => None,
        }
    }
    let mut skolem_roles: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for clause in clauses {
        for atom in clause.body.iter().chain(clause.head.iter()) {
            if let Atom::Role(role, _, target) = atom {
                if let Some(name) = skolem_name(target) {
                    skolem_roles.entry(name.to_string()).or_default().insert(role.clone());
                }
            }
        }
    }
    for clause in clauses {
        let atoms: Vec<&Atom> = clause.body.iter().chain(clause.head.iter()).collect();
        let roles: Vec<(&String, &Term)> = atoms.iter().filter_map(|atom| match atom {
            Atom::Role(role, _, target) => Some((role, target)),
            _ => None,
        }).collect();
        let pure = atoms.iter().all(|atom| match atom {
            Atom::Concept(name, _) => name.starts_with("__dt__"),
            Atom::Eq(..) => true,
            Atom::Role(..) => false,
        });
        // Only a clause that derives a role edge (inclusion, inverse, chain,
        // transitivity, symmetry) lets an edge of one role be an edge of
        // another; roles that merely co-occur in a body stay separate.
        if clause.head.iter().any(|atom| matches!(atom, Atom::Role(..))) {
            for window in roles.windows(2) {
                let (a, b) = (find(&mut parent, window[0].0), find(&mut parent, window[1].0));
                if a != b { parent.insert(a, b); }
            }
        }
        for (role, _) in &roles {
            find(&mut parent, role);
        }
        if pure {
            continue;
        }
        for atom in &atoms {
            let Atom::Concept(name, term) = atom else { continue };
            if !name.starts_with("__dt__") { continue; }
            let mut placed = false;
            for (role, target) in &roles {
                if *target == term {
                    placements.push((name.clone(), (*role).clone()));
                    placed = true;
                }
            }
            if !placed {
                if let Some(roles) = skolem_name(term).and_then(|name| skolem_roles.get(name)) {
                    for role in roles {
                        placements.push((name.clone(), role.clone()));
                    }
                    placed = !roles.is_empty();
                }
            }
            if !placed {
                universal.insert(name.clone());
            }
        }
    }
    let mut groups: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (name, role) in placements {
        let root = find(&mut parent, &role);
        groups.entry(root).or_default().insert(name);
    }
    let mut out: Vec<BTreeSet<String>> = groups.into_values().collect();
    if out.is_empty() && !universal.is_empty() {
        out.push(BTreeSet::new());
    }
    for group in &mut out {
        group.extend(universal.iter().cloned());
    }
    out
}

/// As [`datatype_relation_clauses`]; with `groups`, a finite-difference cover
/// for a range `A` is built per role group from the parts in that group
/// (`None` = one group holding every name). A data node is reached only
/// through role atoms of its group, and every non-relation clause reading a
/// datatype atom on that node is guarded by such a role atom, so only ranges
/// of the node's group can occur in a body that tests the node.
pub fn datatype_relation_clauses_grouped(
    names: &BTreeSet<String>,
    cap: usize,
    groups: Option<&[BTreeSet<String>]>,
) -> Vec<DLClause> {
    // `DataUnionOf` of named datatypes: add the member datatypes to the
    // vocabulary (and to the union's role groups) so that their relations and
    // the union cover `U -> M1 ∨ … ∨ Mk` can be emitted. Inputs without a
    // union keep the original vocabulary and order.
    let unions: Vec<(String, Vec<String>)> = names.iter()
        .filter_map(|name| union_member_names(name).map(|members| (name.clone(), members)))
        .collect();
    let mut expanded_names: BTreeSet<String> = BTreeSet::new();
    let mut expanded_groups: Vec<BTreeSet<String>> = Vec::new();
    if !unions.is_empty() {
        expanded_names = names.clone();
        for (_, members) in &unions {
            expanded_names.extend(members.iter().cloned());
        }
        if let Some(groups) = groups {
            expanded_groups = groups.iter().map(|group| {
                let mut group = group.clone();
                for (union, members) in &unions {
                    if group.contains(union) {
                        group.extend(members.iter().cloned());
                    }
                }
                group
            }).collect();
        }
    }
    let (names, groups): (&BTreeSet<String>, Option<&[BTreeSet<String>]>) = if unions.is_empty() {
        (names, groups)
    } else {
        (&expanded_names, groups.map(|_| expanded_groups.as_slice()))
    };
    // Integral cells. Within one role group, the integral ranges cut the
    // integer line into elementary segments ("cells") on which every range of
    // the group is constant. Each range `A` is covered exactly by its cells:
    // `A(x) → C1(x) ∨ … ∨ Cm(x)`. A cell is named by an equal existing range,
    // by its integer value when it is a single point, and otherwise by the
    // integer facet interval it denotes; the ordinary relation clauses below
    // then relate every cell to every range. With these covers every
    // admissible label of a data node contains a cell, and a cell decides
    // membership in every range of its group, so pairwise clauses can no
    // longer admit a label with no realizing value (e.g. two distinct
    // non-positive natural numbers, or `[8,99]` outside both `<=24` and `>24`).
    let cell_groups: Vec<BTreeSet<String>> = match groups {
        Some(groups) => groups.to_vec(),
        None => vec![names.clone()],
    };
    let cell_covers = integral_cell_covers(names, &cell_groups);
    let mut with_cells: BTreeSet<String> = BTreeSet::new();
    let names = if cell_covers.is_empty() {
        names
    } else {
        with_cells = names.clone();
        for (_, heads) in &cell_covers {
            with_cells.extend(heads.iter().cloned());
        }
        &with_cells
    };
    let entries: Vec<DtEntry> = names.iter().filter_map(|n| classify_name(n)).collect();
    let mut out: Vec<DLClause> = Vec::new();
    let mut new_val_names: BTreeSet<String> = BTreeSet::new();
    // every value concept is a singleton (a data node IS its value)
    for e in &entries {
        if let DtEntry::Value(an, _) = e {
            out.push(singleton_clause(an));
        }
    }
    for (i, a) in entries.iter().enumerate() {
        match a {
            DtEntry::Value(an, av) => {
                for b in entries.iter().skip(i + 1) {
                    match b {
                        DtEntry::Value(bn, bv) => match val_eq(av, bv) {
                            Some(true) => {
                                out.push(clause([cx(an)], [cx(bn)]));
                                out.push(clause([cx(bn)], [cx(an)]));
                            }
                            Some(false) => {
                                // one data node carries one value
                                out.push(clause([cx(an), cx(bn)], []));
                            }
                            None => {}
                        },
                        DtEntry::Range(bn, br) => match val_in_range(av, br) {
                            Some(true) => out.push(clause([cx(an)], [cx(bn)])),
                            Some(false) => out.push(clause([cx(an), cx(bn)], [])),
                            None => {}
                        },
                    }
                }
            }
            DtEntry::Range(an, ar) => {
                for b in entries.iter().skip(i + 1) {
                    match b {
                        DtEntry::Value(bn, bv) => match val_in_range(bv, ar) {
                            Some(true) => out.push(clause([cx(bn)], [cx(an)])),
                            Some(false) => out.push(clause([cx(an), cx(bn)], [])),
                            None => {}
                        },
                        DtEntry::Range(bn, br) => {
                            match range_subsumed(ar, br) {
                                Some(true) => out.push(clause([cx(an)], [cx(bn)])),
                                _ => {}
                            }
                            match range_subsumed(br, ar) {
                                Some(true) => out.push(clause([cx(bn)], [cx(an)])),
                                _ => {}
                            }
                            if range_disjoint(ar, br) == Some(true) {
                                out.push(clause([cx(an), cx(bn)], []));
                            }
                        }
                    }
                }
                // finite cover: __dt__D(x) → ⋁ __dt__val__vi(x); empty cover
                // means the range is empty (→ ⊥), small covers enable
                // finite-range counting via the value disjointness above.
                let cover: Option<Vec<String>> = match ar {
                    DRange::OneOf(_) => {
                        // enumerate via the original serialised literals
                        let text = an.strip_prefix("__dt__c__").unwrap_or("");
                        let mut p = Parser::new(text);
                        match p.parse() {
                            Ok(Node::List("DataOneOf", args)) => glued_atoms(&args),
                            _ => None,
                        }
                    }
                    _ => enumerate_range(ar, cap),
                };
                if let Some(vals) = cover {
                    // Explicit enumerations already occur in full in the input.
                    // The cap limits synthesized interval enumeration, not the
                    // semantics of an explicitly listed finite value space.
                    if vals.len() <= cap || matches!(ar, DRange::OneOf(_)) {
                        let head: Vec<Atom> = vals
                            .iter()
                            .map(|lit| {
                                let vn = format!("__dt__val__{}", lit);
                                new_val_names.insert(vn.clone());
                                cx(&vn)
                            })
                            .collect();
                        out.push(clause([cx(an)], head));
                    }
                }
            }
        }
    }
    for (union, members) in &unions {
        out.push(clause([cx(union)], members.iter().map(|member| cx(member)).collect::<Vec<_>>()));
    }
    // Integral cell covers (see `integral_cell_covers` above).
    for (range, heads) in &cell_covers {
        out.push(clause([cx(range)], heads.iter().map(|head| cx(head)).collect::<Vec<_>>()));
    }
    // relations for value concepts introduced by the covers (against the
    // pre-existing entries) — one more pass, no further covers
    if !new_val_names.is_empty() {
        let fresh: Vec<DtEntry> = new_val_names
            .iter()
            .filter(|n| !names.contains(*n))
            .filter_map(|n| classify_name(n))
            .collect();
        for f in &fresh {
            if let DtEntry::Value(fname, _) = f {
                out.push(singleton_clause(fname));
            }
        }
        for f in &fresh {
            let (fname, fval) = match f {
                DtEntry::Value(n, v) => (n, v),
                _ => continue,
            };
            for e in &entries {
                match e {
                    DtEntry::Value(en, ev) => match val_eq(fval, ev) {
                        Some(true) => {
                            out.push(clause([cx(fname)], [cx(en)]));
                            out.push(clause([cx(en)], [cx(fname)]));
                        }
                        Some(false) => out.push(clause([cx(fname), cx(en)], [])),
                        None => {}
                    },
                    DtEntry::Range(en, er) => match val_in_range(fval, er) {
                        Some(true) => out.push(clause([cx(fname)], [cx(en)])),
                        Some(false) => out.push(clause([cx(fname), cx(en)], [])),
                        None => {}
                    },
                }
            }
            // and among the fresh values themselves
            for g in &fresh {
                let (gname, gval) = match g {
                    DtEntry::Value(n, v) => (n, v),
                    _ => continue,
                };
                if gname <= fname {
                    continue;
                }
                match val_eq(fval, gval) {
                    Some(true) => {
                        out.push(clause([cx(fname)], [cx(gname)]));
                        out.push(clause([cx(gname)], [cx(fname)]));
                    }
                    Some(false) => out.push(clause([cx(fname), cx(gname)], [])),
                    None => {}
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    #[test]
    fn ieee_facet_ranges_preserve_discrete_bounds_and_partitions() {
        for kind in ["float", "double"] {
            let range = |facet: &str, value: &str| parse_complex(&format!(
                "DatatypeRestriction(xsd:{kind} xsd:{facet} \"{value}\"^^xsd:{kind})"));
            let fast = range("maxExclusive", "0.01");
            let very_fast = range("maxExclusive", "0.002");
            assert_eq!(range_subsumed(&very_fast, &fast), Some(true));
            assert_eq!(range_subsumed(&fast, &very_fast), Some(false));
            assert_eq!(range_subsumed(&fast, &range_of_named(&format!("xsd:{kind}"))), Some(true));
            assert_eq!(range_subsumed(&range_of_named(&format!("xsd:{kind}")), &fast), Some(false));
            assert_eq!(range_disjoint(&fast, &range_of_named("xsd:decimal")), Some(true));
            let zero = parse_complex(&format!("DatatypeRestriction(xsd:{kind} xsd:minInclusive \"-0\"^^xsd:{kind} xsd:maxInclusive \"0\"^^xsd:{kind})"));
            for lexical in ["0", "-0"] {
                let value = parse_literal(&format!("\"{lexical}\"^^xsd:{kind}")).unwrap().0;
                assert_eq!(val_in_range(&value, &zero), Some(true));
                assert_eq!(val_in_range(&value, &range("minExclusive", "0")), Some(false));
                assert_eq!(val_in_range(&value, &range("maxExclusive", "-0")), Some(false));
            }
            let nan = parse_literal(&format!("\"NaN\"^^xsd:{kind}")).unwrap().0;
            assert_eq!(val_in_range(&nan, &fast), Some(false));
            for facet in ["minInclusive", "minExclusive", "maxInclusive", "maxExclusive"] {
                assert_eq!(enumerate_range(&range(facet, "NaN"), 8), Some(vec![]));
            }
            assert_eq!(enumerate_range(&range("minExclusive", "INF"), 8), Some(vec![]));
            assert_eq!(enumerate_range(&range("maxExclusive", "-INF"), 8), Some(vec![]));
            let inf = parse_literal(&format!("\"INF\"^^xsd:{kind}")).unwrap().0;
            assert_eq!(val_in_range(&inf, &range("minInclusive", "INF")), Some(true));
            let tiny = if kind == "float" { "1.40129846e-45" } else { "4.9406564584124654e-324" };
            let gap = parse_complex(&format!("DatatypeRestriction(xsd:{kind} xsd:minExclusive \"0\"^^xsd:{kind} xsd:maxExclusive \"{tiny}\"^^xsd:{kind})"));
            assert_eq!(enumerate_range(&gap, 8), Some(vec![]));
            let repeated = parse_complex(&format!("DatatypeRestriction(xsd:{kind} xsd:maxInclusive \"0\"^^xsd:{kind} xsd:maxExclusive \"-0\"^^xsd:{kind})"));
            assert_eq!(range_subsumed(&repeated, &range("maxExclusive", "0")), Some(true));
            assert_eq!(range_disjoint(&repeated, &zero), Some(true));
        }
        let a = parse_complex("DatatypeRestriction(xsd:float xsd:minInclusive \"1\"^^xsd:float)");
        let b = parse_complex("DatatypeRestriction(xsd:double xsd:minInclusive \"1\"^^xsd:double)");
        assert_eq!(range_disjoint(&a, &b), Some(true));
        assert_eq!(range_subsumed(&a, &b), Some(false));
        assert!(matches!(parse_complex("DatatypeRestriction(xsd:float xsd:minInclusive \"1\"^^xsd:double)"), DRange::Unknown));
    }


    #[test]
    fn relation_decidability_rejects_unknowns_and_accepts_concrete_values() {
        let names = ["__dt__string", "__dt__float",
            "__dt__val__\"label\"^^xsd:string", "__dt__val__\"1.0\"^^xsd:float",
            "__dt__val__\"2.0\"^^xsd:float"].into_iter().map(str::to_owned).collect();
        assert!(super::datatype_relations_decidable(&names).is_ok());
        let unknown = ["__dt__opaque".to_owned()].into_iter().collect();
        assert!(super::datatype_relations_decidable(&unknown).is_err());
        let unknown_range = ["__dt__unrecognized".to_owned()].into_iter().collect();
        assert!(super::datatype_relations_decidable(&unknown_range).is_err());
    }
    use super::*;

    #[test]
    fn complement_membership_negates_only_decided_value_relations() {
        let value = parse_literal("\"list error\"").unwrap().0;
        let excluded = parse_complex("DataComplementOf(DataOneOf(\"list error\"))");
        assert_eq!(val_in_range(&value, &excluded), Some(false));
        let other = parse_literal("\"other error\"^^xsd:string").unwrap().0;
        assert_eq!(val_in_range(&other, &excluded), Some(true));
        let unknown = parse_complex("DataComplementOf(ex:unknown)");
        assert_eq!(val_in_range(&value, &unknown), None);
        let double = parse_complex("DataComplementOf(DataComplementOf(DataOneOf(\"list error\")))");
        assert_eq!(val_in_range(&value, &double), Some(true));
        assert_eq!(exact_literal_value_equal("\"list error\"", "\"list error\"^^xsd:string"), Some(true));
    }


    #[test]
    fn ieee_literal_identity_preserves_width_rounding_and_signed_zero() {
        let value = |token: &str| parse_literal(token).unwrap().0;
        assert_eq!(val_eq(&value("\"16777216\"^^xsd:float"),
            &value("\"16777217\"^^xsd:float")), Some(true));
        assert_eq!(val_eq(&value("\"16777216\"^^xsd:double"),
            &value("\"16777217\"^^xsd:double")), Some(false));
        assert_eq!(val_eq(&value("\"0\"^^xsd:float"),
            &value("\"-0\"^^xsd:float")), Some(false));
        assert_eq!(val_eq(&value("\"1\"^^xsd:float"),
            &value("\"1\"^^xsd:double")), Some(false));
        assert_eq!(val_eq(&value("\"1\"^^xsd:float"),
            &value("\"1\"^^xsd:integer")), Some(false));
        let names = names(&["__dt__float", "__dt__integer", "__dt__val__\"17\"^^xsd:float"]);
        let clauses = datatype_relation_clauses(&names, 8);
        assert!(clauses.iter().any(|clause| clause.head.is_empty()
            && format!("{:?}", clause.body).contains("val__")
            && format!("{:?}", clause.body).contains("integer")));
    }

    fn names(v: &[&str]) -> BTreeSet<String> {
        v.iter().map(|s| s.to_string()).collect()
    }

    fn has_pair_clash(clauses: &[DLClause], left: &str, right: &str) -> bool {
        clauses.iter().any(|clause| {
            if !clause.head.is_empty() || clause.body.len() != 2 {
                return false;
            }
            let names: BTreeSet<&str> = clause
                .body
                .iter()
                .filter_map(|atom| match atom {
                    Atom::Concept(name, _) => Some(name.as_str()),
                    _ => None,
                })
                .collect();
            names.contains(left) && names.contains(right)
        })
    }

    #[test]
    fn value_membership_and_tower() {
        let ns = names(&[
            "__dt__val__\"5\"^^xsd:int",
            "__dt__xsd:integer",
            "__dt__xsd:decimal",
            "__dt__xsd:string",
        ]);
        let cls = datatype_relation_clauses(&ns, 8);
        let texts: Vec<String> = cls.iter().map(|c| format!("{:?}", c)).collect();
        // 5 ∈ integer, integer ⊑ decimal, 5 ∉ string (disjoint partition)
        assert!(
            texts
                .iter()
                .any(|t| t.contains("val__\\\"5\\\"") && t.contains("xsd:integer")),
            "missing membership: {:#?}",
            texts
        );
        assert!(
            cls.iter().any(|c| c.body.len() == 1
                && c.head.len() == 1
                && format!("{:?}", c.body[0]).contains("xsd:integer")
                && format!("{:?}", c.head[0]).contains("xsd:decimal")),
            "missing integer ⊑ decimal"
        );
        assert!(
            cls.iter().any(|c| c.head.is_empty()
                && c.body.len() == 2
                && format!("{:?}", c).contains("xsd:string")),
            "missing numeric/string disjointness"
        );
    }

    #[test]
    fn distinct_values_clash_equal_values_merge() {
        let ns = names(&[
            "__dt__val__\"1\"^^xsd:int",
            "__dt__val__\"1.0\"^^xsd:decimal",
            "__dt__val__\"2\"^^xsd:int",
        ]);
        let cls = datatype_relation_clauses(&ns, 8);
        // "1"^^int = "1.0"^^decimal: bidirectional inclusion
        assert!(
            cls.iter()
                .filter(|c| c.body.len() == 1 && c.head.len() == 1)
                .count()
                >= 2,
            "missing value equality inclusions"
        );
        // "1" vs "2": disjoint
        assert!(
            cls.iter().any(|c| c.head.is_empty() && c.body.len() == 2),
            "missing distinct-value clash"
        );
    }

    #[test]
    fn lossy_lexical_families_do_not_emit_false_value_disjointness() {
        // xsd:token collapses runs of whitespace, so these denote the same
        // string value despite different lexical forms.
        let token = "__dt__val__\"a  b\"^^xsd:token";
        let string = "__dt__val__\"a b\"^^xsd:string";
        let clauses = datatype_relation_clauses(&names(&[token, string]), 8);
        assert!(
            !has_pair_clash(&clauses, token, string),
            "whitespace collapse must not become value disjointness: {clauses:#?}"
        );

        // Both lexical forms round to 2^24 in the IEEE binary32 value space.
        let float_left = "__dt__val__\"16777216\"^^xsd:float";
        let float_right = "__dt__val__\"16777217\"^^xsd:float";
        let clauses = datatype_relation_clauses(&names(&[float_left, float_right]), 8);
        assert!(
            !has_pair_clash(&clauses, float_left, float_right),
            "binary32 rounding must not become value disjointness: {clauses:#?}"
        );
    }

    #[test]
    fn exact_bridge_value_oracle_keeps_only_proven_equalities() {
        let value = |literal: &str| format!("__dt__val__{literal}");
        assert_eq!(
            bridge_exact_value_equal(
                &value("\"true\"^^xsd:boolean"),
                &value("\"1\"^^xsd:boolean")
            ),
            Some(true)
        );
        assert_eq!(
            bridge_exact_value_equal(
                &value("\"true\"^^xsd:boolean"),
                &value("\"false\"^^xsd:boolean")
            ),
            Some(false)
        );
        assert_eq!(
            bridge_exact_value_equal(&value("\"01\"^^xsd:integer"), &value("\"1\"^^xsd:integer")),
            Some(true)
        );
        assert_eq!(
            bridge_exact_value_equal(&value("\"1\"^^xsd:integer"), &value("\"2\"^^xsd:integer")),
            Some(false)
        );
        assert_eq!(
            bridge_exact_value_equal(
                &value("\"alpha\"^^xsd:string"),
                &value("\"beta\"^^xsd:string")
            ),
            Some(false)
        );
        assert_eq!(
            bridge_exact_value_equal(&value("\"a  b\"^^xsd:token"), &value("\"a b\"^^xsd:string")),
            None
        );
        assert_eq!(
            bridge_exact_value_equal(
                &value("\"16777216\"^^xsd:float"),
                &value("\"16777217\"^^xsd:float")
            ),
            Some(true)
        );
        assert_eq!(bridge_exact_value_equal(&value("\"0\"^^xsd:float"),
            &value("\"-0\"^^xsd:float")), Some(false));
        assert_eq!(bridge_exact_value_equal(&value("\"1\"^^xsd:float"),
            &value("\"2\"^^xsd:float")), Some(false));
    }

    #[test]
    fn builtin_datatypes_require_the_exact_standard_namespace() {
        const XSD_BOOLEAN: &str = "<http://www.w3.org/2001/XMLSchema#boolean>";
        const CUSTOM_BOOLEAN: &str = "<http://example.org/types#boolean>";
        const RDFS_LITERAL: &str = "<http://www.w3.org/2000/01/rdf-schema#Literal>";

        assert_eq!(datatype_concept_key("xsd:boolean"), "boolean");
        assert_eq!(datatype_concept_key(XSD_BOOLEAN), "boolean");
        assert_eq!(datatype_concept_key("rdfs:Literal"), "Literal");
        assert_eq!(datatype_concept_key(RDFS_LITERAL), "Literal");

        let prefixed_custom = datatype_concept_key("ex:boolean");
        let full_custom = datatype_concept_key(CUSTOM_BOOLEAN);
        assert!(prefixed_custom.starts_with("iri__"));
        assert!(full_custom.starts_with("iri__"));
        assert_ne!(prefixed_custom, "boolean");
        assert_ne!(full_custom, "boolean");
        assert_ne!(prefixed_custom, full_custom);

        // A custom datatype whose local name is Literal is not data top.
        let custom_top_collision = datatype_concept_key("ex:Literal");
        assert!(matches!(
            range_of_internal_name(&custom_top_collision),
            DRange::Unknown
        ));
        assert!(matches!(range_of_named("ex:Literal"), DRange::Unknown));
    }

    #[test]
    fn plain_literal_is_not_data_top() {
        assert!(matches!(range_of_named("rdfs:Literal"), DRange::Top));
        assert!(matches!(
            range_of_named("rdf:PlainLiteral"),
            DRange::Unknown
        ));
        assert!(matches!(
            range_of_internal_name("PlainLiteral"),
            DRange::Unknown
        ));

        let integer = "__dt__integer";
        let plain = "__dt__PlainLiteral";
        let clauses = datatype_relation_clauses(&names(&[integer, plain]), 8);
        assert!(
            !clauses.iter().any(|clause| {
                clause.body.len() == 1
                    && clause.head.len() == 1
                    && format!("{:?}", clause.body[0]).contains(integer)
                    && format!("{:?}", clause.head[0]).contains(plain)
            }),
            "integer must not be subsumed by rdf:PlainLiteral: {clauses:#?}"
        );
    }

    #[test]
    fn custom_builtin_suffixes_never_enter_the_exact_value_or_bridge_oracle() {
        assert_eq!(
            exact_literal_value_equal("\"1\"^^ex:boolean", "\"true\"^^ex:boolean"),
            None
        );
        assert_eq!(
            exact_literal_value_equal("\"5\"^^ex:integer", "\"05\"^^ex:integer"),
            None
        );
        assert_eq!(
            exact_literal_value_equal(
                "\"1\"^^xsd:boolean",
                "\"true\"^^<http://www.w3.org/2001/XMLSchema#boolean>"
            ),
            Some(true)
        );

        let left = "__dt__val__\"1\"^^ex:boolean";
        let right = "__dt__val__\"true\"^^ex:boolean";
        let clauses = datatype_relation_clauses(&names(&[left, right]), 8);
        assert!(
            !has_pair_clash(&clauses, left, right),
            "custom boolean lexical forms must not be declared distinct: {clauses:#?}"
        );

        let custom = format!("__dt__{}", datatype_concept_key("ex:boolean"));
        assert!(!bridge_exact_atomic_name(&custom));
        assert!(!bridge_exact_atomic_name("__dt__ex:boolean"));
    }

    #[test]
    fn opaque_values_are_not_declared_outside_numeric_restrictions() {
        let numeric =
            "__dt__c__DatatypeRestriction(xsd:integer xsd:minInclusive \"0\"^^xsd:integer)";
        for value in [
            "__dt__val__\"5\"^^ex:integer",
            "__dt__val__\"not-a-number\"^^xsd:float",
        ] {
            let clauses = datatype_relation_clauses(&names(&[value, numeric]), 8);
            assert!(
                !has_pair_clash(&clauses, value, numeric),
                "opaque value was falsely excluded from a numeric range: {clauses:#?}"
            );
        }

        let custom_facet =
            "__dt__c__DatatypeRestriction(xsd:integer ex:minInclusive \"0\"^^xsd:integer)";
        let clauses = datatype_relation_clauses(&names(&[custom_facet, "__dt__integer"]), 8);
        assert!(
            !clauses
                .iter()
                .any(|clause| clause.body.len() == 1 && clause.head.len() == 1),
            "a custom facet IRI must keep the restriction opaque: {clauses:#?}"
        );
    }

    #[test]
    fn explicit_finite_cover_is_not_truncated_by_interval_enumeration_cap() {
        let literals: Vec<_> = (0..17).map(|i| format!("\"v{i}\"^^xsd:string")).collect();
        let range = format!("__dt__c__DataOneOf({})", literals.join(" "));
        let clauses = datatype_relation_clauses(&[range.clone()].into_iter().collect(), 8);
        let expected: BTreeSet<_> = literals.iter().map(|v| format!("__dt__val__{v}")).collect();
        let cover = clauses.iter().find(|cl| cl.body == vec![cx(&range)]
            && cl.head.len() == expected.len()).expect("complete explicit cover");
        let actual: BTreeSet<_> = cover.head.iter().map(|atom| match atom {
            Atom::Concept(name, _) => name.clone(), _ => panic!("non-value cover atom"),
        }).collect();
        assert_eq!(actual, expected);
        for value in expected { assert!(clauses.contains(&singleton_clause(&value))); }
    }

    #[test]
    fn boolean_cover_enables_counting() {
        let ns = names(&["__dt__xsd:boolean"]);
        let cls = datatype_relation_clauses(&ns, 8);
        // cover: boolean(x) -> val_true(x) | val_false(x), plus the clash
        // between the two fresh value concepts
        assert!(
            cls.iter().any(|c| c.body.len() == 1 && c.head.len() == 2),
            "missing boolean cover: {:?}",
            cls.len()
        );
        assert!(
            cls.iter().any(|c| c.head.is_empty() && c.body.len() == 2),
            "missing true/false clash"
        );
    }

    #[test]
    fn interval_subsumption_and_disjointness() {
        let ns = names(&[
            "__dt__c__DatatypeRestriction(xsd:integer xsd:minInclusive \"1\"^^xsd:integer xsd:maxInclusive \"3\"^^xsd:integer)",
            "__dt__c__DatatypeRestriction(xsd:integer xsd:minInclusive \"5\"^^xsd:integer xsd:maxInclusive \"9\"^^xsd:integer)",
            "__dt__xsd:integer",
        ]);
        let cls = datatype_relation_clauses(&ns, 8);
        // both intervals ⊑ integer; intervals disjoint; [1,3] gets a cover
        assert!(
            cls.iter()
                .filter(|c| c.body.len() == 1 && c.head.len() == 1)
                .count()
                >= 2,
            "missing interval ⊑ integer"
        );
        assert!(
            cls.iter().any(|c| c.head.is_empty() && c.body.len() == 2),
            "missing interval disjointness"
        );
        assert!(
            cls.iter().any(|c| c.body.len() == 1 && c.head.len() == 3),
            "missing [1,3] cover"
        );
    }

    #[test]
    fn unknown_emits_nothing_wrong() {
        // a pattern-restricted range stays opaque: no relations with string
        let ns = names(&[
            "__dt__c__DatatypeRestriction(xsd:string xsd:pattern \"[a-z]+\")",
            "__dt__xsd:string",
        ]);
        let cls = datatype_relation_clauses(&ns, 8);
        assert!(
            cls.is_empty(),
            "opaque range must emit nothing, got {}",
            cls.len()
        );
    }

    #[test]
    fn integer_and_ieee_float_do_not_get_false_inclusions() {
        let ns = names(&[
            "__dt__integer",
            "__dt__float",
            "__dt__val__\"23\"^^xsd:integer",
        ]);
        let cls = datatype_relation_clauses(&ns, 8);
        assert!(
            !cls.iter().any(|clause| {
                clause.body.len() == 1
                    && clause.head.len() == 1
                    && format!("{:?}", clause.body[0]).contains("integer")
                    && format!("{:?}", clause.head[0]).contains("float")
            }),
            "integer must not be declared a subtype of IEEE float: {cls:#?}"
        );
        assert!(
            !cls.iter().any(|clause| {
                clause.body.len() == 1
                    && clause.head.len() == 1
                    && format!("{:?}", clause.body[0]).contains("val__\\\"23")
                    && format!("{:?}", clause.head[0]).contains("float")
            }),
            "integer literal membership in IEEE float needs a representability proof: {cls:#?}"
        );
    }

    #[test]
    fn lossy_named_datatype_shapes_do_not_imply_identity() {
        for pair in [
            ["__dt__date", "__dt__time"],
            ["__dt__language", "__dt__Name"],
            ["__dt__hexBinary", "__dt__base64Binary"],
        ] {
            let cls = datatype_relation_clauses(&names(&pair), 8);
            assert!(
                !cls.iter()
                    .any(|clause| clause.body.len() == 1 && clause.head.len() == 1),
                "distinct datatype identities were conflated for {pair:?}: {cls:#?}"
            );
        }
    }

    #[test]
    fn rational_interval_is_not_mistaken_for_decimal_interval() {
        let restricted = "__dt__c__DatatypeRestriction(owl:rational xsd:minInclusive \"0\"^^xsd:integer xsd:maxInclusive \"1\"^^xsd:integer)";
        let cls = datatype_relation_clauses(&names(&[restricted, "__dt__decimal"]), 8);
        assert!(
            !cls.iter().any(|clause| {
                clause.body.len() == 1
                    && clause.head.len() == 1
                    && format!("{:?}", clause.body[0]).contains("DatatypeRestriction")
                    && format!("{:?}", clause.head[0]).contains("decimal")
            }),
            "a rational interval contains non-decimal rationals: {cls:#?}"
        );
    }

    #[test]
    fn bridge_finite_cover_checks_exact_values_and_aliases() {
        let range = "__dt__c__DataOneOf(\"1\"^^xsd:int \"2\"^^xsd:int)";
        let one = "__dt__val__\"01\"^^xsd:positiveInteger";
        let two = "__dt__val__\"2\"^^xsd:integer";
        let three = "__dt__val__\"3\"^^xsd:integer";
        assert!(bridge_exact_atomic_name(range));
        assert!(bridge_exact_finite_cover(range, &[two, one, one]));
        assert!(!bridge_exact_finite_cover(range, &[one]));
        assert!(!bridge_exact_finite_cover(range, &[one, two, three]));
        assert!(!bridge_exact_atomic_name("__dt__c__DataOneOf(\"0\"^^xsd:positiveInteger)"));
        assert!(bridge_exact_atomic_name("__dt__c__DataOneOf(\"true\"^^xsd:boolean)"));
    }

    #[test]
    fn bridge_integer_literals_preserve_value_identity_and_declared_bounds() {
        let integer = "__dt__val__\"1\"^^xsd:integer";
        for datatype in ["integer", "int", "nonNegativeInteger", "positiveInteger"] {
            let literal = format!("__dt__val__\"+01\"^^xsd:{datatype}");
            assert!(bridge_exact_atomic_name(&literal));
            assert_eq!(bridge_exact_value_equal(&literal, integer), Some(true));
            assert_eq!(bridge_exact_atomic_subsumed(&literal, "__dt__positiveInteger"), Some(true));
        }
        for literal in [
            "__dt__val__\"0\"^^xsd:positiveInteger",
            "__dt__val__\"-1\"^^xsd:nonNegativeInteger",
            "__dt__val__\"2147483648\"^^xsd:int",
            "__dt__val__\"-2147483649\"^^xsd:int",
            "__dt__val__\"1.0\"^^xsd:integer",
            "__dt__val__\"1e0\"^^xsd:positiveInteger",
        ] {
            assert!(!bridge_exact_atomic_name(literal), "invalid literal admitted: {literal}");
        }
    }

    #[test]
    fn bridge_integral_decimal_literals_preserve_integer_value_identity() {
        for value in -16..=16 {
            let decimal = format!("__dt__val__\"{value}.000\"^^xsd:decimal");
            let integer = format!("__dt__val__\"{value}\"^^xsd:integer");
            assert!(bridge_exact_atomic_name(&decimal));
            assert_eq!(bridge_exact_value_equal(&decimal, &integer), Some(true));
            assert_eq!(bridge_exact_atomic_subsumed(&decimal, &integer), Some(true));
            assert_eq!(bridge_exact_atomic_subsumed(&integer, &decimal), Some(true));
            assert_eq!(bridge_exact_atomic_subsumed(&decimal, "__dt__integer"), Some(true));
            assert_eq!(bridge_exact_atomic_subsumed(&decimal, "__dt__decimal"), Some(true));
            assert_eq!(bridge_exact_atomic_subsumed(&decimal, "__dt__positiveInteger"), Some(value > 0));
            assert_eq!(bridge_exact_atomic_disjoint(&decimal, "__dt__string"), Some(true));
        }
        for spelling in ["+001.000", "1.", " 1.0 "] {
            let decimal = format!("__dt__val__\"{spelling}\"^^<http://www.w3.org/2001/XMLSchema#decimal>");
            assert_eq!(bridge_exact_value_equal(&decimal, "__dt__val__\"1\"^^xsd:integer"), Some(true));
        }
        assert_eq!(bridge_exact_value_equal("__dt__val__\"-.0\"^^xsd:decimal",
            "__dt__val__\"0\"^^xsd:integer"), Some(true));
        for spelling in ["1.5", "-0.25", "1E0", "NaN", "INF", ".", "--1", "1.0.0",
            "170141183460469231731687303715884105728"] {
            let decimal = format!("__dt__val__\"{spelling}\"^^xsd:decimal");
            assert!(!bridge_exact_atomic_name(&decimal), "unsupported or invalid decimal admitted: {spelling}");
        }
        assert!(!bridge_exact_atomic_name("__dt__val__\"1.0\"^^<http://example.org/decimal>"));
    }

    #[test]
    fn bridge_plain_string_literal_is_the_xsd_string_abbreviation() {
        let plain = "__dt__val__\"makesStmtsAbout\"";
        let typed = "__dt__val__\"makesStmtsAbout\"^^xsd:string";
        assert!(bridge_exact_atomic_name(plain));
        assert_eq!(bridge_exact_value_equal(plain, typed), Some(true));
        assert_eq!(bridge_exact_atomic_subsumed(plain, "__dt__string"), Some(true));
        assert_eq!(bridge_exact_atomic_disjoint(plain, "__dt__boolean"), Some(true));
        assert!(!bridge_exact_atomic_name("__dt__val__\"makesStmtsAbout\"@en"));
        assert!(!bridge_exact_atomic_name("__dt__val__\"makesStmtsAbout\"^^<http://km.test/string>"));
    }

    #[test]
    fn bridge_datetime_literals_preserve_owl_value_identity() {
        let value = |text: &str| format!("__dt__val__\"{text}\"^^xsd:dateTime");
        let midnight = value("2000-03-01T00:00:00Z");
        let alias = value("2000-02-29T24:00:00.000+00:00");
        assert!(bridge_exact_atomic_name(&midnight));
        assert_eq!(bridge_exact_value_equal(&midnight, &alias), Some(true));
        assert_eq!(bridge_exact_atomic_subsumed(&midnight, "__dt__dateTime"), Some(true));
        assert_eq!(bridge_exact_atomic_disjoint(&midnight, "__dt__string"), Some(true));
        // OWL uses XML Schema value identity, retaining the timezone offset.
        let est = value("1956-06-25T04:00:00-05:00");
        let cet = value("1956-06-25T10:00:00+01:00");
        assert_eq!(bridge_exact_value_equal(&est, &cet), Some(false));
        assert_eq!(bridge_exact_atomic_disjoint(&est, &cet), Some(true));
        assert_eq!(bridge_exact_value_equal(&midnight, &value("2000-03-01T00:00:00")), Some(false));
        for invalid in ["1900-02-29T00:00:00Z", "2000-01-01T00:00:00+14:01", "2000-01-01T24:00:01"] {
            assert!(!bridge_exact_atomic_name(&value(invalid)));
            assert_eq!(bridge_exact_value_equal(&midnight, &value(invalid)), None);
        }
    }

    #[test]
    fn bridge_tbox_datatype_extension_map_and_cells() {
        let double = |text: &str| format!("__dt__val__\"{text}\"^^xsd:double");
        for name in ["__dt__anyURI", "__dt__double", "__dt__Literal", &double("1.0E-17"), &double("NaN"),
            "__dt__c__DatatypeRestriction(xsd:double xsd:minInclusive \"0.0\"^^xsd:double xsd:maxInclusive \"1.0\"^^xsd:double)"] {
            assert!(bridge_tbox_atomic_name(name), "{name}");
            assert!(!bridge_exact_atomic_name(name), "narrow map unchanged for {name}");
        }
        for name in ["__dt__val__\"+INF\"^^xsd:double", "__dt__PlainLiteral",
            "__dt__c__DatatypeRestriction(xsd:double xsd:minInclusive \"0\"^^xsd:integer)",
            "__dt__c__DatatypeRestriction(xsd:double xsd:pattern \"1.*\")"] {
            assert!(!bridge_tbox_atomic_name(name), "{name}");
        }
        assert_eq!(bridge_exact_atomic_disjoint("__dt__anyURI", "__dt__string"), Some(true));
        assert_eq!(bridge_exact_atomic_subsumed("__dt__anyURI", "__dt__Literal"), Some(true));
        assert_eq!(bridge_exact_atomic_disjoint("__dt__double", "__dt__float"), Some(true));
        assert_eq!(bridge_exact_atomic_disjoint("__dt__double", "__dt__decimal"), Some(true));
        assert_eq!(bridge_exact_value_equal(&double("1"), &double("1.0E0")), Some(true));
        assert_eq!(bridge_exact_value_equal(&double("0.0"), &double("-0.0")), Some(false));
        assert_eq!(bridge_exact_value_equal(&double("NaN"), &double("NaN")), Some(true));
        assert_eq!(bridge_exact_value_equal(&double("1.0"), "__dt__val__\"1.0\"^^xsd:float"), Some(false));
        let nonneg = "__dt__c__DatatypeRestriction(xsd:double xsd:minInclusive \"0.0\"^^xsd:double)";
        let pos = "__dt__c__DatatypeRestriction(xsd:double xsd:minExclusive \"0.0\"^^xsd:double)";
        let neg = "__dt__c__DatatypeRestriction(xsd:double xsd:maxExclusive \"0.0\"^^xsd:double)";
        let unit = "__dt__c__DatatypeRestriction(xsd:double xsd:minInclusive \"0.0\"^^xsd:double xsd:maxInclusive \"1.0\"^^xsd:double)";
        assert_eq!(bridge_exact_atomic_subsumed(&double("-0.0"), nonneg), Some(true));
        assert_eq!(bridge_exact_atomic_disjoint(&double("-0.0"), pos), Some(true));
        assert_eq!(bridge_exact_atomic_disjoint(&double("NaN"), nonneg), Some(true));
        assert_eq!(bridge_exact_atomic_subsumed(&double("NaN"), "__dt__double"), Some(true));
        assert_eq!(bridge_exact_atomic_subsumed(unit, nonneg), Some(true));
        assert_eq!(bridge_exact_atomic_disjoint(pos, neg), Some(true));
        assert_eq!(bridge_exact_atomic_subsumed(unit, pos), Some(false));
        assert_eq!(bridge_exact_atomic_disjoint(unit, pos), Some(false));
        // The SIO vocabulary: [0,1], (0,INF], [-INF,0) under xsd:double.
        let names = ["__dt__double", unit, pos, neg];
        let rel = |names: &[&str]| {
            let names: Vec<String> = names.iter().map(|n| n.to_string()).collect();
            let a = names.clone();
            let b = names;
            (move |i: usize, j: usize| i != j && bridge_exact_atomic_subsumed(&a[i], &a[j]) == Some(true),
             move |i: usize, j: usize| bridge_exact_atomic_disjoint(&b[i], &b[j]) == Some(true))
        };
        let (inclusion, disjoint) = rel(&names);
        assert_eq!(bridge_ieee_cells_realizable(&names, &[false; 4], &inclusion, &disjoint, &[], 2), Some(true));
        // With every interval body-sensitive the label {double} alone is
        // realized only by NaN: one value, so the certificate fails.
        assert_eq!(bridge_ieee_cells_realizable(&names, &[false, true, true, true], &inclusion, &disjoint, &[], 2), Some(false));
        // Missing inclusion evidence makes {[0,1]} without {double} admissible
        // in the graph; a sensitive double then has no realizing value.
        let no_inclusion = |_: usize, _: usize| false;
        assert_eq!(bridge_ieee_cells_realizable(&names, &[true, false, false, false], &no_inclusion, &disjoint, &[], 2), Some(false));
        // Signed zeros: [0,0] has two values unless both are present literals.
        let zero = "__dt__c__DatatypeRestriction(xsd:double xsd:minInclusive \"0.0\"^^xsd:double xsd:maxInclusive \"0.0\"^^xsd:double)";
        let (inclusion, disjoint) = rel(&[zero]);
        assert_eq!(bridge_ieee_cells_realizable(&[zero], &[false], &inclusion, &disjoint, &[], 2), Some(true));
        assert_eq!(bridge_ieee_cells_realizable(&[zero], &[false], &inclusion, &disjoint, &[&double("-0.0")], 2), Some(false));
        assert_eq!(bridge_ieee_cells_realizable(&[zero, "__dt__float"], &[false, false], &inclusion, &disjoint, &[], 2), None);
    }

    #[test]
    fn bridge_tbox_datatype_extension_integral_difference_covers() {
        let cover = |names: &[&str]| {
            let set: BTreeSet<String> = names.iter().map(|n| n.to_string()).collect();
            datatype_relation_clauses(&set, 8).into_iter()
                .filter(|clause| clause.body.len() == 1 && clause.head.len() >= 2)
                .map(|clause| format!("{:?} -> {:?}", clause.body, clause.head))
                .collect::<Vec<_>>()
        };
        let gap = cover(&["__dt__nonNegativeInteger", "__dt__positiveInteger"]);
        assert_eq!(gap.len(), 1, "{gap:?}");
        assert!(gap[0].contains("__dt__positiveInteger") && gap[0].contains("__dt__val__\\\"0\\\"^^xsd:integer"), "{gap:?}");
        // integer \ (positive ∪ negative) = {0}; integer \ positive alone is infinite.
        let both = cover(&["__dt__integer", "__dt__positiveInteger", "__dt__negativeInteger"]);
        assert!(both.iter().any(|c| c.starts_with("[Concept(\"__dt__integer\"") && c.contains("__dt__val__\\\"0\\\"^^xsd:integer")), "{both:?}");
        // integer is split by positiveInteger into the cells (<= 0) and positiveInteger.
        let split = cover(&["__dt__integer", "__dt__positiveInteger"]);
        assert!(split.len() == 1 && split[0].contains("maxInclusive \\\"0\\\"") && split[0].contains("__dt__positiveInteger"), "{split:?}");
        // Exclusive facets at an equal endpoint: nonNegativeInteger > 0 = positiveInteger.
        let positive = "__dt__c__DatatypeRestriction(xsd:nonNegativeInteger xsd:minExclusive \"0\"^^xsd:integer)";
        assert!(!bridge_exact_integral_cover("__dt__nonNegativeInteger", &[positive]));
        assert!(bridge_exact_integral_cover("__dt__nonNegativeInteger", &[positive, "__dt__val__\"0\"^^xsd:integer"]));
        // A wide difference becomes one interval cell.
        let wide = cover(&["__dt__unsignedByte", "__dt__c__DatatypeRestriction(xsd:unsignedByte xsd:minInclusive \"10\"^^xsd:integer)"]);
        assert!(wide.len() == 1 && wide[0].contains("maxInclusive \\\"9\\\""), "{wide:?}");
        assert_eq!(integral_difference((Some(0), Some(10)), &[(Some(2), Some(4)), (Some(3), Some(9))], 8), Some(vec![0, 1, 10]));
        assert_eq!(integral_difference((None, None), &[(None, Some(-1)), (Some(1), None)], 8), Some(vec![0]));
        assert_eq!(integral_difference((None, None), &[(Some(1), None)], 8), None);
    }

    #[test]
    fn bridge_tbox_datatype_extension_union_relations() {
        let union = "__dt__c__DataUnionOf(xsd:decimal xsd:float xsd:integer xsd:long)";
        assert_eq!(union_member_names(union).unwrap(),
            vec!["__dt__decimal", "__dt__float", "__dt__integer", "__dt__long"]);
        assert_eq!(bridge_tbox_atomic_family(union), Some("union"));
        assert_eq!(bridge_tbox_atomic_family("__dt__long"), Some("decimal"));
        let exact = "__dt__c__DataUnionOf(xsd:decimal xsd:float)";
        assert_eq!(bridge_tbox_atomic_family(exact), Some("union"));
        assert_eq!(bridge_exact_atomic_subsumed("__dt__positiveInteger", exact), Some(true));
        assert_eq!(bridge_exact_atomic_subsumed("__dt__float", exact), Some(true));
        assert_eq!(bridge_exact_atomic_disjoint(exact, "__dt__string"), Some(true));
        assert_eq!(bridge_exact_atomic_disjoint(exact, "__dt__double"), Some(true));
        assert_eq!(bridge_exact_atomic_disjoint(exact, "__dt__integer"), Some(false));
        let clauses = datatype_relation_clauses(&[exact.to_string(), "__dt__string".to_string()].into_iter().collect(), 8);
        let atom = |name: &str| Atom::Concept(name.into(), Term::Var("x".into()));
        assert!(clauses.iter().any(|clause| clause.body == vec![atom(exact)]
            && clause.head.contains(&atom("__dt__decimal")) && clause.head.contains(&atom("__dt__float"))));
        assert!(clauses.iter().any(|clause| clause.body == vec![atom("__dt__float")] && clause.head == vec![atom(exact)]));
        assert!(bridge_exact_union_cover(exact, &["__dt__decimal", "__dt__float"]));
        assert!(!bridge_exact_union_cover(exact, &["__dt__decimal"]));
    }

    #[test]
    fn bridge_tbox_datatype_extension_uri_xml_and_decimal_values() {
        let uri = |text: &str| format!("__dt__val__\"{text}\"^^xsd:anyURI");
        assert_eq!(bridge_tbox_atomic_family(&uri("http://x/a")), Some("anyURI"));
        assert_eq!(bridge_exact_value_equal(&uri("http://x/a"), &uri(" http://x/a ")), Some(true), "whiteSpace=collapse");
        assert_eq!(bridge_exact_value_equal(&uri("http://x/a"), &uri("http://x/b")), Some(false));
        assert_eq!(bridge_exact_value_equal(&uri("http://x/a"), "__dt__val__\"http://x/a\"^^xsd:string"), Some(false),
            "anyURI and string value spaces are disjoint");
        assert_eq!(bridge_exact_atomic_subsumed(&uri("http://x/a"), "__dt__anyURI"), Some(true));
        assert_eq!(bridge_exact_atomic_disjoint(&uri("http://x/a"), "__dt__string"), Some(true));
        assert_eq!(datatype_concept_key("rdf:XMLLiteral"), "XMLLiteral");
        assert_eq!(datatype_concept_key("<http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral>"), "XMLLiteral");
        assert_eq!(bridge_tbox_atomic_family("__dt__XMLLiteral"), Some("XMLLiteral"));
        for other in ["__dt__string", "__dt__anyURI", "__dt__integer", "__dt__double", "__dt__boolean"] {
            assert_eq!(bridge_exact_atomic_disjoint("__dt__XMLLiteral", other), Some(true), "{other}");
        }
        assert_eq!(bridge_exact_atomic_subsumed("__dt__XMLLiteral", "__dt__Literal"), Some(true));
        assert!(!bridge_tbox_atomic_name("__dt__val__\"<a/>\"^^rdf:XMLLiteral"), "XML values stay opaque");
        let dec = |text: &str| format!("__dt__val__\"{text}\"^^xsd:decimal");
        assert_eq!(bridge_tbox_atomic_family(&dec("1.50")), Some("decimal"));
        assert!(!bridge_tbox_atomic_name(&dec("1.5E2")), "no exponent in the decimal lexical space");
        assert!(!bridge_tbox_atomic_name(&dec(".")));
        assert_eq!(bridge_exact_value_equal(&dec("1.50"), &dec("1.5")), Some(true));
        assert_eq!(bridge_exact_value_equal(&dec("2.0"), "__dt__val__\"2\"^^xsd:integer"), Some(true));
        assert_eq!(bridge_exact_atomic_disjoint(&dec("1.5"), "__dt__integer"), Some(true));
        assert_eq!(bridge_exact_atomic_subsumed(&dec("1.5"), "__dt__decimal"), Some(true));
    }

    #[test]
    fn bridge_tbox_datatype_extension_facet_intersections() {
        let both = "__dt__c__DataIntersectionOf(DatatypeRestriction(xsd:double xsd:maxInclusive \"1000.0\"^^xsd:double) DatatypeRestriction(xsd:double xsd:minInclusive \"0.0\"^^xsd:double))";
        let single = "__dt__c__DatatypeRestriction(xsd:double xsd:minInclusive \"0.0\"^^xsd:double xsd:maxInclusive \"1000.0\"^^xsd:double)";
        assert_eq!(bridge_tbox_atomic_family(both), Some("double"));
        assert_eq!(bridge_exact_atomic_subsumed(both, single), Some(true));
        assert_eq!(bridge_exact_atomic_subsumed(single, both), Some(true));
        assert_eq!(bridge_exact_atomic_disjoint(both, "__dt__val__\"1000.5\"^^xsd:double"), Some(true));
        assert_eq!(bridge_exact_atomic_disjoint(both, "__dt__val__\"NaN\"^^xsd:double"), Some(true));
        let ints = "__dt__c__DataIntersectionOf(DatatypeRestriction(xsd:integer xsd:minExclusive \"3\"^^xsd:integer) DatatypeRestriction(xsd:integer xsd:maxExclusive \"5\"^^xsd:integer))";
        assert_eq!(bridge_exact_atomic_subsumed("__dt__val__\"4\"^^xsd:integer", ints), Some(true));
        assert_eq!(bridge_exact_atomic_disjoint("__dt__val__\"5\"^^xsd:integer", ints), Some(true));
        let mixed = "__dt__c__DataIntersectionOf(DatatypeRestriction(xsd:double xsd:minInclusive \"0.0\"^^xsd:double) DatatypeRestriction(xsd:float xsd:minInclusive \"0.0\"^^xsd:float))";
        assert!(!bridge_tbox_atomic_name(mixed));
    }

    #[test]
    fn bridge_tbox_datatype_extension_double_enumerations() {
        let one = "__dt__c__DataOneOf(\"1.0\"^^xsd:double)";
        assert_eq!(bridge_tbox_atomic_family(one), Some("finite"));
        assert!(bridge_exact_finite_values(one).is_none(), "the narrow projection map is unchanged");
        assert!(bridge_tbox_finite_cover(one, &["__dt__val__\"1.0\"^^xsd:double"]));
        assert!(bridge_tbox_finite_cover(one, &["__dt__val__\"1\"^^xsd:double"]), "same binary64 value");
        assert!(!bridge_tbox_finite_cover(one, &["__dt__val__\"1\"^^xsd:integer"]), "double is not decimal");
        assert_eq!(bridge_exact_atomic_disjoint(one, "__dt__val__\"0.0\"^^xsd:double"), Some(true));
        assert_eq!(bridge_exact_atomic_subsumed(one, "__dt__double"), Some(true));
    }

    #[test]
    fn bridge_tbox_datatype_extension_decimal_cell_counts() {
        let names = ["__dt__integer", "__dt__nonNegativeInteger", "__dt__positiveInteger", "__dt__decimal"];
        let a: Vec<String> = names.iter().map(|n| n.to_string()).collect();
        let b = a.clone();
        let inclusion = move |i: usize, j: usize| i != j && bridge_exact_atomic_subsumed(&a[i], &a[j]) == Some(true);
        let disjoint = move |i: usize, j: usize| bridge_exact_atomic_disjoint(&b[i], &b[j]) == Some(true);
        assert_eq!(bridge_decimal_cells_realizable(&names, &[false; 4], &inclusion, &disjoint, &[], 2, &[]), Some(true));
        // {nonNegativeInteger, integer, decimal} avoiding positiveInteger: only 0.
        assert_eq!(bridge_decimal_cells_realizable(&names, &[false, false, true, false], &inclusion, &disjoint, &[], 2, &[]), Some(false));
        // {decimal} avoiding integer: infinitely many non-integers remain.
        assert_eq!(bridge_decimal_cells_realizable(&names, &[true, false, false, false], &inclusion, &disjoint, &[], 2, &[]), Some(true));
        let digit = "__dt__c__DatatypeRestriction(xsd:int xsd:minInclusive \"0\"^^xsd:integer xsd:maxInclusive \"9\"^^xsd:integer)";
        let small = ["__dt__int", digit];
        let a: Vec<String> = small.iter().map(|n| n.to_string()).collect();
        let b = a.clone();
        let inclusion = move |i: usize, j: usize| i != j && bridge_exact_atomic_subsumed(&a[i], &a[j]) == Some(true);
        let disjoint = move |i: usize, j: usize| bridge_exact_atomic_disjoint(&b[i], &b[j]) == Some(true);
        assert_eq!(bridge_decimal_cells_realizable(&small, &[false, true], &inclusion, &disjoint, &[], 2, &[]), Some(true));
        let eight: Vec<String> = (0..8).map(|v| format!("__dt__val__\"{v}\"^^xsd:integer")).collect();
        let eight: Vec<&str> = eight.iter().map(String::as_str).collect();
        assert_eq!(bridge_decimal_cells_realizable(&small, &[false, false], &inclusion, &disjoint, &eight, 2, &[]), Some(true));
        let nine: Vec<String> = (0..9).map(|v| format!("__dt__val__\"{v}\"^^xsd:integer")).collect();
        let nine: Vec<&str> = nine.iter().map(String::as_str).collect();
        assert_eq!(bridge_decimal_cells_realizable(&small, &[false, false], &inclusion, &disjoint, &nine, 2, &[]), Some(false));
    }

    #[test]
    fn bridge_atomic_gate_matches_the_exact_10621_fragment() {
        for supported in [
            "__dt__boolean",
            "__dt__dateTime",
            "__dt__decimal",
            "__dt__float",
            "__dt__int",
            "__dt__integer",
            "__dt__nonNegativeInteger",
            "__dt__positiveInteger",
            "__dt__string",
            "__dt__val__\"true\"^^xsd:boolean",
            "__dt__val__\"23\"^^xsd:integer",
            "__dt__val__\"McNeal\"^^xsd:string",
            "__dt__val__\"1.5\"^^xsd:float",
            "__dt__c__DataOneOf(\"true\"^^xsd:boolean \"false\"^^xsd:boolean)",
            "__dt__c__DataOneOf(\"false\"^^xsd:boolean \"true\"^^xsd:boolean)",
        ] {
            assert!(
                bridge_exact_atomic_name(supported),
                "expected exact bridge datatype: {supported}"
            );
        }
        for unsupported in [
            "__dt__opaque",
            "__dt__val__opaque",
            "__dt__val__\"1.5\"^^xsd:double",
            "__dt__c__DataUnionOf(xsd:string xsd:boolean)",
            "__dt__dateTimeStamp",
        ] {
            assert!(
                !bridge_exact_atomic_name(unsupported),
                "unexpected exact bridge datatype: {unsupported}"
            );
        }
        assert_eq!(
            bridge_exact_atomic_subsumed("__dt__positiveInteger", "__dt__nonNegativeInteger"),
            Some(true)
        );
        assert_eq!(
            bridge_exact_atomic_subsumed("__dt__nonNegativeInteger", "__dt__integer"),
            Some(true)
        );
        assert_eq!(
            bridge_exact_atomic_subsumed("__dt__integer", "__dt__decimal"),
            Some(true)
        );
        assert_eq!(
            bridge_exact_atomic_subsumed("__dt__decimal", "__dt__integer"),
            None
        );
        assert_eq!(
            bridge_exact_atomic_subsumed("__dt__val__\"2\"^^xsd:integer", "__dt__positiveInteger"),
            Some(true)
        );
    }
}

pub(crate) mod numeric_cells;
