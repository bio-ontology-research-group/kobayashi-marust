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

/// A parsed literal value in the OWL 2 datatype map.
#[derive(Clone, PartialEq, Debug)]
enum Val {
    Num(Rat),
    Bool(bool),
    /// string with optional language tag
    Str(String, Option<String>),
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
        _ => None,
    }
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
        // float/double: finite values are rationals; specials live alongside.
        // Modelled as the numeric partition without bounds or integrality;
        // see `dt_subsumed` for the (non-)relations with decimal.
        "float" | "double" => NamedDt {
            kind: if local == "float" { "float" } else { "double" },
            part: Partition::Numeric,
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
        // XML Schema's derived string types apply whitespace replacement or
        // collapse before entering the value space.  Until that canonical
        // mapping is represented exactly, preserve the token opaquely: raw
        // lexical inequality is not a proof of value inequality.
        Some("normalizedString" | "token" | "language" | "Name" | "NCName" | "NMTOKEN") => {
            Val::Opaque(tok.to_string())
        }
        // OWL uses IEEE binary32/binary64 value spaces.  Parsing a decimal
        // lexical form as an exact rational (or directly as f64 for xsd:float)
        // can distinguish two spellings that round to the same value.  Keep
        // both widths opaque until their exact value canonicalisation exists.
        Some("float" | "double") => Val::Opaque(tok.to_string()),
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

/// A parsed data range.
#[derive(Clone, Debug)]
enum DRange {
    /// a recognised named datatype
    Named(NamedDt),
    /// one of the ⊤ data ranges (`rdfs:Literal`)
    Top,
    /// numeric interval (facet restriction over a numeric base)
    Num(NumRange),
    /// explicit enumeration
    OneOf(Vec<Val>),
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
                    let tighter_min = |cur: &Option<(Rat, bool)>, nb: (Rat, bool)| match cur {
                        None => Some(nb),
                        Some((c, _)) => {
                            if c.lt(&nb.0).unwrap_or(false) {
                                Some(nb)
                            } else {
                                *cur
                            }
                        }
                    };
                    let tighter_max = |cur: &Option<(Rat, bool)>, nb: (Rat, bool)| match cur {
                        None => Some(nb),
                        Some((c, _)) => {
                            if nb.0.lt(c).unwrap_or(false) {
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
        (Val::Bool(a), Val::Bool(b)) => Some(a == b),
        (Val::Str(a, la), Val::Str(b, lb)) => Some(a == b && la == lb),
        // cross-partition values are always distinct
        (Val::Num(_), Val::Bool(_) | Val::Str(..))
        | (Val::Bool(_), Val::Num(_) | Val::Str(..))
        | (Val::Str(..), Val::Num(_) | Val::Bool(_)) => Some(false),
        (Val::Opaque(a), Val::Opaque(b)) if a == b => Some(true),
        _ => None,
    }
}

fn val_partition(v: &Val) -> Option<Partition> {
    match v {
        Val::Num(_) => Some(Partition::Numeric),
        Val::Bool(_) => Some(Partition::Boolean),
        Val::Str(..) => Some(Partition::Strings),
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
        DRange::Top => Some(true),
        DRange::Unknown => None,
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
            Val::Bool(_) | Val::Str(..) => Some(false),
            Val::Opaque(_) => None,
        },
        DRange::Named(nd) => match v {
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
        (_, DRange::Top) => Some(true),
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
        (DRange::Named(a), DRange::Named(b)) => {
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
            (Val::Num(value), Some("integer")) if value.is_integer() => Some("integer"),
            (Val::Str(_, None), Some("string")) => Some("string"),
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
        return None;
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

pub(crate) fn bridge_exact_atomic_name(name: &str) -> bool {
    bridge_exact_atomic_family(name).is_some()
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
    if !bridge_exact_atomic_name(sub) || !bridge_exact_atomic_name(sup) {
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
    if !bridge_exact_atomic_name(left) || !bridge_exact_atomic_name(right) {
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
            _ => None,
        }
    }

    let left = exact_value(left)?;
    let right = exact_value(right)?;
    val_eq(&left, &right)
}

pub(crate) fn bridge_exact_value_equal(left: &str, right: &str) -> Option<bool> {
    if !bridge_exact_atomic_name(left) || !bridge_exact_atomic_name(right) {
        return None;
    }
    let left = left.strip_prefix("__dt__val__")?;
    let right = right.strip_prefix("__dt__val__")?;
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

/// The datatype-relation clauses for the `__dt__` concepts in `names`
/// (collected from the clause set).  Every emitted clause is justified by the
/// OWL 2 datatype map; unknown relations emit nothing.  `cap` bounds the
/// finite-cover enumeration width.
pub fn datatype_relation_clauses(names: &BTreeSet<String>, cap: usize) -> Vec<DLClause> {
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
                    if vals.len() <= cap {
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
    use super::*;

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
            None
        );
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
            "__dt__val__\"16777217\"^^xsd:float",
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
            "__dt__val__\"1.5\"^^xsd:float",
            "__dt__c__DataOneOf(\"true\"^^xsd:boolean)",
            "__dt__c__DataOneOf(\"true\"^^xsd:boolean \"true\"^^xsd:boolean)",
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
