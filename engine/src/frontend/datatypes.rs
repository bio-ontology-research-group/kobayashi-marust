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
    /// non-finite float/double specials (NaN, +INF, -INF), tagged by name
    Special(&'static str),
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

const TOP_TYPES: &[&str] = &["rdfs:Literal", "Literal", "rdf:PlainLiteral", "PlainLiteral"];

fn named_dt(name: &str) -> Option<NamedDt> {
    let local = name.rsplit(':').next().unwrap_or(name);
    let n = |min: Option<i128>, max: Option<i128>| NamedDt {
        part: Partition::Numeric,
        min,
        max,
        integral: true,
        str_level: None,
        finite_bool: false,
    };
    let s = |lvl: u8| NamedDt {
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
            part: Partition::Numeric,
            min: None,
            max: None,
            integral: false,
            str_level: None,
            finite_bool: false,
        },
        "integer" => n(None, None),
        "nonNegativeInteger" => n(Some(0), None),
        "positiveInteger" => n(Some(1), None),
        "nonPositiveInteger" => n(None, Some(0)),
        "negativeInteger" => n(None, Some(-1)),
        "long" => n(Some(i64::MIN as i128), Some(i64::MAX as i128)),
        "int" => n(Some(i32::MIN as i128), Some(i32::MAX as i128)),
        "short" => n(Some(i16::MIN as i128), Some(i16::MAX as i128)),
        "byte" => n(Some(i8::MIN as i128), Some(i8::MAX as i128)),
        "unsignedLong" => n(Some(0), Some(u64::MAX as i128)),
        "unsignedInt" => n(Some(0), Some(u32::MAX as i128)),
        "unsignedShort" => n(Some(0), Some(u16::MAX as i128)),
        "unsignedByte" => n(Some(0), Some(u8::MAX as i128)),
        "string" => s(3),
        "normalizedString" => s(2),
        "token" => s(1),
        "language" | "Name" | "NCName" | "NMTOKEN" => s(0),
        "boolean" => NamedDt {
            part: Partition::Boolean,
            min: None,
            max: None,
            integral: false,
            str_level: None,
            finite_bool: true,
        },
        "anyURI" => NamedDt {
            part: Partition::Uri,
            min: None,
            max: None,
            integral: false,
            str_level: None,
            finite_bool: false,
        },
        "hexBinary" | "base64Binary" => NamedDt {
            part: Partition::Binary,
            min: None,
            max: None,
            integral: false,
            str_level: None,
            finite_bool: false,
        },
        "dateTime" | "dateTimeStamp" | "date" | "time" | "gYear" | "gMonth" | "gDay"
        | "gYearMonth" | "gMonthDay" | "duration" => NamedDt {
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
    let local = dt.rsplit(':').next().unwrap_or(&dt).to_string();
    let val = match local.as_str() {
        "boolean" => match lex.trim() {
            "true" | "1" => Val::Bool(true),
            "false" | "0" => Val::Bool(false),
            _ => return Some((Val::Opaque(tok.to_string()), Some(dt))),
        },
        "string" | "normalizedString" | "token" | "language" | "Name" | "NCName" | "NMTOKEN" => {
            Val::Str(lex.to_string(), None)
        }
        "float" | "double" => match lex.trim() {
            "NaN" => Val::Special("NaN"),
            "INF" | "+INF" => Val::Special("+INF"),
            "-INF" => Val::Special("-INF"),
            t => match parse_decimal(t) {
                Some(r) => Val::Num(r),
                None => match t.parse::<f64>().ok().and_then(f64_to_rat) {
                    Some(r) => Val::Num(r),
                    None => Val::Opaque(tok.to_string()),
                },
            },
        },
        _ if named_dt(&local).map_or(false, |d| d.part == Partition::Numeric) => {
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

/// Exact conversion of a finite f64 (dyadic rational) when it fits i128.
fn f64_to_rat(f: f64) -> Option<Rat> {
    if !f.is_finite() {
        return None;
    }
    let bits = f.to_bits();
    let sign = if bits >> 63 == 1 { -1i128 } else { 1 };
    let exp = ((bits >> 52) & 0x7ff) as i64;
    let frac = (bits & ((1u64 << 52) - 1)) as i128;
    let (mant, e2) = if exp == 0 {
        (frac, -1074i64)
    } else {
        (frac + (1i128 << 52), exp - 1075)
    };
    if e2 >= 0 {
        if e2 > 70 {
            return None; // would overflow; treat as unknown
        }
        Rat::new(sign * mant.checked_shl(e2 as u32)?, 1)
    } else {
        let s = -e2;
        if s > 120 {
            return None;
        }
        Rat::new(sign * mant, 1i128.checked_shl(s as u32)?)
    }
}

/// A facet-restricted numeric interval (the decidable core of
/// `DatatypeRestriction` over numeric base types).
#[derive(Clone, Debug)]
struct NumRange {
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
    if TOP_TYPES.iter().any(|t| name.ends_with(t) || *t == name) {
        return DRange::Top;
    }
    match named_dt(name) {
        Some(d) => DRange::Named(d),
        None => DRange::Unknown,
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
                    Some(d) if d.part == Partition::Numeric => d,
                    _ => return DRange::Unknown,
                };
                let mut r = NumRange {
                    integral: bd.integral,
                    min: bd.min.map(|m| (Rat::from_int(m), true)),
                    max: bd.max.map(|m| (Rat::from_int(m), true)),
                };
                let mut i = 1;
                while i < toks.len() {
                    let facet = {
                        let f = &toks[i];
                        f.rsplit(':').next().unwrap_or(f).to_string()
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
                    match facet.as_str() {
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
        (Val::Special(a), Val::Special(b)) => Some(a == b),
        // cross-partition values are always distinct
        (Val::Num(_), Val::Bool(_) | Val::Str(..))
        | (Val::Bool(_), Val::Num(_) | Val::Str(..))
        | (Val::Str(..), Val::Num(_) | Val::Bool(_)) => Some(false),
        (Val::Special(_), Val::Num(_)) | (Val::Num(_), Val::Special(_)) => Some(false),
        (Val::Opaque(a), Val::Opaque(b)) if a == b => Some(true),
        _ => None,
    }
}

fn val_partition(v: &Val) -> Option<Partition> {
    match v {
        Val::Num(_) | Val::Special(_) => Some(Partition::Numeric),
        Val::Bool(_) => Some(Partition::Boolean),
        Val::Str(..) => Some(Partition::Strings),
        Val::Opaque(_) => None,
    }
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
            Val::Special(_) => Some(false),
            _ => Some(false),
        },
        DRange::Named(nd) => match v {
            Val::Num(rv) => {
                if nd.part != Partition::Numeric {
                    return Some(false);
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
            Val::Special(_) => Some(false), // specials only via float/double, handled as unknown
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
                    // sound within the decimal/integer tower; float/double
                    // are modelled without bounds and without integrality, so
                    // the bound/integrality checks below are only conclusive
                    // for the tower — report unknown otherwise
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
                    let int_ok = b.integral <= a.integral; // b integral ⇒ a integral
                    if a.integral && lo_ok && hi_ok && int_ok {
                        Some(true)
                    } else if !int_ok || !lo_ok || !hi_ok {
                        Some(false)
                    } else {
                        // non-integral pairs (decimal vs float etc.): the
                        // only safe positive is reflexivity
                        if a == b {
                            Some(true)
                        } else {
                            None
                        }
                    }
                }
                Partition::Strings => match (a.str_level, b.str_level) {
                    (Some(x), Some(y)) if x == y => Some(x != 0 || a == b),
                    (Some(x), Some(y)) => Some(x < y && (x != 0)),
                    _ => None,
                },
                _ => Some(a == b),
            }
        }
        (DRange::Num(r), DRange::Named(b)) => {
            if b.part != Partition::Numeric {
                return Some(false);
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
    Some(DtEntry::Range(name.to_string(), range_of_named(rest)))
}

fn cx(name: &str) -> Atom {
    Atom::Concept(name.to_string(), Term::Var("x".to_string()))
}

/// The datatype-relation clauses for the `__dt__` concepts in `names`
/// (collected from the clause set).  Every emitted clause is justified by the
/// OWL 2 datatype map; unknown relations emit nothing.  `cap` bounds the
/// finite-cover enumeration width.
pub fn datatype_relation_clauses(names: &BTreeSet<String>, cap: usize) -> Vec<DLClause> {
    let entries: Vec<DtEntry> = names.iter().filter_map(|n| classify_name(n)).collect();
    let mut out: Vec<DLClause> = Vec::new();
    let mut new_val_names: BTreeSet<String> = BTreeSet::new();
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
        assert!(texts.iter().any(|t| t.contains("val__\\\"5\\\"") && t.contains("xsd:integer")),
            "missing membership: {:#?}", texts);
        assert!(
            cls.iter().any(|c| c.body.len() == 1 && c.head.len() == 1
                && format!("{:?}", c.body[0]).contains("xsd:integer")
                && format!("{:?}", c.head[0]).contains("xsd:decimal")),
            "missing integer ⊑ decimal"
        );
        assert!(
            cls.iter().any(|c| c.head.is_empty() && c.body.len() == 2
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
            cls.iter().filter(|c| c.body.len() == 1 && c.head.len() == 1).count() >= 2,
            "missing value equality inclusions"
        );
        // "1" vs "2": disjoint
        assert!(
            cls.iter().any(|c| c.head.is_empty() && c.body.len() == 2),
            "missing distinct-value clash"
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
            cls.iter().filter(|c| c.body.len() == 1 && c.head.len() == 1).count() >= 2,
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
        assert!(cls.is_empty(), "opaque range must emit nothing, got {}", cls.len());
    }
}
