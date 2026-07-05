//! Sound ABox datatype-clash precheck.
//!
//! Detects two asserted-data clashes that entail global inconsistency, both
//! invisible to the CB engine (it drops individuals and over-approximates
//! datatypes as opaque concepts):
//!
//! 1. **Range violation**: `DataPropertyRange(P, D)` with
//!    `DataPropertyAssertion(P, a, lit)` where `lit`'s value provably lies
//!    outside `D`'s value space. The witness case is ore_ont_8941: range
//!    `xsd:string` with language-tagged literals (`"x"@de` is an
//!    `rdf:PlainLiteral` pair, never an `xsd:string` value).
//! 2. **Functional clash**: `FunctionalDataProperty(P)` with two assertions on
//!    one individual whose literals provably denote distinct values.
//!
//! Conservative and sound: a clash is reported only when the two value spaces
//! (rule 1) or the two values (rule 2) are provably disjoint/distinct under the
//! OWL 2 datatype map. Datatypes outside the XSD/rdf/rdfs namespaces, lexical
//! forms we do not canonicalise, and `rdfs:Literal`/`rdf:PlainLiteral` ranges
//! never participate. Range and functional constraints are inherited through
//! `SubDataPropertyOf` (transitively): `P ⊑ Q` makes every `P`-assertion a
//! `Q`-assertion.
//!
//! Like `abox_consistency`, this never touches the `IriRegistry`, so internal
//! name assignment is byte-identical with or without the check. Atoms are
//! borrowed from the document text (zero copies); a cap on retained assertions
//! bounds memory and degrades to "no clash found" (incomplete, never unsound).

use std::collections::{HashMap, HashSet};

use super::parse::strip_annotations;
use super::sexpr::Node;

/// Retain at most this many data assertions; beyond it the check degrades to
/// "not detected" rather than growing without bound on assertion-heavy inputs.
const ASSERTION_CAP: usize = 10_000_000;

/// Pairwise-disjoint value-space families of the OWL 2 datatype map. `dateTime`
/// covers `dateTimeStamp`; the string family covers the `xsd:string`-derived
/// types; the decimal family covers the integer tower. `xsd:float`,
/// `xsd:double` and `xsd:decimal` are pairwise disjoint in OWL 2 (unlike XSD).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Family {
    Str,
    LangString,
    Decimal,
    Float,
    Double,
    Boolean,
    DateTime,
    AnyUri,
    HexBinary,
    Base64Binary,
    XmlLiteral,
}

const XSD_IRI: &str = "http://www.w3.org/2001/XMLSchema#";
const RDF_IRI: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
const RDFS_IRI: &str = "http://www.w3.org/2000/01/rdf-schema#";

/// Family of a datatype token (`xsd:int` or a full `<...XMLSchema#int>` IRI).
/// `None` for unknown datatypes AND for the top-like ranges
/// (`rdfs:Literal`, `rdf:PlainLiteral`), neither of which may ever clash.
fn dtype_family(tok: &str) -> Option<Family> {
    let t = tok.trim_start_matches('<').trim_end_matches('>');
    let local = if let Some(rest) = t.strip_prefix(XSD_IRI) {
        rest
    } else if let Some(rest) = t.strip_prefix("xsd:") {
        rest
    } else if let Some(rest) = t.strip_prefix(RDF_IRI).or_else(|| t.strip_prefix("rdf:")) {
        return match rest {
            "langString" => Some(Family::LangString),
            "XMLLiteral" => Some(Family::XmlLiteral),
            _ => None, // incl. rdf:PlainLiteral (contains string AND langString)
        };
    } else if let Some(rest) = t.strip_prefix(RDFS_IRI).or_else(|| t.strip_prefix("rdfs:")) {
        let _ = rest; // rdfs:Literal is the top datatype: compatible with all
        return None;
    } else {
        return None;
    };
    match local {
        "string" | "normalizedString" | "token" | "language" | "Name" | "NCName" | "NMTOKEN" => {
            Some(Family::Str)
        }
        "decimal" | "integer" | "nonNegativeInteger" | "nonPositiveInteger" | "negativeInteger"
        | "positiveInteger" | "long" | "int" | "short" | "byte" | "unsignedLong"
        | "unsignedInt" | "unsignedShort" | "unsignedByte" => Some(Family::Decimal),
        "float" => Some(Family::Float),
        "double" => Some(Family::Double),
        "boolean" => Some(Family::Boolean),
        "dateTime" | "dateTimeStamp" => Some(Family::DateTime),
        "anyURI" => Some(Family::AnyUri),
        "hexBinary" => Some(Family::HexBinary),
        "base64Binary" => Some(Family::Base64Binary),
        _ => None,
    }
}

/// A literal split into lexical form and tag. The tokeniser ends a quoted
/// string at its closing quote, so `"lex"@lang` / `"lex"^^dt` arrive as TWO
/// atoms: the quoted token and a suffix atom (`@lang` / `^^dt`).
#[derive(Debug)]
enum Lit<'a> {
    Plain(&'a str),          // "lex" == "lex"^^xsd:string in OWL 2
    Lang(&'a str, &'a str),  // (lex, lang)
    Typed(&'a str, &'a str), // (lex, datatype token)
}

fn parse_lit<'b>(tok: &'b str, suffix: Option<&'b str>) -> Option<Lit<'b>> {
    if tok.len() < 2 || !tok.starts_with('"') || !tok.ends_with('"') {
        return None;
    }
    let lex = &tok[1..tok.len() - 1];
    match suffix {
        None => Some(Lit::Plain(lex)),
        Some(s) => {
            if let Some(dt) = s.strip_prefix("^^") {
                Some(Lit::Typed(lex, dt))
            } else {
                s.strip_prefix('@').map(|lang| Lit::Lang(lex, lang))
            }
        }
    }
}

fn lit_family(l: &Lit) -> Option<Family> {
    match l {
        Lit::Plain(_) => Some(Family::Str),
        Lit::Lang(..) => Some(Family::LangString),
        Lit::Typed(_, dt) => dtype_family(dt),
    }
}

/// Unescape the two escapes of the functional syntax (`\"` and `\\`).
fn unescape(lex: &str) -> String {
    let mut out = String::with_capacity(lex.len());
    let mut esc = false;
    for c in lex.chars() {
        if esc {
            out.push(c);
            esc = false;
        } else if c == '\\' {
            esc = true;
        } else {
            out.push(c);
        }
    }
    out
}

/// Canonical decimal representation (`sign`, integer digits, fraction digits)
/// or `None` when the lexical form is not plain decimal syntax.
fn canon_decimal(lex: &str) -> Option<(bool, String, String)> {
    let s = lex.trim();
    let (neg, digits) = match s.strip_prefix('-') {
        Some(d) => (true, d),
        None => (false, s.strip_prefix('+').unwrap_or(s)),
    };
    let (int, frac) = match digits.split_once('.') {
        Some((a, b)) => (a, b),
        None => (digits, ""),
    };
    if int.is_empty() && frac.is_empty() {
        return None;
    }
    if !int.chars().all(|c| c.is_ascii_digit()) || !frac.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let int_c = int.trim_start_matches('0').to_string();
    let frac_c = frac.trim_end_matches('0').to_string();
    let neg_c = neg && !(int_c.is_empty() && frac_c.is_empty()); // -0 == 0
    Some((neg_c, int_c, frac_c))
}

/// `true` only when the two literals PROVABLY denote distinct values.
fn provably_distinct(a: &Lit, b: &Lit) -> bool {
    let (fa, fb) = match (lit_family(a), lit_family(b)) {
        (Some(x), Some(y)) => (x, y),
        _ => return false,
    };
    if fa != fb {
        return true; // families are pairwise disjoint
    }
    match (a, b) {
        // string family: value == lexical form only for xsd:string itself
        // (derived types like xsd:token whitespace-collapse); compare only
        // when both are plain/xsd:string.
        (Lit::Plain(x) | Lit::Typed(x, _), Lit::Plain(y) | Lit::Typed(y, _))
            if fa == Family::Str =>
        {
            let xs = is_plain_string(a) && is_plain_string(b);
            xs && unescape(x) != unescape(y)
        }
        (Lit::Lang(x, lx), Lit::Lang(y, ly)) => {
            // language tags compare case-insensitively
            let same_lang = lx.eq_ignore_ascii_case(ly);
            !same_lang || unescape(x) != unescape(y)
        }
        (Lit::Typed(x, _), Lit::Typed(y, _)) if fa == Family::Decimal => {
            match (canon_decimal(x), canon_decimal(y)) {
                (Some(cx), Some(cy)) => cx != cy,
                _ => false,
            }
        }
        (Lit::Typed(x, _), Lit::Typed(y, _)) if fa == Family::Boolean => {
            let norm = |v: &str| match v.trim() {
                "true" | "1" => Some(true),
                "false" | "0" => Some(false),
                _ => None,
            };
            matches!((norm(x), norm(y)), (Some(p), Some(q)) if p != q)
        }
        _ => false,
    }
}

fn is_plain_string(l: &Lit) -> bool {
    match l {
        Lit::Plain(_) => true,
        Lit::Typed(_, dt) => {
            let t = dt.trim_start_matches('<').trim_end_matches('>');
            t == "xsd:string" || t.strip_prefix(XSD_IRI) == Some("string")
        }
        Lit::Lang(..) => false,
    }
}

/// Union-find over interned individual ids (path-halving).
struct Uf {
    parent: Vec<u32>,
}

impl Uf {
    fn new(n: usize) -> Uf {
        Uf {
            parent: (0..n as u32).collect(),
        }
    }
    fn find(&mut self, mut x: u32) -> u32 {
        while self.parent[x as usize] != x {
            let g = self.parent[self.parent[x as usize] as usize];
            self.parent[x as usize] = g;
            x = g;
        }
        x
    }
    fn union(&mut self, a: u32, b: u32) -> bool {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return false;
        }
        self.parent[ra as usize] = rb;
        true
    }
}

/// Bail-out bounds for the ground merge fixpoint: past these the check
/// degrades to the merge-free rules (incomplete, never unsound).
const MERGE_EDGE_CAP: usize = 400_000;
const MERGE_IND_CAP: usize = 200_000;
const MERGE_ITER_CAP: usize = 64;

#[derive(Default)]
pub struct DataAbox<'a> {
    /// property token -> declared range datatype tokens (conjunctive)
    ranges: HashMap<&'a str, Vec<&'a str>>,
    functional: HashSet<&'a str>,
    /// SubDataPropertyOf edges: sub -> direct supers
    supers: HashMap<&'a str, Vec<&'a str>>,
    /// (property, individual, literal-token, suffix atom `@lang`/`^^dt`)
    assertions: Vec<(&'a str, &'a str, &'a str, Option<&'a str>)>,
    /// data at-most-1 constraints from `C ⊑ ≤1 P` / `C ⊑ =1 P` (class, prop)
    dmax1: Vec<(&'a str, &'a str)>,
    // ---- ground object-level data for ≤1-driven individual merging ----
    /// object role assertions (prop, src, dst)
    oedges: Vec<(&'a str, &'a str, &'a str)>,
    symmetric: HashSet<&'a str>,
    /// `InverseObjectProperties(P, Q)` pairs
    inverses: Vec<(&'a str, &'a str)>,
    /// simple `SubObjectPropertyOf`: sub -> direct supers
    osupers: HashMap<&'a str, Vec<&'a str>>,
    /// object at-most-1 constraints (class token, role); class `""` means ⊤
    omax1: Vec<(&'a str, &'a str)>,
    /// named class assertions (class, individual)
    cassert: Vec<(&'a str, &'a str)>,
    /// named `SubClassOf` edges: sub -> direct supers
    csupers: HashMap<&'a str, Vec<&'a str>>,
    odomain: HashMap<&'a str, Vec<&'a str>>,
    orange: HashMap<&'a str, Vec<&'a str>>,
    /// `DifferentIndividuals` groups
    diffs: Vec<Vec<&'a str>>,
    /// `SameIndividual` pairs
    sames: Vec<(&'a str, &'a str)>,
    overflow: bool,
}

/// `ObjectMaxCardinality(1 P)` / `ObjectExactCardinality(1 P)` — UNQUALIFIED
/// at-most-1 in superclass position. Qualified forms (a filler argument) are
/// skipped: merging their successors would need filler typing.
fn atmost1_role<'n, 'a>(node: &'n Node<'a>, kinds: [&str; 2]) -> Option<&'a str> {
    if let Node::List(h, args) = node {
        if (*h == kinds[0] || *h == kinds[1]) && args.len() == 2 {
            if args[0].as_atom() == Some("1") {
                return args[1].as_atom();
            }
        }
    }
    None
}

impl<'a> DataAbox<'a> {
    pub fn observe(&mut self, node: &Node<'a>) {
        let (head, args) = match node {
            Node::List(h, a) => (*h, a),
            Node::Atom(_) => return,
        };
        match head {
            "DataPropertyRange" => {
                let args = strip_annotations(args);
                if let (Some(p), Some(Some(d))) = (
                    args.first().and_then(|n| n.as_atom()),
                    args.get(1).map(|n| n.as_atom()),
                ) {
                    self.ranges.entry(p).or_default().push(d);
                }
            }
            "FunctionalDataProperty" => {
                let args = strip_annotations(args);
                if let Some(p) = args.first().and_then(|n| n.as_atom()) {
                    self.functional.insert(p);
                }
            }
            "SubDataPropertyOf" => {
                let args = strip_annotations(args);
                if let (Some(Some(s)), Some(Some(t))) = (
                    args.first().map(|n| n.as_atom()),
                    args.get(1).map(|n| n.as_atom()),
                ) {
                    self.supers.entry(s).or_default().push(t);
                }
            }
            "DataPropertyAssertion" => {
                let args = strip_annotations(args);
                if self.assertions.len() >= ASSERTION_CAP {
                    self.overflow = true;
                    return;
                }
                if let (Some(Some(p)), Some(Some(i)), Some(Some(l))) = (
                    args.first().map(|n| n.as_atom()),
                    args.get(1).map(|n| n.as_atom()),
                    args.get(2).map(|n| n.as_atom()),
                ) {
                    let suffix = args
                        .get(3)
                        .and_then(|n| n.as_atom())
                        .filter(|s| s.starts_with('@') || s.starts_with("^^"));
                    self.assertions.push((p, i, l, suffix));
                }
            }
            "ObjectPropertyAssertion" => {
                let args = strip_annotations(args);
                if self.oedges.len() >= MERGE_EDGE_CAP {
                    self.overflow = true;
                    return;
                }
                if let (Some(Some(p)), Some(Some(a)), Some(Some(b))) = (
                    args.first().map(|n| n.as_atom()),
                    args.get(1).map(|n| n.as_atom()),
                    args.get(2).map(|n| n.as_atom()),
                ) {
                    self.oedges.push((p, a, b));
                }
            }
            "SymmetricObjectProperty" => {
                let args = strip_annotations(args);
                if let Some(p) = args.first().and_then(|n| n.as_atom()) {
                    self.symmetric.insert(p);
                }
            }
            "InverseObjectProperties" => {
                let args = strip_annotations(args);
                if let (Some(Some(p)), Some(Some(q))) = (
                    args.first().map(|n| n.as_atom()),
                    args.get(1).map(|n| n.as_atom()),
                ) {
                    self.inverses.push((p, q));
                }
            }
            "SubObjectPropertyOf" => {
                let args = strip_annotations(args);
                if let (Some(Some(s)), Some(Some(t))) = (
                    args.first().map(|n| n.as_atom()),
                    args.get(1).map(|n| n.as_atom()),
                ) {
                    self.osupers.entry(s).or_default().push(t);
                }
            }
            "FunctionalObjectProperty" => {
                let args = strip_annotations(args);
                if let Some(p) = args.first().and_then(|n| n.as_atom()) {
                    self.omax1.push(("", p));
                }
            }
            "ObjectPropertyDomain" => {
                let args = strip_annotations(args);
                if let (Some(Some(p)), Some(Some(c))) = (
                    args.first().map(|n| n.as_atom()),
                    args.get(1).map(|n| n.as_atom()),
                ) {
                    self.odomain.entry(p).or_default().push(c);
                }
            }
            "ObjectPropertyRange" => {
                let args = strip_annotations(args);
                if let (Some(Some(p)), Some(Some(c))) = (
                    args.first().map(|n| n.as_atom()),
                    args.get(1).map(|n| n.as_atom()),
                ) {
                    self.orange.entry(p).or_default().push(c);
                }
            }
            "SubClassOf" => {
                let args = strip_annotations(args);
                let (sub, sup) = match (args.first(), args.get(1)) {
                    (Some(a), Some(b)) => (a, b),
                    _ => return,
                };
                let c = match sub.as_atom() {
                    Some(c) => c,
                    None => return,
                };
                if let Some(d) = sup.as_atom() {
                    self.csupers.entry(c).or_default().push(d);
                } else if let Some(r) =
                    atmost1_role(sup, ["ObjectMaxCardinality", "ObjectExactCardinality"])
                {
                    self.omax1.push((c, r));
                } else if let Some(p) =
                    atmost1_role(sup, ["DataMaxCardinality", "DataExactCardinality"])
                {
                    self.dmax1.push((c, p));
                }
            }
            "EquivalentClasses" => {
                let args = strip_annotations(args);
                // named-named pairs feed the hierarchy; a named class equivalent
                // to an at-most-1 restriction inherits the constraint
                for k in 0..args.len() {
                    if let Some(c) = args[k].as_atom() {
                        for other in &args {
                            if let Some(d) = other.as_atom() {
                                if d != c {
                                    self.csupers.entry(c).or_default().push(d);
                                }
                            } else if let Some(r) = atmost1_role(
                                other,
                                ["ObjectMaxCardinality", "ObjectExactCardinality"],
                            ) {
                                self.omax1.push((c, r));
                            } else if let Some(p) =
                                atmost1_role(other, ["DataMaxCardinality", "DataExactCardinality"])
                            {
                                self.dmax1.push((c, p));
                            }
                        }
                    }
                }
            }
            "ClassAssertion" => {
                let args = strip_annotations(args);
                if let (Some(Some(c)), Some(Some(i))) = (
                    args.first().map(|n| n.as_atom()),
                    args.get(1).map(|n| n.as_atom()),
                ) {
                    self.cassert.push((c, i));
                }
            }
            "DifferentIndividuals" => {
                let args = strip_annotations(args);
                let g: Vec<&str> = args.iter().filter_map(|n| n.as_atom()).collect();
                if g.len() >= 2 {
                    self.diffs.push(g);
                }
            }
            "SameIndividual" => {
                let args = strip_annotations(args);
                let g: Vec<&str> = args.iter().filter_map(|n| n.as_atom()).collect();
                for k in 1..g.len() {
                    self.sames.push((g[k - 1], g[k]));
                }
            }
            _ => {}
        }
    }

    /// Reflexive-transitive supers of `p` under `SubDataPropertyOf`.
    fn all_supers(&self, p: &'a str) -> Vec<&'a str> {
        let mut seen: HashSet<&str> = HashSet::new();
        let mut out = vec![p];
        seen.insert(p);
        let mut stack = vec![p];
        while let Some(x) = stack.pop() {
            if let Some(ts) = self.supers.get(x) {
                for &t in ts {
                    if seen.insert(t) {
                        out.push(t);
                        stack.push(t);
                    }
                }
            }
        }
        out
    }

    /// Reflexive-transitive supers of role `p` under simple `SubObjectPropertyOf`.
    fn role_supers(&self, p: &'a str) -> Vec<&'a str> {
        let mut seen: HashSet<&str> = HashSet::new();
        let mut out = vec![p];
        seen.insert(p);
        let mut stack = vec![p];
        while let Some(x) = stack.pop() {
            if let Some(ts) = self.osupers.get(x) {
                for &t in ts {
                    if seen.insert(t) {
                        out.push(t);
                        stack.push(t);
                    }
                }
            }
        }
        out
    }

    /// Ground ≤1-driven merge fixpoint over the named individuals. Returns the
    /// individual interner, the union-find, and the per-root named-class
    /// memberships (closed under the named hierarchy and domain/range typing),
    /// or `None` when a cap was hit (callers then skip the merge-based rules).
    ///
    /// Every step is an entailment: role assertions closed under symmetry /
    /// inverse / sub-roles, typing via declared domain/range, and merging the
    /// `R`-successors of an individual that provably satisfies `≤1 R` (OWL has
    /// no unique-name assumption, so the equality holds in every model).
    #[allow(clippy::type_complexity)]
    fn merged_roots(&self) -> Option<(HashMap<&'a str, u32>, Uf, HashMap<u32, HashSet<&'a str>>)> {
        if self.overflow {
            return None;
        }
        let mut ids: HashMap<&str, u32> = HashMap::new();
        let mut intern = |s: &'a str, ids: &mut HashMap<&'a str, u32>| -> u32 {
            let next = ids.len() as u32;
            *ids.entry(s).or_insert(next)
        };
        let mut raw_edges: Vec<(&str, u32, u32)> = Vec::new();
        for &(p, a, b) in &self.oedges {
            let ia = intern(a, &mut ids);
            let ib = intern(b, &mut ids);
            raw_edges.push((p, ia, ib));
        }
        let mut casserts: Vec<(&str, u32)> = Vec::new();
        for &(c, i) in &self.cassert {
            let ii = intern(i, &mut ids);
            casserts.push((c, ii));
        }
        let mut sames: Vec<(u32, u32)> = Vec::new();
        for &(a, b) in &self.sames {
            let ia = intern(a, &mut ids);
            let ib = intern(b, &mut ids);
            sames.push((ia, ib));
        }
        for g in &self.diffs {
            for x in g {
                intern(x, &mut ids);
            }
        }
        for &(_, i, _, _) in &self.assertions {
            intern(i, &mut ids);
        }
        if ids.len() > MERGE_IND_CAP {
            return None;
        }
        let mut uf = Uf::new(ids.len());
        for (a, b) in sames {
            uf.union(a, b);
        }
        // class ancestors memo (named hierarchy)
        let mut anc_memo: HashMap<&str, Vec<&'a str>> = HashMap::new();
        let mut ancestors =
            |c: &'a str, memo: &mut HashMap<&'a str, Vec<&'a str>>| -> Vec<&'a str> {
                if let Some(v) = memo.get(c) {
                    return v.clone();
                }
                let mut seen: HashSet<&str> = HashSet::new();
                let mut out = vec![c];
                seen.insert(c);
                let mut stack = vec![c];
                while let Some(x) = stack.pop() {
                    if let Some(ts) = self.csupers.get(x) {
                        for &t in ts {
                            if seen.insert(t) {
                                out.push(t);
                                stack.push(t);
                            }
                        }
                    }
                }
                memo.insert(c, out.clone());
                out
            };
        let mut mem: HashMap<u32, HashSet<&'a str>> = HashMap::new();
        for _ in 0..MERGE_ITER_CAP {
            // closed role-assertion set over current roots
            let mut closed: HashSet<(&str, u32, u32)> = HashSet::new();
            let mut work: Vec<(&str, u32, u32)> = Vec::new();
            for &(p, a, b) in &raw_edges {
                let e = (p, uf.find(a), uf.find(b));
                if closed.insert(e) {
                    work.push(e);
                }
            }
            while let Some((p, a, b)) = work.pop() {
                if closed.len() > MERGE_EDGE_CAP {
                    return None;
                }
                let mut push =
                    |e: (&'a str, u32, u32),
                     closed: &mut HashSet<(&'a str, u32, u32)>,
                     work: &mut Vec<(&'a str, u32, u32)>| {
                        if closed.insert(e) {
                            work.push(e);
                        }
                    };
                if let Some(ts) = self.osupers.get(p) {
                    for &t in ts {
                        push((t, a, b), &mut closed, &mut work);
                    }
                }
                if self.symmetric.contains(p) {
                    push((p, b, a), &mut closed, &mut work);
                }
                for &(x, y) in &self.inverses {
                    if x == p {
                        push((y, b, a), &mut closed, &mut work);
                    }
                    if y == p {
                        push((x, b, a), &mut closed, &mut work);
                    }
                }
            }
            // memberships: assertions + domain/range typing, closed under the
            // named hierarchy
            mem.clear();
            for &(c, i) in &casserts {
                let r = uf.find(i);
                mem.entry(r)
                    .or_default()
                    .extend(ancestors(c, &mut anc_memo));
            }
            for &(p, a, b) in &closed {
                if let Some(ds) = self.odomain.get(p) {
                    for &d in ds {
                        mem.entry(a)
                            .or_default()
                            .extend(ancestors(d, &mut anc_memo));
                    }
                }
                if let Some(rs) = self.orange.get(p) {
                    for &c in rs {
                        mem.entry(b)
                            .or_default()
                            .extend(ancestors(c, &mut anc_memo));
                    }
                }
            }
            // ≤1-driven merging
            let mut by_role: HashMap<&str, Vec<(u32, u32)>> = HashMap::new();
            for &(p, a, b) in &closed {
                by_role.entry(p).or_default().push((a, b));
            }
            let mut merged_any = false;
            for &(c, r) in &self.omax1 {
                let pairs = match by_role.get(r) {
                    Some(v) => v,
                    None => continue,
                };
                let mut first_succ: HashMap<u32, u32> = HashMap::new();
                for &(a, b) in pairs {
                    if !c.is_empty() && !mem.get(&a).is_some_and(|s| s.contains(c)) {
                        continue;
                    }
                    match first_succ.get(&a) {
                        Some(&b0) => {
                            if uf.union(b0, b) {
                                merged_any = true;
                            }
                        }
                        None => {
                            first_succ.insert(a, b);
                        }
                    }
                }
            }
            if !merged_any {
                return Some((ids, uf, mem));
            }
        }
        None
    }

    /// `true` iff the asserted ABox provably contradicts the declared data
    /// ranges, at-most-1 constraints, or `DifferentIndividuals`. Sound: every
    /// reported clash is an OWL 2 entailment; caps degrade to "not detected".
    pub fn is_inconsistent(&self) -> bool {
        // rule 1: literal value outside a (possibly inherited) declared range
        // (independent of merging)
        if !self.ranges.is_empty() {
            for &(p, _i, ltok, suf) in &self.assertions {
                let lit = match parse_lit(ltok, suf) {
                    Some(l) => l,
                    None => continue,
                };
                let lf = match lit_family(&lit) {
                    Some(f) => f,
                    None => continue,
                };
                for q in self.all_supers(p) {
                    if let Some(ds) = self.ranges.get(q) {
                        for d in ds {
                            if let Some(rf) = dtype_family(d) {
                                if rf != lf {
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
        let need_merge_rules = !self.diffs.is_empty()
            || !self.dmax1.is_empty()
            || (!self.functional.is_empty() && !self.assertions.is_empty());
        if !need_merge_rules {
            return false;
        }
        let (ids, mut uf, mem) = match self.merged_roots() {
            Some(t) => t,
            None => return false, // capped: conservative
        };
        // rule 2: two provably-distinct values on one (merged) individual for a
        // functional data property or a class-conditional `≤1 P` constraint
        let mut by_key: HashMap<(&str, u32), Vec<(&str, Option<&str>)>> = HashMap::new();
        for &(p, i, ltok, suf) in &self.assertions {
            let r = uf.find(ids[i]);
            for q in self.all_supers(p) {
                let applies = self.functional.contains(q)
                    || self
                        .dmax1
                        .iter()
                        .any(|&(c, dp)| dp == q && mem.get(&r).is_some_and(|s| s.contains(c)));
                if applies {
                    by_key.entry((q, r)).or_default().push((ltok, suf));
                }
            }
        }
        for lits in by_key.values() {
            if lits.len() < 2 {
                continue;
            }
            for (k, &(x, sx)) in lits.iter().enumerate() {
                let lx = match parse_lit(x, sx) {
                    Some(l) => l,
                    None => continue,
                };
                for &(y, sy) in &lits[k + 1..] {
                    if let Some(ly) = parse_lit(y, sy) {
                        if provably_distinct(&lx, &ly) {
                            return true;
                        }
                    }
                }
            }
        }
        // rule 3: a `DifferentIndividuals` pair forced into one equivalence class
        for g in &self.diffs {
            let mut roots: HashMap<u32, &str> = HashMap::new();
            for &x in g {
                let r = uf.find(ids[x]);
                if let Some(prev) = roots.insert(r, x) {
                    if prev != x {
                        return true;
                    }
                }
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::super::sexpr::Parser;
    use super::*;

    fn build<'a>(texts: &'a [&'a str]) -> DataAbox<'a> {
        let mut da = DataAbox::default();
        for t in texts {
            let node = Parser::new(t).parse().unwrap();
            da.observe(&node);
        }
        da
    }

    #[test]
    fn langtag_literal_violates_string_range() {
        // the ore_ont_8941 witness: range xsd:string, assertion "x"@de
        let da = build(&[
            "DataPropertyRange(<http://x#p> xsd:string)",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"x\"@de)",
        ]);
        assert!(da.is_inconsistent());
    }

    #[test]
    fn matching_string_assertion_is_fine() {
        let da = build(&[
            "DataPropertyRange(<http://x#p> xsd:string)",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"x\"^^xsd:string)",
            "DataPropertyAssertion(<http://x#p> <http://x#b> \"plain\")",
        ]);
        assert!(!da.is_inconsistent());
    }

    #[test]
    fn unknown_datatype_never_clashes() {
        let da = build(&[
            "DataPropertyRange(<http://x#p> <http://x#mytype>)",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"x\"@de)",
            "DataPropertyRange(<http://x#q> rdfs:Literal)",
            "DataPropertyAssertion(<http://x#q> <http://x#a> \"5\"^^xsd:int)",
        ]);
        assert!(!da.is_inconsistent());
    }

    #[test]
    fn string_literal_violates_int_range() {
        let da = build(&[
            "DataPropertyRange(<http://x#p> xsd:int)",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"abc\"^^xsd:string)",
        ]);
        assert!(da.is_inconsistent());
    }

    #[test]
    fn range_inherited_through_subproperty() {
        let da = build(&[
            "SubDataPropertyOf(<http://x#p> <http://x#q>)",
            "DataPropertyRange(<http://x#q> xsd:string)",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"x\"@en)",
        ]);
        assert!(da.is_inconsistent());
    }

    #[test]
    fn functional_distinct_strings_clash() {
        let da = build(&[
            "FunctionalDataProperty(<http://x#p>)",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"x\")",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"y\"^^xsd:string)",
        ]);
        assert!(da.is_inconsistent());
    }

    #[test]
    fn functional_same_value_no_clash() {
        let da = build(&[
            "FunctionalDataProperty(<http://x#p>)",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"5\"^^xsd:int)",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"05\"^^xsd:integer)",
            "DataPropertyAssertion(<http://x#p> <http://x#b> \"7\"^^xsd:int)",
        ]);
        assert!(!da.is_inconsistent());
    }

    #[test]
    fn functional_distinct_integers_clash() {
        let da = build(&[
            "FunctionalDataProperty(<http://x#p>)",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"5\"^^xsd:int)",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"6\"^^xsd:int)",
        ]);
        assert!(da.is_inconsistent());
    }

    #[test]
    fn functional_token_vs_string_lexical_not_compared() {
        // xsd:token whitespace-collapses; "a b" token could equal "a  b"
        // string-wise post-normalisation, so no lexical comparison is made.
        let da = build(&[
            "FunctionalDataProperty(<http://x#p>)",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"a  b\"^^xsd:token)",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"a b\")",
        ]);
        assert!(!da.is_inconsistent());
    }

    #[test]
    fn merge_via_symmetric_domain_exact1_then_data_max1_clash() {
        // the ore_ont_13912 witness: Owner is symmetric with domain Photo, so
        // the shared owner is a Photo with two Owner-successors; Photo ⊑ =1
        // Owner merges them; the merged photo has two distinct url strings
        // against Photo ⊑ ≤1 url.
        let da = build(&[
            "SubClassOf(<http://f#Photo> ObjectExactCardinality(1 <http://f#Owner>))",
            "SubClassOf(<http://f#Photo> DataMaxCardinality(1 <http://f#url>))",
            "SymmetricObjectProperty(<http://f#Owner>)",
            "ObjectPropertyDomain(<http://f#Owner> <http://f#Photo>)",
            "ObjectPropertyAssertion(<http://f#Owner> <http://f#p1> <http://f#u>)",
            "DataPropertyAssertion(<http://f#url> <http://f#p1> \"a\")",
            "ObjectPropertyAssertion(<http://f#Owner> <http://f#p2> <http://f#u>)",
            "DataPropertyAssertion(<http://f#url> <http://f#p2> \"b\")",
        ]);
        assert!(da.is_inconsistent());
    }

    #[test]
    fn no_merge_with_distinct_owners() {
        let da = build(&[
            "SubClassOf(<http://f#Photo> ObjectExactCardinality(1 <http://f#Owner>))",
            "SubClassOf(<http://f#Photo> DataMaxCardinality(1 <http://f#url>))",
            "SymmetricObjectProperty(<http://f#Owner>)",
            "ObjectPropertyDomain(<http://f#Owner> <http://f#Photo>)",
            "ObjectPropertyAssertion(<http://f#Owner> <http://f#p1> <http://f#u1>)",
            "DataPropertyAssertion(<http://f#url> <http://f#p1> \"a\")",
            "ObjectPropertyAssertion(<http://f#Owner> <http://f#p2> <http://f#u2>)",
            "DataPropertyAssertion(<http://f#url> <http://f#p2> \"b\")",
        ]);
        assert!(!da.is_inconsistent());
    }

    #[test]
    fn functional_role_merge_clashes_with_different_individuals() {
        let da = build(&[
            "FunctionalObjectProperty(<http://f#r>)",
            "ObjectPropertyAssertion(<http://f#r> <http://f#a> <http://f#b>)",
            "ObjectPropertyAssertion(<http://f#r> <http://f#a> <http://f#c>)",
            "DifferentIndividuals(<http://f#b> <http://f#c>)",
        ]);
        assert!(da.is_inconsistent());
        let ok = build(&[
            "FunctionalObjectProperty(<http://f#r>)",
            "ObjectPropertyAssertion(<http://f#r> <http://f#a> <http://f#b>)",
            "ObjectPropertyAssertion(<http://f#r> <http://f#a> <http://f#c>)",
        ]);
        assert!(!ok.is_inconsistent());
    }

    #[test]
    fn same_individual_violates_different_individuals() {
        let da = build(&[
            "SameIndividual(<http://f#a> <http://f#b>)",
            "DifferentIndividuals(<http://f#a> <http://f#b>)",
        ]);
        assert!(da.is_inconsistent());
    }

    #[test]
    fn functional_lang_pairs() {
        let same = build(&[
            "FunctionalDataProperty(<http://x#p>)",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"x\"@en)",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"x\"@EN)",
        ]);
        assert!(!same.is_inconsistent());
        let diff = build(&[
            "FunctionalDataProperty(<http://x#p>)",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"x\"@en)",
            "DataPropertyAssertion(<http://x#p> <http://x#a> \"x\"@de)",
        ]);
        assert!(diff.is_inconsistent());
    }
}
