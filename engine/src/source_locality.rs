//! Syntactic ⊥-locality modules over complete OWL 2 functional-syntax sources.
//!
//! This is the reuse analysis of the retained `incremental-source` session.
//! It never decides an entailment. It only proves that a named class's
//! answers are unchanged between two revisions, or selects a source subset
//! (a module) that the unchanged `km classify` pipeline then classifies.
//!
//! Semantics (Cuenca Grau, Horrocks, Kazakov, Sattler 2008): for a signature
//! `S`, an axiom is ⊥-local when every interpretation that interprets each
//! class, object property and data property outside `S` as empty satisfies it
//! (individuals, datatypes and literals keep their meaning). If every axiom of
//! `O \ M` is ⊥-local w.r.t. `sig(M) ∪ Σ`, then every model of `M` becomes a
//! model of `O` after emptying the symbols outside `sig(M) ∪ Σ`, so `M` and `O`
//! entail the same axioms over `Σ`. The least such `M` (the least fixpoint of
//! adding non-local axioms) is the ⊥-module. For a class `A` the module of
//! `{A}` also fixes every named subsumer of `A` and whether `A` is
//! satisfiable; for `Σ = ∅` it fixes consistency.
//!
//! Each logical axiom compiles to a monotone formula over symbols: "the
//! axiom is non-local w.r.t. `S`". The compiler only claims locality when a
//! syntactic rule proves it (every unknown construct is non-local; formulas
//! are only ever weakened), so a computed module is always a superset of the
//! exact syntactic module and remains a module. The Lean statement of the
//! transfer argument is `ContextCalculus.IncrementalModuleReuse`.


use crate::frontend::sexpr::{Node, Parser};
use crate::fxhash::FxHashMap;

const OWL: &str = "http://www.w3.org/2002/07/owl#";

/// 128-bit statement fingerprint: two independent folded-multiply lanes
/// (wyhash-style, 16 bytes per step) with a splitmix64 finalizer and the
/// length. Process-local: fingerprints are only compared within one session.
pub fn fingerprint(bytes: &[u8]) -> u128 {
    #[inline(always)]
    fn mum(a: u64, b: u64) -> u64 {
        let r = (a as u128).wrapping_mul(b as u128);
        (r as u64) ^ ((r >> 64) as u64)
    }
    #[inline(always)]
    fn fin(mut z: u64) -> u64 {
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    const S: [u64; 4] = [0xa076_1d64_78bd_642f, 0xe703_7ed1_a0b4_28db,
                         0x8ebc_6af0_9c88_c6e3, 0x5899_65cc_7537_4cc3];
    let len = bytes.len() as u64;
    let (mut h1, mut h2) = (S[0] ^ len, S[2] ^ len.rotate_left(32));
    let mut chunks = bytes.chunks_exact(16);
    for c in &mut chunks {
        let a = u64::from_le_bytes(c[..8].try_into().unwrap());
        let b = u64::from_le_bytes(c[8..].try_into().unwrap());
        h1 = mum(a ^ S[1], b ^ h1);
        h2 = mum(b ^ S[3], a ^ h2).rotate_left(23);
    }
    let rest = chunks.remainder();
    let mut tail = [0u8; 16];
    tail[..rest.len()].copy_from_slice(rest);
    let a = u64::from_le_bytes(tail[..8].try_into().unwrap()) ^ (rest.len() as u64) << 56;
    let b = u64::from_le_bytes(tail[8..].try_into().unwrap());
    h1 = mum(a ^ S[1], b ^ h1);
    h2 = mum(b ^ S[3], a ^ h2);
    ((fin(h1 ^ len) as u128) << 64) | fin(h2 ^ h1.rotate_left(17)) as u128
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StmtKind {
    /// `Declaration(...)`.
    Declaration,
    /// Annotation-only statements: no logical meaning.
    Annotation,
    /// `Import(...)`: never reusable (the session rejects imports).
    Import,
    /// Assertions about named individuals and DL-safe rules.
    Assertion,
    /// Every other statement is treated as a logical axiom.
    Logical,
}

#[derive(Clone, Debug)]
pub struct Stmt {
    pub start: usize,
    pub end: usize,
    pub hash: u128,
    pub kind: StmtKind,
}

/// The top-level statement structure of one functional-syntax document.
#[derive(Clone, Debug)]
pub struct Scan {
    /// Byte offset just after the ontology IRI(s): `text[..open_end]` is the
    /// complete header (prefixes, `Ontology(`, ontology/version IRI).
    pub open_end: usize,
    /// Fingerprint of everything outside the statements.
    pub header_hash: u128,
    pub prefixes: Vec<(String, String)>,
    pub statements: Vec<Stmt>,
}

impl Scan {
    /// Order-independent key of the exact statement multiset plus header.
    pub fn content_key(&self) -> u128 {
        let mut hashes: Vec<u128> = self.statements.iter().map(|s| s.hash).collect();
        hashes.sort_unstable();
        let mut bytes = Vec::with_capacity(16 * (hashes.len() + 1));
        bytes.extend_from_slice(&self.header_hash.to_le_bytes());
        for h in hashes {
            bytes.extend_from_slice(&h.to_le_bytes());
        }
        fingerprint(&bytes)
    }
}

const WS: u8 = 1;
const END: u8 = 2;
const CLASS: [u8; 256] = {
    let mut t = [0u8; 256];
    let mut b = 0;
    while b < 256 {
        if matches!(b, 0x09..=0x0D | 0x20 | 0x85 | 0xA0) {
            t[b] = WS | END;
        } else if b == b'(' as usize || b == b')' as usize {
            t[b] = END;
        }
        b += 1;
    }
    t
};

/// Next token span, mirroring `frontend::sexpr::Tokens` exactly.
fn lex(b: &[u8], mut i: usize) -> Option<(usize, usize)> {
    let n = b.len();
    while i < n {
        let c = b[i];
        if CLASS[c as usize] & WS != 0 {
            i += 1;
            continue;
        }
        if c == b'<' {
            let s = i;
            i += 1;
            while i < n && b[i] != b'>' {
                i += 1;
            }
            if i < n {
                i += 1;
            }
            return Some((s, i));
        }
        if c == b'#' {
            while i < n && b[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if c == b'(' || c == b')' {
            return Some((i, i + 1));
        }
        if c == b'"' {
            let s = i;
            i += 1;
            while i < n {
                if b[i] == b'\\' {
                    i += 2;
                    continue;
                }
                if b[i] == b'"' {
                    i += 1;
                    break;
                }
                i += 1;
            }
            return Some((s, i.min(n)));
        }
        let s = i;
        while i < n && CLASS[b[i] as usize] & END == 0 {
            i += 1;
        }
        return Some((s, i));
    }
    None
}

pub fn scan(text: &str) -> Result<Scan, String> {
    let b = text.as_bytes();
    let mut i = 0;
    let mut prefixes = Vec::new();
    let tok = |s: usize, e: usize| &text[s..e];
    // Header: Prefix(...) declarations, then `Ontology(`.
    loop {
        let (s, e) = lex(b, i).ok_or("functional syntax without Ontology(")?;
        match tok(s, e) {
            "Prefix" => {
                let (ps, pe) = lex(b, e).ok_or("truncated Prefix")?;
                if tok(ps, pe) != "(" {
                    return Err("malformed Prefix".into());
                }
                let mut j = pe;
                let mut joined = String::new();
                loop {
                    let (s2, e2) = lex(b, j).ok_or("truncated Prefix")?;
                    j = e2;
                    if tok(s2, e2) == ")" {
                        break;
                    }
                    joined.push_str(tok(s2, e2));
                }
                let eq = joined.find('=').ok_or("malformed Prefix")?;
                let name = joined[..eq].trim().to_string();
                let iri = joined[eq + 1..].trim();
                let iri = iri.strip_prefix('<').and_then(|x| x.strip_suffix('>'))
                    .ok_or("malformed Prefix IRI")?;
                prefixes.push((name, iri.to_string()));
                i = j;
            }
            "Ontology" => {
                let (ps, pe) = lex(b, e).ok_or("truncated Ontology")?;
                if tok(ps, pe) != "(" {
                    return Err("malformed Ontology".into());
                }
                i = pe;
                break;
            }
            other => return Err(format!("unexpected header token {other:?}")),
        }
    }
    // Ontology IRI and version IRI: tokens not followed by `(`.
    let mut open_end = i;
    loop {
        let (s, e) = lex(b, i).ok_or("unterminated Ontology")?;
        let t = tok(s, e);
        if t == ")" || t == "(" {
            break;
        }
        match lex(b, e) {
            Some((s2, e2)) if tok(s2, e2) == "(" => break,
            _ => {
                i = e;
                open_end = e;
            }
        }
    }
    let mut statements = Vec::new();
    let mut closed = false;
    loop {
        let Some((s, e)) = lex(b, i) else { break };
        let t = tok(s, e);
        if t == ")" {
            closed = true;
            i = e;
            break;
        }
        let (ps, pe) = lex(b, e).ok_or("truncated statement")?;
        if tok(ps, pe) != "(" {
            return Err(format!("unexpected token {t:?} in ontology body"));
        }
        let mut depth = 1usize;
        let mut j = pe;
        while depth > 0 {
            let (s2, e2) = lex(b, j).ok_or("unterminated statement")?;
            match &b[s2..e2] {
                b"(" => depth += 1,
                b")" => depth -= 1,
                _ => {}
            }
            j = e2;
        }
        let kind = match t {
            "Declaration" => StmtKind::Declaration,
            "Import" => StmtKind::Import,
            "Annotation" | "AnnotationAssertion" | "SubAnnotationPropertyOf"
            | "AnnotationPropertyDomain" | "AnnotationPropertyRange" => StmtKind::Annotation,
            "ClassAssertion" | "ObjectPropertyAssertion" | "NegativeObjectPropertyAssertion"
            | "DataPropertyAssertion" | "NegativeDataPropertyAssertion" | "SameIndividual"
            | "DifferentIndividuals" | "DLSafeRule" => StmtKind::Assertion,
            _ => StmtKind::Logical,
        };
        statements.push(Stmt { start: s, end: j, hash: fingerprint(&b[s..j]), kind });
        i = j;
    }
    if !closed {
        return Err("unterminated Ontology".into());
    }
    if lex(b, i).is_some() {
        return Err("trailing tokens after Ontology".into());
    }
    let mut h = Vec::with_capacity(open_end + 64);
    h.extend_from_slice(&b[..open_end]);
    Ok(Scan { open_end, header_hash: fingerprint(&h), prefixes, statements })
}

/// Monotone formula over symbol ids: "is in the signature".
#[derive(Clone, Debug)]
enum F {
    T,
    Fa,
    V(u32),
    And(Vec<F>),
    Or(Vec<F>),
}

fn and2(a: F, b: F) -> F {
    match (a, b) {
        (F::Fa, _) | (_, F::Fa) => F::Fa,
        (F::T, x) | (x, F::T) => x,
        (F::And(mut v), F::And(w)) => {
            v.extend(w);
            F::And(v)
        }
        (F::And(mut v), x) | (x, F::And(mut v)) => {
            v.push(x);
            F::And(v)
        }
        (a, b) => F::And(vec![a, b]),
    }
}

fn or2(a: F, b: F) -> F {
    match (a, b) {
        (F::T, _) | (_, F::T) => F::T,
        (F::Fa, x) | (x, F::Fa) => x,
        (F::Or(mut v), F::Or(w)) => {
            v.extend(w);
            F::Or(v)
        }
        (F::Or(mut v), x) | (x, F::Or(mut v)) => {
            v.push(x);
            F::Or(v)
        }
        (a, b) => F::Or(vec![a, b]),
    }
}

const AND_CAP: usize = 256;
const OR_CAP: usize = 200_000;

/// Disjunctive normal form; `None` is `true`. Only ever weakens `f`.
fn dnf(f: &F) -> Option<Vec<Vec<u32>>> {
    match f {
        F::T => None,
        F::Fa => Some(Vec::new()),
        F::V(v) => Some(vec![vec![*v]]),
        F::Or(cs) => {
            let mut out = Vec::new();
            for c in cs {
                out.extend(dnf(c)?);
                if out.len() > OR_CAP {
                    return None;
                }
            }
            Some(out)
        }
        F::And(cs) => {
            let mut parts: Vec<Vec<Vec<u32>>> = Vec::new();
            for c in cs {
                if let Some(d) = dnf(c) {
                    if d.is_empty() {
                        return Some(Vec::new());
                    }
                    parts.push(d);
                }
            }
            if parts.is_empty() {
                return None;
            }
            // Drop the widest factors (a weakening) until the product fits.
            parts.sort_by_key(|p| p.len());
            let mut size = 1usize;
            let mut keep = 0;
            for p in &parts {
                if keep > 0 && size.saturating_mul(p.len()) > AND_CAP {
                    break;
                }
                size = size.saturating_mul(p.len());
                keep += 1;
            }
            parts.truncate(keep);
            let mut acc: Vec<Vec<u32>> = vec![Vec::new()];
            for p in parts {
                let mut next = Vec::with_capacity(acc.len() * p.len());
                for a in &acc {
                    for c in &p {
                        let mut x = a.clone();
                        x.extend_from_slice(c);
                        next.push(x);
                    }
                }
                acc = next;
            }
            Some(acc)
        }
    }
}

/// Compiled locality index of one revision.
pub struct LocalityIndex {
    /// Assertions and rules are outside every module (see `build`).
    pub tbox_mode: bool,
    /// Per logical axiom: it mentions a nominal (TBox mode only). A class
    /// whose module holds such an axiom is affected by every change
    /// (`IncrementalModuleReuse.nominal_module_entails_iff`).
    pub nominal: Vec<bool>,
    /// Almost only EL-style constructors occur (predicts module cost only).
    pub el_like: bool,
    pub assertions: crate::fxhash::FxHashSet<u128>,
    pub symbols: Vec<Box<str>>,
    sym_ids: FxHashMap<Box<str>, u32>,
    /// Published name (source spelling) of each symbol.
    pub names: Vec<Box<str>>,
    name_ids: FxHashMap<Box<str>, u32>,
    /// Some entity is spelled in two ways; published names are then not a
    /// function of the symbol and reuse must decline.
    pub spelling_conflict: bool,
    pub is_class: Vec<bool>,
    /// Per logical axiom.
    pub axiom_hash: Vec<u128>,
    axiom_always: Vec<bool>,
    sig_off: Vec<u32>,
    sig: Vec<u32>,
    /// Conjunctions: literal ranges and owning axiom.
    conj_off: Vec<u32>,
    conj_lits: Vec<u32>,
    conj_axiom: Vec<u32>,
    /// symbol -> conjunctions containing it (CSR).
    occ_off: Vec<u32>,
    occ: Vec<u32>,
    pub axiom_by_hash: FxHashMap<u128, u32>,
    /// Declaration statement hash -> declared entity symbol.
    pub decl_entity: FxHashMap<u128, u32>,
}

struct Builder<'p> {
    prefixes: &'p [(String, String)],
    symbols: Vec<Box<str>>,
    sym_ids: FxHashMap<Box<str>, u32>,
    is_class: Vec<bool>,
    names: Vec<Box<str>>,
    spelling_conflict: bool,
    /// No universal object property occurs, every compiled construct is
    /// understood, and (outside TBox mode) no nominal occurs.
    individual_free: bool,
    /// Only EL-style constructors were seen (a cost heuristic, no semantics).
    el_like: bool,
    /// TBox mode: nominals (`ObjectOneOf`, `ObjectHasValue`) are read as
    /// empty, the masked side of the disjoint-union argument.
    nominal_bot: bool,
    /// The axiom being compiled mentions a nominal.
    cur_nominal: bool,
}

impl Builder<'_> {
    fn resolve(&self, tok: &str) -> Option<String> {
        if let Some(inner) = tok.strip_prefix('<') {
            return Some(inner.strip_suffix('>').unwrap_or(inner).to_string());
        }
        let c = *tok.as_bytes().first()?;
        if c == b'"' || c == b'^' || c == b'@' || c.is_ascii_digit() || c == b'-' || c == b'+'
            || tok.starts_with("_:")
        {
            return None;
        }
        let p = tok.find(':')?;
        let (pre, local) = (&tok[..=p], &tok[p + 1..]);
        for (name, iri) in self.prefixes.iter().rev() {
            if name == pre {
                return Some(format!("{iri}{local}"));
            }
        }
        let builtin = match pre {
            "owl:" => OWL,
            "rdf:" => "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
            "rdfs:" => "http://www.w3.org/2000/01/rdf-schema#",
            "xsd:" => "http://www.w3.org/2001/XMLSchema#",
            "xml:" => "http://www.w3.org/XML/1998/namespace",
            _ => return None,
        };
        Some(format!("{builtin}{local}"))
    }

    fn is_builtin(&self, node: &Node<'_>, local: &str) -> bool {
        node.as_atom().and_then(|t| self.resolve(t)).is_some_and(|iri| {
            iri.strip_prefix(OWL) == Some(local)
        })
    }

    /// Intern a resolved IRI, recording its source spelling: the published
    /// taxonomy names an entity by its spelling (a prefixed name, or a full
    /// IRI without brackets).
    fn intern(&mut self, iri: &str, tok: &str) -> u32 {
        let spelling = tok.strip_prefix('<').and_then(|x| x.strip_suffix('>')).unwrap_or(tok);
        if let Some(&id) = self.sym_ids.get(iri) {
            if &*self.names[id as usize] != spelling {
                self.spelling_conflict = true;
            }
            return id;
        }
        let id = self.symbols.len() as u32;
        let key: Box<str> = iri.into();
        self.symbols.push(key.clone());
        self.sym_ids.insert(key, id);
        self.names.push(spelling.into());
        self.is_class.push(false);
        id
    }

    fn collect(&mut self, node: &Node<'_>, out: &mut Vec<u32>) {
        match node {
            Node::Atom(t) => {
                if let Some(iri) = self.resolve(t) {
                    out.push(self.intern(&iri, t));
                }
            }
            Node::List(h, args) => {
                if *h == "Annotation" {
                    return;
                }
                for a in args {
                    self.collect(a, out);
                }
            }
        }
    }

    fn role(&mut self, node: &Node<'_>) -> F {
        match node {
            Node::Atom(t) => match self.resolve(t) {
                Some(iri) if iri == format!("{OWL}topObjectProperty") => {
                    self.individual_free = false;
                    F::T
                }
                Some(iri) if iri == format!("{OWL}bottomObjectProperty") => F::Fa,
                Some(iri) => F::V(self.intern(&iri, t)),
                None => F::T,
            },
            Node::List("ObjectInverseOf", args) if args.len() == 1 => {
                self.el_like = false;
                self.role(&args[0])
            }
            _ => {
                self.individual_free = false;
                F::T
            }
        }
    }

    fn dprop(&mut self, node: &Node<'_>) -> F {
        match node {
            Node::Atom(t) => match self.resolve(t) {
                Some(iri) if iri == format!("{OWL}topDataProperty") => F::T,
                Some(iri) if iri == format!("{OWL}bottomDataProperty") => F::Fa,
                Some(iri) => F::V(self.intern(&iri, t)),
                None => F::T,
            },
            _ => F::T,
        }
    }

    /// (not provably ⊥, not provably ⊤) under emptying symbols outside S.
    fn class(&mut self, node: &Node<'_>) -> (F, F) {
        let unknown = (F::T, F::T);
        match node {
            Node::Atom(t) => match self.resolve(t) {
                Some(iri) if iri == format!("{OWL}Thing") => (F::T, F::Fa),
                Some(iri) if iri == format!("{OWL}Nothing") => (F::Fa, F::T),
                Some(iri) => {
                    let id = self.intern(&iri, t);
                    self.is_class[id as usize] = true;
                    (F::V(id), F::T)
                }
                None => {
                    self.individual_free = false;
                    unknown
                }
            },
            Node::List(head, args) => {
                if matches!(*head, "ObjectComplementOf" | "ObjectUnionOf" | "ObjectAllValuesFrom"
                    | "ObjectMinCardinality" | "ObjectMaxCardinality" | "ObjectExactCardinality"
                    | "ObjectHasSelf" | "DataAllValuesFrom" | "DataMinCardinality"
                    | "DataMaxCardinality" | "DataExactCardinality")
                {
                    self.el_like = false;
                }
                let card = |a: Option<&Node<'_>>| -> Option<u64> {
                    a.and_then(|n| n.as_atom()).and_then(|t| t.parse::<u64>().ok())
                };
                match *head {
                    "ObjectIntersectionOf" if !args.is_empty() => {
                        let (mut nb, mut nt) = (F::T, F::Fa);
                        for a in args {
                            let (b, t) = self.class(a);
                            nb = and2(nb, b);
                            nt = or2(nt, t);
                        }
                        (nb, nt)
                    }
                    "ObjectUnionOf" if !args.is_empty() => {
                        let (mut nb, mut nt) = (F::Fa, F::T);
                        for a in args {
                            let (b, t) = self.class(a);
                            nb = or2(nb, b);
                            nt = and2(nt, t);
                        }
                        (nb, nt)
                    }
                    "ObjectComplementOf" if args.len() == 1 => {
                        let (b, t) = self.class(&args[0]);
                        (t, b)
                    }
                    // TBox mode: a nominal is empty on the masked side.
                    "ObjectOneOf" if self.nominal_bot && !args.is_empty() => {
                        self.cur_nominal = true;
                        (F::Fa, F::T)
                    }
                    "ObjectHasValue" if self.nominal_bot && args.len() == 2 => {
                        self.cur_nominal = true;
                        self.role(&args[0]);
                        (F::Fa, F::T)
                    }
                    "ObjectOneOf" => {
                        if args.is_empty() {
                            (F::Fa, F::T)
                        } else {
                            self.individual_free = false;
                            unknown
                        }
                    }
                    "ObjectSomeValuesFrom" if args.len() == 2 => {
                        let r = self.role(&args[0]);
                        let (b, _) = self.class(&args[1]);
                        (and2(r, b), F::T)
                    }
                    "ObjectAllValuesFrom" if args.len() == 2 => {
                        let r = self.role(&args[0]);
                        let (_, t) = self.class(&args[1]);
                        (F::T, and2(r, t))
                    }
                    "ObjectHasValue" | "ObjectHasSelf" if !args.is_empty() => {
                        if *head == "ObjectHasValue" {
                            self.individual_free = false;
                        }
                        (self.role(&args[0]), F::T)
                    }
                    "ObjectMinCardinality" | "ObjectMaxCardinality" | "ObjectExactCardinality"
                        if args.len() == 2 || args.len() == 3 =>
                    {
                        let Some(n) = card(args.first()) else { return unknown };
                        let r = self.role(&args[1]);
                        let filler = match args.get(2) {
                            Some(c) => self.class(c).0,
                            None => F::T,
                        };
                        let nonempty = and2(r, filler);
                        match (*head, n) {
                            ("ObjectMinCardinality", 0) => (F::T, F::Fa),
                            ("ObjectMinCardinality", _) => (nonempty, F::T),
                            ("ObjectMaxCardinality", _) | ("ObjectExactCardinality", 0) => {
                                (F::T, nonempty)
                            }
                            _ => (nonempty, F::T),
                        }
                    }
                    "DataSomeValuesFrom" if args.len() >= 2 => {
                        let mut nb = F::T;
                        for p in &args[..args.len() - 1] {
                            let f = self.dprop(p);
                            nb = and2(nb, f);
                        }
                        (nb, F::T)
                    }
                    "DataAllValuesFrom" if args.len() >= 2 => {
                        let mut nt = F::T;
                        for p in &args[..args.len() - 1] {
                            let f = self.dprop(p);
                            nt = and2(nt, f);
                        }
                        (F::T, nt)
                    }
                    // The literal may be split into lexical form and
                    // `^^datatype` / `@lang` tokens: only the property counts.
                    "DataHasValue" if args.len() >= 2 => (self.dprop(&args[0]), F::T),
                    "DataMinCardinality" | "DataMaxCardinality" | "DataExactCardinality"
                        if args.len() == 2 || args.len() == 3 =>
                    {
                        let Some(n) = card(args.first()) else { return unknown };
                        let p = self.dprop(&args[1]);
                        match (*head, n) {
                            ("DataMinCardinality", 0) => (F::T, F::Fa),
                            ("DataMinCardinality", _) => (p, F::T),
                            ("DataMaxCardinality", _) | ("DataExactCardinality", 0) => (F::T, p),
                            _ => (p, F::T),
                        }
                    }
                    _ => {
                        self.individual_free = false;
                        unknown
                    }
                }
            }
        }
    }

    fn pairs(&mut self, fs: Vec<F>) -> F {
        if fs.len() > 400 {
            return fs.into_iter().fold(F::Fa, or2);
        }
        let mut out = F::Fa;
        for i in 0..fs.len() {
            for j in i + 1..fs.len() {
                out = or2(out, and2(fs[i].clone(), fs[j].clone()));
            }
        }
        out
    }

    /// Non-locality formula of one logical axiom.
    fn axiom(&mut self, head: &str, args: &[&Node<'_>]) -> F {
        if matches!(head, "DisjointUnion" | "FunctionalObjectProperty" | "InverseFunctionalObjectProperty"
            | "SymmetricObjectProperty" | "AsymmetricObjectProperty" | "IrreflexiveObjectProperty"
            | "InverseObjectProperties" | "DisjointObjectProperties" | "DLSafeRule")
        {
            self.el_like = false;
        }
        let class_nb = |s: &mut Self, n: &Node<'_>| s.class(n).0;
        match (head, args.len()) {
            ("SubClassOf", 2) => {
                let (b, _) = self.class(args[0]);
                let (_, t) = self.class(args[1]);
                and2(b, t)
            }
            ("EquivalentClasses", n) if n >= 1 => {
                let (mut nb, mut nt) = (F::Fa, F::Fa);
                for a in args {
                    let (b, t) = self.class(a);
                    nb = or2(nb, b);
                    nt = or2(nt, t);
                }
                and2(nb, nt)
            }
            ("DisjointClasses", n) if n >= 1 => {
                let fs = args.iter().map(|a| class_nb(self, a)).collect();
                self.pairs(fs)
            }
            ("DisjointUnion", n) if n >= 1 => {
                args.iter().fold(F::Fa, |acc, a| {
                    let f = class_nb(self, a);
                    or2(acc, f)
                })
            }
            ("SubObjectPropertyOf", 2) => {
                let sub = match args[0] {
                    Node::List("ObjectPropertyChain", rs) => {
                        rs.iter().fold(F::T, |acc, r| {
                            let f = self.role(r);
                            and2(acc, f)
                        })
                    }
                    r => self.role(r),
                };
                let sup_top = self.is_builtin(args[1], "topObjectProperty");
                if sup_top { F::Fa } else { sub }
            }
            ("EquivalentObjectProperties", _) | ("InverseObjectProperties", _) => {
                args.iter().fold(F::Fa, |acc, r| {
                    let f = self.role(r);
                    or2(acc, f)
                })
            }
            ("DisjointObjectProperties", _) => {
                let fs = args.iter().map(|r| self.role(r)).collect();
                self.pairs(fs)
            }
            ("ObjectPropertyDomain", 2) | ("ObjectPropertyRange", 2) => {
                let r = self.role(args[0]);
                let (_, t) = self.class(args[1]);
                and2(r, t)
            }
            ("FunctionalObjectProperty", 1)
            | ("InverseFunctionalObjectProperty", 1)
            | ("IrreflexiveObjectProperty", 1)
            | ("AsymmetricObjectProperty", 1)
            | ("TransitiveObjectProperty", 1)
            | ("SymmetricObjectProperty", 1) => self.role(args[0]),
            ("SubDataPropertyOf", 2) => {
                let sup_top = self.is_builtin(args[1], "topDataProperty");
                let sub = self.dprop(args[0]);
                if sup_top { F::Fa } else { sub }
            }
            ("EquivalentDataProperties", _) => args.iter().fold(F::Fa, |acc, p| {
                let f = self.dprop(p);
                or2(acc, f)
            }),
            ("DisjointDataProperties", _) => {
                let fs = args.iter().map(|p| self.dprop(p)).collect();
                self.pairs(fs)
            }
            ("DataPropertyDomain", 2) => {
                let p = self.dprop(args[0]);
                let (_, t) = self.class(args[1]);
                and2(p, t)
            }
            ("DataPropertyRange", 2) | ("FunctionalDataProperty", 1) => self.dprop(args[0]),
            ("HasKey", n) if n >= 1 => self.class(args[0]).0,
            ("ClassAssertion", 2) => self.class(args[0]).1,
            ("NegativeObjectPropertyAssertion", 3) => self.role(args[0]),
            ("NegativeDataPropertyAssertion", 3) => self.dprop(args[0]),
            ("ReflexiveObjectProperty", 1) => {
                self.role(args[0]);
                F::T
            }
            ("DatatypeDefinition", 2) => F::T,
            ("ObjectPropertyAssertion", 3) | ("DataPropertyAssertion", 3)
            | ("SameIndividual", _) | ("DifferentIndividuals", _) | ("DLSafeRule", _) => {
                self.individual_free = false;
                F::T
            }
            // Every unknown statement: non-local, and it may mention
            // individuals.
            _ => {
                self.individual_free = false;
                F::T
            }
        }
    }
}

impl LocalityIndex {
    /// `tbox`: leave assertions and DL-safe rules out of every module, and
    /// read nominals as empty. Only valid when the remaining axioms mention no
    /// universal object property (checked; otherwise the full index is built),
    /// both revisions are known consistent (the caller's obligation), and a
    /// class whose module holds a `nominal` axiom is treated as affected
    /// (`affected_classes_tbox`): the disjoint-union argument covers only
    /// nominal-free modules.
    pub fn build(text: &str, scan: &Scan, tbox: bool) -> Result<Self, String> {
        let ix = Self::build_mode(text, scan, tbox)?;
        if tbox && !ix.tbox_mode {
            return Self::build_mode(text, scan, false);
        }
        Ok(ix)
    }

    fn build_mode(text: &str, scan: &Scan, tbox: bool) -> Result<Self, String> {
        let mut bld = Builder {
            prefixes: &scan.prefixes,
            symbols: Vec::new(),
            sym_ids: FxHashMap::default(),
            is_class: Vec::new(),
            names: Vec::new(),
            spelling_conflict: false,
            individual_free: true,
            el_like: true,
            nominal_bot: tbox,
            cur_nominal: false,
        };
        let mut assertions = crate::fxhash::FxHashSet::default();
        let mut non_el = 0usize;
        let mut axiom_hash = Vec::new();
        let mut axiom_always = Vec::new();
        let mut nominal: Vec<bool> = Vec::new();
        let (mut sig_off, mut sig) = (vec![0u32], Vec::new());
        let (mut conj_off, mut conj_lits, mut conj_axiom) = (vec![0u32], Vec::new(), Vec::new());
        let mut axiom_by_hash = FxHashMap::default();
        let mut decl_entity = FxHashMap::default();
        let mut buf = Vec::new();
        for st in &scan.statements {
            let slice = &text[st.start..st.end];
            match st.kind {
                StmtKind::Annotation => continue,
                StmtKind::Import => return Err("imports are not reusable".into()),
                StmtKind::Declaration => {
                    let node = Parser::new(slice).parse()?;
                    if let Node::List(_, args) = &node {
                        for a in args {
                            if let Node::List(kind, inner) = a {
                                if *kind == "Annotation" {
                                    continue;
                                }
                                if let Some(Node::Atom(t)) = inner.first() {
                                    if let Some(iri) = bld.resolve(t) {
                                        let id = bld.intern(&iri, t);
                                        if *kind == "Class" {
                                            bld.is_class[id as usize] = true;
                                        }
                                        decl_entity.insert(st.hash, id);
                                    }
                                }
                            }
                        }
                    }
                    continue;
                }
                StmtKind::Assertion if tbox => {
                    // The disjoint-union argument needs assertions (and rule
                    // atoms) free of the universal object property.
                    if slice.contains("topObjectProperty") {
                        bld.individual_free = false;
                    }
                    assertions.insert(st.hash);
                    continue;
                }
                StmtKind::Assertion | StmtKind::Logical => {}
            }
            if axiom_by_hash.contains_key(&st.hash) {
                continue; // duplicate statement: one axiom
            }
            let node = Parser::new(slice).parse()?;
            let (head, args) = match &node {
                Node::List(h, a) => (*h, a.iter().filter(|n| n.head() != Some("Annotation")).collect::<Vec<_>>()),
                Node::Atom(_) => return Err("malformed statement".into()),
            };
            bld.el_like = true;
            bld.cur_nominal = false;
            let f = bld.axiom(head, &args);
            nominal.push(bld.cur_nominal);
            if !bld.el_like {
                non_el += 1;
            }
            buf.clear();
            for a in &args {
                bld.collect(a, &mut buf);
            }
            buf.sort_unstable();
            buf.dedup();
            let id = axiom_hash.len() as u32;
            axiom_by_hash.insert(st.hash, id);
            axiom_hash.push(st.hash);
            sig.extend_from_slice(&buf);
            sig_off.push(sig.len() as u32);
            match dnf(&f) {
                None => axiom_always.push(true),
                Some(conjs) => {
                    let mut always = false;
                    for mut c in conjs {
                        c.sort_unstable();
                        c.dedup();
                        if c.is_empty() {
                            always = true;
                            break;
                        }
                        conj_lits.extend_from_slice(&c);
                        conj_off.push(conj_lits.len() as u32);
                        conj_axiom.push(id);
                    }
                    axiom_always.push(always);
                }
            }
        }
        let nsym = bld.symbols.len();
        let mut counts = vec![0u32; nsym + 1];
        for &l in &conj_lits {
            counts[l as usize + 1] += 1;
        }
        for i in 0..nsym {
            counts[i + 1] += counts[i];
        }
        let occ_off = counts.clone();
        let mut fill = counts;
        let mut occ = vec![0u32; conj_lits.len()];
        for c in 0..conj_axiom.len() {
            for &l in &conj_lits[conj_off[c] as usize..conj_off[c + 1] as usize] {
                occ[fill[l as usize] as usize] = c as u32;
                fill[l as usize] += 1;
            }
        }
        Ok(LocalityIndex {
            tbox_mode: tbox && bld.individual_free,
            nominal,
            // At most 1 % of the axioms use non-EL constructors.
            el_like: non_el * 100 <= axiom_hash.len(),
            assertions,
            symbols: bld.symbols,
            sym_ids: bld.sym_ids,
            is_class: bld.is_class,
            name_ids: bld.names.iter().enumerate().map(|(i, n)| (n.clone(), i as u32)).collect(),
            names: bld.names,
            spelling_conflict: bld.spelling_conflict,
            axiom_hash,
            axiom_always,
            sig_off,
            sig,
            conj_off,
            conj_lits,
            conj_axiom,
            occ_off,
            occ,
            axiom_by_hash,
            decl_entity,
        })
    }

    pub fn symbol(&self, iri: &str) -> Option<u32> {
        self.sym_ids.get(iri).copied()
    }

    /// Symbol of a published name.
    pub fn named(&self, name: &str) -> Option<u32> {
        self.name_ids.get(name).copied()
    }

    pub fn axiom_count(&self) -> usize {
        self.axiom_hash.len()
    }

    fn sig_of(&self, ax: u32) -> &[u32] {
        &self.sig[self.sig_off[ax as usize] as usize..self.sig_off[ax as usize + 1] as usize]
    }

    fn need(&self, c: usize) -> u32 {
        self.conj_off[c + 1] - self.conj_off[c]
    }

    /// Module of `seeds` with `disabled` axioms absent: (axioms, signature).
    pub fn module(&self, seeds: &[u32], disabled: &[bool]) -> (Vec<u32>, Vec<bool>) {
        let mut st = State::fresh(self);
        let mut queue = Vec::new();
        for ax in 0..self.axiom_hash.len() {
            if self.axiom_always[ax] && !disabled[ax] {
                st.fire(self, ax as u32, &mut queue);
            }
        }
        for &s in seeds {
            st.add(s, &mut queue);
        }
        st.run(self, &mut queue, disabled, &mut |_| false);
        let axioms = (0..self.axiom_hash.len() as u32).filter(|&a| st.in_mod[a as usize]).collect();
        (axioms, st.in_s)
    }

    /// Whether the module of the empty signature contains no `marked` axiom.
    pub fn empty_module_avoids(&self, marked: &[bool]) -> bool {
        let none = vec![false; self.axiom_hash.len()];
        let (base, _) = self.module(&[], &none);
        !base.iter().any(|&a| marked[a as usize])
    }

    /// Statement fingerprints of the module of the empty signature.
    pub fn empty_module_statements(&self) -> Vec<u128> {
        let none = vec![false; self.axiom_hash.len()];
        let (base, _) = self.module(&[], &none);
        base.iter().map(|&a| self.axiom_hash[a as usize]).collect()
    }

    /// Classes whose module contains a `marked` axiom. `None`: the module of
    /// the empty signature does, so every class (and consistency) is affected.
    /// `affected_classes` with every nominal axiom also marked: in TBox
    /// mode, a class is unaffected only if its module avoids `marked` and
    /// mentions no nominal. Outside TBox mode no axiom is a `nominal` one.
    pub fn affected_classes_tbox(&self, marked: &[bool]) -> Option<Vec<u32>> {
        let trig: Vec<bool> = marked.iter().zip(&self.nominal).map(|(m, n)| *m || *n).collect();
        self.affected_classes(&trig)
    }

    /// Some axiom of `module` mentions a nominal: in TBox mode it is then not
    /// a module of the complete revision (assertions and nominals are left out).
    pub fn module_has_nominal(&self, module: &[u32]) -> bool {
        module.iter().any(|&a| self.nominal[a as usize])
    }

    pub fn affected_classes(&self, marked: &[bool]) -> Option<Vec<u32>> {
        let none = vec![false; self.axiom_hash.len()];
        let mut base = State::fresh(self);
        let mut queue = Vec::new();
        for ax in 0..self.axiom_hash.len() {
            if self.axiom_always[ax] {
                base.fire(self, ax as u32, &mut queue);
            }
        }
        base.run(self, &mut queue, &none, &mut |_| false);
        if (0..self.axiom_hash.len()).any(|a| base.in_mod[a] && marked[a]) {
            return None;
        }
        // Depth-first over a forest in which every class's parent lies in
        // its module signature (a single-literal trigger `B` of an axiom whose
        // signature contains class `A` puts `A` into the module of `B`). Then
        // the module of a class is the closure of its own seed added to its
        // parent's state, so each class only propagates its delta. A class
        // whose delta fires a marked axiom is affected together with its whole
        // subtree (their modules contain its module).
        let nsym = self.symbols.len();
        let candidate = |a: u32| self.is_class[a as usize] && !base.in_s[a as usize];
        let mut parent = vec![u32::MAX; nsym];
        for c in 0..self.conj_axiom.len() {
            if self.conj_off[c + 1] - self.conj_off[c] != 1 {
                continue;
            }
            let b = self.conj_lits[self.conj_off[c] as usize];
            if !candidate(b) || parent[b as usize] != u32::MAX {
                continue;
            }
            if let Some(&a) = self
                .sig_of(self.conj_axiom[c])
                .iter()
                .find(|&&a| a != b && candidate(a))
            {
                parent[b as usize] = a;
            }
        }
        let mut child_off = vec![0u32; nsym + 1];
        for b in 0..nsym {
            if parent[b] != u32::MAX {
                child_off[parent[b] as usize + 1] += 1;
            }
        }
        for i in 0..nsym {
            child_off[i + 1] += child_off[i];
        }
        let mut fill = child_off.clone();
        let mut children = vec![0u32; child_off[nsym] as usize];
        for b in 0..nsym {
            if parent[b] != u32::MAX {
                let p = parent[b] as usize;
                children[fill[p] as usize] = b as u32;
                fill[p] += 1;
            }
        }
        drop(fill);
        let mut visited = vec![false; nsym];
        let mut affected = vec![false; nsym];
        let mut work = base.clone();
        work.logging = true;
        work.log_s.clear();
        work.log_c.clear();
        work.log_m.clear();
        // (node, checkpoint, next child index)
        let mut frames: Vec<(u32, (usize, usize, usize), u32)> = Vec::new();
        let mut sub: Vec<u32> = Vec::new();
        let roots: Vec<u32> = (0..nsym as u32)
            .filter(|&a| candidate(a) && parent[a as usize] == u32::MAX)
            .chain((0..nsym as u32).filter(|&a| candidate(a)))
            .collect();
        for root in roots {
            if visited[root as usize] {
                continue;
            }
            let mut next = Some(root);
            loop {
                if let Some(node) = next.take() {
                    visited[node as usize] = true;
                    let cp = (work.log_s.len(), work.log_c.len(), work.log_m.len());
                    queue.clear();
                    work.add(node, &mut queue);
                    let hit = work.run_logged(self, &mut queue, &none, &mut |ev| match ev {
                        Event::Axiom(ax) => marked[ax as usize],
                        Event::Symbol(_) => false,
                    });
                    if hit {
                        work.undo_to(cp);
                        sub.clear();
                        sub.push(node);
                        while let Some(x) = sub.pop() {
                            affected[x as usize] = true;
                            visited[x as usize] = true;
                            for &y in &children[child_off[x as usize] as usize..child_off[x as usize + 1] as usize] {
                                if !affected[y as usize] {
                                    sub.push(y);
                                }
                            }
                        }
                    } else {
                        frames.push((node, cp, child_off[node as usize]));
                    }
                }
                let Some(top) = frames.last_mut() else { break };
                let (node, cp, pos) = *top;
                if pos < child_off[node as usize + 1] {
                    top.2 += 1;
                    let child = children[pos as usize];
                    if !visited[child as usize] {
                        next = Some(child);
                    }
                } else {
                    work.undo_to(cp);
                    frames.pop();
                }
            }
        }
        let out: Vec<u32> = (0..nsym as u32).filter(|&a| affected[a as usize] && candidate(a)).collect();
        Some(out)
    }
}

enum Event {
    Axiom(u32),
    Symbol(u32),
}

#[derive(Clone)]
struct State {
    in_s: Vec<bool>,
    remaining: Vec<u32>,
    in_mod: Vec<bool>,
    logging: bool,
    log_s: Vec<u32>,
    log_c: Vec<u32>,
    log_m: Vec<u32>,
}

impl State {
    fn fresh(ix: &LocalityIndex) -> Self {
        State {
            in_s: vec![false; ix.symbols.len()],
            remaining: (0..ix.conj_axiom.len()).map(|c| ix.need(c)).collect(),
            in_mod: vec![false; ix.axiom_hash.len()],
            logging: false,
            log_s: Vec::new(),
            log_c: Vec::new(),
            log_m: Vec::new(),
        }
    }

    fn log_start(&mut self) {
        self.logging = true;
        self.log_s.clear();
        self.log_c.clear();
        self.log_m.clear();
    }

    /// Revert every logged change after `cp` (nested checkpoints).
    fn undo_to(&mut self, cp: (usize, usize, usize)) {
        for &s in &self.log_s[cp.0..] {
            self.in_s[s as usize] = false;
        }
        for &c in &self.log_c[cp.1..] {
            self.remaining[c as usize] += 1;
        }
        for &m in &self.log_m[cp.2..] {
            self.in_mod[m as usize] = false;
        }
        self.log_s.truncate(cp.0);
        self.log_c.truncate(cp.1);
        self.log_m.truncate(cp.2);
    }

    fn undo(&mut self, base: &State) {
        for &s in &self.log_s {
            self.in_s[s as usize] = base.in_s[s as usize];
        }
        for &c in &self.log_c {
            self.remaining[c as usize] = base.remaining[c as usize];
        }
        for &m in &self.log_m {
            self.in_mod[m as usize] = base.in_mod[m as usize];
        }
        self.logging = false;
    }

    fn add(&mut self, s: u32, queue: &mut Vec<u32>) {
        if !self.in_s[s as usize] {
            self.in_s[s as usize] = true;
            if self.logging {
                self.log_s.push(s);
            }
            queue.push(s);
        }
    }

    fn fire(&mut self, ix: &LocalityIndex, ax: u32, queue: &mut Vec<u32>) {
        if self.in_mod[ax as usize] {
            return;
        }
        self.in_mod[ax as usize] = true;
        if self.logging {
            self.log_m.push(ax);
        }
        for &t in ix.sig_of(ax) {
            self.add(t, queue);
        }
    }

    fn run(&mut self, ix: &LocalityIndex, queue: &mut Vec<u32>, disabled: &[bool],
           stop: &mut dyn FnMut(Event) -> bool) -> bool {
        self.run_logged(ix, queue, disabled, stop)
    }

    /// Propagate; `stop` may end the run early (returns true).
    fn run_logged(&mut self, ix: &LocalityIndex, queue: &mut Vec<u32>, disabled: &[bool],
                  stop: &mut dyn FnMut(Event) -> bool) -> bool {
        while let Some(s) = queue.pop() {
            if stop(Event::Symbol(s)) {
                queue.clear();
                return true;
            }
            let (lo, hi) = (ix.occ_off[s as usize] as usize, ix.occ_off[s as usize + 1] as usize);
            for k in lo..hi {
                let c = ix.occ[k] as usize;
                if self.logging {
                    self.log_c.push(c as u32);
                }
                self.remaining[c] -= 1;
                if self.remaining[c] == 0 {
                    let ax = ix.conj_axiom[c];
                    if !self.in_mod[ax as usize] && !disabled[ax as usize] {
                        if stop(Event::Axiom(ax)) {
                            queue.clear();
                            return true;
                        }
                        self.fire(ix, ax, queue);
                    }
                }
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn index(src: &str) -> (Scan, LocalityIndex) {
        let scan = scan(src).unwrap();
        let ix = LocalityIndex::build(src, &scan, false).unwrap();
        (scan, ix)
    }

    const SRC: &str = "Prefix(:=<http://e/>)\nOntology(<http://e/o>\nDeclaration(Class(:A))\n\
        SubClassOf(:A :B)\nSubClassOf(:B ObjectSomeValuesFrom(:r :C))\n\
        EquivalentClasses(:D ObjectIntersectionOf(:B :E))\nSubClassOf(:F :G)\n\
        AnnotationAssertion(rdfs:label :A \"a (b)\")\n)\n";

    #[test]
    fn scan_splits_statements_and_header() {
        let s = scan(SRC).unwrap();
        assert_eq!(s.statements.len(), 6);
        assert_eq!(s.statements[0].kind, StmtKind::Declaration);
        assert_eq!(s.statements[5].kind, StmtKind::Annotation);
        assert!(SRC[..s.open_end].ends_with("<http://e/o>"));
    }

    #[test]
    fn modules_follow_bottom_locality() {
        let (_, ix) = index(SRC);
        let a = ix.symbol("http://e/A").unwrap();
        let none = vec![false; ix.axiom_count()];
        let (m, sig) = ix.module(&[a], &none);
        // A ⊑ B, B ⊑ ∃r.C; the definition of D needs E, F ⊑ G is unrelated.
        assert_eq!(m.len(), 2);
        assert!(!sig[ix.symbol("http://e/F").unwrap() as usize]);
        let mut marked = vec![false; ix.axiom_count()];
        marked[3] = true; // F ⊑ G
        let affected = ix.affected_classes(&marked).unwrap();
        let names: Vec<_> = affected.iter().map(|&s| &*ix.symbols[s as usize]).collect();
        assert_eq!(names, vec!["http://e/F"]);
        let mut marked = vec![false; ix.axiom_count()];
        marked[1] = true; // B ⊑ ∃r.C affects A and B (and D, whose module has B ⊓ E... no)
        let mut names: Vec<_> = ix.affected_classes(&marked).unwrap().iter()
            .map(|&s| ix.symbols[s as usize].to_string()).collect();
        names.sort();
        assert_eq!(names, vec!["http://e/A", "http://e/B", "http://e/D"]);
    }
    /// The depth-first affected set equals the naive per-class modules.
    fn naive_affected(ix: &LocalityIndex, marked: &[bool]) -> Option<Vec<u32>> {
        let none = vec![false; ix.axiom_count()];
        let (base, _) = ix.module(&[], &none);
        if base.iter().any(|&a| marked[a as usize]) {
            return None;
        }
        let mut out = Vec::new();
        for s in 0..ix.symbols.len() as u32 {
            if !ix.is_class[s as usize] {
                continue;
            }
            let (m, _) = ix.module(&[s], &none);
            if m.iter().any(|&a| marked[a as usize]) {
                out.push(s);
            }
        }
        Some(out)
    }

    #[test]
    fn depth_first_affected_matches_per_class_modules() {
        let src = "Prefix(:=<http://e/>)\nOntology(<http://e/o>\n\
            SubClassOf(:A :B)\nSubClassOf(:B :C)\nSubClassOf(:C :A)\n\
            EquivalentClasses(:D ObjectIntersectionOf(:B ObjectSomeValuesFrom(:r :E)))\n\
            SubClassOf(:E ObjectSomeValuesFrom(:s :F))\nSubClassOf(:F :G)\n\
            SubClassOf(ObjectIntersectionOf(:G :H) :K)\nSubClassOf(:L :H)\nSubClassOf(:L :G)\n\
            SubObjectPropertyOf(:s :r)\nTransitiveObjectProperty(:r)\n\
            ObjectPropertyDomain(:t :M)\nSubClassOf(:N ObjectAllValuesFrom(:t :P))\n\
            SubClassOf(:Q ObjectMinCardinality(2 :t :N))\nDisjointClasses(:P :Q :R)\n\
            SubClassOf(:S ObjectComplementOf(:T))\nSubClassOf(ObjectUnionOf(:U :V) :W)\n)\n";
        let (_, ix) = index(src);
        for a in 0..ix.axiom_count() {
            let mut marked = vec![false; ix.axiom_count()];
            marked[a] = true;
            let mut fast = ix.affected_classes(&marked);
            let mut slow = naive_affected(&ix, &marked);
            if let Some(v) = fast.as_mut() { v.sort(); }
            if let Some(v) = slow.as_mut() { v.sort(); }
            assert_eq!(fast, slow, "axiom {a}");
        }
    }

    #[test]
    fn told_proofs_follow_inclusions_conjunctions_and_definitions() {
        let src = "Prefix(:=<http://e/>)\nOntology(<http://e/o>\n\
            SubClassOf(:A :B)\nSubClassOf(:B ObjectIntersectionOf(:C :D))\n\
            EquivalentClasses(:E ObjectIntersectionOf(:C ObjectUnionOf(:A :F)))\n\
            EquivalentClasses(:G ObjectSomeValuesFrom(:r :A))\nSubClassOf(:H ObjectSomeValuesFrom(:r :A))\n)\n";
        let s = scan(src).unwrap();
        let t = ToldProofs::build(src, &s);
        let none = crate::fxhash::FxHashSet::default();
        assert!(t.proves_all(":A", &[":B", ":C", ":D", ":E"], &none));
        assert!(t.proves_all("http://e/A", &[":E"], &none));
        // Existential definitions are not told: H ⊑ G needs a reasoner.
        assert!(!t.proves_all(":H", &[":G"], &none));
        assert!(!t.proves_all(":C", &[":E"], &none));
        // Masking the deleted `A ⊑ B` removes every proof through it.
        let ab = s.statements.iter().find(|st| &src[st.start..st.end] == "SubClassOf(:A :B)").unwrap().hash;
        let removed: crate::fxhash::FxHashSet<u128> = [ab].into_iter().collect();
        assert!(!t.proves_all(":A", &[":B"], &removed));
        assert!(!t.proves_all(":A", &[":E"], &removed));
    }

    #[test]
    fn typed_data_has_value_keeps_tbox_mode() {
        let src = "Prefix(:=<http://e/>)\nPrefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nOntology(<http://e/o>\n\
            SubClassOf(:A DataHasValue(:p \"1.0\"^^xsd:float))\nSubClassOf(:B :A)\nClassAssertion(:B :a)\n)\n";
        let s = scan(src).unwrap();
        let ix = LocalityIndex::build(src, &s, true).unwrap();
        assert!(ix.tbox_mode);
        assert_eq!(ix.axiom_count(), 2);
    }

    #[test]
    fn tbox_mode_requires_universal_role_free_axioms() {
        let plain = "Prefix(:=<http://e/>)\nOntology(<http://e/o>\nSubClassOf(:A :B)\n\
            ClassAssertion(:A :a)\nObjectPropertyAssertion(:r :a :b)\n)\n";
        let s = scan(plain).unwrap();
        let ix = LocalityIndex::build(plain, &s, true).unwrap();
        assert!(ix.tbox_mode);
        assert_eq!(ix.axiom_count(), 1);
        assert_eq!(ix.assertions.len(), 2);
        let nominal = "Prefix(:=<http://e/>)\nOntology(<http://e/o>\nSubClassOf(:A ObjectHasValue(:r :a))\n\
            ClassAssertion(:A :a)\n)\n";
        let s = scan(nominal).unwrap();
        let ix = LocalityIndex::build(nominal, &s, true).unwrap();
        assert!(ix.tbox_mode);
        assert_eq!(ix.axiom_count(), 1);
        assert_eq!(ix.nominal, vec![true]);
        let universal = "Prefix(:=<http://e/>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\
            Ontology(<http://e/o>\nSubClassOf(:A :B)\n\
            ClassAssertion(ObjectAllValuesFrom(owl:topObjectProperty :B) :a)\n)\n";
        let s = scan(universal).unwrap();
        assert!(!LocalityIndex::build(universal, &s, true).unwrap().tbox_mode);
    }
}

/// Syntactic subsumption proofs between named classes in one revision
/// (`IncrementalModuleReuse.Told`): told inclusions `A ⊑ B`, `A ⊑ B₁ ⊓ … ⊓ Bₙ`,
/// equivalences, and the backward direction of definitions `X ≡ D` whose `D`
/// is built from names with `⊓`/`⊔` (`D` is closed structurally: a name in
/// the set, every conjunct, some disjunct). Every rule is a sound inference,
/// so a proved inclusion is entailed by the revision.
///
/// Classes are keyed by their resolved IRI; `spelling` maps the published
/// spelling (as in the taxonomy) to it.
pub struct ToldProofs {
    ids: FxHashMap<String, u32>,
    spelling: FxHashMap<String, u32>,
    /// Edges with the fingerprint of the statement that justifies them.
    edges: Vec<Vec<(u32, u128)>>,
    /// `(X, D, statement)` for every definition with a name-only Boolean body.
    definitions: Vec<(u32, Told, u128)>,
    thing: u32,
}

#[derive(Clone)]
enum Told {
    Name(u32),
    And(Vec<Told>),
    Or(Vec<Told>),
}

impl ToldProofs {
    pub fn build(text: &str, scan: &Scan) -> Self {
        let bld = Builder {
            prefixes: &scan.prefixes,
            symbols: Vec::new(),
            sym_ids: FxHashMap::default(),
            is_class: Vec::new(),
            names: Vec::new(),
            spelling_conflict: false,
            individual_free: true,
            el_like: true,
            nominal_bot: false,
            cur_nominal: false,
        };
        let mut t = ToldProofs {
            ids: FxHashMap::default(),
            spelling: FxHashMap::default(),
            edges: Vec::new(),
            definitions: Vec::new(),
            thing: 0,
        };
        t.thing = t.id(&format!("{OWL}Thing"), None);
        for st in &scan.statements {
            if st.kind != StmtKind::Logical {
                continue;
            }
            let slice = &text[st.start..st.end];
            if !(slice.starts_with("SubClassOf") || slice.starts_with("EquivalentClasses")) {
                continue;
            }
            let tag = st.hash;
            let Ok(node) = Parser::new(slice).parse() else { continue };
            let Node::List(head, args) = &node else { continue };
            let args: Vec<&Node<'_>> = args.iter().filter(|n| n.head() != Some("Annotation")).collect();
            match (*head, args.len()) {
                ("SubClassOf", 2) => {
                    let Some(a) = t.name(&bld, args[0]) else { continue };
                    for b in t.conjuncts(&bld, args[1]) {
                        t.edge(a, b, tag);
                    }
                }
                ("EquivalentClasses", n) if n >= 2 => {
                    let names: Vec<Option<u32>> = args.iter().map(|x| t.name(&bld, x)).collect();
                    for (i, a) in names.iter().enumerate() {
                        let Some(a) = *a else { continue };
                        for (j, x) in args.iter().enumerate() {
                            if i == j {
                                continue;
                            }
                            // Forward: a ⊑ x, through x's conjuncts.
                            for b in t.conjuncts(&bld, x) {
                                t.edge(a, b, tag);
                            }
                            // Backward: x ⊑ a, a definition when x is a Boolean
                            // combination of names (a plain name is an edge).
                            match names[j] {
                                Some(b) => t.edge(b, a, tag),
                                None => {
                                    if let Some(d) = t.boolean(&bld, x) {
                                        t.definitions.push((a, d, tag));
                                    }
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        t
    }

    fn id(&mut self, iri: &str, spelling: Option<&str>) -> u32 {
        let id = match self.ids.get(iri) {
            Some(&id) => id,
            None => {
                let id = self.edges.len() as u32;
                self.ids.insert(iri.to_string(), id);
                self.edges.push(Vec::new());
                id
            }
        };
        if let Some(sp) = spelling {
            self.spelling.entry(sp.to_string()).or_insert(id);
        }
        id
    }

    fn edge(&mut self, a: u32, b: u32, tag: u128) {
        if a != b {
            self.edges[a as usize].push((b, tag));
        }
    }

    fn name(&mut self, bld: &Builder<'_>, node: &Node<'_>) -> Option<u32> {
        let tok = node.as_atom()?;
        let iri = bld.resolve(tok)?;
        let spelling = tok.strip_prefix('<').and_then(|x| x.strip_suffix('>')).unwrap_or(tok);
        Some(self.id(&iri, Some(spelling)))
    }

    /// Named conjuncts of a superclass expression (`B` or `B₁ ⊓ … ⊓ Bₙ`,
    /// nested); other parts prove nothing and are skipped.
    fn conjuncts(&mut self, bld: &Builder<'_>, node: &Node<'_>) -> Vec<u32> {
        match node {
            Node::Atom(_) => self.name(bld, node).into_iter().collect(),
            Node::List("ObjectIntersectionOf", args) => {
                args.iter().flat_map(|a| self.conjuncts(bld, a)).collect()
            }
            _ => Vec::new(),
        }
    }

    fn boolean(&mut self, bld: &Builder<'_>, node: &Node<'_>) -> Option<Told> {
        match node {
            Node::Atom(_) => self.name(bld, node).map(Told::Name),
            Node::List("ObjectIntersectionOf", args) if !args.is_empty() => {
                args.iter().map(|a| self.boolean(bld, a)).collect::<Option<Vec<_>>>().map(Told::And)
            }
            Node::List("ObjectUnionOf", args) if !args.is_empty() => {
                args.iter().map(|a| self.boolean(bld, a)).collect::<Option<Vec<_>>>().map(Told::Or)
            }
            _ => None,
        }
    }

    fn holds(d: &Told, set: &[bool]) -> bool {
        match d {
            Told::Name(n) => set[*n as usize],
            Told::And(v) => v.iter().all(|x| Self::holds(x, set)),
            Told::Or(v) => v.iter().any(|x| Self::holds(x, set)),
        }
    }

    /// Whether every class in `supers` (published spellings) is proved a
    /// superclass of `subject` without the statements in `removed` (the
    /// proofs were built on a base revision; a deletion masks its statements).
    /// Unknown names fail.
    pub fn proves_all(&self, subject: &str, supers: &[&str], removed: &crate::fxhash::FxHashSet<u128>) -> bool {
        let look = |name: &str| self.spelling.get(name).or_else(|| self.ids.get(name)).copied();
        let Some(a) = look(subject) else { return supers.is_empty() };
        let mut wanted = Vec::with_capacity(supers.len());
        for s in supers {
            match look(s) {
                Some(b) => wanted.push(b),
                None => return false,
            }
        }
        let n = self.edges.len();
        let mut set = vec![false; n];
        let mut stack = vec![a];
        set[a as usize] = true;
        set[self.thing as usize] = true;
        loop {
            while let Some(x) = stack.pop() {
                for &(y, tag) in &self.edges[x as usize] {
                    if !set[y as usize] && !removed.contains(&tag) {
                        set[y as usize] = true;
                        stack.push(y);
                    }
                }
            }
            if wanted.iter().all(|&b| set[b as usize]) {
                return true;
            }
            let mut grew = false;
            for (x, d, tag) in &self.definitions {
                if !set[*x as usize] && !removed.contains(tag) && Self::holds(d, &set) {
                    set[*x as usize] = true;
                    stack.push(*x);
                    grew = true;
                }
            }
            if !grew {
                return false;
            }
        }
    }
}

/// Diagnostic: `km locality-probe OLD NEW` reuse statistics for a deletion.
pub fn probe(old: &str, new: &str) -> Result<String, String> {
    let t0 = std::time::Instant::now();
    let so = scan(old)?;
    let sn = scan(new)?;
    let t_scan = t0.elapsed().as_secs_f64();
    let t1 = std::time::Instant::now();
    let ix = LocalityIndex::build(old, &so, true)?;
    let t_index = t1.elapsed().as_secs_f64();
    let kept: std::collections::HashSet<u128> = sn.statements.iter().map(|s| s.hash).collect();
    let mut marked = vec![false; ix.axiom_count()];
    let mut removed = 0;
    for (a, h) in ix.axiom_hash.iter().enumerate() {
        if !kept.contains(h) {
            marked[a] = true;
            removed += 1;
        }
    }
    let t2 = std::time::Instant::now();
    if std::env::var_os("KM_LOCALITY_DEBUG").is_some() {
        let none = vec![false; ix.axiom_count()];
        let (base, sig) = ix.module(&[], &none);
        let names: Vec<&str> = (0..sig.len()).filter(|&i| sig[i]).map(|i| &*ix.names[i]).collect();
        eprintln!("empty module: {} axioms, {} nominal, {} marked; signature {:?}", base.len(),
            base.iter().filter(|&&a| ix.nominal[a as usize]).count(),
            base.iter().filter(|&&a| marked[a as usize]).count(), &names[..names.len().min(40)]);
    }
    let affected = ix.affected_classes_tbox(&marked);
    let t_aff = t2.elapsed().as_secs_f64();
    let classes = ix.is_class.iter().filter(|c| **c).count();
    let t3 = std::time::Instant::now();
    let (u_axioms, _) = match &affected {
        Some(a) => ix.module(a, &marked),
        None => (Vec::new(), Vec::new()),
    };
    let t_mod = t3.elapsed().as_secs_f64();
    if std::env::var_os("KM_LOCALITY_DEBUG").is_some() {
        if let Some(a) = &affected {
            let mut sizes: Vec<(usize, u32)> = a.iter().map(|&s| (ix.module(&[s], &marked).0.len(), s)).collect();
            sizes.sort();
            for (n, s) in sizes.iter().rev().take(10) {
                eprintln!("affected {} module={n}", ix.names[*s as usize]);
            }
            let q = |f: f64| sizes.get(((sizes.len() as f64 - 1.0) * f) as usize).map(|x| x.0).unwrap_or(0);
            eprintln!("module sizes: n={} min={} median={} p90={} max={}", sizes.len(), q(0.0), q(0.5), q(0.9), q(1.0));
        }
    }
    Ok(serde_json::json!({
        "statements": so.statements.len(), "axioms": ix.axiom_count(), "symbols": ix.symbols.len(),
        "classes": classes, "removed": removed, "tbox_mode": ix.tbox_mode,
        "nominal_axioms": ix.nominal.iter().filter(|n| **n).count(),
        "affected": affected.as_ref().map(|a| a.len() as i64).unwrap_or(-1),
        "module_axioms": u_axioms.len(),
        "scan_s": t_scan, "index_s": t_index, "affected_s": t_aff, "module_s": t_mod,
    }).to_string())
}
