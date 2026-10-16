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
    let tok = |s: usize, e: usize| text.get(s..e).ok_or("token crosses a UTF-8 boundary");
    // Header: Prefix(...) declarations, then `Ontology(`.
    loop {
        let (s, e) = lex(b, i).ok_or("functional syntax without Ontology(")?;
        match tok(s, e)? {
            "Prefix" => {
                let (ps, pe) = lex(b, e).ok_or("truncated Prefix")?;
                if tok(ps, pe)? != "(" {
                    return Err("malformed Prefix".into());
                }
                let mut j = pe;
                let mut joined = String::new();
                loop {
                    let (s2, e2) = lex(b, j).ok_or("truncated Prefix")?;
                    j = e2;
                    if tok(s2, e2)? == ")" {
                        break;
                    }
                    joined.push_str(tok(s2, e2)?);
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
                if tok(ps, pe)? != "(" {
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
        let t = tok(s, e)?;
        if t == ")" || t == "(" {
            break;
        }
        match lex(b, e) {
            Some((s2, e2)) if tok(s2, e2)? == "(" => break,
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
        let t = tok(s, e)?;
        if t == ")" {
            closed = true;
            i = e;
            break;
        }
        let (ps, pe) = lex(b, e).ok_or("truncated statement")?;
        if tok(ps, pe)? != "(" {
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

/// Compiler work separated from whole-index assembly.
#[derive(Clone, Debug, Default)]
pub struct CompileReuse {
    pub reused_compiled_axioms: usize,
    pub compiled_axioms: usize,
    pub csr_axiom_records: usize,
    pub csr_conjunctions: usize,
    pub csr_literal_records: usize,
}

/// Compiled locality index of one revision.
pub struct LocalityIndex {
    /// Actual compiler provenance, independent of TBox admissibility.
    pub full_mode: bool,
    /// Complete, resolved source is in the positive object fragment audited by
    /// `positive_tbox_named_query`. Requires prior complete source validation;
    /// never true for a TBox build that skips assertions. No publication alone.
    pub positive_object_source: bool,
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
    /// Per-axiom class-kind contributions; aggregate is_class is not reusable.
    class_off: Vec<u32>,
    class_lits: Vec<u32>,
    /// Bit0 individual-free, bit1 non-EL, bit2 positive object axiom.
    compile_flags: Vec<u8>,
    /// All source IRI occurrences: compiler/public-name/declaration provenance.
    sig_off: Vec<u32>,
    sig: Vec<u32>,
    /// Masked class/role occurrences only; individuals do not seed locality.
    local_sig_off: Vec<u32>,
    local_sig: Vec<u32>,
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
    /// Exact Class-kind declarations, separate from punned entity identity.
    class_declarations: FxHashMap<u128, u32>,
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
    cur_classes: Vec<u32>,
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

    // Pure admission: never intern symbols or alter producer/locality ordering.
    fn positive_object_role(&self, node: &Node<'_>) -> bool {
        match node {
            Node::Atom(t) => self.resolve(t).is_some_and(|iri| !matches!(
                iri.strip_prefix(OWL), Some("topObjectProperty" | "bottomObjectProperty"
                    | "topDataProperty" | "bottomDataProperty"))),
            Node::List("ObjectInverseOf", a) if a.len() == 1 && a[0].as_atom().is_some() =>
                self.positive_object_role(&a[0]),
            _ => false,
        }
    }

    fn positive_object_class(&self, node: &Node<'_>) -> bool {
        match node {
            Node::Atom(t) => self.resolve(t).is_some_and(|iri| iri != "http://www.w3.org/2002/07/owl#Nothing"),
            Node::List("ObjectIntersectionOf" | "ObjectUnionOf", a) if a.len() >= 2 =>
                a.iter().all(|n| self.positive_object_class(n)),
            Node::List("ObjectSomeValuesFrom" | "ObjectAllValuesFrom", a) if a.len() == 2 =>
                self.positive_object_role(&a[0]) && self.positive_object_class(&a[1]),
            Node::List("ObjectHasSelf", a) if a.len() == 1 => self.positive_object_role(&a[0]),
            _ => false,
        }
    }

    fn positive_individual(&self, node: &Node<'_>) -> bool {
        node.as_atom().is_some_and(|t| self.resolve(t).is_some()
            || t.strip_prefix("_:").is_some_and(|label| !label.is_empty()))
    }

    fn positive_object_axiom(&self, head: &str, a: &[&Node<'_>]) -> bool {
        let roles = || a.iter().all(|n| self.positive_object_role(n));
        match head {
            "SubClassOf" if a.len() == 2 => a.iter().all(|n| self.positive_object_class(n)),
            "EquivalentClasses" if a.len() >= 2 => a.iter().all(|n| self.positive_object_class(n)),
            "SubObjectPropertyOf" if a.len() == 2 => {
                let left = match a[0] {
                    Node::List("ObjectPropertyChain", rs) if rs.len() >= 2 =>
                        rs.iter().all(|r| self.positive_object_role(r)),
                    r => self.positive_object_role(r),
                };
                left && self.positive_object_role(a[1])
            }
            "EquivalentObjectProperties" if a.len() >= 2 => roles(),
            "InverseObjectProperties" if a.len() == 2 => roles(),
            "ObjectPropertyDomain" | "ObjectPropertyRange" if a.len() == 2 =>
                self.positive_object_role(a[0]) && self.positive_object_class(a[1]),
            "TransitiveObjectProperty" | "FunctionalObjectProperty" |
            "InverseFunctionalObjectProperty" | "SymmetricObjectProperty" |
            "ReflexiveObjectProperty" if a.len() == 1 => roles(),
            "ClassAssertion" if a.len() == 2 =>
                self.positive_object_class(a[0]) && self.positive_individual(a[1]),
            "ObjectPropertyAssertion" if a.len() == 3 => self.positive_object_role(a[0])
                && a[1..].iter().all(|n| self.positive_individual(n)),
            "SameIndividual" if a.len() >= 2 => a.iter().all(|n| self.positive_individual(n)),
            _ => false,
        }
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

    fn replay_symbol(&mut self, old: &LocalityIndex, symbol: u32, remap: &mut [u32]) -> u32 {
        let slot = &mut remap[symbol as usize];
        if *slot == u32::MAX {
            *slot = self.intern(&old.symbols[symbol as usize], &old.names[symbol as usize]);
        }
        *slot
    }

    /// Conservative lexical candidates for the resolved universal role.
    /// Resolution searches the last binding, so confirm each candidate using
    /// the same resolver as compilation (including prefix rebindings).
    fn universal_role_aliases(&self) -> Vec<String> {
        let top = format!("{OWL}topObjectProperty");
        let mut aliases = Vec::new();
        for (prefix, base) in self.prefixes {
            if let Some(local) = top.strip_prefix(base) {
                let alias = format!("{prefix}{local}");
                // The existing standard substring already covers these.
                if !alias.contains("topObjectProperty")
                    && self.resolve(&alias).as_deref() == Some(top.as_str())
                {
                    aliases.push(alias);
                }
            }
        }
        aliases.sort_unstable();
        aliases.dedup();
        aliases
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

    fn individual(&self, node: &Node<'_>) -> bool {
        node.as_atom().is_some_and(|n| n.starts_with("_:") || self.resolve(n).is_some())
    }

    fn collect_local_role(&mut self, node: &Node<'_>, out: &mut Vec<u32>) -> bool {
        match node {
            Node::Atom(t) if self.resolve(t).is_some() => { self.collect(node, out); true }
            Node::List("ObjectInverseOf", a) if a.len() == 1 =>
                matches!(a[0], Node::Atom(_)) && self.collect_local_role(&a[0], out),
            _ => false,
        }
    }

    /// Returns false for an unknown/malformed shape: the WHOLE axiom then
    /// retains its original occurrence signature. Individual interpretation is
    /// unchanged by mask; a punned IRI still counts in every class/role slot.
    fn collect_local_class(&mut self, node: &Node<'_>, out: &mut Vec<u32>) -> bool {
        match node {
            Node::Atom(t) if self.resolve(t).is_some() => { self.collect(node, out); true }
            Node::List("ObjectOneOf", a) if !a.is_empty() => a.iter().all(|n| self.individual(n)),
            Node::List("ObjectHasValue", a) if a.len() == 2 =>
                self.individual(&a[1]) && self.collect_local_role(&a[0], out),
            Node::List("ObjectHasSelf", a) if a.len() == 1 => self.collect_local_role(&a[0], out),
            Node::List("ObjectIntersectionOf" | "ObjectUnionOf", a) if !a.is_empty() =>
                a.iter().all(|n| self.collect_local_class(n, out)),
            Node::List("ObjectComplementOf", a) if a.len() == 1 => self.collect_local_class(&a[0], out),
            Node::List("ObjectSomeValuesFrom" | "ObjectAllValuesFrom", a) if a.len() == 2 =>
                self.collect_local_role(&a[0], out) && self.collect_local_class(&a[1], out),
            Node::List("ObjectMinCardinality" | "ObjectMaxCardinality" | "ObjectExactCardinality", a)
                if a.len() == 2 || a.len() == 3 =>
                a[0].as_atom().is_some_and(|n| n.parse::<u64>().is_ok())
                    && self.collect_local_role(&a[1], out)
                    && (a.len() == 2 || self.collect_local_class(&a[2], out)),
            // Data class constructors, including DataHasValue, retain the
            // complete original axiom signature through the fallback.
            _ => false,
        }
    }

    fn collect_local_axiom(&mut self, head: &str, a: &[&Node<'_>], out: &mut Vec<u32>) -> bool {
        match (head, a.len()) {
            ("SubClassOf", 2) => a.iter().all(|n| self.collect_local_class(n, out)),
            ("EquivalentClasses" | "DisjointClasses" | "DisjointUnion", n) if n > 0 =>
                a.iter().all(|n| self.collect_local_class(n, out)),
            ("ObjectPropertyDomain" | "ObjectPropertyRange", 2) =>
                self.collect_local_role(a[0], out) && self.collect_local_class(a[1], out),
            ("ClassAssertion", 2) => self.individual(a[1]) && self.collect_local_class(a[0], out),
            ("ObjectPropertyAssertion" | "NegativeObjectPropertyAssertion", 3) =>
                self.individual(a[1]) && self.individual(a[2]) && self.collect_local_role(a[0], out),
            ("DataPropertyAssertion" | "NegativeDataPropertyAssertion", n)
                if (n == 3 || n == 4 && a[3].as_atom().is_some_and(|s| s.starts_with("^^") || s.starts_with('@')))
                    && a[2].as_atom().is_some_and(|s| s.starts_with('"') && s.ends_with('"')) =>
                self.individual(a[1]) && matches!(a[0], Node::Atom(_)) && self.collect_local_role(a[0], out),
            ("SameIndividual" | "DifferentIndividuals", n) if n >= 2 =>
                a.iter().all(|n| self.individual(n)),
            _ => false,
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
                    self.cur_classes.push(id);
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
    /// Class-kind contributions from exactly the retained source statements.
    /// Caller proves exact statement containment/identity before selecting this
    /// view. Unlike aggregate `is_class`, it cannot retain an obsolete Class
    /// kind merely because a same-IRI property or individual still exists.
    /// No locality rule or compiled formula changes; this is a source view.
    /// Returns None for TBox compiler provenance: skipped assertions/rules
    /// cannot supply a complete source class-domain view.
    pub fn live_class_names(&self, present: impl Fn(u128) -> bool) -> Option<Vec<&str>> {
        if !self.full_mode { return None; }
        let mut classes = vec![false; self.names.len()];
        for (id, hash) in self.axiom_hash.iter().enumerate() {
            if present(*hash) {
                for &symbol in &self.class_lits[self.class_off[id] as usize..self.class_off[id + 1] as usize] {
                    classes[symbol as usize] = true;
                }
            }
        }
        for (&hash, &symbol) in &self.class_declarations {
            if present(hash) { classes[symbol as usize] = true; }
        }
        Some(self.names.iter().zip(classes).filter_map(|(name, class)| class.then_some(name.as_ref())).collect())
    }
    /// The session's public class-kind domain over an exact enabled source.
    /// Besides actual Class contributions, preserve present source spellings
    /// of Thing/Nothing even when they occur solely as individuals/properties.
    /// The caller still adds its four unconditional standard builtin names.
    pub fn live_public_class_names(&self, present: impl Fn(u128) -> bool) -> Option<Vec<&str>> {
        if !self.full_mode { return None; }
        let builtin: Vec<bool> = self.symbols.iter().map(|symbol| matches!(symbol.as_ref(),
            "http://www.w3.org/2002/07/owl#Thing" | "http://www.w3.org/2002/07/owl#Nothing")).collect();
        let has_builtin = builtin.iter().any(|present| *present);
        let mut classes = vec![false; self.names.len()];
        for (id, hash) in self.axiom_hash.iter().enumerate() {
            if !present(*hash) { continue; }
            for &symbol in &self.class_lits[self.class_off[id] as usize..self.class_off[id + 1] as usize] {
                classes[symbol as usize] = true;
            }
            // Ordinary indices without either builtin avoid this signature walk.
            if has_builtin {
                for &symbol in self.sig_of(id as u32) {
                    if builtin[symbol as usize] { classes[symbol as usize] = true; }
                }
            }
        }
        for (&hash, &symbol) in &self.class_declarations {
            if present(hash) { classes[symbol as usize] = true; }
        }
        if has_builtin {
            for (&hash, &symbol) in &self.decl_entity {
                if builtin[symbol as usize] && present(hash) { classes[symbol as usize] = true; }
            }
        }
        Some(self.names.iter().zip(classes).filter_map(|(name, class)| class.then_some(name.as_ref())).collect())
    }

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

    pub fn build_reusing_full<'a>(
        text: &str, scan: &Scan, old: &LocalityIndex, old_header: &str,
        old_statement: impl Fn(u128) -> Option<&'a str>,
    ) -> Result<(Self, CompileReuse), String> {
        let lookup: &dyn Fn(u128) -> Option<&'a str> = &old_statement;
        let donor = (old.full_mode && !old.spelling_conflict
            && text[..scan.open_end] == *old_header).then_some((old, lookup));
        Self::build_mode_reusing(text, scan, false, donor)
    }

    fn build_mode(text: &str, scan: &Scan, tbox: bool) -> Result<Self, String> {
        Self::build_mode_reusing(text, scan, tbox, None).map(|(index, _)| index)
    }

    fn build_mode_reusing<'a>(text: &str, scan: &Scan, tbox: bool,
        donor: Option<(&LocalityIndex, &dyn Fn(u128) -> Option<&'a str>)>)
        -> Result<(Self, CompileReuse), String>
    {
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
            cur_classes: Vec::new(),
        };
        // Header-sized work only; never parse every skipped ABox assertion.
        let universal_role_aliases = if tbox { bld.universal_role_aliases() } else { Vec::new() };
        let mut stats = CompileReuse::default();
        let mut donor_remap = donor.map(|(old, _)| vec![u32::MAX; old.symbols.len()]);
        let mut all_individual_free = true;
        let mut all_positive_object = !tbox;
        let (mut class_off, mut class_lits) = (vec![0u32], Vec::new());
        let mut compile_flags = Vec::new();
        let mut assertions = crate::fxhash::FxHashSet::default();
        let mut non_el = 0usize;
        let mut axiom_hash = Vec::new();
        let mut axiom_always = Vec::new();
        let mut nominal: Vec<bool> = Vec::new();
        let (mut sig_off, mut sig) = (vec![0u32], Vec::new());
        let (mut local_sig_off, mut local_sig) = (vec![0u32], Vec::new());
        let (mut conj_off, mut conj_lits, mut conj_axiom) = (vec![0u32], Vec::new(), Vec::new());
        let mut axiom_by_hash = FxHashMap::default();
        let mut decl_entity = FxHashMap::default();
        let mut class_declarations = FxHashMap::default();
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
                                            class_declarations.insert(st.hash, id);
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
                    if slice.contains("topObjectProperty")
                        || universal_role_aliases.iter().any(|alias| slice.contains(alias))
                    {
                        all_individual_free = false;
                    }
                    assertions.insert(st.hash);
                    continue;
                }
                StmtKind::Assertion | StmtKind::Logical => {}
            }
            if axiom_by_hash.contains_key(&st.hash) {
                continue; // duplicate statement: one axiom
            }
            let id = axiom_hash.len() as u32;
            axiom_by_hash.insert(st.hash, id);
            axiom_hash.push(st.hash);
            bld.el_like = true;
            bld.cur_nominal = false;
            bld.individual_free = true;
            bld.cur_classes.clear();
            let previous = donor.and_then(|(old, lookup)| {
                let &old_id = old.axiom_by_hash.get(&st.hash)?;
                (lookup(st.hash) == Some(slice)).then_some((old, old_id as usize))
            });
            let positive_object;
            if let Some((old, old_id)) = previous {
                stats.reused_compiled_axioms += 1;
                let remap = donor_remap.as_mut().expect("accepted donor remap");
                buf.clear();
                for &symbol in old.sig_of(old_id as u32) {
                    buf.push(bld.replay_symbol(old, symbol, remap));
                }
                buf.sort_unstable();
                buf.dedup();
                sig.extend_from_slice(&buf);
                sig_off.push(sig.len() as u32);
                buf.clear();
                for &symbol in old.local_sig_of(old_id as u32) {
                    buf.push(bld.replay_symbol(old, symbol, remap));
                }
                buf.sort_unstable();
                buf.dedup();
                local_sig.extend_from_slice(&buf);
                local_sig_off.push(local_sig.len() as u32);
                for &symbol in &old.class_lits[old.class_off[old_id] as usize..old.class_off[old_id + 1] as usize] {
                    let symbol = bld.replay_symbol(old, symbol, remap);
                    bld.is_class[symbol as usize] = true;
                    bld.cur_classes.push(symbol);
                }
                bld.individual_free = old.compile_flags[old_id] & 1 != 0;
                bld.el_like = old.compile_flags[old_id] & 2 == 0;
                bld.cur_nominal = old.nominal[old_id];
                positive_object = old.compile_flags[old_id] & 4 != 0;
                axiom_always.push(old.axiom_always[old_id]);
                // Owners are monotone in axiom build order. Avoid an O(A*C)
                // scan of all conjunctions for every copied axiom.
                let first = old.conj_axiom.partition_point(|&owner| owner < old_id as u32);
                let last = old.conj_axiom.partition_point(|&owner| owner <= old_id as u32);
                for c in first..last {
                    buf.clear();
                    for &symbol in &old.conj_lits[old.conj_off[c] as usize..old.conj_off[c + 1] as usize] {
                        buf.push(bld.replay_symbol(old, symbol, remap));
                    }
                    buf.sort_unstable();
                    buf.dedup();
                    conj_lits.extend_from_slice(&buf);
                    conj_off.push(conj_lits.len() as u32);
                    conj_axiom.push(id);
                }
            } else {
                stats.compiled_axioms += 1;
                let node = Parser::new(slice).parse()?;
                let (head, args) = match &node {
                    Node::List(h, a) => (*h, a.iter().filter(|n| n.head() != Some("Annotation")).collect::<Vec<_>>()),
                    Node::Atom(_) => return Err("malformed statement".into()),
                };
                positive_object = !tbox && bld.positive_object_axiom(head, &args);
                let f = bld.axiom(head, &args);
                buf.clear();
                for a in &args { bld.collect(a, &mut buf); }
                buf.sort_unstable();
                buf.dedup();
                sig.extend_from_slice(&buf);
                sig_off.push(sig.len() as u32);
                buf.clear();
                if !bld.collect_local_axiom(head, &args, &mut buf) {
                    buf.clear();
                    buf.extend_from_slice(&sig[sig_off[id as usize] as usize..]);
                }
                buf.sort_unstable();
                buf.dedup();
                local_sig.extend_from_slice(&buf);
                local_sig_off.push(local_sig.len() as u32);
                match dnf(&f) {
                    None => axiom_always.push(true),
                    Some(conjs) => {
                        let mut always = false;
                        for mut c in conjs {
                            c.sort_unstable();
                            c.dedup();
                            if c.is_empty() { always = true; break; }
                            conj_lits.extend_from_slice(&c);
                            conj_off.push(conj_lits.len() as u32);
                            conj_axiom.push(id);
                        }
                        axiom_always.push(always);
                    }
                }
            }
            nominal.push(bld.cur_nominal);
            if !bld.el_like { non_el += 1; }
            all_individual_free &= bld.individual_free;
            all_positive_object &= positive_object;
            compile_flags.push(u8::from(bld.individual_free) | (u8::from(!bld.el_like) << 1)
                | (u8::from(positive_object) << 2));
            bld.cur_classes.sort_unstable();
            bld.cur_classes.dedup();
            class_lits.extend_from_slice(&bld.cur_classes);
            class_off.push(class_lits.len() as u32);
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
        stats.csr_axiom_records = axiom_hash.len();
        stats.csr_conjunctions = conj_axiom.len();
        stats.csr_literal_records = conj_lits.len();
        Ok((LocalityIndex {
            full_mode: !tbox,
            positive_object_source: all_positive_object,
            tbox_mode: tbox && all_individual_free,
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
            class_off,
            class_lits,
            compile_flags,
            sig_off,
            sig,
            local_sig_off,
            local_sig,
            conj_off,
            conj_lits,
            conj_axiom,
            occ_off,
            occ,
            axiom_by_hash,
            decl_entity,
            class_declarations,
        }, stats))
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

    pub fn assembly_work(&self) -> (usize, usize, usize) {
        (self.axiom_hash.len(), self.conj_axiom.len(), self.conj_lits.len())
    }

    fn sig_of(&self, ax: u32) -> &[u32] {
        &self.sig[self.sig_off[ax as usize] as usize..self.sig_off[ax as usize + 1] as usize]
    }

    fn local_sig_of(&self, ax: u32) -> &[u32] {
        &self.local_sig[self.local_sig_off[ax as usize] as usize..self.local_sig_off[ax as usize + 1] as usize]
    }

    fn need(&self, c: usize) -> u32 {
        self.conj_off[c + 1] - self.conj_off[c]
    }

    /// Module of `seeds` with `disabled` axioms absent. The returned signature
    /// includes ORIGINAL occurrences of selected axioms for declaration
    /// emission, including named individuals. Those extra occurrences are
    /// added only after the logical fixpoint and never seed locality again.
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
        let axioms: Vec<u32> = (0..self.axiom_hash.len() as u32).filter(|&a| st.in_mod[a as usize]).collect();
        for &a in &axioms {
            for &symbol in self.sig_of(a) { st.in_s[symbol as usize] = true; }
        }
        (axioms, st.in_s)
    }

    /// Whether the module of the empty signature contains no `marked` axiom.
    pub fn empty_module_avoids(&self, marked: &[bool]) -> bool {
        let none = vec![false; self.axiom_hash.len()];
        self.empty_module_avoids_with_disabled(marked, &none)
    }

    /// The empty-signature module in a retained index with prior deletions.
    /// `disabled` refers to this index's original axiom ids, not the revision's
    /// compacted positions. Disabled axioms cannot activate or mark a module.
    pub fn empty_module_avoids_with_disabled(&self, marked: &[bool], disabled: &[bool]) -> bool {
        assert_eq!(marked.len(), self.axiom_count());
        assert_eq!(disabled.len(), self.axiom_count());
        let (base, _) = self.module(&[], disabled);
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
        let none = vec![false; self.axiom_hash.len()];
        self.affected_classes_tbox_with_disabled(marked, &none)
    }

    /// As `affected_classes_tbox`, in the theory left after `disabled` axioms
    /// are removed. Nominal axioms count only while they remain enabled.
    pub fn affected_classes_tbox_with_disabled(
        &self, marked: &[bool], disabled: &[bool],
    ) -> Option<Vec<u32>> {
        assert_eq!(marked.len(), self.axiom_count());
        assert_eq!(disabled.len(), self.axiom_count());
        let trig: Vec<bool> = marked.iter().zip(&self.nominal).map(|(m, n)| *m || *n).collect();
        self.affected_classes_with_disabled(&trig, disabled)
    }

    /// Some axiom of `module` mentions a nominal: in TBox mode it is then not
    /// a module of the complete revision (assertions and nominals are left out).
    pub fn module_has_nominal(&self, module: &[u32]) -> bool {
        module.iter().any(|&a| self.nominal[a as usize])
    }

    pub fn affected_classes(&self, marked: &[bool]) -> Option<Vec<u32>> {
        let none = vec![false; self.axiom_hash.len()];
        self.affected_classes_with_disabled(marked, &none)
    }

    /// A masked index denotes exactly its enabled axiom formulas, with the
    /// original symbol/axiom ids retained. Every propagation and the DFS parent
    /// forest must use that same theory; a deleted parent's trigger must never
    /// make its former descendants inherit a module they no longer contain.
    pub fn affected_classes_with_disabled(
        &self, marked: &[bool], disabled: &[bool],
    ) -> Option<Vec<u32>> {
        assert_eq!(marked.len(), self.axiom_count());
        assert_eq!(disabled.len(), self.axiom_count());
        let mut base = State::fresh(self);
        let mut queue = Vec::new();
        for ax in 0..self.axiom_hash.len() {
            if self.axiom_always[ax] && !disabled[ax] {
                base.fire(self, ax as u32, &mut queue);
            }
        }
        base.run(self, &mut queue, disabled, &mut |_| false);
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
            if disabled[self.conj_axiom[c] as usize]
                || self.conj_off[c + 1] - self.conj_off[c] != 1
            {
                continue;
            }
            let b = self.conj_lits[self.conj_off[c] as usize];
            if !candidate(b) || parent[b as usize] != u32::MAX {
                continue;
            }
            if let Some(&a) = self
                .local_sig_of(self.conj_axiom[c])
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
                    let hit = work.run_logged(self, &mut queue, disabled, &mut |ev| match ev {
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
        for &t in ix.local_sig_of(ax) {
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
    use std::collections::BTreeSet;

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

    fn masked_fixture(axioms: &[&str]) -> String {
        let mut text = "Prefix(:=<http://e/>)\nOntology(<http://e/o>\n".to_string();
        // Keep the complete symbol universe when removing logical axioms, as
        // the retained source session does: declaration deletion is refused.
        for class in ["A", "B", "C", "D", "E", "F", "G", "H"] {
            text.push_str(&format!("Declaration(Class(:{class}))\n"));
        }
        text.push_str("Declaration(ObjectProperty(:r))\nDeclaration(NamedIndividual(:a))\n");
        for axiom in axioms {
            text.push_str(axiom);
            text.push('\n');
        }
        text.push_str(")\n");
        text
    }

    fn signature_names(ix: &LocalityIndex, sig: &[bool]) -> BTreeSet<String> {
        sig.iter().enumerate().filter(|(_, yes)| **yes)
            .map(|(s, _)| ix.symbols[s].to_string()).collect()
    }

    fn affected_names(ix: &LocalityIndex, ids: Option<Vec<u32>>) -> Option<BTreeSet<String>> {
        ids.map(|ids| ids.into_iter().map(|s| ix.symbols[s as usize].to_string()).collect())
    }

    /// An original-id masked view must agree with a separately compiled source
    /// containing exactly its enabled statements. Compare by IRI and statement
    /// hash, never by the fresh index's potentially different numeric ids.
    fn assert_masked_matches_fresh(src: &str, ix: &LocalityIndex, disabled: &[bool]) {
        let s = scan(src).unwrap();
        let removed: BTreeSet<_> = ix.axiom_hash.iter().enumerate()
            .filter(|(a, _)| disabled[*a]).map(|(_, h)| *h).collect();
        let mut reduced = src[..s.open_end].to_string();
        reduced.push('\n');
        for st in &s.statements {
            if !removed.contains(&st.hash) {
                reduced.push_str(&src[st.start..st.end]);
                reduced.push('\n');
            }
        }
        reduced.push_str(")\n");
        let rs = scan(&reduced).unwrap();
        let fresh = LocalityIndex::build(&reduced, &rs, ix.tbox_mode).unwrap();
        assert_eq!(ix.tbox_mode, fresh.tbox_mode);
        let none = vec![false; fresh.axiom_count()];
        let classes: Vec<_> = ix.symbols.iter().enumerate()
            .filter(|(s, _)| ix.is_class[*s]).map(|(s, iri)| (s as u32, &**iri)).collect();
        let fresh_classes: BTreeSet<_> = fresh.symbols.iter().enumerate()
            .filter(|(s, _)| fresh.is_class[*s]).map(|(_, iri)| &**iri).collect();
        assert_eq!(classes.iter().map(|(_, iri)| *iri).collect::<BTreeSet<_>>(), fresh_classes);
        // Include the empty signature so deleted always-nonlocal axioms cannot
        // survive in the base of the affected-subject DFS.
        for seeds in std::iter::once(Vec::new()).chain(classes.iter().map(|(s, _)| vec![*s])) {
            let fresh_seeds: Vec<_> = seeds.iter()
                .map(|s| fresh.symbol(&ix.symbols[*s as usize]).unwrap()).collect();
            let (old_module, old_sig) = ix.module(&seeds, disabled);
            let (new_module, new_sig) = fresh.module(&fresh_seeds, &none);
            assert_eq!(old_module.iter().map(|a| ix.axiom_hash[*a as usize]).collect::<BTreeSet<_>>(),
                new_module.iter().map(|a| fresh.axiom_hash[*a as usize]).collect::<BTreeSet<_>>());
            assert_eq!(signature_names(ix, &old_sig), signature_names(&fresh, &new_sig));
        }
        // Empty, single and simultaneous marks include already disabled axioms.
        // A stale mark must have no effect once its owner axiom is absent.
        for mark in 0..ix.axiom_count() + 2 {
            let marked: Vec<_> = (0..ix.axiom_count())
                .map(|a| mark == a || mark == ix.axiom_count() + 1).collect();
            let fresh_marked: Vec<_> = fresh.axiom_hash.iter()
                .map(|h| marked[ix.axiom_by_hash[h] as usize]).collect();
            assert_eq!(ix.empty_module_avoids_with_disabled(&marked, disabled),
                fresh.empty_module_avoids(&fresh_marked));
            assert_eq!(affected_names(ix, ix.affected_classes_with_disabled(&marked, disabled)),
                affected_names(&fresh, fresh.affected_classes(&fresh_marked)));
            assert_eq!(affected_names(ix, ix.affected_classes_tbox_with_disabled(&marked, disabled)),
                affected_names(&fresh, fresh.affected_classes_tbox(&fresh_marked)));
            // Independently check the optimized DFS against one masked module
            // extraction per class, including its nominal conservative marks.
            let trig: Vec<_> = marked.iter().zip(&ix.nominal).map(|(m, n)| *m || *n).collect();
            let (base, _) = ix.module(&[], disabled);
            let naive = if base.iter().any(|a| trig[*a as usize]) {
                None
            } else {
                Some(classes.iter().filter(|(s, _)| {
                    ix.module(&[*s], disabled).0.iter().any(|a| trig[*a as usize])
                }).map(|(_, iri)| (*iri).to_string()).collect::<BTreeSet<_>>())
            };
            assert_eq!(affected_names(ix, ix.affected_classes_tbox_with_disabled(&marked, disabled)), naive);
        }
    }

    #[test]
    fn masked_affected_forest_ignores_deleted_parent_owners() {
        let src = masked_fixture(&["SubClassOf(:A :B)", "SubClassOf(:B :C)", "SubClassOf(:D :E)"]);
        let (_, ix) = index(&src);
        let mut disabled = vec![false; ix.axiom_count()];
        disabled[0] = true;
        let marked = vec![false, true, false];
        let affected = affected_names(&ix, ix.affected_classes_with_disabled(&marked, &disabled)).unwrap();
        assert_eq!(affected, BTreeSet::from(["http://e/B".to_string()]));
        // Without skipping the deleted A->B forest owner, A inherits B's
        // marked module despite having no path to it in the reduced source.
        assert_masked_matches_fresh(&src, &ix, &disabled);
    }

    #[test]
    fn masked_modules_match_fresh_across_successive_deletion_subsets() {
        let src = masked_fixture(&[
            "SubClassOf(:A :B)", "SubClassOf(:B :C)", "SubClassOf(:C :A)",
            "SubClassOf(:D :E)", "SubClassOf(:E :F)",
            "SubClassOf(ObjectIntersectionOf(:B :E) :G)",
            "SubClassOf(:H :B)", "SubClassOf(:H :E)",
        ]);
        let (_, ix) = index(&src);
        // Every subset is reachable by successive deletions. Cycles, branches
        // and conjunctive triggers exercise the logged DFS and its rollback.
        for bits in 0..1u32 << ix.axiom_count() {
            let disabled: Vec<_> = (0..ix.axiom_count()).map(|a| bits & (1 << a) != 0).collect();
            assert_masked_matches_fresh(&src, &ix, &disabled);
        }
    }

    #[test]
    fn masked_global_and_nominal_axioms_match_fresh_reduced_sources() {
        let global = masked_fixture(&[
            "SubClassOf(owl:Thing :G)", "SubClassOf(:G :H)",
            "ReflexiveObjectProperty(:r)", "ObjectPropertyDomain(:r :D)",
            "SubClassOf(:A :B)",
        ]);
        let (_, ix) = index(&global);
        for bits in 0..1u32 << ix.axiom_count() {
            let disabled: Vec<_> = (0..ix.axiom_count()).map(|a| bits & (1 << a) != 0).collect();
            assert_masked_matches_fresh(&global, &ix, &disabled);
        }
        let nominal = masked_fixture(&[
            "SubClassOf(:A ObjectHasValue(:r :a))", "SubClassOf(:D :A)",
            "SubClassOf(:B :C)", "ClassAssertion(:B :a)",
        ]);
        let s = scan(&nominal).unwrap();
        let ix = LocalityIndex::build(&nominal, &s, true).unwrap();
        assert!(ix.tbox_mode);
        assert!(ix.nominal.iter().any(|n| *n));
        for bits in 0..1u32 << ix.axiom_count() {
            let disabled: Vec<_> = (0..ix.axiom_count()).map(|a| bits & (1 << a) != 0).collect();
            assert_masked_matches_fresh(&nominal, &ix, &disabled);
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
    fn told_queries_traverse_thing_and_query_local_global_seeds() {
        let text="Prefix(:=<urn:global#>) Ontology(SubClassOf(:A :B) SubClassOf(owl:Thing :G) SubClassOf(:G :H) SubClassOf(:Seed :Tail))";
        let scanned=scan(text).unwrap(); let proofs=ToldProofs::build(text,&scanned);
        let none=crate::fxhash::FxHashSet::default();
        assert!(proofs.proves_all(":A",&[":G",":H"],&none));
        let global=scanned.statements.iter().find(|s|text[s.start..s.end].contains("owl:Thing")).unwrap().hash;
        let removed=crate::fxhash::FxHashSet::from_iter([global]);
        assert!(!proofs.proves_all(":A",&[":G"],&removed));
        assert!(proofs.proves_all_with_globals(":A",&[":Tail"],&none,&["urn:global#Seed".into()]));
        assert!(!proofs.proves_all(":A",&[":Tail"],&none),"global seeds cannot mutate the donor");
        assert!(!proofs.proves_all_with_globals(":A",&[":Tail"],&none,&["urn:global#Unknown".into()]));
        assert!(!proofs.proves_all_with_globals(":A",&[":Unknown"],&none,&["urn:global#Unknown".into()]));
    }

    #[test]
    fn told_global_role_seeds_come_only_from_actual_new_source() {
        let old="Prefix(:=<urn:global#>) Ontology(SubClassOf(:A :B) SubClassOf(:G :H) ReflexiveObjectProperty(:r) SubObjectPropertyOf(:r :s) ObjectPropertyRange(:s :G))";
        let old_scan=scan(old).unwrap(); let proofs=ToldProofs::build(old,&old_scan);
        let none=crate::fxhash::FxHashSet::default();
        let globals=crate::incr_global::global_named_classes(old,&old_scan).unwrap();
        assert!(proofs.proves_all_with_globals(":A",&[":G",":H"],&none,&globals));
        for deleted in ["ReflexiveObjectProperty(:r)","SubObjectPropertyOf(:r :s)","ObjectPropertyRange(:s :G)"] {
            let new=old.replace(deleted,""); let new_scan=scan(&new).unwrap();
            let actual=crate::incr_global::global_named_classes(&new,&new_scan).unwrap();
            assert!(!proofs.proves_all_with_globals(":A",&[":G",":H"],&none,&actual));
        }
    }

    #[test]
    fn told_global_resolved_iris_do_not_use_colliding_source_spellings() {
        let text="Prefix(:=<urn:base#>) Prefix(urn:=<urn:other#>) Ontology(SubClassOf(:S :T) SubClassOf(urn:A :Wrong) SubClassOf(<urn:A> :Right) SubClassOf(urn:Missing :Wrong))";
        let scanned=scan(text).unwrap(); let proofs=ToldProofs::build(text,&scanned);
        let none=crate::fxhash::FxHashSet::default();
        let globals=vec!["urn:A".to_owned()];
        assert!(proofs.proves_all_with_globals(":S",&[":Right"],&none,&globals));
        assert!(!proofs.proves_all_with_globals(":S",&[":Wrong"],&none,&globals));
        // This string is only a source spelling for urn:other#Missing.
        // No class with the resolved IRI urn:Missing exists in the graph.
        assert!(!proofs.proves_all_with_globals(":S",&[":Wrong"],&none,&["urn:Missing".into()]));
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

    fn full_reuse(old_text: &str, old: &LocalityIndex, text: &str) -> (LocalityIndex, CompileReuse) {
        let old_scan = scan(old_text).unwrap();
        let new_scan = scan(text).unwrap();
        LocalityIndex::build_reusing_full(text, &new_scan, old, &old_text[..old_scan.open_end], |hash| {
            old_scan.statements.iter().find(|st| st.hash == hash)
                .map(|st| &old_text[st.start..st.end])
        }).unwrap()
    }

    fn assert_full_reuse_equivalent(actual: &LocalityIndex, fresh: &LocalityIndex) {
        use std::collections::{BTreeMap, BTreeSet};
        let kinds = |ix: &LocalityIndex| -> BTreeMap<String, (String, bool)> {
            ix.symbols.iter().enumerate().map(|(i, iri)|
                (iri.to_string(), (ix.names[i].to_string(), ix.is_class[i]))).collect()
        };
        assert_eq!(kinds(actual), kinds(fresh));
        assert_eq!((actual.full_mode, actual.tbox_mode, actual.el_like, actual.spelling_conflict),
            (fresh.full_mode, fresh.tbox_mode, fresh.el_like, fresh.spelling_conflict));
        assert_eq!(actual.positive_object_source, fresh.positive_object_source);
        assert_eq!(actual.axiom_hash, fresh.axiom_hash);
        assert_eq!(actual.axiom_always, fresh.axiom_always);
        assert_eq!(actual.nominal, fresh.nominal);
        assert_eq!(actual.compile_flags, fresh.compile_flags);
        for ax in 0..actual.axiom_count() {
            let signature = |ix: &LocalityIndex, local: bool| -> BTreeSet<String> {
                let ids = if local { ix.local_sig_of(ax as u32) } else { ix.sig_of(ax as u32) };
                ids.iter().map(|&id| ix.symbols[id as usize].to_string()).collect()
            };
            assert_eq!(signature(actual, false), signature(fresh, false));
            assert_eq!(signature(actual, true), signature(fresh, true));
            let formulas = |ix: &LocalityIndex| -> Vec<BTreeSet<String>> {
                ix.conj_axiom.iter().enumerate().filter(|(_, owner)| **owner == ax as u32)
                    .map(|(c, _)| ix.conj_lits[ix.conj_off[c] as usize..ix.conj_off[c + 1] as usize]
                        .iter().map(|&id| ix.symbols[id as usize].to_string()).collect()).collect()
            };
            assert_eq!(formulas(actual), formulas(fresh));
            let classes = |ix: &LocalityIndex| -> BTreeSet<String> {
                ix.class_lits[ix.class_off[ax] as usize..ix.class_off[ax + 1] as usize]
                    .iter().map(|&id| ix.symbols[id as usize].to_string()).collect()
            };
            assert_eq!(classes(actual), classes(fresh));
        }
        let seed_names: Vec<_> = std::iter::once(None)
            .chain(fresh.symbols.iter().map(|name| Some(&**name))).collect();
        for name in seed_names {
            let module = |ix: &LocalityIndex| {
                let seeds: Vec<_> = name.and_then(|name| ix.symbol(name)).into_iter().collect();
                let (axioms, signature) = ix.module(&seeds, &vec![false; ix.axiom_count()]);
                let axioms: BTreeSet<_> = axioms.iter().map(|&id| ix.axiom_hash[id as usize]).collect();
                let signature: BTreeSet<_> = signature.iter().enumerate().filter(|(_, yes)| **yes)
                    .map(|(id, _)| ix.symbols[id].to_string()).collect();
                (axioms, signature)
            };
            assert_eq!(module(actual), module(fresh), "seed {name:?}");
        }
        for ax in 0..actual.axiom_count() {
            let mut marked = vec![false; actual.axiom_count()];
            marked[ax] = true;
            assert_eq!(actual.empty_module_avoids(&marked), fresh.empty_module_avoids(&marked));
            assert_eq!(affected_names(actual, actual.affected_classes(&marked)),
                affected_names(fresh, fresh.affected_classes(&marked)));
        }
    }

    #[test]
    fn precise_signature_keeps_selected_individual_declarations_without_locality_feedback() {
        let text = "Prefix(:=<urn:precise#>) Ontology(Declaration(Class(:A)) Declaration(Class(:B)) \
            Declaration(Class(:Meta)) Declaration(NamedIndividual(:A)) \
            ClassAssertion(:Meta :A) SubClassOf(:A :B))";
        let (scan, ix) = index(text);
        let added = scan.statements.iter().find(|s| text[s.start..s.end].starts_with("SubClassOf")).unwrap().hash;
        let mark: Vec<_> = ix.axiom_hash.iter().map(|h| *h == added).collect();
        assert!(ix.empty_module_avoids(&mark));
        let (module, declaration_signature) = ix.module(&[], &vec![false; ix.axiom_count()]);
        assert_eq!(module.len(), 1);
        assert!(declaration_signature[ix.symbol("urn:precise#A").unwrap() as usize]);
        let selected: BTreeSet<_> = module.iter().copied().collect();
        let kept: Vec<_> = scan.statements.iter().filter(|s| match s.kind {
            StmtKind::Declaration => ix.decl_entity.get(&s.hash).is_some_and(|id| declaration_signature[*id as usize]),
            StmtKind::Logical | StmtKind::Assertion => ix.axiom_by_hash.get(&s.hash).is_some_and(|id| selected.contains(id)),
            _ => false,
        }).map(|s| &text[s.start..s.end]).collect();
        assert!(kept.contains(&"Declaration(NamedIndividual(:A))"));
        assert!(kept.contains(&"ClassAssertion(:Meta :A)"));
        assert!(!kept.contains(&"SubClassOf(:A :B)"));
        let emitted = format!("{}\n{}\n)", &text[..scan.open_end], kept.join("\n"));
        let es = super::scan(&emitted).unwrap();
        let extracted = LocalityIndex::build(&emitted, &es, false).unwrap();
        assert!(extracted.decl_entity.values().any(|id| extracted.symbols[*id as usize].as_ref() == "urn:precise#A"));
        assert_eq!(extracted.axiom_count(), 1);
    }

    #[test]
    fn precise_nominal_assertion_and_fixed_literal_positions_preserve_unknown_fallback() {
        let header = "Prefix(:=<urn:precise#>) Ontology(";
        for body in ["ClassAssertion(:Meta :A)", "ObjectPropertyAssertion(:r :A :Z)",
            "NegativeObjectPropertyAssertion(:r :A :Z)", "DataPropertyAssertion(:p :A \"v\"^^<urn:fixed>)",
            "NegativeDataPropertyAssertion(:p :A \"v\"@en)", "SameIndividual(:A :Z)",
            "DifferentIndividuals(:A :Z)", "SubClassOf(ObjectOneOf(:A) :N)",
            "ClassAssertion(ObjectHasValue(:r :A) :Z)"] {
            let text = format!("{header}{body} SubClassOf(:A :B))");
            let (_, ix) = index(&text);
            let a = ix.symbol("urn:precise#A").unwrap();
            assert!(!ix.local_sig_of(0).contains(&a), "{body}");
            assert!(ix.sig_of(0).contains(&a), "original occurrence lost: {body}");
            let (module, _) = ix.module(&[], &vec![false; ix.axiom_count()]);
            assert!(!module.contains(&1), "punned individual seeded class: {body}");
        }
        for body in ["ClassAssertion(Mystery(:X) :A)", "Mystery(ObjectOneOf(:A))",
            "ObjectPropertyAssertion(Mystery(:r) :A :Z)",
            "SubClassOf(:N ObjectHasValue(:r Mystery(:A)))", "SubClassOf(:N DataHasValue(:p \"v\"))"] {
            let text = format!("{header}{body})");
            let (_, ix) = index(&text);
            assert_eq!(ix.local_sig_of(0), ix.sig_of(0), "{body}");
        }
        let (_, ix) = index(&format!("{header}ClassAssertion(:A :Z) SubClassOf(:A :B))"));
        assert!(ix.module(&[], &vec![false; ix.axiom_count()]).0.contains(&1), "class position must remain");
    }

    #[test]
    fn precise_occurrence_and_locality_records_survive_exact_donor_replay() {
        let header = "Prefix(:=<urn:precise#>) Prefix(o:=<http://www.w3.org/2002/07/owl#>) Ontology(";
        let body = "Declaration(Class(:A)) Declaration(NamedIndividual(:A)) Declaration(NamedIndividual(o:Thing)) \
            ClassAssertion(:Meta :A) ClassAssertion(:Meta o:Thing) ObjectPropertyAssertion(:r :A :Z) \
            DataPropertyAssertion(:p :A \"v\"^^<urn:fixed>) SubClassOf(ObjectOneOf(:A) :N) \
            SubClassOf(:N ObjectHasValue(:r :Z)) SameIndividual(:A :Z) SubClassOf(:A :B)";
        let old_text = format!("{header}{body})");
        let (_, old) = index(&old_text);
        let text = format!("{header}{body} SubClassOf(:B :C))");
        let (_, fresh) = index(&text);
        let (actual, stats) = full_reuse(&old_text, &old, &text);
        assert_eq!(stats.reused_compiled_axioms, old.axiom_count());
        assert_eq!(stats.compiled_axioms, 1);
        assert_full_reuse_equivalent(&actual, &fresh);
        let public = actual.live_public_class_names(|_| true).unwrap();
        assert!(public.contains(&"o:Thing"), "individual-only builtin alias must remain");
        let a = actual.symbol("urn:precise#A").unwrap();
        assert!(!actual.local_sig_of(0).contains(&a));
        assert!(actual.sig_of(0).contains(&a));
    }

    #[test]
    fn compiled_full_reuse_matches_fresh_across_all_64_subsets() {
        let axioms = ["SubClassOf(:A :B)", "SubClassOf(:B ObjectSomeValuesFrom(:r :C))",
            "ClassAssertion(:A :a)", "EquivalentClasses(:D ObjectIntersectionOf(:B :E))",
            "SubObjectPropertyOf(:r :s)", "DisjointClasses(:B :F)"];
        let source = |subset: usize| {
            let mut text = String::from("Prefix(:=<http://e/>) Ontology(<http://e/o>\n");
            for c in ["A", "B", "C", "D", "E", "F"] {
                text.push_str(&format!("Declaration(Class(:{c}))\n"));
            }
            text.push_str("Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(NamedIndividual(:a))\n");
            for i in (0..axioms.len()).rev() {
                if subset & (1 << i) != 0 { text.push_str(axioms[i]); text.push('\n'); }
            }
            text.push_str(")\n"); text
        };
        let old_text = source(63);
        let old = LocalityIndex::build(&old_text, &scan(&old_text).unwrap(), false).unwrap();
        for subset in 0..64 {
            let text = source(subset);
            let fresh = LocalityIndex::build(&text, &scan(&text).unwrap(), false).unwrap();
            let (actual, stats) = full_reuse(&old_text, &old, &text);
            assert_eq!(stats.reused_compiled_axioms, subset.count_ones() as usize);
            assert_eq!(stats.compiled_axioms, 0);
            assert_eq!(stats.csr_axiom_records, fresh.axiom_count());
            assert_full_reuse_equivalent(&actual, &fresh);
        }
    }

    #[test]
    fn compiled_full_reuse_recomputes_class_kinds_and_local_flags() {
        let header = "Prefix(:=<http://e/>) Ontology(<http://e/o>\n";
        let old_text = format!("{header}Declaration(Class(:A)) Declaration(ObjectProperty(:A))\nSubObjectPropertyOf(:A :r)\nSubClassOf(:B ObjectUnionOf(:C :D))\nSubClassOf(:E ObjectOneOf(:a))\nClassAssertion(:E :a)\n)");
        let old = LocalityIndex::build(&old_text, &scan(&old_text).unwrap(), false).unwrap();
        let text = format!("{header}Declaration(ObjectProperty(:A))\nSubObjectPropertyOf(:A :r)\nSubClassOf(:N :M)\n)");
        let fresh = LocalityIndex::build(&text, &scan(&text).unwrap(), false).unwrap();
        let (actual, stats) = full_reuse(&old_text, &old, &text);
        assert_eq!((stats.reused_compiled_axioms, stats.compiled_axioms), (1, 1));
        assert!(!actual.is_class[actual.symbol("http://e/A").unwrap() as usize]);
        assert!(actual.el_like);
        assert_full_reuse_equivalent(&actual, &fresh);
    }

    #[test]
    fn tbox_assertion_guard_recognizes_resolved_universal_role_aliases() {
        for (prefixes, role, universal) in [
            ("", "owl:topObjectProperty", true),
            ("", "<http://www.w3.org/2002/07/owl#topObjectProperty>", true),
            ("Prefix(t:=<http://www.w3.org/2002/07/owl#topObject>)", "t:Property", true),
            ("Prefix(t:=<http://www.w3.org/2002/07/owl#top>)", "t:ObjectProperty", true),
            ("Prefix(:=<http://www.w3.org/2002/07/owl#topObject>)", ":Property", true),
            ("Prefix(t:=<http://www.w3.org/2002/07/owl#topObjectProperty>)", "t:", true),
            ("Prefix(t:=<http://www.w3.org/2002/07/owl#topObject>) Prefix(t:=<urn:user#>)", "t:Property", false),
            ("Prefix(t:=<urn:user#>) Prefix(t:=<http://www.w3.org/2002/07/owl#topObject>)", "t:Property", true),
        ] {
            let text = format!("Prefix(e:=<urn:e#>) {prefixes} Ontology(<urn:e/o> Declaration(Class(e:B)) Declaration(NamedIndividual(e:a)) ClassAssertion(ObjectAllValuesFrom({role} e:B) e:a))");
            let scanned = scan(&text).unwrap();
            let internal = LocalityIndex::build_mode(&text, &scanned, true).unwrap();
            assert_eq!(!internal.tbox_mode, universal, "role={role}, prefixes={prefixes}");
            let public = LocalityIndex::build(&text, &scanned, true).unwrap();
            if universal {
                // The public wrapper retries full compilation, keeping the
                // assertion, rather than changing its meaning or verdict.
                assert!(public.full_mode);
                assert_eq!(public.axiom_count(), 1);
                let full = LocalityIndex::build(&text, &scanned, false).unwrap();
                assert_full_reuse_equivalent(&public, &full);
            } else {
                assert!(public.tbox_mode);
                assert_eq!(public.assertions.len(), 1);
            }
        }
    }

    #[test]
    fn compiled_full_reuse_requires_actual_full_provenance() {
        let text = "Prefix(:=<http://e/>) Ontology(<http://e/o> SubClassOf(:A :B) ClassAssertion(ObjectAllValuesFrom(owl:topObjectProperty :B) :a))";
        let scanned = scan(text).unwrap();
        let refused = LocalityIndex::build_mode(text, &scanned, true).unwrap();
        assert!(!refused.tbox_mode);
        assert!(!refused.full_mode);
        assert_eq!(refused.axiom_count(), 1);
        let (actual, stats) = full_reuse(text, &refused, text);
        assert_eq!(stats.reused_compiled_axioms, 0);
        let fresh = LocalityIndex::build(text, &scanned, false).unwrap();
        assert_full_reuse_equivalent(&actual, &fresh);
        // The public wrapper already retries full compilation after refusal.
        let retried = LocalityIndex::build(text, &scanned, true).unwrap();
        assert!(retried.full_mode);
        let (actual, stats) = full_reuse(text, &retried, text);
        assert_eq!(stats.reused_compiled_axioms, 2);
        assert_full_reuse_equivalent(&actual, &fresh);
    }

    #[test]
    fn compiled_full_reuse_checks_headers_text_and_spelling_conflicts() {
        let old_text = "Prefix(:=<http://e/>) Ontology(<http://e/o> SubClassOf(:A :B))";
        let old_scan = scan(old_text).unwrap();
        let old = LocalityIndex::build(old_text, &old_scan, false).unwrap();
        let changed = "Prefix(:=<http://e/>) Ontology(<http://e/o> SubClassOf(:C :D))";
        let mut changed_scan = scan(changed).unwrap();
        changed_scan.statements[0].hash = old_scan.statements[0].hash;
        let (actual, stats) = LocalityIndex::build_reusing_full(changed, &changed_scan,
            &old, &old_text[..old_scan.open_end], |_| Some(&old_text[old_scan.statements[0].start..old_scan.statements[0].end])).unwrap();
        assert_eq!(stats.reused_compiled_axioms, 0);
        let fresh = LocalityIndex::build(changed, &changed_scan, false).unwrap();
        assert_full_reuse_equivalent(&actual, &fresh);
        let remapped = old_text.replace("http://e/", "http://other/");
        let (_, stats) = full_reuse(old_text, &old, &remapped);
        assert_eq!(stats.reused_compiled_axioms, 0);
        let conflict = "Prefix(:=<http://e/>) Ontology(<http://e/o> SubClassOf(:A :B) Declaration(Class(<http://e/A>)))";
        let conflict_ix = LocalityIndex::build(conflict, &scan(conflict).unwrap(), false).unwrap();
        assert!(conflict_ix.spelling_conflict);
        let (actual, stats) = full_reuse(old_text, &old, conflict);
        assert_eq!(stats.reused_compiled_axioms, 1);
        assert_full_reuse_equivalent(&actual, &conflict_ix);
        let (actual, stats) = full_reuse(conflict, &conflict_ix, old_text);
        assert_eq!(stats.reused_compiled_axioms, 0);
        assert_full_reuse_equivalent(&actual, &old);
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
#[derive(Clone)]
pub struct ToldProofs {
    ids: std::sync::Arc<FxHashMap<std::sync::Arc<str>, u32>>,
    spelling: std::sync::Arc<FxHashMap<std::sync::Arc<str>, u32>>,
    edges: Vec<std::sync::Arc<Vec<(u32, u128)>>>,
    definitions: std::sync::Arc<Vec<(u32, Told, u128)>>,
    thing: u32,
    supports: Vec<(u128, std::sync::Arc<ToldSupport>)>,
    // Counts reflect every recorded name touch in the enabled source.
    name_refs: Vec<usize>,
    spelling_refs: FxHashMap<std::sync::Arc<str>, usize>,
    spelling_conflict: bool,
    free_ids: Vec<u32>,
    recording: Option<ToldSupport>,
    record_ids: Vec<u32>,
    record_used: Vec<u32>,
}

#[derive(Clone, Default)]
struct ToldSupport {
    // Every name touch, including touches before a Boolean extraction declines.
    names: Vec<(u32, std::sync::Arc<str>, Option<std::sync::Arc<str>>)>,
    edges: Vec<(u32, u32)>,
    definitions: Vec<(u32, Told)>,
    id_count: u32,
}

#[derive(Default, Debug)]
pub struct ToldReuse {
    pub parsed_statements: usize,
    pub reused_statements: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Told {
    Name(u32),
    And(Vec<Told>),
    Or(Vec<Told>),
}

impl Told {
    fn remap(&self, ids: &[u32]) -> Self {
        match self {
            Self::Name(id) => Self::Name(ids[*id as usize]),
            Self::And(v) => Self::And(v.iter().map(|x| x.remap(ids)).collect()),
            Self::Or(v) => Self::Or(v.iter().map(|x| x.remap(ids)).collect()),
        }
    }
}

impl ToldProofs {
    pub fn build(text: &str, scan: &Scan) -> Self {
        Self::build_reusing(text, scan, None).0
    }

    /// Donor lookup must describe the exact source that compiled `old`, even
    /// when a retained deletion base uses a masked view of that graph.
    fn build_replaying<'a>(text: &str, scan: &Scan,
        donor: Option<(&Self, &str, &dyn Fn(u128) -> Option<&'a str>)>)
        -> (Self, ToldReuse)
    {
        let bld = Self::resolver(scan);
        let mut t = ToldProofs {
            ids: std::sync::Arc::new(FxHashMap::default()), spelling: std::sync::Arc::new(FxHashMap::default()),
            edges: Vec::new(), definitions: std::sync::Arc::new(Vec::new()), thing: 0,
            name_refs: Vec::new(), spelling_refs: FxHashMap::default(), spelling_conflict: false, free_ids: Vec::new(),
            supports: Vec::new(), recording: None,
            record_ids: Vec::new(), record_used: Vec::new(),
        };
        t.thing = t.id(&format!("{OWL}Thing"), None);
        let donor = donor.filter(|(_, header, _)| text[..scan.open_end] == **header);
        let mut by_hash = FxHashMap::default();
        if let Some((old, _, _)) = donor {
            for (hash, support) in &old.supports {
                by_hash.entry(*hash).or_insert(support);
            }
        }
        let mut stats = ToldReuse::default();
        let mut replay_ids = Vec::new();
        for st in &scan.statements {
            if st.kind != StmtKind::Logical { continue; }
            let slice = &text[st.start..st.end];
            if !(slice.starts_with("SubClassOf") || slice.starts_with("EquivalentClasses")) { continue; }
            let shared = donor.and_then(|(_, _, lookup)| {
                (lookup(st.hash) == Some(slice)).then(|| by_hash.get(&st.hash).copied()).flatten()
            });
            let support = if let Some(support) = shared {
                stats.reused_statements += 1;
                t.replay(support, st.hash, &mut replay_ids);
                std::sync::Arc::clone(support)
            } else {
                stats.parsed_statements += 1;
                t.recording = Some(ToldSupport::default());
                t.parse_statement(&bld, slice, st.hash);
                let support = std::sync::Arc::new(t.recording.take().expect("support recorder"));
                for id in t.record_used.drain(..) { t.record_ids[id as usize] = u32::MAX; }
                support
            };
            t.supports.push((st.hash, support));
        }
        // Scratch maps are not retained across reasoning revisions.
        t.record_ids = Vec::new(); t.record_used = Vec::new();
        (t, stats)
    }

    fn resolver(scan: &Scan) -> Builder<'_> {
        Builder {
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
            cur_classes: Vec::new(),
        }
    }

    pub fn build_reusing<'a>(text: &str, scan: &Scan,
        donor: Option<(&Self, &str, &dyn Fn(u128) -> Option<&'a str>)>)
        -> (Self, ToldReuse)
    {
        if let Some((old, header, lookup)) = donor.filter(|(old, header, _)|
            !old.spelling_conflict && text[..scan.open_end] == **header)
        {
            if let Some(result) = old.patch(text, scan, lookup) { return result; }
        }
        Self::build_replaying(text, scan, None)
    }

    fn patch<'a>(&self, text: &str, scan: &Scan,
        lookup: &dyn Fn(u128) -> Option<&'a str>) -> Option<(Self, ToldReuse)>
    {
        let mut old_counts: FxHashMap<u128, (usize, &std::sync::Arc<ToldSupport>)> = FxHashMap::default();
        for (tag, support) in &self.supports {
            let entry = old_counts.entry(*tag).or_insert((0, support)); entry.0 += 1;
        }
        let mut wanted = Vec::new();
        let mut kept_counts: FxHashMap<u128, usize> = FxHashMap::default();
        for st in &scan.statements {
            if st.kind != StmtKind::Logical { continue; }
            let slice = &text[st.start..st.end];
            if !(slice.starts_with("SubClassOf") || slice.starts_with("EquivalentClasses")) { continue; }
            let shared = old_counts.get(&st.hash).filter(|_| lookup(st.hash) == Some(slice))
                .map(|(_, support)| *support);
            if shared.is_some() { *kept_counts.entry(st.hash).or_default() += 1; }
            wanted.push((st, shared));
        }
        let dirty: crate::fxhash::FxHashSet<u128> = old_counts.iter()
            .filter(|(tag, (count, _))| kept_counts.get(tag).copied().unwrap_or(0) != *count)
            .map(|(tag, _)| *tag).collect();
        let mut next = self.clone();
        for (tag, support) in &self.supports {
            if dirty.contains(tag) { next.remove_support(support, *tag); }
        }
        next.supports.clear();
        if next.supports.capacity() > wanted.len().saturating_mul(2).saturating_add(64) {
            next.supports = Vec::with_capacity(wanted.len());
        }
        let bld = Self::resolver(scan);
        let mut replay_ids = Vec::new();
        let mut stats = ToldReuse::default();
        for (st, shared) in wanted {
            let support = match shared {
                Some(support) => {
                    stats.reused_statements += 1;
                    if dirty.contains(&st.hash) { next.replay(support, st.hash, &mut replay_ids); }
                    std::sync::Arc::clone(support)
                }
                None => {
                    stats.parsed_statements += 1;
                    next.recording = Some(ToldSupport::default());
                    next.parse_statement(&bld, &text[st.start..st.end], st.hash);
                    let support = std::sync::Arc::new(next.recording.take().expect("support recorder"));
                    for id in next.record_used.drain(..) { next.record_ids[id as usize] = u32::MAX; }
                    support
                }
            };
            next.supports.push((st.hash, support));
        }
        // A published spelling can denote different resolved IRIs (e.g.
        // q:A versus literal <q:A>). Rebuild in exact NEW order in that case.
        if next.spelling_conflict { return None; }
        next.record_ids = Vec::new(); next.record_used = Vec::new();
        if next.ids.capacity() > next.ids.len().saturating_mul(2).saturating_add(64) {
            std::sync::Arc::make_mut(&mut next.ids).shrink_to_fit();
        }
        if next.spelling.capacity() > next.spelling.len().saturating_mul(2).saturating_add(64) {
            std::sync::Arc::make_mut(&mut next.spelling).shrink_to_fit();
        }
        if next.spelling_refs.capacity() > next.spelling_refs.len().saturating_mul(2).saturating_add(64) {
            next.spelling_refs.shrink_to_fit();
        }
        // Reclaim sparse historical ID slots amortized over a large shrink.
        // Ordinary updates recycle free slots without rebuilding any graph.
        if next.edges.len() > next.ids.len().saturating_mul(2).saturating_add(64) {
            let lookup: FxHashMap<u128, &str> = scan.statements.iter()
                .map(|s| (s.hash, &text[s.start..s.end])).collect();
            let remapped = Self::build_replaying(text, scan,
                Some((&next, &text[..scan.open_end], &|tag| lookup.get(&tag).copied()))).0;
            return Some((remapped, stats));
        }
        Some((next, stats))
    }

    fn remove_support(&mut self, support: &ToldSupport, tag: u128) {
        let mut ids = vec![u32::MAX; support.id_count as usize];
        for (local, iri, _) in &support.names { ids[*local as usize] = self.ids[iri]; }
        let owners: crate::fxhash::FxHashSet<u32> = support.edges.iter().map(|(a,_)| ids[*a as usize]).collect();
        for id in owners {
            let row = std::sync::Arc::make_mut(&mut self.edges[id as usize]);
            row.retain(|(_,h)| *h != tag);
            Self::trim_buffer(row);
        }
        if !support.definitions.is_empty() {
            let definitions = std::sync::Arc::make_mut(&mut self.definitions);
            definitions.retain(|(_,_,h)| *h != tag);
            Self::trim_buffer(definitions);
        }
        for (local, iri, spelling) in &support.names {
            let id = ids[*local as usize];
            self.name_refs[id as usize] -= 1;
            if self.name_refs[id as usize] == 0 {
                std::sync::Arc::make_mut(&mut self.ids).remove(iri);
                debug_assert!(self.edges[id as usize].is_empty());
                self.edges[id as usize] = std::sync::Arc::new(Vec::new());
                self.free_ids.push(id);
            }
            if let Some(spelling) = spelling {
                let refs = self.spelling_refs.get_mut(spelling.as_ref()).expect("spelling contribution");
                *refs -= 1;
                if *refs == 0 {
                    self.spelling_refs.remove(spelling.as_ref());
                    std::sync::Arc::make_mut(&mut self.spelling).remove(spelling);
                }
            }
        }
    }

    fn trim_buffer<T>(values: &mut Vec<T>) {
        if values.is_empty() { *values = Vec::new(); }
        else if values.capacity() > values.len().saturating_mul(2).saturating_add(64) {
            values.shrink_to_fit();
        }
    }

    fn replay(&mut self, support: &ToldSupport, tag: u128, ids: &mut Vec<u32>) {
        ids.clear(); ids.resize(support.id_count as usize, u32::MAX);
        for (local, iri, spelling) in &support.names {
            ids[*local as usize] = self.id(iri, spelling.as_deref());
        }
        for &(a, b) in &support.edges { self.edge(ids[a as usize], ids[b as usize], tag); }
        for (a, d) in &support.definitions {
            self.definition(ids[*a as usize], d.remap(ids), tag);
        }
    }

    fn definition(&mut self, a: u32, d: Told, tag: u128) {
        if let Some(record) = &mut self.recording {
            record.definitions.push((self.record_ids[a as usize], d.remap(&self.record_ids)));
        }
        std::sync::Arc::make_mut(&mut self.definitions).push((a, d, tag));
    }

    fn parse_statement(&mut self, bld: &Builder<'_>, slice: &str, tag: u128) {
            let Ok(node) = Parser::new(slice).parse() else { return };
            let Node::List(head, args) = &node else { return };
            let args: Vec<&Node<'_>> = args.iter().filter(|n| n.head() != Some("Annotation")).collect();
            match (*head, args.len()) {
                ("SubClassOf", 2) => {
                    let Some(a) = self.name(bld, args[0]) else { return };
                    for b in self.conjuncts(bld, args[1]) {
                        self.edge(a, b, tag);
                    }
                }
                ("EquivalentClasses", n) if n >= 2 => {
                    let names: Vec<Option<u32>> = args.iter().map(|x| self.name(bld, x)).collect();
                    for (i, a) in names.iter().enumerate() {
                        let Some(a) = *a else { continue };
                        for (j, x) in args.iter().enumerate() {
                            if i == j {
                                continue;
                            }
                            // Forward: a ⊑ x, through x's conjuncts.
                            for b in self.conjuncts(bld, x) {
                                self.edge(a, b, tag);
                            }
                            // Backward: x ⊑ a, a definition when x is a Boolean
                            // combination of names (a plain name is an edge).
                            match names[j] {
                                Some(b) => self.edge(b, a, tag),
                                None => {
                                    if let Some(d) = self.boolean(bld, x) {
                                        self.definition(a, d, tag);
                                    }
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
    }

    fn id(&mut self, iri: &str, spelling: Option<&str>) -> u32 {
        let (iri, id) = match self.ids.get_key_value(iri) {
            Some((key, &id)) => (std::sync::Arc::clone(key), id),
            None => {
                let id = match self.free_ids.pop() {
                    Some(id) => id,
                    None => { let id = self.edges.len() as u32; self.edges.push(std::sync::Arc::new(Vec::new())); self.name_refs.push(0); id }
                };
                let key = std::sync::Arc::<str>::from(iri);
                std::sync::Arc::make_mut(&mut self.ids).insert(key.clone(), id);
                (key, id)
            }
        };
        self.name_refs[id as usize] += 1;
        let spelling = spelling.map(|sp| {
            let key = match self.spelling.get_key_value(sp) {
                Some((key, &prior)) => {
                    self.spelling_conflict |= prior != id;
                    key.clone()
                },
                None => {
                    let key = if sp == iri.as_ref() { iri.clone() } else { std::sync::Arc::<str>::from(sp) };
                    std::sync::Arc::make_mut(&mut self.spelling).insert(key.clone(), id);
                    key
                }
            };
            if let Some(count) = self.spelling_refs.get_mut(sp) { *count += 1; }
            else { self.spelling_refs.insert(key.clone(), 1); }
            key
        });
        if let Some(record) = &mut self.recording {
            if self.record_ids.len() <= id as usize { self.record_ids.resize(id as usize + 1, u32::MAX); }
            if self.record_ids[id as usize] == u32::MAX {
                self.record_ids[id as usize] = record.id_count;
                record.id_count += 1;
                self.record_used.push(id);
            }
            record.names.push((self.record_ids[id as usize], iri, spelling));
        }
        id
    }

    fn edge(&mut self, a: u32, b: u32, tag: u128) {
        if a != b {
            std::sync::Arc::make_mut(&mut self.edges[a as usize]).push((b, tag));
            if let Some(record) = &mut self.recording {
                record.edges.push((self.record_ids[a as usize], self.record_ids[b as usize]));
            }
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
        self.proves_all_with_globals(subject, supers, removed, &[])
    }

    /// As above, with independently proved global classes of actual NEW.
    /// Known global ids seed this query only; unknown ids are ignored and no
    /// persisted graph/name map is changed. The caller owns their provenance.
    pub(crate) fn proves_all_with_globals(&self, subject: &str, supers: &[&str],
        removed: &crate::fxhash::FxHashSet<u128>, globals: &[String]) -> bool {
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
        let mut stack = vec![a, self.thing];
        set[a as usize] = true;
        set[self.thing as usize] = true;
        for global in globals {
            // Globals are resolved IRIs, never published source spellings.
            // A prefixed token can spell an unrelated resolved IRI verbatim.
            if let Some(id) = self.ids.get(global.as_str()).copied() {
                if !set[id as usize] { set[id as usize] = true; stack.push(id); }
            }
        }
        loop {
            while let Some(x) = stack.pop() {
                for &(y, tag) in self.edges[x as usize].iter() {
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
            for (x, d, tag) in self.definitions.iter() {
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

#[cfg(test)]
mod positive_object_tests {
    use super::*;
    fn index(body: &str) -> LocalityIndex {
        let text = format!("Prefix(:=<urn:test#>) Prefix(o:=<http://www.w3.org/2002/07/owl#>) Ontology({body})");
        LocalityIndex::build(&text, &scan(&text).unwrap(), false).unwrap()
    }
    #[test]
    fn resolved_positive_fragment_and_aliases() {
        assert!(index("SubClassOf(:A ObjectAllValuesFrom(ObjectInverseOf(:r) ObjectUnionOf(:B owl:Thing))) ClassAssertion(:A :a) ObjectPropertyAssertion(:r :a :b) SameIndividual(:a <urn:test#a>) ClassAssertion(:A _:x) SameIndividual(_:x _:y)").positive_object_source);
        for bad in ["SubClassOf(:A o:Nothing)", "SubClassOf(:A ObjectSomeValuesFrom(o:topObjectProperty :B))", "ObjectPropertyAssertion(ObjectInverseOf(o:bottomObjectProperty) :a :b)", "DifferentIndividuals(:a :b)", "DifferentIndividuals(:a <urn:test#a>)", "SubClassOf(:A ObjectComplementOf(:B))", "ClassAssertion(ObjectOneOf(:a) :b)", "SubClassOf(:A ObjectMinCardinality(1 :r :B))", "DataPropertyAssertion(:d :a \"x\")", "DisjointClasses(:A :B)", "Unknown(:A)", "SubClassOf(:A)", "ObjectPropertyAssertion(:r :a)"] {
            assert!(!index(bad).positive_object_source, "{bad}");
        }
    }
    #[test]
    fn all_supported_axiom_expansions_and_tbox_refusal() {
        let body = "EquivalentClasses(:A :B :C) SubObjectPropertyOf(ObjectPropertyChain(:r ObjectInverseOf(:s)) :t) EquivalentObjectProperties(:r :s) InverseObjectProperties(:r :s) ObjectPropertyDomain(:r :A) ObjectPropertyRange(:r :B) TransitiveObjectProperty(:r) FunctionalObjectProperty(:r) InverseFunctionalObjectProperty(:r) SymmetricObjectProperty(:r) ReflexiveObjectProperty(:r) ClassAssertion(ObjectHasSelf(:r) :a)";
        assert!(index(body).positive_object_source);
        let text = format!("Prefix(:=<urn:test#>) Ontology({body})");
        assert!(!LocalityIndex::build(&text, &scan(&text).unwrap(), true).unwrap().positive_object_source);
        // Skipped assertion must not turn a TBox slice into a source certificate.
        let text = "Prefix(:=<urn:test#>) Ontology(SubClassOf(:A :B) DifferentIndividuals(:a :b))";
        assert!(!LocalityIndex::build(text, &scan(text).unwrap(), true).unwrap().positive_object_source);
    }
    #[test]
    fn exact_donor_flags_recompute_complete_source() {
        let old = "Prefix(:=<urn:test#>) Ontology(SubClassOf(:A :B) ClassAssertion(:A :a))";
        let scan_old = scan(old).unwrap();
        let donor = LocalityIndex::build(old, &scan_old, false).unwrap();
        for text in [old.to_owned(), old.replace("ClassAssertion(:A :a)", "DifferentIndividuals(:a :b)"), old.replace("ClassAssertion(:A :a)", "SameIndividual(:a :b)")] {
            let sc = scan(&text).unwrap();
            let (ix, stats) = LocalityIndex::build_reusing_full(&text, &sc, &donor, &old[..scan_old.open_end], |h| scan_old.statements.iter().find(|s| s.hash == h).map(|s| &old[s.start..s.end])).unwrap();
            let fresh = LocalityIndex::build(&text, &sc, false).unwrap();
            assert_eq!(ix.positive_object_source, fresh.positive_object_source);
            assert_eq!(ix.compile_flags, fresh.compile_flags);
            assert!(stats.reused_compiled_axioms >= 1);
        }
    }

}

#[cfg(test)]
mod live_class_domain_tests {
    use super::*;
    use std::collections::{BTreeSet, HashSet};
    #[test]
    fn retained_class_kind_equals_fresh_index_for_every_statement_subset() {
        let head="Prefix(:=<urn:view#>) Ontology(";
        let statements=["Declaration(Class(:P))", "Declaration(ObjectProperty(:P))",
            "Declaration(NamedIndividual(:P))", "SubClassOf(:A :B)",
            "SubClassOf(:C ObjectSomeValuesFrom(:P :D))", "ClassAssertion(:E :P)",
            "Declaration(AnnotationProperty(:Note))", "Declaration(Class(owl:Thing))",
            "SubClassOf(:P ObjectOneOf(:i))", "Declaration(DataProperty(:E))"];
        let whole=format!("{head}{})",statements.join(" "));
        let sc=scan(&whole).unwrap();let ix=LocalityIndex::build(&whole,&sc,false).unwrap();
        for mask in 0usize..1<<statements.len() {
            let text=format!("{head}{})",statements.iter().enumerate().filter(|(n,_)| mask & (1<<n) != 0).map(|(_,s)|*s).collect::<Vec<_>>().join(" "));
            let new_scan=scan(&text).unwrap();
            let present:HashSet<_>=new_scan.statements.iter().map(|s|s.hash).collect();
            let fresh=LocalityIndex::build(&text,&new_scan,false).unwrap();
            let expected:BTreeSet<_>=fresh.names.iter().zip(&fresh.is_class).filter(|(_,c)|**c).map(|(n,_)|n.as_ref()).collect();
            let actual:BTreeSet<_>=ix.live_class_names(|h|present.contains(&h)).unwrap().into_iter().collect();
            assert_eq!(actual,expected,"mask={mask}");
        }
    }
    #[test]
    fn tbox_provenance_cannot_publish_a_full_source_domain_view() {
        let text="Prefix(:=<urn:view#>) Ontology(ClassAssertion(:A :a))";
        let sc=scan(text).unwrap();let ix=LocalityIndex::build(text,&sc,true).unwrap();
        assert!(!ix.full_mode);
        assert!(ix.live_class_names(|_|true).is_none());
    }
    #[test]
    fn replayed_compilation_keeps_exact_live_class_contributions() {
        let before="Prefix(:=<urn:view#>) Ontology(Declaration(Class(:P)) Declaration(ObjectProperty(:P)) SubClassOf(:A :B))";
        let old_scan=scan(before).unwrap();let old=LocalityIndex::build(before,&old_scan,false).unwrap();
        let union="Prefix(:=<urn:view#>) Ontology(Declaration(ObjectProperty(:P)) SubClassOf(:A :B) Declaration(Class(:P)) SubClassOf(:B :C))";
        let sc=scan(union).unwrap();
        let (ix,stats)=LocalityIndex::build_reusing_full(union,&sc,&old,&before[..old_scan.open_end],|h|old_scan.statements.iter().find(|s|s.hash==h).map(|s|&before[s.start..s.end])).unwrap();
        assert_eq!(stats.reused_compiled_axioms,1);
        let new="Prefix(:=<urn:view#>) Ontology(Declaration(ObjectProperty(:P)) SubClassOf(:B :C))";
        let ns=scan(new).unwrap();let hashes:HashSet<_>=ns.statements.iter().map(|s|s.hash).collect();
        let live:BTreeSet<_>=ix.live_class_names(|h|hashes.contains(&h)).unwrap().into_iter().collect();
        assert_eq!(live,BTreeSet::from([":B",":C"]));
    }
}

#[cfg(test)]
mod live_public_class_domain_tests {
    use super::*;
    use std::collections::{BTreeSet, HashSet};
    fn public_domain(ix: &LocalityIndex) -> BTreeSet<String> {
        let mut names: BTreeSet<_> = ix.names.iter().zip(&ix.symbols).zip(&ix.is_class)
            .filter(|((_, symbol), class)| **class || matches!(symbol.as_ref(),
                "http://www.w3.org/2002/07/owl#Thing" | "http://www.w3.org/2002/07/owl#Nothing"))
            .map(|((name, _), _)| name.to_string()).collect();
        names.extend(["owl:Thing", "owl:Nothing", "http://www.w3.org/2002/07/owl#Thing",
            "http://www.w3.org/2002/07/owl#Nothing"].into_iter().map(str::to_owned));
        names
    }
    #[test]
    fn masked_public_domain_matches_fresh_builtin_alias_and_punning_subsets() {
        let header = "Prefix(:=<urn:public#>) Prefix(o:=<http://www.w3.org/2002/07/owl#>) Ontology(";
        let statements = ["Declaration(Class(:P))", "Declaration(ObjectProperty(:P))",
            "Declaration(NamedIndividual(o:Thing))", "Declaration(NamedIndividual(o:Nothing))",
            "ClassAssertion(:A o:Thing)", "ClassAssertion(:P o:Nothing)",
            "SubClassOf(:A :B)", "Declaration(NamedIndividual(:a))",
            "Declaration(ObjectProperty(o:Thing))", "SubClassOf(:B o:Nothing)"];
        let whole = format!("{header}{})", statements.join(" "));
        let scan_all = scan(&whole).unwrap();
        let union = LocalityIndex::build(&whole, &scan_all, false).unwrap();
        for mask in 0usize..1 << statements.len() {
            let text = format!("{header}{})", statements.iter().enumerate()
                .filter(|(n, _)| mask & (1 << n) != 0).map(|(_, s)| *s).collect::<Vec<_>>().join(" "));
            let sc = scan(&text).unwrap(); let enabled: HashSet<_> = sc.statements.iter().map(|s| s.hash).collect();
            let fresh = LocalityIndex::build(&text, &sc, false).unwrap();
            let mut actual: BTreeSet<_> = union.live_public_class_names(|h| enabled.contains(&h))
                .unwrap().into_iter().map(str::to_owned).collect();
            actual.extend(["owl:Thing", "owl:Nothing", "http://www.w3.org/2002/07/owl#Thing",
                "http://www.w3.org/2002/07/owl#Nothing"].into_iter().map(str::to_owned));
            assert_eq!(actual, public_domain(&fresh), "mask={mask}");
        }
        let empty: HashSet<u128> = HashSet::new();
        let names = union.live_public_class_names(|h| empty.contains(&h)).unwrap();
        assert!(!names.contains(&"o:Thing") && !names.contains(&"o:Nothing"), "old-only aliases must disappear");
    }
    #[test]
    fn public_domain_builtin_reference_replay_and_tbox_refusal() {
        let before = "Prefix(:=<urn:public#>) Prefix(o:=<http://www.w3.org/2002/07/owl#>) Ontology(Declaration(Class(:P)) Declaration(NamedIndividual(o:Thing)) ClassAssertion(:P o:Thing))";
        let old_scan = scan(before).unwrap(); let old = LocalityIndex::build(before, &old_scan, false).unwrap();
        let (union, stats) = LocalityIndex::build_reusing_full(before, &old_scan, &old,
            &before[..old_scan.open_end], |h| old_scan.statements.iter().find(|s| s.hash == h).map(|s| &before[s.start..s.end])).unwrap();
        assert_eq!(stats.reused_compiled_axioms, 1);
        let only_assertion = old_scan.statements.iter().filter(|s| s.kind == StmtKind::Assertion).map(|s| s.hash).collect::<HashSet<_>>();
        let actual = union.live_public_class_names(|h| only_assertion.contains(&h)).unwrap();
        assert!(actual.contains(&"o:Thing") && actual.contains(&":P"));
        let tbox = LocalityIndex::build(before, &old_scan, true).unwrap();
        assert!(!tbox.full_mode);
        assert!(tbox.live_public_class_names(|_| true).is_none());
    }
}

#[cfg(test)]
mod told_reuse_tests {
    use super::*;
    fn ontology(body: &str) -> String {
        format!("Prefix(:=<http://e/>) Prefix(q:=<http://e/>) Ontology(<http://e/o> {body})")
    }
    fn reused(old_text: &str, old: &ToldProofs, new_text: &str) -> (ToldProofs, ToldReuse) {
        let old_scan = scan(old_text).unwrap();
        let new_scan = scan(new_text).unwrap();
        let lookup = |hash| old_scan.statements.iter().find(|s| s.hash == hash)
            .map(|s| &old_text[s.start..s.end]);
        ToldProofs::build_reusing(new_text, &new_scan,
            Some((old, &old_text[..old_scan.open_end], &lookup)))
    }
    fn exact_fresh(text: &str, actual: &ToldProofs) {
        let fresh = ToldProofs::build(text, &scan(text).unwrap());
        fn name(graph: &ToldProofs, id: u32) -> &str {
            graph.ids.iter().find(|(_,value)| **value==id).unwrap().0
        }
        fn boolean(graph: &ToldProofs, value: &Told) -> String {
            match value {
                Told::Name(id) => format!("N({})",name(graph,*id)),
                Told::And(v) => format!("And{:?}",v.iter().map(|x|boolean(graph,x)).collect::<Vec<_>>()),
                Told::Or(v) => format!("Or{:?}",v.iter().map(|x|boolean(graph,x)).collect::<Vec<_>>()),
            }
        }
        fn normalized(graph: &ToldProofs) -> (std::collections::BTreeMap<String,String>,Vec<(String,String,u128)>,Vec<(String,String,u128)>) {
            let spellings=graph.spelling.iter().map(|(sp,id)|(sp.to_string(),name(graph,*id).to_owned())).collect();
            let mut edges=Vec::new();
            for (id,row) in graph.edges.iter().enumerate() {
                for (target,tag) in row.iter() {edges.push((name(graph,id as u32).to_owned(),name(graph,*target).to_owned(),*tag));}
            }
            let mut definitions:Vec<_>=graph.definitions.iter().map(|(id,value,tag)|(name(graph,*id).to_owned(),boolean(graph,value),*tag)).collect();
            edges.sort();definitions.sort();(spellings,edges,definitions)
        }
        assert_eq!(actual.ids.keys().collect::<std::collections::BTreeSet<_>>(),fresh.ids.keys().collect::<std::collections::BTreeSet<_>>());
        assert_eq!(normalized(actual),normalized(&fresh));
        assert_eq!(name(actual,actual.thing),name(&fresh,fresh.thing));
        assert_eq!(actual.supports.len(), fresh.supports.len());
        let names = [":A",":B",":C",":D",":X","q:A","http://e/A","http://www.w3.org/2002/07/owl#Thing"];
        for subject in names { for target in names {
            for removed in [crate::fxhash::FxHashSet::default(), actual.supports.iter().take(1).map(|(h,_)|*h).collect()] {
                assert_eq!(actual.proves_all(subject,&[target],&removed),fresh.proves_all(subject,&[target],&removed));
            }
        }}
    }
    #[test]
    fn told_reuse_matches_fresh_add_delete_mixed_and_annotations() {
        let revisions = [
            ontology("SubClassOf(:A :B) EquivalentClasses(:C ObjectIntersectionOf(:A :B))"),
            ontology("SubClassOf(:A :B) EquivalentClasses(:C ObjectIntersectionOf(:A :B)) SubClassOf(:B :D)"),
            ontology("EquivalentClasses(:C ObjectIntersectionOf(:A :B)) SubClassOf(:B :D)"),
            ontology("EquivalentClasses(:C ObjectIntersectionOf(:A :B)) SubClassOf(:A :X)"),
            ontology("AnnotationAssertion(:note :A \"ignored\") EquivalentClasses(:C ObjectIntersectionOf(:A :B)) SubClassOf(:A :X)"),
        ];
        let mut graph = ToldProofs::build(&revisions[0], &scan(&revisions[0]).unwrap());
        for i in 1..revisions.len() {
            let (next, stats) = reused(&revisions[i-1], &graph, &revisions[i]);
            exact_fresh(&revisions[i], &next);
            assert!(stats.reused_statements > 0);
            if i==4 { assert_eq!(stats.parsed_statements,0); }
            graph = next;
        }
    }
    #[test]
    fn told_reuse_replays_spelling_names_and_duplicate_supports_in_new_order() {
        let old = ontology("SubClassOf(:A :B) EquivalentClasses(ObjectIntersectionOf(:A :B) :C) SubClassOf(q:A :D)");
        let graph = ToldProofs::build(&old, &scan(&old).unwrap());
        let new = ontology("SubClassOf(q:A :D) EquivalentClasses(ObjectIntersectionOf(:A :B) :C) SubClassOf(:A :B) SubClassOf(:A :B)");
        let (next, stats) = reused(&old, &graph, &new);
        assert_eq!(stats.parsed_statements,0); assert_eq!(stats.reused_statements,4);
        exact_fresh(&new,&next);
        let partial = ontology("EquivalentClasses(ObjectIntersectionOf(:A :B) :C ObjectUnionOf(:D ObjectSomeValuesFrom(:r :X)) :A)");
        let fresh = ToldProofs::build(&partial,&scan(&partial).unwrap());
        let (next,stats) = reused(&partial,&fresh,&partial);
        assert_eq!(stats.parsed_statements,0);exact_fresh(&partial,&next);
        assert!(next.ids.contains_key("http://e/D")); // touched before unsupported branch.
        assert!(next.proves_all(":C",&[":A",":B"],&crate::fxhash::FxHashSet::default()));
    }
    #[test]
    fn told_reuse_historical_supports_header_and_collision_checks() {
        let old = ontology("SubClassOf(:A :B) SubClassOf(:B :C)");
        let original = ToldProofs::build(&old,&scan(&old).unwrap());
        let deleted = ontology("SubClassOf(:B :C)");
        // Simulate a deletion base retaining the older unmodified told graph.
        let new = ontology("SubClassOf(:B :C) SubClassOf(:C :D)");
        let (next,stats)=reused(&old,&original,&new); // exact original provenance, not `deleted`.
        assert_eq!(stats.reused_statements,1);assert_eq!(stats.parsed_statements,1);
        exact_fresh(&new,&next);assert!(!next.proves_all(":A",&[":B"],&Default::default()));
        let (restored,stats)=reused(&old,&original,&old);
        assert_eq!(stats.reused_statements,2);exact_fresh(&old,&restored);
        let moved=deleted.replace("http://e/","http://other/");
        let (next,stats)=reused(&old,&original,&moved);
        assert_eq!(stats.reused_statements,0);assert_eq!(stats.parsed_statements,1);exact_fresh(&moved,&next);
        let changed=ontology("SubClassOf(:X :D)");let mut forged=scan(&changed).unwrap();
        let old_scan=scan(&old).unwrap();forged.statements[0].hash=old_scan.statements[0].hash;
        let lookup=|hash| old_scan.statements.iter().find(|s|s.hash==hash).map(|s|&old[s.start..s.end]);
        let (next,stats)=ToldProofs::build_reusing(&changed,&forged,Some((&original,&old[..old_scan.open_end],&lookup)));
        assert_eq!(stats.reused_statements,0);assert_eq!(stats.parsed_statements,1);
        assert!(next.proves_all(":X",&[":D"],&Default::default()));assert!(!next.proves_all(":A",&[":B"],&Default::default()));
    }
    #[test]
    fn told_reuse_cow_preserves_older_graph_and_unchanged_owner_rows() {
        let old=ontology("SubClassOf(:A :B) SubClassOf(:X :Y)");
        let graph=ToldProofs::build(&old,&scan(&old).unwrap());
        let snapshot=graph.clone();
        assert!(std::sync::Arc::ptr_eq(&graph.ids,&snapshot.ids));
        let new=ontology("SubClassOf(:B :C) SubClassOf(:X :Y)");
        let (next,stats)=reused(&old,&graph,&new);
        assert_eq!(stats.parsed_statements,1);assert_eq!(stats.reused_statements,1);
        assert!(graph.proves_all(":A",&[":B"],&Default::default()));
        assert!(snapshot.proves_all(":A",&[":B"],&Default::default()));
        assert!(!next.proves_all(":A",&[":B"],&Default::default()));
        assert!(!graph.proves_all(":B",&[":C"],&Default::default()));
        assert!(next.proves_all(":B",&[":C"],&Default::default()));
        assert!(std::sync::Arc::ptr_eq(&graph.edges[graph.ids["http://e/X"] as usize],
            &next.edges[next.ids["http://e/X"] as usize]));
        exact_fresh(&new,&next);exact_fresh(&old,&graph);
    }
    #[test]
    fn told_reuse_ambiguous_published_spellings_rebuild_in_new_order() {
        let old=ontology("SubClassOf(q:A :B)");
        let graph=ToldProofs::build(&old,&scan(&old).unwrap());
        let new=ontology("SubClassOf(<q:A> :C) SubClassOf(q:A :B)");
        let (next,stats)=reused(&old,&graph,&new);
        assert_eq!(stats.reused_statements,0);assert_eq!(stats.parsed_statements,2);
        assert!(next.spelling_conflict);exact_fresh(&new,&next);
        assert!(next.proves_all("q:A",&[":C"],&Default::default()));
        let reordered=ontology("SubClassOf(q:A :B) SubClassOf(<q:A> :C)");
        let (reordered_graph,stats)=reused(&new,&next,&reordered);
        assert_eq!(stats.reused_statements,0);exact_fresh(&reordered,&reordered_graph);
        assert!(reordered_graph.proves_all("q:A",&[":B"],&Default::default()));
        assert!(!reordered_graph.proves_all("q:A",&[":C"],&Default::default()));
    }
    #[test]
    fn told_reuse_large_shrink_compacts_live_graph_without_changing_donor() {
        let old=ontology(&(0..100).map(|i|format!("SubClassOf(:X{i} :Y{i})")).collect::<String>());
        let graph=ToldProofs::build(&old,&scan(&old).unwrap());
        let new=ontology("SubClassOf(:X0 :Y0)");
        let (next,stats)=reused(&old,&graph,&new);
        assert_eq!(stats.parsed_statements,0);assert_eq!(stats.reused_statements,1);
        assert_eq!(next.edges.len(),3);assert_eq!(next.ids.len(),3);
        assert_eq!(graph.ids.len(),201);exact_fresh(&new,&next);
    }
    #[test]
    fn told_reuse_shrinks_removed_duplicate_rule_buffers() {
        let support="EquivalentClasses(:A ObjectIntersectionOf(:B :C))";
        let old=ontology(&support.repeat(200));
        let graph=ToldProofs::build(&old,&scan(&old).unwrap());
        let new=ontology(support);
        let (next,stats)=reused(&old,&graph,&new);
        assert_eq!(stats.parsed_statements,0);assert_eq!(stats.reused_statements,1);
        for row in &next.edges { assert!(row.capacity()<=row.len()*2+64); }
        assert!(next.definitions.capacity()<=next.definitions.len()*2+64);
        assert!(graph.edges[graph.ids["http://e/A"] as usize].len()>100);
        assert!(graph.proves_all(":A",&[":B",":C"],&Default::default()));
        exact_fresh(&new,&next);
    }
    #[test]
    fn told_reuse_many_aliases_shrink_spelling_and_support_buffers() {
        let prefixes=(0..200).map(|i|format!("Prefix(p{i}:=<http://e/>) ")).collect::<String>();
        let header=format!("{prefixes} Prefix(:=<http://e/>) Ontology(<http://e/o> ");
        let old=format!("{header}{})",(0..200).map(|i|format!("SubClassOf(p{i}:A :B) ")).collect::<String>());
        let graph=ToldProofs::build(&old,&scan(&old).unwrap());
        let new=format!("{header}SubClassOf(p0:A :B))");
        let (next,stats)=reused(&old,&graph,&new);
        assert_eq!(stats.parsed_statements,0);assert_eq!(stats.reused_statements,1);
        assert!(next.spelling.capacity()<=next.spelling.len()*2+64);
        assert!(next.spelling_refs.capacity()<=next.spelling_refs.len()*2+64);
        assert!(next.supports.capacity()<=next.supports.len()*2+64);
        assert_eq!(next.edges.len(),3);exact_fresh(&new,&next);
        assert!(graph.spelling.contains_key("p199:A"));
    }
    #[test]
    fn told_reuse_long_replacements_drop_obsolete_names_and_share_supports() {
        let mut text=ontology("SubClassOf(:A :B) SubClassOf(:X0 :Y0)");
        let mut graph=ToldProofs::build(&text,&scan(&text).unwrap());
        for i in 1..100 {
            let new=ontology(&format!("SubClassOf(:A :B) SubClassOf(:X{i} :Y{i})"));
            let (next,stats)=reused(&text,&graph,&new);
            assert_eq!(stats.reused_statements,1);assert_eq!(stats.parsed_statements,1);
            assert!(std::sync::Arc::ptr_eq(&graph.supports[0].1,&next.supports[0].1));
            assert_eq!(next.ids.len(),5);assert_eq!(next.spelling.len(),4);
            assert!(!next.ids.contains_key(format!("http://e/X{}",i-1).as_str()));
            exact_fresh(&new,&next);text=new;graph=next;
        }
    }
}
