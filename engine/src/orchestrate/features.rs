//! Structural + expressivity feature extraction for the routing decision tree.
//!
//! These features are computed BY THE REASONER (`km features <ont>`, and at
//! classify time before routing) so train-time and run-time features come from
//! ONE code path — no Python/Rust drift. They are purely structural (clause-shape
//! + DL-construct profile), never the ontology identity (the no-benchmark-
//! hardcoding rule).
//!
//! Three signal families:
//!   1. clause-shape features over the normalised DL-clause set (streamed, so the
//!      ORE giants never materialise in memory);
//!   2. pre-absorption features — what `KM_ABSORB` would change (the absorbed-vs-
//!      plain / 6246 routing axis): the disjunction profile of the plain vs the
//!      absorbed clause set and their delta;
//!   3. the DL-construct profile (complement, inverse, Q, O, F, datatypes, role
//!      chains, ...) scanned from the OWL functional-syntax source.
//!
//! `km features` prints this as JSON; `route_tree.py` trains a tree on it and
//! `km classify` will consult the learned tree to pick a route.

use std::collections::HashSet;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;
use std::process::{Command, Stdio};

use serde::de::{DeserializeSeed, Deserializer, IgnoredAny, MapAccess, SeqAccess, Visitor};

use crate::json_io::{JAtom, JClause, JTerm};

use super::tmpfile::TempPath;
use super::{Config, OrchestrateError};

// ---------------------------------------------------------------------------
// clause-shape accumulator (Rust port of ont_features.Acc)
// ---------------------------------------------------------------------------
#[derive(Default)]
struct Acc {
    n_clauses: u64,
    concepts: HashSet<String>,
    roles: HashSet<String>,
    n_disj: u64,
    max_disj_w: usize,
    n_top: u64,
    n_top_disj2: u64,
    n_bottom: u64,
    n_bottom2: u64,
    n_exist: u64,
    n_eq: u64,
    n_aux: u64,
    n_horn: u64,
    has_trans: bool,
    n_chain: u64,
    sum_body: u64,
    max_body: usize,
    sum_head: u64,
    max_head: usize,
    top_pairs: HashSet<(String, String)>,
    bot_pairs: HashSet<(String, String)>,
}

fn is_fun(t: &JTerm) -> bool {
    matches!(t, JTerm::Fun { .. })
}
fn is_aux(t: &JTerm) -> bool {
    matches!(t, JTerm::Aux { .. })
}
fn ordered(a: &str, b: &str) -> (String, String) {
    if a <= b {
        (a.to_string(), b.to_string())
    } else {
        (b.to_string(), a.to_string())
    }
}

impl Acc {
    fn add(&mut self, c: &JClause) {
        self.n_clauses += 1;
        let mut bc: Vec<&str> = Vec::new();
        let mut hc: Vec<&str> = Vec::new();
        let mut broles: usize = 0;
        let mut hrole: Option<&str> = None;
        let mut hroles: usize = 0;
        let mut broles_names: Vec<&str> = Vec::new();
        let mut saw_fun = false;
        let mut saw_aux = false;
        let mut saw_eq = false;

        for a in &c.body {
            match a {
                JAtom::Concept { concept, term } => {
                    self.concepts.insert(concept.clone());
                    bc.push(concept);
                    if is_fun(term) {
                        saw_fun = true;
                    }
                    if is_aux(term) {
                        saw_aux = true;
                    }
                }
                JAtom::Role { role, source, target } => {
                    self.roles.insert(role.clone());
                    broles += 1;
                    broles_names.push(role);
                    for t in [source, target] {
                        if is_fun(t) {
                            saw_fun = true;
                        }
                        if is_aux(t) {
                            saw_aux = true;
                        }
                    }
                }
                JAtom::Eq { .. } => saw_eq = true,
            }
        }
        for a in &c.head {
            match a {
                JAtom::Concept { concept, term } => {
                    self.concepts.insert(concept.clone());
                    hc.push(concept);
                    if is_fun(term) {
                        saw_fun = true;
                    }
                    if is_aux(term) {
                        saw_aux = true;
                    }
                }
                JAtom::Role { role, source, target } => {
                    self.roles.insert(role.clone());
                    hroles += 1;
                    hrole = Some(role);
                    for t in [source, target] {
                        if is_fun(t) {
                            saw_fun = true;
                        }
                        if is_aux(t) {
                            saw_aux = true;
                        }
                    }
                }
                JAtom::Eq { .. } => saw_eq = true,
            }
        }

        let nb = c.body.len();
        let nh = c.head.len();
        self.sum_body += nb as u64;
        self.max_body = self.max_body.max(nb);
        self.sum_head += nh as u64;
        self.max_head = self.max_head.max(nh);
        if saw_fun {
            self.n_exist += 1;
        }
        if saw_aux {
            self.n_aux += 1;
        }
        if saw_eq {
            self.n_eq += 1;
        }

        if hc.len() >= 2 {
            self.n_disj += 1;
            self.max_disj_w = self.max_disj_w.max(hc.len());
        }
        if hc.len() <= 1 {
            self.n_horn += 1;
        }
        if nb == 0 {
            self.n_top += 1;
            if hc.len() == 2 {
                self.n_top_disj2 += 1;
                self.top_pairs.insert(ordered(hc[0], hc[1]));
            }
        }
        if nh == 0 {
            self.n_bottom += 1;
            if bc.len() == 2 {
                self.n_bottom2 += 1;
                self.bot_pairs.insert(ordered(bc[0], bc[1]));
            }
        }

        // transitivity / role chains: r(x,y) & s(y,z) -> t(x,z), no head concept
        if broles == 2 && hroles == 1 && hc.is_empty() {
            self.n_chain += 1;
            if let Some(r) = hrole {
                if broles_names.len() == 2 && broles_names[0] == r && broles_names[1] == r {
                    self.has_trans = true;
                }
            }
        }
    }

    fn n_compl_definer(&self) -> u64 {
        self.top_pairs.intersection(&self.bot_pairs).count() as u64
    }
}

// ---------------------------------------------------------------------------
// streaming clause reader: deserialize `{"clauses":[...], ...}` one clause at a
// time (O(1) memory; the giants are 450-580 MB / multi-million clauses).
// ---------------------------------------------------------------------------
struct StreamClauses<'a>(&'a mut Acc);
impl<'de, 'a> DeserializeSeed<'de> for StreamClauses<'a> {
    type Value = ();
    fn deserialize<D: Deserializer<'de>>(self, d: D) -> Result<(), D::Error> {
        struct MapV<'a>(&'a mut Acc);
        impl<'de, 'a> Visitor<'de> for MapV<'a> {
            type Value = ();
            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                f.write_str("a clause-set object")
            }
            fn visit_map<M: MapAccess<'de>>(self, mut m: M) -> Result<(), M::Error> {
                while let Some(k) = m.next_key::<String>()? {
                    if k == "clauses" {
                        m.next_value_seed(SeqSeed(&mut *self.0))?;
                    } else {
                        m.next_value::<IgnoredAny>()?;
                    }
                }
                Ok(())
            }
        }
        d.deserialize_map(MapV(self.0))
    }
}
struct SeqSeed<'a>(&'a mut Acc);
impl<'de, 'a> DeserializeSeed<'de> for SeqSeed<'a> {
    type Value = ();
    fn deserialize<D: Deserializer<'de>>(self, d: D) -> Result<(), D::Error> {
        struct SeqV<'a>(&'a mut Acc);
        impl<'de, 'a> Visitor<'de> for SeqV<'a> {
            type Value = ();
            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                f.write_str("a clause array")
            }
            fn visit_seq<S: SeqAccess<'de>>(self, mut s: S) -> Result<(), S::Error> {
                while let Some(c) = s.next_element::<JClause>()? {
                    self.0.add(&c);
                }
                Ok(())
            }
        }
        d.deserialize_seq(SeqV(self.0))
    }
}

fn stream_acc(path: &Path) -> Result<Acc, OrchestrateError> {
    let mut acc = Acc::default();
    let rdr = BufReader::new(File::open(path)?);
    let mut de = serde_json::Deserializer::from_reader(rdr);
    StreamClauses(&mut acc).deserialize(&mut de)?;
    Ok(acc)
}

// ---------------------------------------------------------------------------
// ofn runner (a given KM_ABSORB; optional --meta)
// ---------------------------------------------------------------------------
fn run_ofn(cfg: &Config, ont: &Path, absorb: bool, meta: Option<&Path>) -> (Option<TempPath>, i32) {
    let clauses = TempPath::new(".feat.clauses.json");
    let (prog, pre) = cfg.ofn_cmd();
    let mut cmd = Command::new(&prog);
    cmd.args(&pre).arg(ont);
    if let Some(m) = meta {
        cmd.arg("--meta").arg(m);
    }
    let f = match File::create(clauses.path()) {
        Ok(f) => f,
        Err(_) => return (None, -1),
    };
    cmd.stdin(Stdio::null())
        .stdout(f)
        .stderr(Stdio::null())
        .env("KM_ABSORB", if absorb { "1" } else { "0" });
    match cmd.status() {
        Ok(st) => {
            let code = st.code().unwrap_or(-1);
            (Some(clauses), code)
        }
        Err(_) => (None, -1),
    }
}

#[derive(serde::Deserialize, Default)]
struct Meta {
    #[serde(default)]
    named: Vec<String>,
    #[serde(default)]
    declared: Vec<String>,
    #[serde(default)]
    el_rbox_safe: bool,
}

// ---------------------------------------------------------------------------
// DL-construct profile: count `Keyword(` occurrences in the functional-syntax
// source (streamed line by line). Purely structural expressivity signal.
// ---------------------------------------------------------------------------
#[derive(Default)]
struct Constructs {
    complement: u64,
    union: u64,
    inverse: u64,
    qcard: u64,
    nominal: u64,
    functional: u64,
    trans: u64,
    chain: u64,
    role_hier: u64,
    datatype: u64,
    forall: u64,
    exists: u64,
    has_self: u64,
    has_key: u64,
    rule: u64,
    disjoint: u64,
    equiv: u64,
    subclass: u64,
    abox: u64,
}

/// `(keyword, &mut field)` families. Each keyword is matched as `Keyword(` so an
/// IRI that merely contains the word is not counted.
fn scan_constructs(ont: &Path) -> Constructs {
    // family -> its functional-syntax keywords
    const FAMILIES: &[(&str, &[&str])] = &[
        ("complement", &["ObjectComplementOf", "DataComplementOf"]),
        ("union", &["ObjectUnionOf", "DisjointUnion"]),
        ("inverse", &["ObjectInverseOf", "InverseObjectProperties", "InverseFunctionalObjectProperty"]),
        (
            "qcard",
            &[
                "ObjectMinCardinality",
                "ObjectMaxCardinality",
                "ObjectExactCardinality",
                "DataMinCardinality",
                "DataMaxCardinality",
                "DataExactCardinality",
            ],
        ),
        ("nominal", &["ObjectOneOf", "ObjectHasValue", "DataHasValue"]),
        ("functional", &["FunctionalObjectProperty", "InverseFunctionalObjectProperty", "FunctionalDataProperty"]),
        ("trans", &["TransitiveObjectProperty"]),
        ("chain", &["ObjectPropertyChain"]),
        ("role_hier", &["SubObjectPropertyOf", "SubDataPropertyOf"]),
        (
            "datatype",
            &[
                "DataSomeValuesFrom",
                "DataAllValuesFrom",
                "DataHasValue",
                "DatatypeRestriction",
                "DataMinCardinality",
                "DataMaxCardinality",
                "DataExactCardinality",
            ],
        ),
        ("forall", &["ObjectAllValuesFrom"]),
        ("exists", &["ObjectSomeValuesFrom"]),
        ("self", &["ObjectHasSelf"]),
        ("key", &["HasKey"]),
        ("rule", &["DLSafeRule"]),
        ("disjoint", &["DisjointClasses", "DisjointUnion", "DisjointObjectProperties", "DisjointDataProperties"]),
        ("equiv", &["EquivalentClasses"]),
        ("subclass", &["SubClassOf"]),
        (
            "abox",
            &[
                "ClassAssertion",
                "ObjectPropertyAssertion",
                "NegativeObjectPropertyAssertion",
                "DataPropertyAssertion",
                "SameIndividual",
                "DifferentIndividuals",
            ],
        ),
    ];
    let mut counts: std::collections::HashMap<&str, u64> = std::collections::HashMap::new();
    let file = match File::open(ont) {
        Ok(f) => f,
        Err(_) => return Constructs::default(),
    };
    let rdr = BufReader::new(file);
    for line in rdr.lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => continue, // non-UTF8 line: skip (functional syntax is ASCII)
        };
        for (fam, kws) in FAMILIES {
            let mut c = 0u64;
            for kw in *kws {
                c += count_token(&line, kw);
            }
            if c > 0 {
                *counts.entry(*fam).or_insert(0) += c;
            }
        }
    }
    let g = |k: &str| counts.get(k).copied().unwrap_or(0);
    Constructs {
        complement: g("complement"),
        union: g("union"),
        inverse: g("inverse"),
        qcard: g("qcard"),
        nominal: g("nominal"),
        functional: g("functional"),
        trans: g("trans"),
        chain: g("chain"),
        role_hier: g("role_hier"),
        datatype: g("datatype"),
        forall: g("forall"),
        exists: g("exists"),
        has_self: g("self"),
        has_key: g("key"),
        rule: g("rule"),
        disjoint: g("disjoint"),
        equiv: g("equiv"),
        subclass: g("subclass"),
        abox: g("abox"),
    }
}

/// Count occurrences of `kw` immediately followed by `(` in `line`.
fn count_token(line: &str, kw: &str) -> u64 {
    let mut n = 0u64;
    let mut start = 0usize;
    while let Some(i) = line[start..].find(kw) {
        let at = start + i;
        let after = at + kw.len();
        if line[after..].starts_with('(') {
            n += 1;
        }
        start = after;
    }
    n
}

// ---------------------------------------------------------------------------
// the feature vector
// ---------------------------------------------------------------------------
#[derive(serde::Serialize)]
pub struct Features {
    pub ont: String,
    pub status: String,
    // --- clause-shape (plain / KM_ABSORB=0 base) ---
    pub n_clauses: u64,
    pub n_concept: u64,
    pub n_role: u64,
    pub n_named: u64,
    pub n_declared: u64,
    pub n_disj: u64,
    pub max_disj_width: usize,
    pub frac_disj: f64,
    pub n_top: u64,
    pub n_top_disj2: u64,
    pub n_bottom: u64,
    pub n_bottom2: u64,
    pub n_compl_definer: u64,
    pub n_exist: u64,
    pub frac_exist: f64,
    pub n_eq: u64,
    pub n_aux: u64,
    pub n_horn: u64,
    pub frac_horn: f64,
    pub is_pure_horn: u8,
    pub has_trans: u8,
    pub n_chain: u64,
    pub avg_body_len: f64,
    pub max_body_len: usize,
    pub avg_head_len: f64,
    pub max_head_len: usize,
    pub el_rbox_safe: u8,
    // --- pre-absorption (what KM_ABSORB would change: absorbed-vs-plain axis) ---
    pub n_clauses_absorbed: u64,
    pub n_disj_absorbed: u64,
    pub n_top_disj2_absorbed: u64,
    pub n_compl_definer_absorbed: u64,
    pub disj_removed_by_absorb: i64,
    pub frac_disj_removed: f64,
    pub clauses_delta_absorb: i64,
    // --- DL-construct profile (from the functional-syntax source) ---
    pub c_complement: u64,
    pub c_union: u64,
    pub c_inverse: u64,
    pub c_qcard: u64,
    pub c_nominal: u64,
    pub c_functional: u64,
    pub c_trans: u64,
    pub c_chain: u64,
    pub c_role_hier: u64,
    pub c_datatype: u64,
    pub c_forall: u64,
    pub c_exists: u64,
    pub c_self: u64,
    pub c_haskey: u64,
    pub c_rule: u64,
    pub c_disjoint: u64,
    pub c_equiv: u64,
    pub c_subclass: u64,
    pub c_abox: u64,
    // routing-critical expressivity flags (the DL "letters")
    pub has_complement: u8,
    pub has_inverse: u8,
    pub has_qcard: u8,
    pub has_nominal: u8,
    pub has_functional: u8,
    pub has_datatype: u8,
    pub has_chain: u8,
    pub has_role_hier: u8,
    pub has_self: u8,
    pub has_keys: u8,
    pub has_rules: u8,
    pub has_abox: u8,
}

fn r5(x: f64) -> f64 {
    (x * 1e5).round() / 1e5
}
fn r4(x: f64) -> f64 {
    (x * 1e4).round() / 1e4
}
fn b(x: u64) -> u8 {
    u8::from(x > 0)
}

/// Compute the feature vector for `ont`. Runs the frontend (plain, and absorbed
/// iff the plain set has disjunctions) and scans the source for the DL profile.
pub fn extract(cfg: &Config, ont: &Path) -> Features {
    let name = ont
        .file_name()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_default();
    let con = scan_constructs(ont);

    let blank = |status: &str| Features {
        ont: name.clone(),
        status: status.to_string(),
        n_clauses: 0,
        n_concept: 0,
        n_role: 0,
        n_named: 0,
        n_declared: 0,
        n_disj: 0,
        max_disj_width: 0,
        frac_disj: 0.0,
        n_top: 0,
        n_top_disj2: 0,
        n_bottom: 0,
        n_bottom2: 0,
        n_compl_definer: 0,
        n_exist: 0,
        frac_exist: 0.0,
        n_eq: 0,
        n_aux: 0,
        n_horn: 0,
        frac_horn: 0.0,
        is_pure_horn: 0,
        has_trans: 0,
        n_chain: 0,
        avg_body_len: 0.0,
        max_body_len: 0,
        avg_head_len: 0.0,
        max_head_len: 0,
        el_rbox_safe: 0,
        n_clauses_absorbed: 0,
        n_disj_absorbed: 0,
        n_top_disj2_absorbed: 0,
        n_compl_definer_absorbed: 0,
        disj_removed_by_absorb: 0,
        frac_disj_removed: 0.0,
        clauses_delta_absorb: 0,
        c_complement: con.complement,
        c_union: con.union,
        c_inverse: con.inverse,
        c_qcard: con.qcard,
        c_nominal: con.nominal,
        c_functional: con.functional,
        c_trans: con.trans,
        c_chain: con.chain,
        c_role_hier: con.role_hier,
        c_datatype: con.datatype,
        c_forall: con.forall,
        c_exists: con.exists,
        c_self: con.has_self,
        c_haskey: con.has_key,
        c_rule: con.rule,
        c_disjoint: con.disjoint,
        c_equiv: con.equiv,
        c_subclass: con.subclass,
        c_abox: con.abox,
        has_complement: b(con.complement),
        has_inverse: b(con.inverse),
        has_qcard: b(con.qcard),
        has_nominal: b(con.nominal),
        has_functional: b(con.functional),
        has_datatype: b(con.datatype),
        has_chain: b(con.chain),
        has_role_hier: b(con.role_hier),
        has_self: b(con.has_self),
        has_keys: b(con.has_key),
        has_rules: b(con.rule),
        has_abox: b(con.abox),
    };

    if !ont.exists() {
        return blank("no_ont");
    }
    let meta_tmp = TempPath::new(".feat.meta.json");
    let (plain, code) = run_ofn(cfg, ont, false, Some(meta_tmp.path()));
    if code == 3 {
        return blank("ofn_unsupported");
    }
    if code != 0 {
        return blank("ofn_fail");
    }
    let plain = match plain {
        Some(p) => p,
        None => return blank("ofn_fail"),
    };
    let meta: Meta = File::open(meta_tmp.path())
        .ok()
        .and_then(|f| serde_json::from_reader(BufReader::new(f)).ok())
        .unwrap_or_default();
    let acc = match stream_acc(plain.path()) {
        Ok(a) => a,
        Err(_) => return blank("parse_fail"),
    };

    let mut f = blank("ok");
    let n = acc.n_clauses.max(1) as f64;
    f.n_clauses = acc.n_clauses;
    f.n_concept = acc.concepts.len() as u64;
    f.n_role = acc.roles.len() as u64;
    f.n_named = meta.named.len() as u64;
    f.n_declared = meta.declared.len() as u64;
    f.n_disj = acc.n_disj;
    f.max_disj_width = acc.max_disj_w;
    f.frac_disj = r5(acc.n_disj as f64 / n);
    f.n_top = acc.n_top;
    f.n_top_disj2 = acc.n_top_disj2;
    f.n_bottom = acc.n_bottom;
    f.n_bottom2 = acc.n_bottom2;
    f.n_compl_definer = acc.n_compl_definer();
    f.n_exist = acc.n_exist;
    f.frac_exist = r5(acc.n_exist as f64 / n);
    f.n_eq = acc.n_eq;
    f.n_aux = acc.n_aux;
    f.n_horn = acc.n_horn;
    f.frac_horn = r5(acc.n_horn as f64 / n);
    f.is_pure_horn = u8::from(acc.n_disj == 0);
    f.has_trans = u8::from(acc.has_trans);
    f.n_chain = acc.n_chain;
    f.avg_body_len = r4(acc.sum_body as f64 / n);
    f.max_body_len = acc.max_body;
    f.avg_head_len = r4(acc.sum_head as f64 / n);
    f.max_head_len = acc.max_head;
    f.el_rbox_safe = u8::from(meta.el_rbox_safe);

    // pre-absorption: only run the absorbed pass when there is something for
    // absorption to act on (a disjunction); otherwise it is a no-op (EL/Horn).
    if acc.n_disj > 0 {
        let (absorbed, acode) = run_ofn(cfg, ont, true, None);
        if acode == 0 {
            if let Some(ap) = absorbed {
                if let Ok(aa) = stream_acc(ap.path()) {
                    f.n_clauses_absorbed = aa.n_clauses;
                    f.n_disj_absorbed = aa.n_disj;
                    f.n_top_disj2_absorbed = aa.n_top_disj2;
                    f.n_compl_definer_absorbed = aa.n_compl_definer();
                    f.disj_removed_by_absorb = acc.n_disj as i64 - aa.n_disj as i64;
                    f.frac_disj_removed = r5(f.disj_removed_by_absorb as f64 / acc.n_disj.max(1) as f64);
                    f.clauses_delta_absorb = aa.n_clauses as i64 - acc.n_clauses as i64;
                }
            }
        }
    } else {
        // no disjunctions: absorption changes nothing -> absorbed == plain.
        f.n_clauses_absorbed = acc.n_clauses;
    }
    f
}
