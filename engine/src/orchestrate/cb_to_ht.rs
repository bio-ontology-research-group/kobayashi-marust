//! Convert CB DL-clauses into HT-clauses (the tableau `TInput`). A faithful port
//! of `engine/py/cb_to_ht.py`: the only transform is *reverse Skolemization*
//! (a function symbol `f` from `Body → r(x,f(x))` + `Body → C_i(f(x))` becomes
//! the HT existential `Body → ∃r.fil(x)`), plus RBox edge clauses, the ≥n/≤n
//! slot/eq encodings, nominal fencing, the Horrocks-Sattler transitivity
//! propagation, and the `KM_HT_EMELIM` complementary-definer elimination.
//!
//! Byte-identity with the Python reference depends on two things, both preserved
//! here: concept/role ids are assigned in FIRST-SEEN (insertion) order, and the
//! HT-clauses are emitted in exactly the same pass order.

use std::collections::HashMap;

use crate::json_io::{JAtom, JClause, JTerm};

// ---------------------------------------------------------------------------
// output (TInput) types
// ---------------------------------------------------------------------------
#[derive(serde::Serialize, Clone)]
#[serde(tag = "k")]
pub enum HAtom {
    #[serde(rename = "c")]
    Concept { neg: bool, c: usize, t: usize },
    #[serde(rename = "r")]
    Role { r: usize, s: usize, t: usize },
    #[serde(rename = "eq")]
    Eq { s: usize, t: usize },
    #[serde(rename = "e")]
    Exist { r: usize, neg: bool, c: usize, t: usize },
}

#[derive(serde::Serialize, Clone)]
pub struct HtClause {
    pub body: Vec<HAtom>,
    pub head: Vec<HAtom>,
}

#[derive(serde::Serialize, Clone)]
pub struct Fenced {
    pub reason: String,
    pub detail: String,
}

#[derive(serde::Serialize)]
pub struct TInput {
    pub concepts: Vec<String>,
    pub roles: Vec<String>,
    pub clauses: Vec<HtClause>,
    pub queries: Vec<usize>,
    pub dropped: usize,
    pub fenced: Vec<Fenced>,
    pub inverse: bool,
    pub number: bool,
    pub nominals: Vec<usize>,
}

// ---------------------------------------------------------------------------
// name helpers (mirror cb_to_ht.short / is_internal / is_bottom)
// ---------------------------------------------------------------------------
fn short(n: &str) -> &str {
    let after_hash = n.rsplit('#').next().unwrap_or(n);
    after_hash.rsplit('/').next().unwrap_or(after_hash)
}
fn is_bottom(n: &str) -> bool {
    let s = short(n);
    s == "Nothing" || s == "owl:Nothing"
}
fn is_internal(n: &str) -> bool {
    let s = short(n);
    s.starts_with("Q_")
        || s.starts_with("__")
        || s.starts_with("aux_")
        || s.starts_with("def_")
        || (s.contains(':') && s != "Nothing" && s != "owl:Nothing")
}

fn term_is_fun(t: &JTerm) -> bool {
    matches!(t, JTerm::Fun { .. })
}
/// `f(x)` only (arg must be var x); else None.
fn fun_sym(t: &JTerm) -> Option<&str> {
    if let JTerm::Fun { function, arg } = t {
        if let JTerm::Var { name } = arg.as_ref() {
            if name == "x" {
                return Some(function);
            }
        }
    }
    None
}
fn atom_has_fun(a: &JAtom) -> bool {
    match a {
        JAtom::Concept { term, .. } => term_is_fun(term),
        JAtom::Role { source, target, .. } => term_is_fun(source) || term_is_fun(target),
        JAtom::Eq { .. } => true, // treat as non-ALC
    }
}
/// f(x) ≈ g(x) between two Skolem function terms -> (f, g), else None.
fn eq_fun_pair(a: &JAtom) -> Option<(String, String)> {
    if let JAtom::Eq { left, right } = a {
        if let (Some(fi), Some(fj)) = (fun_sym(left), fun_sym(right)) {
            return Some((fi.to_string(), fj.to_string()));
        }
    }
    None
}

// ---------------------------------------------------------------------------
// id registries (first-seen order)
// ---------------------------------------------------------------------------
struct Ids {
    con_names: Vec<String>,
    con_id: HashMap<String, usize>,
    rol_names: Vec<String>,
    rol_id: HashMap<String, usize>,
}
impl Ids {
    fn new() -> Ids {
        Ids { con_names: Vec::new(), con_id: HashMap::new(), rol_names: Vec::new(), rol_id: HashMap::new() }
    }
    fn cid(&mut self, n: &str) -> usize {
        if let Some(&i) = self.con_id.get(n) {
            return i;
        }
        let i = self.con_names.len();
        self.con_names.push(n.to_string());
        self.con_id.insert(n.to_string(), i);
        i
    }
    fn rid(&mut self, n: &str) -> usize {
        if let Some(&i) = self.rol_id.get(n) {
            return i;
        }
        let i = self.rol_names.len();
        self.rol_names.push(n.to_string());
        self.rol_id.insert(n.to_string(), i);
        i
    }
}

fn mk_varmap() -> HashMap<String, usize> {
    let mut m = HashMap::new();
    m.insert("x".to_string(), 0);
    m
}
fn vnum(vm: &mut HashMap<String, usize>, name: &str) -> usize {
    if let Some(&v) = vm.get(name) {
        return v;
    }
    let nv = vm.values().copied().max().map(|m| m + 1).unwrap_or(0);
    vm.insert(name.to_string(), nv);
    nv
}

struct ExjRec {
    body: Vec<JAtom>,
    role: Option<String>,
    fillers: Vec<String>,
    ok: bool,
}

/// insertion-ordered multimap (role name -> concept list), mirroring Python dict
struct OrderedMM {
    keys: Vec<String>,
    vals: HashMap<String, Vec<String>>,
}
impl OrderedMM {
    fn new() -> OrderedMM {
        OrderedMM { keys: Vec::new(), vals: HashMap::new() }
    }
    fn push(&mut self, k: &str, v: &str) {
        if !self.vals.contains_key(k) {
            self.keys.push(k.to_string());
            self.vals.insert(k.to_string(), Vec::new());
        }
        self.vals.get_mut(k).unwrap().push(v.to_string());
    }
    fn get(&self, k: &str) -> &[String] {
        self.vals.get(k).map(|v| v.as_slice()).unwrap_or(&[])
    }
    fn iter(&self) -> impl Iterator<Item = (&String, &Vec<String>)> {
        self.keys.iter().map(move |k| (k, self.vals.get(k).unwrap()))
    }
}

// ---------------------------------------------------------------------------
// convert
// ---------------------------------------------------------------------------
pub fn convert(clauses: &[JClause], rbox: Option<&[Vec<String>]>, named: &std::collections::HashSet<String>) -> TInput {
    let mut ids = Ids::new();
    let mut dropped: usize = 0;
    let mut ht: Vec<HtClause> = Vec::new();

    // exj as an insertion-ordered map: f -> ExjRec
    let mut exj_order: Vec<String> = Vec::new();
    let mut exj: HashMap<String, ExjRec> = HashMap::new();

    let mut passthrough: Vec<JClause> = Vec::new();
    let mut eq_clauses: Vec<JClause> = Vec::new();
    let mut distinct_pairs: Vec<(String, String)> = Vec::new();

    // ---- pass 1: collect existential-introduction clauses by function symbol ----
    for c in clauses {
        let mut head_funs: Vec<String> = Vec::new();
        for a in &c.head {
            match a {
                JAtom::Concept { term, .. } => {
                    if let Some(f) = fun_sym(term) {
                        if !head_funs.iter().any(|x| x == f) {
                            head_funs.push(f.to_string());
                        }
                    }
                }
                JAtom::Role { source, target, .. } => {
                    for t in [source, target] {
                        if let Some(f) = fun_sym(t) {
                            if !head_funs.iter().any(|x| x == f) {
                                head_funs.push(f.to_string());
                            }
                        }
                    }
                }
                JAtom::Eq { .. } => {}
            }
        }
        if !head_funs.is_empty() {
            if c.body.iter().any(atom_has_fun) || head_funs.len() != 1 {
                dropped += 1;
                continue;
            }
            let f = head_funs.pop().unwrap();
            if !exj.contains_key(&f) {
                exj_order.push(f.clone());
                exj.insert(
                    f.clone(),
                    ExjRec { body: c.body.clone(), role: None, fillers: Vec::new(), ok: true },
                );
            }
            let rec = exj.get_mut(&f).unwrap();
            for a in &c.head {
                match a {
                    JAtom::Role { role, source, target } if fun_sym(target) == Some(f.as_str()) => {
                        let src_is_x = matches!(source, JTerm::Var { name } if name == "x");
                        if src_is_x {
                            if rec.role.is_some() && rec.role.as_deref() != Some(role.as_str()) {
                                rec.ok = false;
                            }
                            rec.role = Some(role.clone());
                        } else {
                            rec.ok = false;
                        }
                    }
                    JAtom::Concept { concept, term } if fun_sym(term) == Some(f.as_str()) => {
                        rec.fillers.push(concept.clone());
                    }
                    _ => {
                        rec.ok = false;
                    }
                }
            }
            continue;
        }
        // ---- no head function symbols ----
        let body_eq_pairs: Vec<(String, String)> = c.body.iter().filter_map(eq_fun_pair).collect();
        if !body_eq_pairs.is_empty() && c.head.is_empty() {
            distinct_pairs.extend(body_eq_pairs);
        } else if c.body.iter().any(atom_has_fun) {
            dropped += 1;
        } else if c.head.iter().chain(c.body.iter()).any(|a| matches!(a, JAtom::Eq { .. })) {
            eq_clauses.push(c.clone());
        } else {
            passthrough.push(c.clone());
        }
    }

    let mut funcs_needing_slot: std::collections::HashSet<String> = std::collections::HashSet::new();
    for (fi, fj) in &distinct_pairs {
        funcs_needing_slot.insert(fi.clone());
        funcs_needing_slot.insert(fj.clone());
    }

    // ---- parse the RBox ----
    let mut fenced: Vec<Fenced> = Vec::new();
    let mut subrole_pairs: Vec<(String, String)> = Vec::new();
    let mut inverse_pairs: Vec<(String, String)> = Vec::new();
    let mut domains = OrderedMM::new();
    let mut ranges = OrderedMM::new();
    if let Some(rb) = rbox {
        for ax in rb {
            match ax.first().map(String::as_str) {
                Some("subrole") => subrole_pairs.push((ax[1].clone(), ax[2].clone())),
                Some("inverse") => inverse_pairs.push((ax[1].clone(), ax[2].clone())),
                Some("domain") => domains.push(&ax[1], &ax[2]),
                Some("range") => ranges.push(&ax[1], &ax[2]),
                Some("fenced") => fenced.push(Fenced { reason: ax[1].clone(), detail: ax[2].clone() }),
                _ => fenced.push(Fenced { reason: "unknown-rbox".into(), detail: format!("{:?}", ax) }),
            }
        }
    }

    // reflexive-transitive super-role closure
    let super_roles = |r: &str| -> Vec<String> {
        let mut seen: Vec<String> = vec![r.to_string()];
        let mut frontier: Vec<String> = vec![r.to_string()];
        while let Some(cur) = frontier.pop() {
            for (sub, sup) in &subrole_pairs {
                if *sub == cur && !seen.iter().any(|s| s == sup) {
                    seen.push(sup.clone());
                    frontier.push(sup.clone());
                }
            }
        }
        seen
    };

    // ---- emit existentials ----
    for f in &exj_order {
        let rec = &exj[f];
        if !rec.ok || rec.role.is_none() || rec.fillers.is_empty() {
            dropped += 1;
            continue;
        }
        let mut vm = mk_varmap();
        let mut bod: Vec<HAtom> = Vec::new();
        let mut bad = false;
        for a in &rec.body {
            match a {
                JAtom::Concept { concept, term: JTerm::Var { name } } => {
                    let v = vnum(&mut vm, name);
                    bod.push(HAtom::Concept { neg: false, c: ids.cid(concept), t: v });
                }
                JAtom::Role { role, source: JTerm::Var { name: sn }, target: JTerm::Var { name: tn } } => {
                    let s = vnum(&mut vm, sn);
                    let t = vnum(&mut vm, tn);
                    bod.push(HAtom::Role { r: ids.rid(role), s, t });
                }
                _ => bad = true,
            }
        }
        if bad {
            dropped += 1;
            continue;
        }
        let mut fillers = rec.fillers.clone();
        if funcs_needing_slot.contains(f) {
            fillers.push(format!("__slot__{}", f));
        }
        let fil = if fillers.len() == 1 && !is_bottom(&fillers[0]) {
            ids.cid(&fillers[0])
        } else {
            let dname = format!("def_exfil_{}", f);
            let fil = ids.cid(&dname);
            for cn in &fillers {
                if is_bottom(cn) {
                    ht.push(HtClause {
                        body: vec![HAtom::Concept { neg: false, c: ids.cid(&dname), t: 0 }],
                        head: vec![],
                    });
                } else {
                    let cc = ids.cid(cn);
                    ht.push(HtClause {
                        body: vec![HAtom::Concept { neg: false, c: ids.cid(&dname), t: 0 }],
                        head: vec![HAtom::Concept { neg: false, c: cc, t: 0 }],
                    });
                }
            }
            fil
        };
        let role = rec.role.as_ref().unwrap();
        let rrole = ids.rid(role);
        ht.push(HtClause { body: bod.clone(), head: vec![HAtom::Exist { r: rrole, neg: false, c: fil, t: 0 }] });
        // domain-obligation propagation
        for sup in super_roles(role) {
            let ds: Vec<String> = domains.get(&sup).to_vec();
            for d in ds {
                let dc = ids.cid(&d);
                ht.push(HtClause { body: bod.clone(), head: vec![HAtom::Concept { neg: false, c: dc, t: 0 }] });
            }
        }
    }

    // slot disjointness
    for (fi, fj) in &distinct_pairs {
        let ci = ids.cid(&format!("__slot__{}", fi));
        let cj = ids.cid(&format!("__slot__{}", fj));
        ht.push(HtClause {
            body: vec![
                HAtom::Concept { neg: false, c: ci, t: 0 },
                HAtom::Concept { neg: false, c: cj, t: 0 },
            ],
            head: vec![],
        });
    }

    // ---- passthrough (function-free) clauses ----
    for c in &passthrough {
        let mut vm = mk_varmap();
        let mut bod: Vec<HAtom> = Vec::new();
        let mut hed: Vec<HAtom> = Vec::new();
        let mut bad = false;
        for a in &c.body {
            match a {
                JAtom::Concept { concept, term: JTerm::Var { name } } => {
                    let v = vnum(&mut vm, name);
                    bod.push(HAtom::Concept { neg: false, c: ids.cid(concept), t: v });
                }
                JAtom::Role { role, source: JTerm::Var { name: sn }, target: JTerm::Var { name: tn } } => {
                    let s = vnum(&mut vm, sn);
                    let t = vnum(&mut vm, tn);
                    bod.push(HAtom::Role { r: ids.rid(role), s, t });
                }
                _ => bad = true,
            }
        }
        for a in &c.head {
            match a {
                JAtom::Concept { concept, term: JTerm::Var { name } } => {
                    if is_bottom(concept) {
                        continue;
                    }
                    let v = vnum(&mut vm, name);
                    hed.push(HAtom::Concept { neg: false, c: ids.cid(concept), t: v });
                }
                JAtom::Role { role, source: JTerm::Var { name: sn }, target: JTerm::Var { name: tn } } => {
                    let s = vnum(&mut vm, sn);
                    let t = vnum(&mut vm, tn);
                    hed.push(HAtom::Role { r: ids.rid(role), s, t });
                }
                _ => bad = true,
            }
        }
        if bad {
            dropped += 1;
            continue;
        }
        ht.push(HtClause { body: bod, head: hed });
    }

    // ---- eq clauses (≤n / functional / inverse-functional) ----
    let mut number = false;
    for c in &eq_clauses {
        let mut vm = mk_varmap();
        let mut bod: Vec<HAtom> = Vec::new();
        let mut hed: Vec<HAtom> = Vec::new();
        let mut bad = false;
        for a in &c.body {
            match a {
                JAtom::Concept { concept, term: JTerm::Var { name } } => {
                    let v = vnum(&mut vm, name);
                    bod.push(HAtom::Concept { neg: false, c: ids.cid(concept), t: v });
                }
                JAtom::Role { role, source: JTerm::Var { name: sn }, target: JTerm::Var { name: tn } } => {
                    let s = vnum(&mut vm, sn);
                    let t = vnum(&mut vm, tn);
                    bod.push(HAtom::Role { r: ids.rid(role), s, t });
                }
                JAtom::Eq { left: JTerm::Var { name: ln }, right: JTerm::Var { name: rn } } => {
                    let s = vnum(&mut vm, ln);
                    let t = vnum(&mut vm, rn);
                    bod.push(HAtom::Eq { s, t });
                }
                _ => bad = true,
            }
        }
        for a in &c.head {
            match a {
                JAtom::Eq { left: JTerm::Var { name: ln }, right: JTerm::Var { name: rn } } => {
                    let s = vnum(&mut vm, ln);
                    let t = vnum(&mut vm, rn);
                    hed.push(HAtom::Eq { s, t });
                }
                JAtom::Concept { concept, term: JTerm::Var { name } } => {
                    if is_bottom(concept) {
                        continue;
                    }
                    let v = vnum(&mut vm, name);
                    hed.push(HAtom::Concept { neg: false, c: ids.cid(concept), t: v });
                }
                JAtom::Role { role, source: JTerm::Var { name: sn }, target: JTerm::Var { name: tn } } => {
                    let s = vnum(&mut vm, sn);
                    let t = vnum(&mut vm, tn);
                    hed.push(HAtom::Role { r: ids.rid(role), s, t });
                }
                _ => bad = true,
            }
        }
        if bad {
            dropped += 1;
            continue;
        }
        if hed.iter().any(|h| matches!(h, HAtom::Eq { .. })) {
            number = true;
        }
        ht.push(HtClause { body: bod, head: hed });
    }

    // ---- RBox edge clauses ----
    for (sub, sup) in &subrole_pairs {
        let rs = ids.rid(sub);
        let rp = ids.rid(sup);
        ht.push(HtClause {
            body: vec![HAtom::Role { r: rs, s: 0, t: 1 }],
            head: vec![HAtom::Role { r: rp, s: 0, t: 1 }],
        });
    }
    for (a, b) in &inverse_pairs {
        let ra = ids.rid(a);
        let rb = ids.rid(b);
        ht.push(HtClause {
            body: vec![HAtom::Role { r: ra, s: 0, t: 1 }],
            head: vec![HAtom::Role { r: rb, s: 1, t: 0 }],
        });
        ht.push(HtClause {
            body: vec![HAtom::Role { r: rb, s: 0, t: 1 }],
            head: vec![HAtom::Role { r: ra, s: 1, t: 0 }],
        });
    }
    {
        let dom_keys: Vec<(String, Vec<String>)> =
            domains.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
        for (r, ds) in dom_keys {
            let rr = ids.rid(&r);
            for d in ds {
                let dc = ids.cid(&d);
                ht.push(HtClause {
                    body: vec![HAtom::Role { r: rr, s: 0, t: 1 }],
                    head: vec![HAtom::Concept { neg: false, c: dc, t: 0 }],
                });
            }
        }
        let ran_keys: Vec<(String, Vec<String>)> =
            ranges.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
        for (r, cs) in ran_keys {
            let rr = ids.rid(&r);
            for cc in cs {
                let c1 = ids.cid(&cc);
                ht.push(HtClause {
                    body: vec![HAtom::Role { r: rr, s: 0, t: 1 }],
                    head: vec![HAtom::Concept { neg: false, c: c1, t: 1 }],
                });
            }
        }
    }

    // ---- nominals ----
    let mut nom_names: Vec<String> =
        ids.con_names.iter().filter(|n| short(n).starts_with("__nom__")).cloned().collect();
    nom_names.sort();
    nom_names.dedup();
    let mut nominal_ids: Vec<usize> = nom_names.iter().map(|n| ids.con_id[n]).collect();

    if !nominal_ids.is_empty() && !inverse_pairs.is_empty() {
        fenced.push(Fenced {
            reason: "nominal+inverse(SHOI/SHOIQ)".into(),
            detail: format!("{} nominal(s) together with inverse roles", nominal_ids.len()),
        });
        nominal_ids = Vec::new();
    }
    if !inverse_pairs.is_empty() && number {
        fenced.push(Fenced {
            reason: "inverse+number(SHIQ)".into(),
            detail: "inverse roles together with number restrictions".into(),
        });
    }

    // ---- transitivity: Horrocks-Sattler universal propagation ----
    if std::env::var_os("KM_HT_NO_TRANS_ENC").is_none() {
        let mut transitive_roles: std::collections::HashSet<usize> = std::collections::HashSet::new();
        for c in &ht {
            let rb: Vec<&HAtom> = c.body.iter().filter(|a| matches!(a, HAtom::Role { .. })).collect();
            let rh: Vec<&HAtom> = c.head.iter().filter(|a| matches!(a, HAtom::Role { .. })).collect();
            if c.body.len() == 2 && rb.len() == 2 && c.head.len() == 1 && rh.len() == 1 {
                if let (HAtom::Role { r: r1, s: r1s, t: r1t }, HAtom::Role { r: r2, s: r2s, t: r2t }, HAtom::Role { r: hr, s: hs, t: ht_ }) =
                    (rb[0], rb[1], rh[0])
                {
                    if r1 == r2 && r2 == hr && r1t == r2s && hs == r1s && ht_ == r2t && r1s != r2t {
                        transitive_roles.insert(*hr);
                    }
                }
            }
        }
        if !transitive_roles.is_empty() {
            let mut extra: Vec<HtClause> = Vec::new();
            let mut seen: std::collections::HashSet<(usize, usize)> = std::collections::HashSet::new();
            for c in &ht {
                let rb: Vec<&HAtom> = c.body.iter().filter(|a| matches!(a, HAtom::Role { .. })).collect();
                let cb: Vec<&HAtom> = c.body.iter().filter(|a| matches!(a, HAtom::Concept { .. })).collect();
                let ch: Vec<&HAtom> = c.head.iter().filter(|a| matches!(a, HAtom::Concept { .. })).collect();
                if c.body.len() == 2 && rb.len() == 1 && cb.len() == 1 {
                    if let (HAtom::Role { r, s: rs, t: rt }, HAtom::Concept { neg, c: uc, t: ut }) = (rb[0], cb[0]) {
                        let any_ch_at_rt = ch.iter().any(|cc| matches!(cc, HAtom::Concept { t, .. } if t == rt));
                        if transitive_roles.contains(r) && !*neg && ut == rs && any_ch_at_rt {
                            let key = (*r, *uc);
                            if !seen.contains(&key) {
                                seen.insert(key);
                                extra.push(HtClause {
                                    body: vec![
                                        HAtom::Role { r: *r, s: *rs, t: *rt },
                                        HAtom::Concept { neg: false, c: *uc, t: *rs },
                                    ],
                                    head: vec![HAtom::Concept { neg: false, c: *uc, t: *rt }],
                                });
                            }
                        }
                    }
                }
            }
            ht.extend(extra);
        }
    }

    // ---- queries ----
    let mut queries: Vec<usize> = Vec::new();
    for (i, n) in ids.con_names.iter().enumerate() {
        if (named.contains(n) || !is_internal(n)) && !is_bottom(n) {
            queries.push(i);
        }
    }
    queries.sort();
    queries.dedup();

    // ---- KM_HT_EMELIM ----
    if std::env::var_os("KM_HT_EMELIM").is_some() {
        let (out, n_elim) = elim_complements(ht, &ids.con_names);
        ht = out;
        if std::env::var_os("KM_HT_STATS").is_some() {
            eprintln!("cb_to_ht [emelim] eliminated {} complementary pairs", n_elim);
        }
    }

    nominal_ids.sort();
    nominal_ids.dedup();
    TInput {
        concepts: ids.con_names,
        roles: ids.rol_names,
        clauses: ht,
        queries,
        dropped,
        fenced,
        inverse: !inverse_pairs.is_empty(),
        number,
        nominals: nominal_ids,
    }
}

// ---------------------------------------------------------------------------
// KM_HT_EMELIM: complementary-definer excluded-middle elimination (B ≡ ¬A)
// ---------------------------------------------------------------------------
/// If `atoms` are ALL positive concept atoms over a single variable, return
/// their concept ids; else None.
fn pos_concepts(atoms: &[HAtom]) -> Option<Vec<usize>> {
    let mut out = Vec::new();
    let mut var: Option<usize> = None;
    for a in atoms {
        match a {
            HAtom::Concept { neg: false, c, t } => {
                match var {
                    None => var = Some(*t),
                    Some(v) if v != *t => return None,
                    _ => {}
                }
                out.push(*c);
            }
            _ => return None,
        }
    }
    Some(out)
}

fn sub_atom(a: &HAtom, sub: &HashMap<usize, usize>) -> HAtom {
    if let HAtom::Concept { neg, c, t } = a {
        if let Some(&k) = sub.get(c) {
            return HAtom::Concept { neg: !*neg, c: k, t: *t };
        }
    }
    a.clone()
}

pub fn elim_complements(ht: Vec<HtClause>, con_names: &[String]) -> (Vec<HtClause>, usize) {
    use std::collections::HashSet;
    // `em` keeps INSERTION order (Python dict) — order decides which substitution
    // wins under the chain-free `used` guard, so it must not be sorted.
    let mut em: Vec<(usize, usize)> = Vec::new();
    let mut em_seen: HashSet<(usize, usize)> = HashSet::new();
    let mut dj: HashSet<(usize, usize)> = HashSet::new();
    let mut protected: HashSet<usize> = HashSet::new();
    let pair = |v: &[usize]| -> (usize, usize) {
        let (a, b) = (v[0], v[1]);
        if a <= b { (a, b) } else { (b, a) }
    };
    for c in &ht {
        for a in c.body.iter().chain(c.head.iter()) {
            if let HAtom::Exist { c: fc, .. } = a {
                protected.insert(*fc);
            }
        }
        if c.body.is_empty() {
            if let Some(h) = pos_concepts(&c.head) {
                if h.len() == 2 && h[0] != h[1] {
                    let p = pair(&h);
                    if em_seen.insert(p) {
                        em.push(p);
                    }
                }
            }
        }
        if c.head.is_empty() {
            if let Some(b) = pos_concepts(&c.body) {
                if b.len() == 2 && b[0] != b[1] {
                    dj.insert(pair(&b));
                }
            }
        }
    }
    let pairs: Vec<(usize, usize)> = em.into_iter().filter(|p| dj.contains(p)).collect();
    if pairs.is_empty() {
        return (ht, 0);
    }
    let internal = |i: usize| -> bool { is_internal(&con_names[i]) };
    let mut sub: HashMap<usize, usize> = HashMap::new();
    let mut used: HashSet<usize> = HashSet::new();
    for p in pairs {
        let (a, b) = p; // canonical a<=b == Python sorted(p) -> (a,b)
        let (elim, keep) = if internal(b) && !internal(a) {
            (b, a)
        } else if internal(a) && !internal(b) {
            (a, b)
        } else {
            (b, a) // both internal/named: drop the larger id (b, since a<=b)
        };
        if protected.contains(&elim) {
            continue;
        }
        if used.contains(&elim) || used.contains(&keep) {
            continue;
        }
        sub.insert(elim, keep);
        used.insert(elim);
        used.insert(keep);
    }
    if sub.is_empty() {
        return (ht, 0);
    }
    let elim_pairs: HashSet<(usize, usize)> =
        sub.iter().map(|(&e, &k)| if e <= k { (e, k) } else { (k, e) }).collect();
    let mut out: Vec<HtClause> = Vec::new();
    for c in &ht {
        if c.body.is_empty() {
            if let Some(h) = pos_concepts(&c.head) {
                if h.len() == 2 && elim_pairs.contains(&pair(&h)) {
                    continue;
                }
            }
        }
        if c.head.is_empty() {
            if let Some(b) = pos_concepts(&c.body) {
                if b.len() == 2 && elim_pairs.contains(&pair(&b)) {
                    continue;
                }
            }
        }
        out.push(HtClause {
            body: c.body.iter().map(|a| sub_atom(a, &sub)).collect(),
            head: c.head.iter().map(|a| sub_atom(a, &sub)).collect(),
        });
    }
    let n = sub.len();
    (out, n)
}
