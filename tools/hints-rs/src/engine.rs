//! Global model construction over the checker's normal form.
//!
//! A model is a set of elements, each with a closed type (a set of
//! normal-form names, interned) and symmetric edges labelled by up-closed
//! role sets. `Engine::saturate` runs a worklist: a type absorbs the names
//! its neighbours push through universals and is re-closed (Horn
//! propagation, depth-first choice on disjunctive gcis); existential and
//! at-least clauses reuse an element whose type already holds what is
//! needed (one element per needed filler type on Horn inputs) or create
//! one; at-most clauses fold surplus neighbours; a nominal name pins its
//! element. Changes inside a transaction are journalled so a failed witness
//! can be rolled back. Untrusted: `check::verify` and the proved checker
//! judge the result.

use crate::nf::Nf;
use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{BuildHasherDefault, Hasher};
use std::rc::Rc;
use std::time::Instant;

#[derive(Default, Clone, Copy)]
pub struct Fx(u64);
impl Hasher for Fx {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0.rotate_left(5) ^ b as u64).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
        }
    }
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.0 = (self.0.rotate_left(5) ^ i as u64).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.0 = (self.0.rotate_left(5) ^ i).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.write_u64(i as u64)
    }
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
}
pub type FxB = BuildHasherDefault<Fx>;
pub type FxMap<K, V> = HashMap<K, V, FxB>;
pub type FxSet<K> = HashSet<K, FxB>;

pub type Id = u32;
pub const NONE: u32 = u32::MAX;
/// typemap keys for "created for this seed" (set ids stay below 2^31)
pub const SEED_KEY: u32 = 1 << 31;
/// forbid flag: forbid all rowclasses outside `target`
pub const CLEAN_FB: u32 = 1 << 31;

/// Interned sorted sets of u32 (concept sets and role labels).
pub struct Sets {
    pub v: Vec<Rc<[u32]>>,
    m: FxMap<Rc<[u32]>, u32>,
}

impl Sets {
    pub fn new() -> Sets {
        let mut s = Sets { v: Vec::new(), m: FxMap::default() };
        s.intern(Vec::new());
        s
    }
    pub fn intern(&mut self, v: Vec<u32>) -> u32 {
        if let Some(&i) = self.m.get(v.as_slice()) {
            return i;
        }
        let r: Rc<[u32]> = v.into();
        let i = self.v.len() as u32;
        self.v.push(r.clone());
        self.m.insert(r, i);
        i
    }
    #[inline]
    pub fn get(&self, i: u32) -> Rc<[u32]> {
        self.v[(i & !CLEAN_FB) as usize].clone()
    }
    #[inline]
    pub fn has(&self, i: u32, x: u32) -> bool {
        self.v[(i & !CLEAN_FB) as usize].binary_search(&x).is_ok()
    }
    pub fn subset(&self, a: u32, b: u32) -> bool {
        let (a, b) = (a & !CLEAN_FB, b & !CLEAN_FB);
        if a == b {
            return true;
        }
        let (a, b) = (&self.v[a as usize], &self.v[b as usize]);
        if a.len() > b.len() {
            return false;
        }
        if a.len() * 8 < b.len() {
            return a.iter().all(|x| b.binary_search(x).is_ok());
        }
        let mut j = 0;
        for &x in a.iter() {
            while j < b.len() && b[j] < x {
                j += 1;
            }
            if j == b.len() || b[j] != x {
                return false;
            }
            j += 1;
        }
        true
    }
    pub fn union(&mut self, a: u32, b: u32) -> u32 {
        let clean = (a | b) & CLEAN_FB;
        let (a, b) = (a & !CLEAN_FB, b & !CLEAN_FB);
        if a == b || b == 0 {
            return a | clean;
        }
        if a == 0 {
            return b | clean;
        }
        let v = merge_sorted(&self.v[a as usize], &self.v[b as usize]);
        self.intern(v) | clean
    }
    pub fn union_vec(&mut self, a: u32, b: &[u32]) -> u32 {
        let clean = a & CLEAN_FB;
        let a = a & !CLEAN_FB;
        if b.is_empty() {
            return a | clean;
        }
        let v = merge_sorted(&self.v[a as usize], b);
        self.intern(v) | clean
    }
    pub fn len(&self) -> usize {
        self.v.len()
    }
}

pub fn merge_sorted(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        if a[i] < b[j] {
            out.push(a[i]);
            i += 1;
        } else if a[i] > b[j] {
            out.push(b[j]);
            j += 1;
        } else {
            out.push(a[i]);
            i += 1;
            j += 1;
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

/// `a \ b` for sorted slices.
pub fn minus_sorted(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut out = Vec::new();
    let mut j = 0;
    for &x in a {
        while j < b.len() && b[j] < x {
            j += 1;
        }
        if j == b.len() || b[j] != x {
            out.push(x);
        }
    }
    out
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CloseRes {
    Ok(u32),
    Clash,
    Budget,
}

#[derive(Debug, Clone)]
pub struct Fail {
    pub reason: String,
    pub blame: Vec<u32>,
}
impl Fail {
    pub fn new(r: &str, blame: Vec<u32>) -> Fail {
        Fail { reason: r.to_string(), blame }
    }
    pub fn is_budget(&self) -> bool {
        self.reason.contains("budget") || self.reason.contains("memory cap")
    }
}

#[derive(Clone)]
pub struct Elem {
    pub ty: u32,
    pub forced: u32,
    pub forbid: u32,
    pub target: u32,
    pub edges: Vec<(Id, u32)>,
    pub pending: Vec<u32>,
    pub nom: bool,
    /// a witness or a nominal element: do not fold surplus neighbours into it
    pub pinned: bool,
    pub owner: Id,
    pub alive: bool,
}

struct Journal {
    n0: usize,
    saved: FxMap<Id, Elem>,
    edge_len_saved: FxMap<Id, usize>,
    uf_saved: Vec<(Id, Id)>,
    tm_added: Vec<u32>,
    nom_saved: Vec<(u32, Option<Id>)>,
}

pub struct Model {
    pub elems: Vec<Elem>,
    pub uf: Vec<Id>,
    pub typemap: FxMap<u32, Vec<Id>>,
    pub nom_elem: FxMap<u32, Id>,
    queue: VecDeque<Id>,
    inq: Vec<bool>,
    journal: Option<Journal>,
}

impl Model {
    pub fn new() -> Model {
        Model {
            elems: Vec::new(),
            uf: Vec::new(),
            typemap: FxMap::default(),
            nom_elem: FxMap::default(),
            queue: VecDeque::new(),
            inq: Vec::new(),
            journal: None,
        }
    }
    pub fn clone_base(&self) -> Model {
        assert!(self.journal.is_none());
        Model {
            elems: self.elems.clone(),
            uf: self.uf.clone(),
            typemap: self.typemap.clone(),
            nom_elem: self.nom_elem.clone(),
            queue: VecDeque::new(),
            inq: vec![false; self.elems.len()],
            journal: None,
        }
    }
    #[inline]
    pub fn find(&self, mut x: Id) -> Id {
        while self.uf[x as usize] != x {
            x = self.uf[x as usize];
        }
        x
    }
    #[inline]
    pub fn em(&mut self, i: Id) -> &mut Elem {
        if let Some(j) = &mut self.journal {
            if (i as usize) < j.n0 && !j.saved.contains_key(&i) {
                let mut orig = self.elems[i as usize].clone();
                if let Some(len0) = j.edge_len_saved.remove(&i) {
                    orig.edges.truncate(len0);
                }
                j.saved.insert(i, orig);
            }
        }
        &mut self.elems[i as usize]
    }
    #[inline]
    pub fn push_edge(&mut self, i: Id, y: Id, l: u32) {
        if let Some(j) = &mut self.journal {
            if (i as usize) < j.n0 && !j.saved.contains_key(&i) && !j.edge_len_saved.contains_key(&i) {
                j.edge_len_saved.insert(i, self.elems[i as usize].edges.len());
            }
        }
        self.elems[i as usize].edges.push((y, l));
    }
    #[inline]
    pub fn update_edge(&mut self, i: Id, y: Id, u: u32) {
        if let Some(j) = &mut self.journal {
            if (i as usize) < j.n0 && !j.saved.contains_key(&i) {
                let len0 = j.edge_len_saved.get(&i).copied().unwrap_or(self.elems[i as usize].edges.len());
                if let Some(p) = self.elems[i as usize].edges[len0..].iter_mut().rev().find(|p| p.0 == y) {
                    p.1 = u;
                    return;
                }
                let mut orig = self.elems[i as usize].clone();
                if j.edge_len_saved.remove(&i).is_some() {
                    orig.edges.truncate(len0);
                }
                j.saved.insert(i, orig);
            }
        }
        if let Some(p) = self.elems[i as usize].edges.iter_mut().rev().find(|p| p.0 == y) {
            p.1 = u;
        }
    }
    pub fn set_uf(&mut self, i: Id, p: Id) {
        if let Some(j) = &mut self.journal {
            if (i as usize) < j.n0 {
                j.uf_saved.push((i, self.uf[i as usize]));
            }
        }
        self.uf[i as usize] = p;
    }
    pub fn set_nom(&mut self, o: u32, e: Id) {
        let old = self.nom_elem.insert(o, e);
        if let Some(j) = &mut self.journal {
            j.nom_saved.push((o, old));
        }
    }
    pub fn tm_push(&mut self, t: u32, e: Id) {
        self.typemap.entry(t).or_default().push(e);
        if let Some(j) = &mut self.journal {
            j.tm_added.push(t);
        }
    }
    pub fn tm_clear(&mut self) {
        self.typemap.clear();
    }
    pub fn push_elem(&mut self, e: Elem) -> Id {
        let id = self.elems.len() as Id;
        let t = e.ty;
        self.elems.push(e);
        self.uf.push(id);
        self.inq.push(false);
        if t != 0 {
            self.tm_push(t, id);
        }
        id
    }
    #[inline]
    pub fn enqueue(&mut self, x: Id) {
        if !self.inq[x as usize] {
            self.inq[x as usize] = true;
            self.queue.push_back(x);
        }
    }
    pub fn begin(&mut self) {
        assert!(self.journal.is_none());
        self.journal = Some(Journal {
            n0: self.elems.len(),
            saved: FxMap::default(),
            edge_len_saved: FxMap::default(),
            uf_saved: Vec::new(),
            tm_added: Vec::new(),
            nom_saved: Vec::new(),
        });
    }
    #[allow(dead_code)]
    pub fn in_txn(&self) -> bool {
        self.journal.is_some()
    }
    /// Pre-existing elements whose type/fields changed in the open transaction.
    pub fn saved_iter(&self) -> impl Iterator<Item = (&Id, &Elem)> {
        self.journal.iter().flat_map(|j| j.saved.iter())
    }
    /// Pre-existing elements changed in the open transaction: (id, saved copy).
    #[allow(dead_code)]
    pub fn changed(&self) -> Vec<(Id, Elem)> {
        match &self.journal {
            Some(j) => j.saved.iter().map(|(k, v)| (*k, v.clone())).collect(),
            None => Vec::new(),
        }
    }
    pub fn commit(&mut self) {
        self.journal = None;
    }
    pub fn rollback(&mut self) {
        let j = self.journal.take().expect("no transaction");
        for (t, _) in j.tm_added.iter().rev().map(|t| (*t, ())) {
            if let Some(v) = self.typemap.get_mut(&t) {
                v.pop();
                if v.is_empty() {
                    self.typemap.remove(&t);
                }
            }
        }
        self.elems.truncate(j.n0);
        self.uf.truncate(j.n0);
        for (i, len0) in j.edge_len_saved {
            if !j.saved.contains_key(&i) {
                self.elems[i as usize].edges.truncate(len0);
            }
        }
        for (i, e) in j.saved {
            self.elems[i as usize] = e;
        }
        for (i, p) in j.uf_saved.into_iter().rev() {
            self.uf[i as usize] = p;
        }
        for (o, old) in j.nom_saved.into_iter().rev() {
            match old {
                Some(e) => {
                    self.nom_elem.insert(o, e);
                }
                None => {
                    self.nom_elem.remove(&o);
                }
            }
        }
        while let Some(x) = self.queue.pop_front() {
            if (x as usize) < self.inq.len() {
                self.inq[x as usize] = false;
            }
        }
        self.inq.truncate(self.elems.len());
        for b in self.inq.iter_mut() {
            *b = false;
        }
    }
    #[allow(dead_code)]
    pub fn queue_empty(&self) -> bool {
        self.queue.is_empty()
    }
    pub fn pop(&mut self) -> Option<Id> {
        let x = self.queue.pop_front()?;
        self.inq[x as usize] = false;
        Some(x)
    }
    pub fn canonical(&self) -> impl Iterator<Item = Id> + '_ {
        (0..self.elems.len() as Id).filter(move |&i| self.elems[i as usize].alive && self.uf[i as usize] == i)
    }
    pub fn edge_label(&self, x: Id, y: Id) -> Option<u32> {
        let ex = &self.elems[x as usize].edges;
        let ey = &self.elems[y as usize].edges;
        if ey.len() < ex.len() && !ey.iter().any(|e| e.0 == x) {
            return None;
        }
        ex.iter().find(|e| e.0 == y).map(|e| e.1)
    }
}

#[derive(Clone)]
pub struct Opts {
    pub loops: bool,
    pub close_budget: u64,
    pub step_budget: u64,
    pub node_budget: usize,
    pub reuse_scan: usize,
    pub mem_cap_mb: usize,
    pub deadline: Option<Instant>,
}

impl Default for Opts {
    fn default() -> Opts {
        Opts {
            loops: true,
            close_budget: 20000,
            step_budget: 50_000_000,
            node_budget: 3_000_000,
            reuse_scan: 16,
            mem_cap_mb: 7500,
            deadline: None,
        }
    }
}

pub fn current_mem_mb() -> usize {
    if let Ok(s) = std::fs::read_to_string("/proc/self/statm") {
        let mut it = s.split_ascii_whitespace();
        let vm_pages: usize = it.next().and_then(|x| x.parse().ok()).unwrap_or(0);
        let rss_pages: usize = it.next().and_then(|x| x.parse().ok()).unwrap_or(0);
        return vm_pages.max(rss_pages) / 256;
    }
    0
}

#[derive(Default, Debug, Clone)]
pub struct Stats {
    pub closures: u64,
    pub close_runs: u64,
    pub steps: u64,
    pub reused: u64,
    pub created: u64,
    pub merges: u64,
    pub folds: u64,
    pub reclose_scratch: u64,
}

/// Role -> neighbours of one element, extended as edges are appended.
#[derive(Default)]
struct NbrIdx {
    map: FxMap<u32, Vec<Id>>,
    concepts: FxMap<u32, FxSet<u32>>,
    seen_ty: FxSet<(u32, u32)>,
    upto: usize,
    queries: usize,
}

impl NbrIdx {
    fn has(&mut self, en: &Engine, m: &Model, x: Id, r: u32, b: u32) -> bool {
        self.queries += 1;
        let edges = &m.elems[x as usize].edges;
        while self.upto < edges.len() {
            let (y, l) = edges[self.upto];
            for &rr in en.labs.v[l as usize].iter() {
                let v = self.map.entry(rr).or_default();
                v.push(y);
                if self.concepts.contains_key(&rr) {
                    let ty = m.elems[y as usize].ty;
                    if self.seen_ty.insert((rr, ty)) {
                        self.concepts
                            .entry(rr)
                            .or_default()
                            .extend(en.sets.v[(ty & !CLEAN_FB) as usize].iter().copied());
                    }
                }
            }
            self.upto += 1;
        }
        if let Some(set) = self.concepts.get(&r) {
            return set.contains(&b);
        }
        match self.map.get(&r) {
            Some(v) => {
                if self.queries >= 64 && v.len() >= 32 {
                    let set = self.concepts.entry(r).or_default();
                    for &yk in v.iter() {
                        let ty = m.elems[yk as usize].ty;
                        if self.seen_ty.insert((r, ty)) {
                            set.extend(en.sets.v[(ty & !CLEAN_FB) as usize].iter().copied());
                        }
                    }
                    return set.contains(&b);
                }
                v.iter().any(|&y| en.sets.has(m.elems[y as usize].ty, b))
            }
            None => false,
        }
    }
}

pub struct Engine<'a> {
    pub nf: &'a Nf,
    pub sets: Sets,
    pub labs: Sets,
    lab_flip: Vec<u32>,
    lab_up: Vec<u32>,
    lab_union: FxMap<(u32, u32), u32>,
    fwd_cache: FxMap<(u32, u32), u32>,
    bwd_cache: FxMap<(u32, u32), u32>,
    hcons_cache: FxMap<u32, bool>,
    self_push: Vec<Vec<u32>>,
    bounce: Vec<Vec<(u32, u32)>>,
    has_bounce: bool,
    r_direct_st: Vec<u32>,
    r_up_st: Vec<u32>,
    w_role_st: Vec<u32>,
    w_role_list: Vec<Vec<u32>>,
    conflict_peers: Vec<Vec<u32>>,
    hclose_len: Vec<u32>,
    memo: FxMap<(u32, u32, u32, bool), CloseRes>,
    pub bad: FxSet<u32>,
    mark: Vec<u32>,
    cmark: Vec<u32>,
    stamp: u32,
    cnt: Vec<u32>,
    cstamp: Vec<u32>,
    fmark: Vec<u32>,
    fstamp: u32,
    tmark: Vec<u32>,
    tstamp: u32,
    runs: u64,
    cur_target: Rc<[u32]>,
    cur_target_id: u32,
    cur_clean: bool,
    cur_tst: u32,
    cur_nomok: bool,
    pub opt: Opts,
    pub stats: Stats,
    pub debug: bool,
    dbg_created: FxMap<u32, u64>,
    /// data clauses: a closed type without a data star is a clash
    pub data: Option<(crate::data::DataNf, crate::data::Values)>,
    pub dreq: Vec<u32>,
    pub has_data: Vec<bool>,
    data_ok: FxMap<u32, bool>,
    /// one-step lookahead on successors: closed type -> its successor seeds close
    succ_ok: FxMap<u32, bool>,
    nest: u32,
    cur_forbid: u32,
    pub rowclasses: u32,
    pub is_rowclass: Vec<bool>,
    pub mem_hit: bool,
    pub empty_auto_inert: Vec<(u32, u32)>,
    pub empty_other: Vec<u32>,
}

impl<'a> Engine<'a> {
    pub fn new(nf: &'a Nf, opt: Opts) -> Engine<'a> {
        let mut labs = Sets::new();
        let lab_up: Vec<u32> = (0..2 * nf.m).map(|r| labs.intern(nf.up[r].clone())).collect();
        let mut self_push: Vec<Vec<u32>> = vec![Vec::new(); nf.n];
        let mut bounce: Vec<Vec<(u32, u32)>> = vec![Vec::new(); nf.n];
        let mut has_bounce = false;
        let mut conflict_peers: Vec<Vec<u32>> = vec![Vec::new(); nf.n];
        let mut hclose_len: Vec<u32> = vec![1; nf.n];
        // Precompute sound self-implications `a -> c` from `some a r b` (or `atleast a k r b`)
        // combined with `b ->* b'` and `all b' (-r) c`, plus binary conflict peers `(a1, a2)`
        // whose outgoing role obligations clash on any common successor.
        if !nf.all.is_empty() || !nf.le.is_empty() {
            let t_pre = Instant::now();
            let max_rounds = if nf.n > 50_000 { 1 } else { 5 };
            let max_passes = if nf.n > 50_000 { 1 } else { 3 };
            let by_filler = crate::nf::Csr::build(
                nf.n,
                nf.ex
                    .iter()
                    .map(|&(a, r, b)| (b, (a, 1u32, r)))
                    .chain(nf.ge.iter().filter(|x| x.1 >= 1).map(|&(a, k, r, b)| (b, (a, k, r)))),
            );
            let nr = 2 * nf.m;
            let le_by_role = crate::nf::Csr::build(
                nr,
                nf.le.iter().filter(|&&(_, _, r, _)| (r as usize) < nr).map(|&(a, k, r, c)| (r, (a, k, c))),
            );
            let mut unit_empty: Vec<u32> = nf
                .gci_empty
                .iter()
                .filter_map(|&g| {
                    let h = &nf.gci[g as usize].1;
                    if h.len() == 1 { Some(h[0]) } else { None }
                })
                .collect();
            let disj2_empty: Vec<(u32, u32)> = nf
                .gci_empty
                .iter()
                .filter_map(|&g| {
                    let h = &nf.gci[g as usize].1;
                    if h.len() == 2 { Some((h[0], h[1])) } else { None }
                })
                .collect();
            let has_empty_head = nf.gci.iter().any(|(_, h)| h.is_empty());
            let mut hmark = vec![0u32; nf.n];
            let mut hcnt = vec![0u32; nf.gci.len()];
            let mut hcst = vec![0u32; nf.gci.len()];
            let mut hst = 0u32;
            let mut hq = Vec::new();
            let mut hvis = Vec::new();
            // Precompute Horn closure of `unit_empty` once so `top` universals are not
            // re-scanned for every filler `b`.
            let mut top_mark = vec![false; nf.n];
            if !unit_empty.is_empty() && nf.n > 50_000 {
                hst = hst.wrapping_add(1);
                hq.clear();
                hvis.clear();
                for &u0 in &unit_empty {
                    if hmark[u0 as usize] != hst {
                        hmark[u0 as usize] = hst;
                        hq.push(u0);
                        hvis.push(u0);
                    }
                }
                while let Some(u) = hq.pop() {
                    for &g in nf.gci_by_body.get(u) {
                        let gi = g as usize;
                        if hcst[gi] != hst {
                            hcst[gi] = hst;
                            hcnt[gi] = 0;
                        }
                        hcnt[gi] += 1;
                        if hcnt[gi] == nf.body_len[gi] {
                            let h = &nf.gci[gi].1;
                            if h.len() == 1 && hmark[h[0] as usize] != hst {
                                hmark[h[0] as usize] = hst;
                                hq.push(h[0]);
                                hvis.push(h[0]);
                            }
                        }
                    }
                }
                let mut top_all: Vec<(u32, u32)> = Vec::new();
                for &bp in &hvis {
                    top_mark[bp as usize] = true;
                    top_all.extend_from_slice(nf.all_by.get(bp));
                }
                top_all.sort_unstable();
                top_all.dedup();
                let mut top_bwd: Vec<Vec<u32>> = vec![Vec::new(); nr];
                for r in 0..nr {
                    let up_r = &nf.up[r];
                    for &(s, c) in &top_all {
                        if up_r.binary_search(&(s ^ 1)).is_ok() {
                            top_bwd[r].push(c);
                        }
                    }
                    top_bwd[r].sort_unstable();
                    top_bwd[r].dedup();
                }
                for &(a, r, _) in &nf.ex {
                    if (r as usize) < nr {
                        for &c in &top_bwd[r as usize] {
                            if c != a && !self_push[a as usize].contains(&c) {
                                self_push[a as usize].push(c);
                            }
                        }
                    }
                }
                for &(a, k, r, _) in &nf.ge {
                    if k >= 1 && (r as usize) < nr {
                        for &c in &top_bwd[r as usize] {
                            if c != a && !self_push[a as usize].contains(&c) {
                                self_push[a as usize].push(c);
                            }
                        }
                    }
                }
            }
            for round in 0..max_rounds {
                if t_pre.elapsed().as_secs() >= 2 {
                    break;
                }
                for pass in 0..max_passes {
                    if t_pre.elapsed().as_secs() >= 2 {
                        break;
                    }
                    let mut changed = false;
                    for b in 0..nf.n as u32 {
                        let reqs_b = by_filler.get(b);
                        if reqs_b.is_empty() {
                            continue;
                        }
                        if t_pre.elapsed().as_secs() >= 2 {
                            break;
                        }
                        hst = hst.wrapping_add(1);
                        hq.clear();
                        hvis.clear();
                        let push_h = |x: u32, hmark: &mut [u32], hq: &mut Vec<u32>, hvis: &mut Vec<u32>| {
                            if hmark[x as usize] != hst {
                                hmark[x as usize] = hst;
                                hq.push(x);
                                hvis.push(x);
                            }
                        };
                        for &u0 in &unit_empty {
                            push_h(u0, &mut hmark, &mut hq, &mut hvis);
                        }
                        push_h(b, &mut hmark, &mut hq, &mut hvis);
                        let mut clash = false;
                        while let Some(u) = hq.pop() {
                            if conflict_peers[u as usize].iter().any(|&p| hmark[p as usize] == hst) {
                                clash = true;
                                break;
                            }
                            for &c in &self_push[u as usize] {
                                push_h(c, &mut hmark, &mut hq, &mut hvis);
                            }
                            for &g in nf.gci_by_body.get(u) {
                                let gi = g as usize;
                                if hcst[gi] != hst {
                                    hcst[gi] = hst;
                                    hcnt[gi] = 0;
                                }
                                hcnt[gi] += 1;
                                if hcnt[gi] == nf.body_len[gi] {
                                    let h = &nf.gci[gi].1;
                                    if h.is_empty() {
                                        clash = true;
                                        break;
                                    } else if h.len() == 1 {
                                        push_h(h[0], &mut hmark, &mut hq, &mut hvis);
                                    }
                                }
                            }
                            if clash {
                                break;
                            }
                        }
                        if round == 0 && pass == 0 {
                            hclose_len[b as usize] = if clash { u32::MAX } else { hvis.len() as u32 };
                        }
                        if clash {
                            continue;
                        }
                        let mut all_on_b: Vec<(u32, u32)> = Vec::new();
                        for &bp in &hvis {
                            if !top_mark[bp as usize] {
                                all_on_b.extend_from_slice(nf.all_by.get(bp));
                            }
                        }
                        if all_on_b.is_empty() {
                            continue;
                        }
                        all_on_b.sort_unstable();
                        all_on_b.dedup();
                        if all_on_b.len() * reqs_b.len() > 50_000 {
                            continue;
                        }
                        for &(a, _k, r) in reqs_b {
                            let up_r = &nf.up[r as usize];
                            for &(s, c) in &all_on_b {
                                let fs = s ^ 1;
                                if up_r.binary_search(&fs).is_ok() && c != a && !self_push[a as usize].contains(&c) {
                                    self_push[a as usize].push(c);
                                    changed = true;
                                }
                            }
                        }
                    }
                    if !changed {
                        break;
                    }
                }
                if nf.n > 50_000 || t_pre.elapsed().as_secs() >= 2 {
                    break;
                }
                let mut pair_checks = 0usize;
                let mut pair_clash: FxMap<(u32, u32), bool> = FxMap::default();
                for b in 0..nf.n as u32 {
                    let reqs_b = by_filler.get(b);
                    if reqs_b.is_empty() {
                        continue;
                    }
                    hst = hst.wrapping_add(1);
                    hq.clear();
                    hvis.clear();
                    let push_h = |x: u32, hmark: &mut [u32], hq: &mut Vec<u32>, hvis: &mut Vec<u32>| {
                        if hmark[x as usize] != hst {
                            hmark[x as usize] = hst;
                            hq.push(x);
                            hvis.push(x);
                        }
                    };
                    for &u0 in &unit_empty {
                        push_h(u0, &mut hmark, &mut hq, &mut hvis);
                    }
                    push_h(b, &mut hmark, &mut hq, &mut hvis);
                    let mut b_clash = false;
                    while let Some(u) = hq.pop() {
                        if conflict_peers[u as usize].iter().any(|&p| hmark[p as usize] == hst) {
                            b_clash = true;
                            break;
                        }
                        for &c in &self_push[u as usize] {
                            push_h(c, &mut hmark, &mut hq, &mut hvis);
                        }
                        for &g in nf.gci_by_body.get(u) {
                            let gi = g as usize;
                            if hcst[gi] != hst {
                                hcst[gi] = hst;
                                hcnt[gi] = 0;
                            }
                            hcnt[gi] += 1;
                            if hcnt[gi] == nf.body_len[gi] {
                                let h = &nf.gci[gi].1;
                                if h.is_empty() {
                                    b_clash = true;
                                    break;
                                } else if h.len() == 1 {
                                    push_h(h[0], &mut hmark, &mut hq, &mut hvis);
                                }
                            }
                        }
                        if b_clash {
                            break;
                        }
                    }
                    if b_clash {
                        for &(a1, _, _) in reqs_b {
                            if !conflict_peers[a1 as usize].contains(&a1) {
                                conflict_peers[a1 as usize].push(a1);
                            }
                        }
                        continue;
                    }
                    if !nf.le.is_empty() {
                        for &(a1, k1, r) in reqs_b {
                            for &s in &nf.up[r as usize] {
                                for &(a2, k2, c2) in le_by_role.get(s) {
                                    if k1 > k2 && hmark[c2 as usize] == hst {
                                        if !conflict_peers[a1 as usize].contains(&a2) {
                                            conflict_peers[a1 as usize].push(a2);
                                        }
                                        if !conflict_peers[a2 as usize].contains(&a1) {
                                            conflict_peers[a2 as usize].push(a1);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    if (has_empty_head || round > 0) && pair_checks < 100_000 {
                        for &(a1, _k1, r) in reqs_b {
                            if pair_checks >= 100_000 {
                                break;
                            }
                            for &s in &nf.up[r as usize] {
                                let alls = nf.all_by_role.get(s);
                                if alls.len() > 512 {
                                    continue;
                                }
                                for &(a2, c) in alls {
                                    let pk = (b.min(c), b.max(c));
                                    let is_cl = match pair_clash.get(&pk) {
                                        Some(&cl) => cl,
                                        None => {
                                            pair_checks += 1;
                                            hst = hst.wrapping_add(1);
                                            hq.clear();
                                            hvis.clear();
                                            for &u0 in &unit_empty {
                                                if hmark[u0 as usize] != hst {
                                                    hmark[u0 as usize] = hst;
                                                    hq.push(u0);
                                                    hvis.push(u0);
                                                }
                                            }
                                            for &seed_x in &[b, c] {
                                                if hmark[seed_x as usize] != hst {
                                                    hmark[seed_x as usize] = hst;
                                                    hq.push(seed_x);
                                                    hvis.push(seed_x);
                                                }
                                            }
                                            let mut cl = false;
                                            while let Some(u) = hq.pop() {
                                                if conflict_peers[u as usize].iter().any(|&p| hmark[p as usize] == hst) {
                                                    cl = true;
                                                    break;
                                                }
                                                for &cp in &self_push[u as usize] {
                                                    if hmark[cp as usize] != hst {
                                                        hmark[cp as usize] = hst;
                                                        hq.push(cp);
                                                        hvis.push(cp);
                                                    }
                                                }
                                                for &g in nf.gci_by_body.get(u) {
                                                    let gi = g as usize;
                                                    if hcst[gi] != hst {
                                                        hcst[gi] = hst;
                                                        hcnt[gi] = 0;
                                                    }
                                                    hcnt[gi] += 1;
                                                    if hcnt[gi] == nf.body_len[gi] {
                                                        let h = &nf.gci[gi].1;
                                                        if h.is_empty() {
                                                            cl = true;
                                                            break;
                                                        } else if h.len() == 1 && hmark[h[0] as usize] != hst {
                                                            hmark[h[0] as usize] = hst;
                                                            hq.push(h[0]);
                                                            hvis.push(h[0]);
                                                        }
                                                    }
                                                }
                                                if cl {
                                                    break;
                                                }
                                            }
                                            pair_clash.insert(pk, cl);
                                            cl
                                        }
                                    };
                                    if is_cl {
                                        if !conflict_peers[a1 as usize].contains(&a2) {
                                            conflict_peers[a1 as usize].push(a2);
                                        }
                                        if !conflict_peers[a2 as usize].contains(&a1) {
                                            conflict_peers[a2 as usize].push(a1);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                if round == 4 {
                    break;
                }
                let mut any_new_push = false;
                for &(h0, h1) in &disj2_empty {
                    for (hj, hother) in [(h0, h1), (h1, h0)] {
                        hst = hst.wrapping_add(1);
                        hq.clear();
                        hvis.clear();
                        for &u0 in &unit_empty {
                            if hmark[u0 as usize] != hst {
                                hmark[u0 as usize] = hst;
                                hq.push(u0);
                                hvis.push(u0);
                            }
                        }
                        if hmark[hj as usize] != hst {
                            hmark[hj as usize] = hst;
                            hq.push(hj);
                            hvis.push(hj);
                        }
                        let mut cl_hj = false;
                        while let Some(u) = hq.pop() {
                            if conflict_peers[u as usize].iter().any(|&p| hmark[p as usize] == hst) {
                                cl_hj = true;
                                break;
                            }
                            for &cp in &self_push[u as usize] {
                                if hmark[cp as usize] != hst {
                                    hmark[cp as usize] = hst;
                                    hq.push(cp);
                                    hvis.push(cp);
                                }
                            }
                            for &g in nf.gci_by_body.get(u) {
                                let gi = g as usize;
                                if hcst[gi] != hst {
                                    hcst[gi] = hst;
                                    hcnt[gi] = 0;
                                }
                                hcnt[gi] += 1;
                                if hcnt[gi] == nf.body_len[gi] {
                                    let h = &nf.gci[gi].1;
                                    if h.is_empty() {
                                        cl_hj = true;
                                        break;
                                    } else if h.len() == 1 && hmark[h[0] as usize] != hst {
                                        hmark[h[0] as usize] = hst;
                                        hq.push(h[0]);
                                        hvis.push(h[0]);
                                    }
                                }
                            }
                            if cl_hj {
                                break;
                            }
                        }
                        if cl_hj {
                            if !conflict_peers[hj as usize].contains(&hj) {
                                conflict_peers[hj as usize].push(hj);
                            }
                            if !unit_empty.contains(&hother) {
                                unit_empty.push(hother);
                                any_new_push = true;
                            }
                            continue;
                        }
                        let mut peers: Vec<u32> = Vec::new();
                        for &u in &hvis {
                            peers.extend_from_slice(&conflict_peers[u as usize]);
                        }
                        peers.sort_unstable();
                        peers.dedup();
                        for p in peers {
                            if !conflict_peers[hj as usize].contains(&p) {
                                conflict_peers[hj as usize].push(p);
                            }
                            if !conflict_peers[p as usize].contains(&hj) {
                                conflict_peers[p as usize].push(hj);
                            }
                            if hother != p && !self_push[p as usize].contains(&hother) {
                                self_push[p as usize].push(hother);
                                any_new_push = true;
                            }
                        }
                    }
                }
                if !any_new_push {
                    break;
                }
            }
            if !nf.all.is_empty() && nf.all.len() <= 50_000 && t_pre.elapsed().as_secs() < 3 {
                let mut distinct_d: Vec<u32> = nf.all.iter().map(|&(_, _, d)| d).collect();
                distinct_d.sort_unstable();
                distinct_d.dedup();
                if distinct_d.len() <= 8_000 {
                    let mut all_on_d: FxMap<u32, Vec<(u32, u32)>> = FxMap::default();
                    for &d in &distinct_d {
                        if t_pre.elapsed().as_secs() >= 4 {
                            break;
                        }
                        hst = hst.wrapping_add(1);
                        hq.clear();
                        hvis.clear();
                        for &u0 in &unit_empty {
                            if hmark[u0 as usize] != hst {
                                hmark[u0 as usize] = hst;
                                hq.push(u0);
                                hvis.push(u0);
                            }
                        }
                        if hmark[d as usize] != hst {
                            hmark[d as usize] = hst;
                            hq.push(d);
                            hvis.push(d);
                        }
                        let mut cl = false;
                        while let Some(u) = hq.pop() {
                            if conflict_peers[u as usize].iter().any(|&p| hmark[p as usize] == hst) {
                                cl = true;
                                break;
                            }
                            for &cp in &self_push[u as usize] {
                                if hmark[cp as usize] != hst {
                                    hmark[cp as usize] = hst;
                                    hq.push(cp);
                                    hvis.push(cp);
                                }
                            }
                            for &g in nf.gci_by_body.get(u) {
                                let gi = g as usize;
                                if hcst[gi] != hst {
                                    hcst[gi] = hst;
                                    hcnt[gi] = 0;
                                }
                                hcnt[gi] += 1;
                                if hcnt[gi] == nf.body_len[gi] {
                                    let h = &nf.gci[gi].1;
                                    if h.is_empty() {
                                        cl = true;
                                        break;
                                    } else if h.len() == 1 && hmark[h[0] as usize] != hst {
                                        hmark[h[0] as usize] = hst;
                                        hq.push(h[0]);
                                        hvis.push(h[0]);
                                    }
                                }
                            }
                            if cl {
                                break;
                            }
                        }
                        if !cl {
                            let mut v: Vec<(u32, u32)> = Vec::new();
                            for &bp in &hvis {
                                if !top_mark[bp as usize] {
                                    v.extend_from_slice(nf.all_by.get(bp));
                                }
                            }
                            v.sort_unstable();
                            v.dedup();
                            if !v.is_empty() {
                                all_on_d.insert(d, v);
                            }
                        }
                    }
                    for &(a_all, s, d) in &nf.all {
                        if (s as usize) >= nr {
                            continue;
                        }
                        if let Some(v) = all_on_d.get(&d) {
                            let up_s = &nf.up[s as usize];
                            for &(s2, c2) in v {
                                if c2 != a_all
                                    && up_s.binary_search(&(s2 ^ 1)).is_ok()
                                    && !bounce[a_all as usize].contains(&(s, c2))
                                {
                                    bounce[a_all as usize].push((s, c2));
                                    has_bounce = true;
                                }
                            }
                        }
                    }
                }
            }
        }
        let nr = 2 * nf.m;
        let mut en = Engine {
            nf,
            sets: Sets::new(),
            labs,
            lab_flip: Vec::new(),
            lab_up,
            lab_union: FxMap::default(),
            fwd_cache: FxMap::default(),
            bwd_cache: FxMap::default(),
            hcons_cache: FxMap::default(),
            self_push,
            bounce,
            has_bounce,
            r_direct_st: vec![0; nr],
            r_up_st: vec![0; nr],
            w_role_st: vec![0; nr],
            w_role_list: vec![Vec::new(); nr],
            conflict_peers,
            hclose_len,
            memo: FxMap::default(),
            bad: FxSet::default(),
            mark: vec![0; nf.n],
            cmark: vec![0; nf.n],
            stamp: 0,
            cnt: vec![0; nf.gci.len()],
            cstamp: vec![0; nf.gci.len()],
            fmark: vec![0; nf.n],
            fstamp: 0,
            tmark: vec![0; nf.n],
            tstamp: 0,
            runs: 0,
            cur_target: Rc::from(Vec::new()),
            cur_target_id: 0,
            cur_clean: false,
            cur_tst: 0,
            cur_nomok: false,
            opt,
            stats: Stats::default(),
            debug: std::env::var("KM_HINTS_DEBUG").is_ok(),
            dbg_created: FxMap::default(),
            data: None,
            dreq: vec![0; nf.n],
            has_data: vec![false; nf.n],
            data_ok: FxMap::default(),
            succ_ok: FxMap::default(),
            nest: 0,
            cur_forbid: 0,
            rowclasses: 0,
            is_rowclass: vec![false; nf.n],
            mem_hit: false,
            empty_auto_inert: Vec::new(),
            empty_other: Vec::new(),
        };
        en.rebuild_empty_inert();
        en
    }

    pub fn rebuild_empty_inert(&mut self) {
        self.empty_auto_inert.clear();
        self.empty_other.clear();
        let nf = self.nf;
        let check_static = |x: u32| -> bool {
            let xu = x as usize;
            !nf.named[xu]
                && !nf.is_nom[xu]
                && nf.ex_by.get(x).is_empty()
                && nf.ge_by.get(x).is_empty()
                && nf.all_by.get(x).is_empty()
                && !nf.has_le[xu]
                && self.dreq[xu] == 0
                && (!self.has_data[xu]
                    || self.data.as_ref().map_or(false, |(d, _)| !d.datmost_by.contains_key(&x)))
                && self.bounce[xu].is_empty()
                && nf.gci_by_body.get(x).is_empty()
                && self.self_push[xu].is_empty()
        };
        for &g in &nf.gci_empty {
            let h = &nf.gci[g as usize].1;
            if h.len() <= 1 {
                self.empty_other.push(g);
                continue;
            }
            let mut best: Option<((bool, u32), u32)> = None;
            for &cand in h {
                if check_static(cand) {
                    let k = (self.has_data[cand as usize], cand);
                    if best.map_or(true, |b| k < b.0) {
                        best = Some((k, cand));
                    }
                }
            }
            if let Some((_, cand)) = best {
                self.empty_auto_inert.push((g, cand));
            } else {
                self.empty_other.push(g);
            }
        }
    }

    #[inline]
    pub fn mem_exceeded(&mut self) -> bool {
        if self.mem_hit {
            return true;
        }
        if self.opt.mem_cap_mb > 0 && current_mem_mb() >= self.opt.mem_cap_mb {
            self.mem_hit = true;
            return true;
        }
        false
    }

    pub fn has_data_star(&mut self, ds: Vec<u32>) -> bool {
        if ds.is_empty() || self.data.is_none() {
            return true;
        }
        let did = self.sets.intern(ds);
        if let Some(&b) = self.data_ok.get(&did) {
            return b;
        }
        let (d, v) = self.data.as_ref().unwrap();
        let b = crate::data::star(d, v, &self.sets.v[did as usize]).is_some();
        self.data_ok.insert(did, b);
        b
    }

    #[inline]
    pub fn has_conflict_peer(&self, a: u32, b: u32) -> bool {
        self.conflict_peers[a as usize].contains(&b)
    }

    pub fn clean_forbid(&mut self, forbid: u32, _target: u32) -> u32 {
        if self.rowclasses == 0 {
            return forbid;
        }
        forbid | CLEAN_FB
    }

    pub fn close_clean(&mut self, seed: u32, forbid: u32, target: u32, nomok: bool) -> CloseRes {
        let r = self.close(seed, forbid, target, nomok);
        if let CloseRes::Ok(t) = r {
            if self.rowclasses != 0 && (forbid & CLEAN_FB) == 0 {
                let is_dirty = self
                    .sets
                    .get(t)
                    .iter()
                    .any(|&b| self.is_rowclass[b as usize] && !self.sets.has(target, b));
                if is_dirty {
                    let cfb = self.clean_forbid(forbid, target);
                    if let CloseRes::Ok(t_clean) = self.close(seed, cfb, target, nomok) {
                        return CloseRes::Ok(t_clean);
                    }
                }
            }
        }
        r
    }

    pub fn set_data(&mut self, d: crate::data::DataNf, v: crate::data::Values) {
        self.dreq = vec![0; self.nf.n];
        self.has_data = vec![false; self.nf.n];
        let mut in_pos = vec![false; self.nf.n];
        let mut in_neg = vec![false; self.nf.n];
        let mut by_u: FxMap<u32, Vec<u32>> = FxMap::default();
        let add_u = |by_u: &mut FxMap<u32, Vec<u32>>, d: &crate::data::DataNf, a: u32, u: u32| {
            by_u.entry(u).or_default().push(a);
            for &(u_sub, u_sup) in &d.dsub {
                if u_sub == u {
                    by_u.entry(u_sup).or_default().push(a);
                }
            }
        };
        for c in &d.dsome {
            if (c.0 as usize) < self.nf.n {
                self.dreq[c.0 as usize] += 1;
                self.has_data[c.0 as usize] = true;
                in_pos[c.0 as usize] = true;
                add_u(&mut by_u, &d, c.0, c.1);
            }
        }
        for c in &d.datleast {
            if (c.0 as usize) < self.nf.n {
                self.dreq[c.0 as usize] += c.1;
                self.has_data[c.0 as usize] = true;
                if c.1 >= 1 {
                    in_pos[c.0 as usize] = true;
                }
                add_u(&mut by_u, &d, c.0, c.2);
            }
        }
        for c in &d.dall {
            if (c.0 as usize) < self.nf.n {
                self.has_data[c.0 as usize] = true;
                in_neg[c.0 as usize] = true;
                add_u(&mut by_u, &d, c.0, c.1);
            }
        }
        for c in &d.datmost {
            if (c.0 as usize) < self.nf.n {
                self.has_data[c.0 as usize] = true;
                in_neg[c.0 as usize] = true;
                add_u(&mut by_u, &d, c.0, c.2);
            }
        }
        // Precompute singleton and pairwise data conflicts per data property
        let t_data = Instant::now();
        let mut checks = 0usize;
        for a in 0..self.nf.n as u32 {
            if in_pos[a as usize] && checks < 20_000 && t_data.elapsed().as_secs() < 2 {
                checks += 1;
                let ok = crate::data::star(&d, &v, &[a]).is_some();
                let id = self.sets.intern(vec![a]);
                self.data_ok.insert(id, ok);
                if !ok && !self.conflict_peers[a as usize].contains(&a) {
                    self.conflict_peers[a as usize].push(a);
                }
            }
        }
        let check_pair = |en: &mut Self, a1: u32, a2: u32| {
            let (x, y) = if a1 <= a2 { (a1, a2) } else { (a2, a1) };
            let id = en.sets.intern(vec![x, y]);
            if let std::collections::hash_map::Entry::Vacant(e) = en.data_ok.entry(id) {
                let ok = crate::data::star(&d, &v, &[x, y]).is_some();
                e.insert(ok);
                if !ok {
                    if !en.conflict_peers[x as usize].contains(&y) {
                        en.conflict_peers[x as usize].push(y);
                    }
                    if !en.conflict_peers[y as usize].contains(&x) {
                        en.conflict_peers[y as usize].push(x);
                    }
                }
            }
        };
        let empty_pairs: Vec<(u32, u32)> = self
            .nf
            .gci_empty
            .iter()
            .filter_map(|&g| {
                let h = &self.nf.gci[g as usize].1;
                if h.len() == 2 && self.has_data[h[0] as usize] && self.has_data[h[1] as usize] {
                    Some((h[0], h[1]))
                } else {
                    None
                }
            })
            .collect();
        for (h0, h1) in empty_pairs {
            check_pair(self, h0, h1);
        }
        let mut pair_checks = 0usize;
        for cs in by_u.values_mut() {
            if t_data.elapsed().as_secs() >= 2 {
                break;
            }
            cs.sort_unstable();
            cs.dedup();
            if cs.len() <= 256 {
                for i in 0..cs.len() {
                    let a1 = cs[i];
                    if self.conflict_peers[a1 as usize].contains(&a1) {
                        continue;
                    }
                    for &a2 in &cs[i + 1..] {
                        if self.conflict_peers[a2 as usize].contains(&a2) {
                            continue;
                        }
                        if !((in_pos[a1 as usize] && (in_neg[a2 as usize] || in_pos[a2 as usize]))
                            || (in_pos[a2 as usize] && in_neg[a1 as usize]))
                        {
                            continue;
                        }
                        if pair_checks >= 50_000 {
                            break;
                        }
                        pair_checks += 1;
                        check_pair(self, a1, a2);
                    }
                }
            } else {
                // Large data property (many oneOf assertions): check general negs against all pos,
                // and bucket single-oneOf concepts by their candidate value-type index.
                let mut pos_cs: Vec<u32> = Vec::new();
                let mut neg_general: Vec<u32> = Vec::new();
                let mut by_ty_idx: FxMap<usize, Vec<u32>> = FxMap::default();
                for &a in cs.iter() {
                    if self.conflict_peers[a as usize].contains(&a) {
                        continue;
                    }
                    if in_pos[a as usize] {
                        pos_cs.push(a);
                        if let Some(ixs) = d.dsome_by.get(&a) {
                            for &i in ixs {
                                for &p in &d.dsome[i].2 {
                                    if d.is_oneof_atom.get(&p).copied().unwrap_or(false) {
                                        if let Some(t_ixs) = v.by_atom.get(&p) {
                                            for &ti in t_ixs {
                                                by_ty_idx.entry(ti).or_default().push(a);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    if in_neg[a as usize] {
                        let is_pure_oneof_dall = !d.datmost_by.contains_key(&a)
                            && d.dall_by.get(&a).map_or(false, |ixs| {
                                ixs.len() == 1 && {
                                    let lits = &d.dall[ixs[0]].2;
                                    lits.len() == 1
                                        && matches!(lits[0], crate::data::Lit::Neg(j) if d.is_oneof_atom.get(&j).copied().unwrap_or(false))
                                }
                            });
                        if is_pure_oneof_dall {
                            if let Some(ixs) = d.dall_by.get(&a) {
                                if let crate::data::Lit::Neg(j) = d.dall[ixs[0]].2[0] {
                                    if let Some(t_ixs) = v.by_atom.get(&j) {
                                        for &ti in t_ixs {
                                            by_ty_idx.entry(ti).or_default().push(a);
                                        }
                                    }
                                }
                            }
                        } else {
                            neg_general.push(a);
                        }
                    }
                }
                for &a1 in &pos_cs {
                    for &a2 in &neg_general {
                        if a1 != a2 && pair_checks < 100_000 {
                            pair_checks += 1;
                            check_pair(self, a1, a2);
                        }
                    }
                }
                for bucket in by_ty_idx.values_mut() {
                    bucket.sort_unstable();
                    bucket.dedup();
                    if bucket.len() > 1 && bucket.len() <= 1024 {
                        for i in 0..bucket.len() {
                            for &a2 in &bucket[i + 1..] {
                                if (in_pos[bucket[i] as usize] || in_pos[a2 as usize]) && pair_checks < 500_000 {
                                    pair_checks += 1;
                                    check_pair(self, bucket[i], a2);
                                }
                            }
                        }
                    }
                }
            }
        }
        for &g in &self.nf.gci_empty {
            let h = &self.nf.gci[g as usize].1;
            if h.len() == 2 {
                let (h0, h1) = (h[0], h[1]);
                let p0 = self.conflict_peers[h0 as usize].clone();
                for p in p0 {
                    if p != h0 && h1 != p && !self.self_push[p as usize].contains(&h1) {
                        self.self_push[p as usize].push(h1);
                    }
                }
                let p1 = self.conflict_peers[h1 as usize].clone();
                for p in p1 {
                    if p != h1 && h0 != p && !self.self_push[p as usize].contains(&h0) {
                        self.self_push[p as usize].push(h0);
                    }
                }
            }
        }
        self.hcons_cache.clear();
        self.data = Some((d, v));
        self.rebuild_empty_inert();
    }

    // ---------- labels ----------
    pub fn lab_of_role(&self, r: u32) -> u32 {
        self.lab_up[r as usize]
    }
    pub fn flip(&mut self, l: u32) -> u32 {
        while self.lab_flip.len() < self.labs.len() {
            self.lab_flip.push(NONE);
        }
        let f = self.lab_flip[l as usize];
        if f != NONE {
            return f;
        }
        let mut v: Vec<u32> = self.labs.get(l).iter().map(|r| r ^ 1).collect();
        v.sort_unstable();
        let f = self.labs.intern(v);
        while self.lab_flip.len() < self.labs.len() {
            self.lab_flip.push(NONE);
        }
        self.lab_flip[l as usize] = f;
        self.lab_flip[f as usize] = l;
        f
    }
    /// The up-closure of a role set.
    pub fn upclose(&mut self, roles: &[u32]) -> u32 {
        let mut v: Vec<u32> = Vec::new();
        for &r in roles {
            v.extend_from_slice(&self.nf.up[r as usize]);
        }
        v.sort_unstable();
        v.dedup();
        self.labs.intern(v)
    }
    pub fn lab_or(&mut self, a: u32, b: u32) -> u32 {
        if a == b {
            return a;
        }
        let k = if a < b { (a, b) } else { (b, a) };
        if let Some(&u) = self.lab_union.get(&k) {
            return u;
        }
        let u = self.labs.union(a, b);
        self.lab_union.insert(k, u);
        u
    }
    pub fn loop_lab(&mut self, l: u32) -> u32 {
        let f = self.flip(l);
        self.lab_or(l, f)
    }

    /// Names pushed by universals from type `t` along label `l`.
    pub fn fwd(&mut self, t: u32, l: u32) -> u32 {
        if self.nf.all.is_empty() {
            return 0;
        }
        if let Some(&f) = self.fwd_cache.get(&(t, l)) {
            return f;
        }
        let ts = self.sets.get(t);
        let ls = self.labs.get(l);
        let mut out = Vec::new();
        let n_role: usize = ls.iter().map(|&s| self.nf.all_by_role.get(s).len()).sum();
        if n_role < ts.len() {
            for &s in ls.iter() {
                for &(a, c) in self.nf.all_by_role.get(s) {
                    if self.sets.has(t, a) {
                        out.push(c);
                    }
                }
            }
        } else {
            for &a in ts.iter() {
                for &(s, c) in self.nf.all_by.get(a) {
                    if ls.binary_search(&s).is_ok() {
                        out.push(c);
                    }
                }
            }
        }
        out.sort_unstable();
        out.dedup();
        let f = self.sets.intern(out);
        self.fwd_cache.insert((t, l), f);
        f
    }

    /// Names on an `l`-successor of `tx` that would push a name outside `tx`
    /// back into `tx` along `fl = flip(l)`.
    pub fn bwd_forbid(&mut self, tx: u32, fl: u32) -> u32 {
        if self.nf.all.is_empty() {
            return 0;
        }
        if let Some(&f) = self.bwd_cache.get(&(tx, fl)) {
            return f;
        }
        let fls = self.labs.get(fl);
        let mut out = Vec::new();
        for &s in fls.iter() {
            for &(a, c) in self.nf.all_by_role.get(s) {
                if !self.sets.has(tx, c) {
                    out.push(a);
                }
            }
        }
        out.sort_unstable();
        out.dedup();
        let f = self.sets.intern(out);
        self.bwd_cache.insert((tx, fl), f);
        f
    }

    /// Concepts forbidden on any `l`-successor of `tx` by `atmost _ 0 r_le c` with `r_le in l`,
    /// or `a_le` with `atmost a_le 0 r_le c` where `r_le in flip(l)` and `c in tx`.
    pub fn le0_forbid(&self, tx: u32, l: u32) -> Vec<u32> {
        if self.nf.le.is_empty() {
            return Vec::new();
        }
        let mut out = Vec::new();
        for &a in self.sets.v[(tx & !CLEAN_FB) as usize].iter() {
            if self.nf.has_le[a as usize] {
                for &(k, r_le, c) in self.nf.le_by.get(a) {
                    if k == 0 && self.labs.has(l, r_le) {
                        out.push(c);
                    }
                }
            }
        }
        for &(a_le, k, r_le, c) in &self.nf.le {
            if k == 0 && self.labs.has(l, r_le ^ 1) && self.sets.has(tx, c) {
                out.push(a_le);
            }
        }
        out.sort_unstable();
        out.dedup();
        out
    }

    // ---------- closure ----------
    pub fn clear_memo(&mut self) {
        self.memo.clear();
        self.succ_ok.clear();
    }

    #[inline]
    fn is_forbid(&self, a: u32, fst: u32, st: u32) -> bool {
        self.fmark[a as usize] == fst
            || self.cmark[a as usize] == st
            || (self.cur_clean && self.is_rowclass[a as usize] && self.tmark[a as usize] != self.cur_tst)
    }

    /// A closed type containing `seed`, avoiding `forbid` and the nogoods,
    /// preferring unnamed heads, then named heads in `target`.
    pub fn close(&mut self, seed: u32, forbid: u32, target: u32, nomok: bool) -> CloseRes {
        if self.mem_exceeded() {
            return CloseRes::Budget;
        }
        if let Some(d) = self.opt.deadline {
            if Instant::now() > d {
                return CloseRes::Budget;
            }
        }
        let key = (seed, forbid, target, nomok);
        if let Some(&r) = self.memo.get(&key) {
            // an entry made inside a cut-off lookahead may not have been checked
            if let CloseRes::Ok(t) = r {
                self.cur_target = self.sets.get(target);
                self.cur_target_id = target;
                self.cur_nomok = nomok;
                self.cur_forbid = forbid;
                self.cur_clean = (forbid & CLEAN_FB) != 0 && self.rowclasses != 0;
                if self.nest < 2 && !self.succ_check(t) {
                    self.memo.remove(&key);
                } else {
                    return r;
                }
            } else {
                return r;
            }
        }
        self.stats.closures += 1;
        let clean = (forbid & CLEAN_FB) != 0 && self.rowclasses != 0;
        self.fstamp += 1;
        let fs = self.sets.get(forbid & !CLEAN_FB);
        for &a in fs.iter() {
            self.fmark[a as usize] = self.fstamp;
        }
        self.cur_target = self.sets.get(target);
        self.cur_target_id = target;
        let tst = if clean {
            self.tstamp += 1;
            for &a in self.cur_target.iter() {
                self.tmark[a as usize] = self.tstamp;
            }
            self.tstamp
        } else {
            0
        };
        self.cur_clean = clean;
        self.cur_tst = tst;
        self.cur_nomok = nomok;
        self.cur_forbid = forbid;
        if self.nest == 0 {
            self.runs = 0;
        }
        let s = self.sets.get(seed);
        let r = self.close_from(&s, 0);
        if !matches!(r, CloseRes::Budget) {
            self.memo.insert(key, r);
        }
        r
    }

    /// Pure Horn + self_push consistency of a seed (cached, independent of forbid/target).
    fn horn_consistent(&mut self, seed_id: u32) -> bool {
        if let Some(&b) = self.hcons_cache.get(&seed_id) {
            return b;
        }
        let nf = self.nf;
        self.stamp = self.stamp.wrapping_add(1);
        if self.stamp == 0 {
            for x in self.mark.iter_mut() {
                *x = 0;
            }
            for x in self.cmark.iter_mut() {
                *x = 0;
            }
            for x in self.cstamp.iter_mut() {
                *x = 0;
            }
            self.stamp = 1;
        }
        let st = self.stamp;
        let mut q: Vec<u32> = Vec::new();
        macro_rules! hadd {
            ($a:expr) => {{
                let a = $a;
                if self.mark[a as usize] != st {
                    if self.cmark[a as usize] == st {
                        self.hcons_cache.insert(seed_id, false);
                        return false;
                    }
                    self.mark[a as usize] = st;
                    for i in 0..self.conflict_peers[a as usize].len() {
                        let p = self.conflict_peers[a as usize][i];
                        if self.mark[p as usize] == st {
                            self.hcons_cache.insert(seed_id, false);
                            return false;
                        }
                        self.cmark[p as usize] = st;
                    }
                    q.push(a);
                }
            }};
        }
        for &g in &nf.gci_empty {
            let h = &nf.gci[g as usize].1;
            if h.is_empty() {
                self.hcons_cache.insert(seed_id, false);
                return false;
            } else if h.len() == 1 {
                hadd!(h[0]);
            }
        }
        for &a in self.sets.get(seed_id).iter() {
            hadd!(a);
        }
        while let Some(a) = q.pop() {
            for i in 0..self.self_push[a as usize].len() {
                let c = self.self_push[a as usize][i];
                hadd!(c);
            }
            for &g in nf.gci_by_body.get(a) {
                let gi = g as usize;
                if self.cstamp[gi] != st {
                    self.cstamp[gi] = st;
                    self.cnt[gi] = 0;
                }
                self.cnt[gi] += 1;
                if self.cnt[gi] == nf.body_len[gi] {
                    let h = &nf.gci[gi].1;
                    if h.is_empty() {
                        self.hcons_cache.insert(seed_id, false);
                        return false;
                    } else if h.len() == 1 {
                        hadd!(h[0]);
                    }
                }
            }
        }
        self.hcons_cache.insert(seed_id, true);
        true
    }

    /// Check that for every `atmost 0/1 r_max c` in `ts`, all `ex_by`/`ge_by` fillers
    /// on `ts` under `r_max` are jointly Horn-consistent.
    fn check_atmost1_horn(&mut self, ts: &[u32]) -> bool {
        let nf = self.nf;
        let mut max_roles: Vec<(u32, u32, u32)> = Vec::new();
        for &a in ts {
            if nf.has_le[a as usize] {
                for &(k, r_max, c) in nf.le_by.get(a) {
                    if k <= 1 && !max_roles.contains(&(k, r_max, c)) {
                        max_roles.push((k, r_max, c));
                    }
                }
            }
        }
        if max_roles.is_empty() {
            return true;
        }
        for (k_max, r_max, c) in max_roles {
            let c_top = nf.gci_empty.iter().any(|&g| nf.gci[g as usize].1 == [c]);
            let mut comb: Vec<u32> = Vec::new();
            let mut n_fillers = 0usize;
            for &a in ts {
                for &(s, d) in nf.all_by.get(a) {
                    if self.labs.has(self.lab_of_role(s), r_max) {
                        comb.push(d);
                    }
                }
                for &(r, b) in nf.ex_by.get(a) {
                    if self.labs.has(self.lab_of_role(r), r_max) && (c_top || b == c) {
                        if k_max == 0 {
                            return false;
                        }
                        comb.push(b);
                        n_fillers += 1;
                    }
                }
                for &(k, r, b) in nf.ge_by.get(a) {
                    if self.labs.has(self.lab_of_role(r), r_max) && (c_top || b == c) {
                        if k > k_max {
                            return false;
                        }
                        comb.push(b);
                        n_fillers += 1;
                    }
                }
            }
            if n_fillers > 1 {
                comb.sort_unstable();
                comb.dedup();
                let cid = self.sets.intern(comb);
                if !self.horn_consistent(cid) {
                    return false;
                }
            }
        }
        true
    }

    /// Every existential of the closed type `t` has a successor seed that
    /// closes (one step; nested closures save and restore the outer state).
    fn succ_check(&mut self, t: u32) -> bool {
        if let Some(&b) = self.succ_ok.get(&t) {
            if !b || self.cur_forbid == 0 {
                return b;
            }
        }
        if self.nest >= 2 {
            return true;
        }
        let nf = self.nf;
        let ts = self.sets.get(t);
        if !self.check_atmost1_horn(&ts) {
            self.succ_ok.insert(t, false);
            return false;
        }
        let mut reqs: Vec<(u32, u32, u32)> = Vec::new();
        let mut les: Vec<(u32, u32, u32)> = Vec::new();
        for &a in ts.iter() {
            for &(r, b) in nf.ex_by.get(a) {
                reqs.push((1, r, b));
            }
            for &(k, r, b) in nf.ge_by.get(a) {
                reqs.push((k, r, b));
            }
            if nf.has_le[a as usize] {
                for &(k, r, c) in nf.le_by.get(a) {
                    les.push((k, r, c));
                }
            }
        }
        if reqs.is_empty() {
            self.succ_ok.insert(t, true);
            return true;
        }
        for &(k1, r1, b1) in &reqs {
            if k1 > 1 && nf.is_nom[b1 as usize] {
                self.succ_ok.insert(t, false);
                return false;
            }
            let l1 = self.lab_of_role(r1);
            for &(k2, r2, c2) in &les {
                if k1 > k2 && self.labs.has(l1, r2) && b1 == c2 {
                    self.succ_ok.insert(t, false);
                    return false;
                }
            }
        }
        // save the outer closure's state (do not reset `runs` so nested checks share the budget)
        let (ft, tg, tg_id, nk, fst, cln, tst) = (
            self.cur_forbid,
            self.cur_target.clone(),
            self.cur_target_id,
            self.cur_nomok,
            self.fstamp,
            self.cur_clean,
            self.cur_tst,
        );
        self.nest += 1;
        let mut ok = true;
        let mut hit_budget = false;
        // check combined `atmost 1` filler seeds first
        for &(k_max, r_max, c_max) in &les {
            if k_max != 1 {
                continue;
            }
            let c_top = nf.gci_empty.iter().any(|&g| nf.gci[g as usize].1 == [c_max]);
            let mut extra_b = Vec::new();
            let mut extra_r = Vec::new();
            for &(k1, r1, b1) in &reqs {
                let l1 = self.lab_of_role(r1);
                if self.labs.has(l1, r_max) && (c_top || b1 == c_max) {
                    if k1 > 1 {
                        ok = false;
                        break;
                    }
                    extra_b.push(b1);
                    extra_r.push(r1);
                }
            }
            if !ok {
                break;
            }
            if extra_b.len() > 1 {
                extra_b.sort_unstable();
                extra_b.dedup();
                let l_comb = self.upclose(&extra_r);
                let f_comb = self.fwd(t, l_comb);
                let s_comb = self.sets.union_vec(f_comb, &extra_b);
                let fb0 = self.sets.intern(self.le0_forbid(t, l_comb));
                match self.close(s_comb, fb0, 0, true) {
                    CloseRes::Clash => {
                        ok = false;
                        break;
                    }
                    CloseRes::Budget => hit_budget = true,
                    CloseRes::Ok(_) => {}
                }
            }
        }
        if ok {
            for (k, r, b) in reqs {
                let l = self.lab_of_role(r);
                let f = self.fwd(t, l);
                let seed = self.sets.union_vec(f, &[b]);
                let fl = self.flip(l);
                let fb0 = self.sets.intern(self.le0_forbid(t, l));
                if self.sets.get(seed).iter().any(|&o| nf.is_nom[o as usize]) {
                    if k > 1 {
                        ok = false;
                        break;
                    }
                    if fb0 != 0 && matches!(self.close(seed, fb0, 0, true), CloseRes::Clash) {
                        ok = false;
                        break;
                    }
                    continue;
                }
                // Try memo-friendly `close(seed, fb0, 0, false)` first; only compute
                // parent-specific `bwd_forbid(t, fl)` if `ts0` pushes outside `t`.
                let cr0 = self.close(seed, fb0, 0, false);
                let cr = match cr0 {
                    CloseRes::Ok(ts0) if {
                        let bk0 = self.fwd(ts0, fl);
                        self.sets.subset(bk0, t)
                    } =>
                    {
                        CloseRes::Ok(ts0)
                    }
                    CloseRes::Clash => CloseRes::Clash,
                    _ => {
                        let bfb = self.bwd_forbid(t, fl);
                        let fb = self.sets.union(fb0, bfb);
                        let cr_fb = if fb != fb0 { self.close(seed, fb, 0, false) } else { CloseRes::Clash };
                        match cr_fb {
                            CloseRes::Ok(ts_fb) => CloseRes::Ok(ts_fb),
                            CloseRes::Budget => {
                                hit_budget = true;
                                cr0
                            }
                            CloseRes::Clash => cr0,
                        }
                    }
                };
                match cr {
                    CloseRes::Clash => {
                        ok = false;
                        break;
                    }
                    CloseRes::Ok(mut ts2) => {
                        // the successor's universals back into t must close with t
                        let mut cur_fb = fb0;
                        let mut hseed_opt: Option<Vec<u32>> = None;
                        for _ in 0..8 {
                            let bk = self.fwd(ts2, fl);
                            if self.sets.subset(bk, t) {
                                break;
                            }
                            let u = self.sets.union(t, bk);
                            match self.close(u, ft, tg_id, nk) {
                                CloseRes::Ok(_) => break,
                                CloseRes::Budget => {
                                    hit_budget = true;
                                    break;
                                }
                                CloseRes::Clash => {
                                    let hseed = hseed_opt.get_or_insert_with(|| {
                                        let mut hs: Vec<u32> = self.sets.get(seed).to_vec();
                                        for &g in &nf.gci_empty {
                                            let h = &nf.gci[g as usize].1;
                                            if h.len() == 1 && !hs.contains(&h[0]) {
                                                hs.push(h[0]);
                                            }
                                        }
                                        let mut qi = 0;
                                        while qi < hs.len() {
                                            let a = hs[qi];
                                            qi += 1;
                                            for &c in &self.self_push[a as usize] {
                                                if !hs.contains(&c) {
                                                    hs.push(c);
                                                }
                                            }
                                            for &gi in nf.gci_by_body.get(a) {
                                                let (body, head) = &nf.gci[gi as usize];
                                                if head.len() == 1 && body.iter().all(|x| hs.contains(x)) && !hs.contains(&head[0]) {
                                                    hs.push(head[0]);
                                                }
                                            }
                                        }
                                        hs.sort_unstable();
                                        hs
                                    });
                                    let ts2_s = self.sets.get(ts2);
                                    let fl_s = self.labs.get(fl);
                                    let mut bad_a = Vec::new();
                                    for &a in ts2_s.iter() {
                                        if hseed.binary_search(&a).is_ok() {
                                            continue;
                                        }
                                        for &(s_fl, c) in nf.all_by.get(a) {
                                            if fl_s.binary_search(&s_fl).is_ok() && !self.sets.has(t, c) {
                                                let uc = self.sets.union_vec(t, &[c]);
                                                if matches!(self.close(uc, ft, tg_id, nk), CloseRes::Clash) {
                                                    bad_a.push(a);
                                                    break;
                                                }
                                            }
                                        }
                                    }
                                    if bad_a.is_empty() {
                                        for &a in ts2_s.iter() {
                                            if hseed.binary_search(&a).is_ok() {
                                                continue;
                                            }
                                            if nf.all_by.get(a).iter().any(|&(s_fl, c)| fl_s.binary_search(&s_fl).is_ok() && !self.sets.has(t, c)) {
                                                bad_a.push(a);
                                            }
                                        }
                                    }
                                    if bad_a.is_empty() {
                                        ok = false;
                                        break;
                                    }
                                    let next_fb = self.sets.union_vec(cur_fb, &bad_a);
                                    if next_fb == cur_fb {
                                        ok = false;
                                        break;
                                    }
                                    cur_fb = next_fb;
                                    match self.close(seed, cur_fb, 0, false) {
                                        CloseRes::Ok(ts_next) => ts2 = ts_next,
                                        CloseRes::Budget => {
                                            hit_budget = true;
                                            break;
                                        }
                                        CloseRes::Clash => {
                                            ok = false;
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                        if !ok {
                            break;
                        }
                        let bk_final = self.fwd(ts2, fl);
                        if !self.sets.subset(bk_final, t) {
                            let u = self.sets.union(t, bk_final);
                            if matches!(self.close(u, ft, tg_id, nk), CloseRes::Clash) {
                                ok = false;
                                break;
                            }
                        }
                        // if k > 1 and the successor picked a nominal, check that k distinct
                        // elements can satisfy `seed`
                        if k > 1 {
                            if let Some(o0) = self.first_nom(ts2) {
                                let mut used = vec![o0];
                                for _ in 1..k.min(4) {
                                    let fbn = self.sets.union_vec(fb0, &used);
                                    match self.close(seed, fbn, 0, false) {
                                        CloseRes::Clash => {
                                            ok = false;
                                            break;
                                        }
                                        CloseRes::Ok(tsn) => match self.first_nom(tsn) {
                                            Some(on) => {
                                                used.push(on);
                                                used.sort_unstable();
                                                used.dedup();
                                            }
                                            None => break,
                                        },
                                        CloseRes::Budget => {
                                            hit_budget = true;
                                            break;
                                        }
                                    }
                                }
                                if !ok {
                                    break;
                                }
                            }
                            for &(k2, r2, c2) in &les {
                                if k > k2 && self.labs.has(l, r2) && self.sets.has(ts2, c2) {
                                    let fc = self.sets.union_vec(fb0, &[c2]);
                                    if matches!(self.close(seed, fc, 0, false), CloseRes::Clash) {
                                        ok = false;
                                        break;
                                    }
                                }
                            }
                            if !ok {
                                break;
                            }
                        }
                    }
                    CloseRes::Budget => hit_budget = true,
                }
            }
        }
        self.nest -= 1;
        // restore: forbid marks, target
        self.fstamp = fst.max(self.fstamp) + 1;
        let fs = self.sets.get(ft & !CLEAN_FB);
        for &a in fs.iter() {
            self.fmark[a as usize] = self.fstamp;
        }
        if cln {
            self.tstamp = tst.max(self.tstamp) + 1;
            for &a in tg.iter() {
                self.tmark[a as usize] = self.tstamp;
            }
            self.cur_tst = self.tstamp;
        } else {
            self.cur_tst = 0;
        }
        self.cur_forbid = ft;
        self.cur_target = tg;
        self.cur_target_id = tg_id;
        self.cur_nomok = nk;
        self.cur_clean = cln;
        if !hit_budget && ft == 0 {
            self.succ_ok.insert(t, ok);
        }
        ok
    }

    fn rank(&self, h: u32) -> u32 {
        let nf = self.nf;
        if nf.is_nom[h as usize] {
            if self.cur_nomok {
                3
            } else {
                4
            }
        } else if !nf.named[h as usize] {
            0
        } else if self.cur_target.binary_search(&h).is_ok() {
            1
        } else {
            2
        }
    }

    fn close_from(&mut self, seed: &[u32], depth: u32) -> CloseRes {
        self.runs += 1;
        self.stats.close_runs += 1;
        if self.runs > self.opt.close_budget || depth > 4000 {
            return CloseRes::Budget;
        }
        if self.stats.close_runs & 31 == 0 {
            if self.stats.close_runs & 255 == 0 && self.mem_exceeded() {
                return CloseRes::Budget;
            }
            if let Some(d) = self.opt.deadline {
                if Instant::now() > d {
                    return CloseRes::Budget;
                }
            }
        }
        let nf = self.nf;
        self.stamp = self.stamp.wrapping_add(1);
        if self.stamp == 0 {
            for x in self.mark.iter_mut() {
                *x = 0;
            }
            for x in self.cmark.iter_mut() {
                *x = 0;
            }
            for x in self.cstamp.iter_mut() {
                *x = 0;
            }
            for x in self.r_direct_st.iter_mut() {
                *x = 0;
            }
            for x in self.r_up_st.iter_mut() {
                *x = 0;
            }
            for x in self.w_role_st.iter_mut() {
                *x = 0;
            }
            self.stamp = 1;
        }
        let st = self.stamp;
        let fst = self.fstamp;
        let mut t: Vec<u32> = Vec::with_capacity(seed.len() + 16);
        let mut q: Vec<u32> = Vec::new();
        let mut pend: Vec<u32> = Vec::new();
        macro_rules! add {
            ($a:expr) => {{
                let a = $a;
                if self.mark[a as usize] != st {
                    if self.is_forbid(a, fst, st) {
                        return CloseRes::Clash;
                    }
                    self.mark[a as usize] = st;
                    for i in 0..self.conflict_peers[a as usize].len() {
                        let p = self.conflict_peers[a as usize][i];
                        if self.mark[p as usize] == st {
                            return CloseRes::Clash;
                        }
                        self.cmark[p as usize] = st;
                    }
                    t.push(a);
                    q.push(a);
                }
            }};
        }
        for i_e in 0..self.empty_other.len() {
            let g = self.empty_other[i_e];
            let h = &nf.gci[g as usize].1;
            match h.len() {
                0 => return CloseRes::Clash,
                1 => add!(h[0]),
                _ => pend.push(g),
            }
        }
        for &a in seed {
            add!(a);
        }
        let mut auto_checked = false;
        loop {
            while let Some(a) = q.pop() {
                for i in 0..self.self_push[a as usize].len() {
                    let c = self.self_push[a as usize][i];
                    add!(c);
                }
                if self.has_bounce {
                    let nr = self.r_direct_st.len();
                    for &(r, _) in nf.ex_by.get(a) {
                        let ru = r as usize;
                        if ru < nr && self.r_direct_st[ru] != st {
                            self.r_direct_st[ru] = st;
                            for i in 0..nf.up[ru].len() {
                                let su = nf.up[ru][i] as usize;
                                if self.r_up_st[su] != st {
                                    self.r_up_st[su] = st;
                                    if self.w_role_st[su] == st {
                                        for j in 0..self.w_role_list[su].len() {
                                            let c2 = self.w_role_list[su][j];
                                            add!(c2);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    for &(k, r, _) in nf.ge_by.get(a) {
                        let ru = r as usize;
                        if k >= 1 && ru < nr && self.r_direct_st[ru] != st {
                            self.r_direct_st[ru] = st;
                            for i in 0..nf.up[ru].len() {
                                let su = nf.up[ru][i] as usize;
                                if self.r_up_st[su] != st {
                                    self.r_up_st[su] = st;
                                    if self.w_role_st[su] == st {
                                        for j in 0..self.w_role_list[su].len() {
                                            let c2 = self.w_role_list[su][j];
                                            add!(c2);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    for i in 0..self.bounce[a as usize].len() {
                        let (s, c2) = self.bounce[a as usize][i];
                        let su = s as usize;
                        if self.r_up_st[su] == st {
                            add!(c2);
                        } else {
                            if self.w_role_st[su] != st {
                                self.w_role_st[su] = st;
                                self.w_role_list[su].clear();
                            }
                            self.w_role_list[su].push(c2);
                        }
                    }
                }
                for &g in nf.gci_by_body.get(a) {
                    let gi = g as usize;
                    if self.cstamp[gi] != st {
                        self.cstamp[gi] = st;
                        self.cnt[gi] = 0;
                    }
                    self.cnt[gi] += 1;
                    if self.cnt[gi] == nf.body_len[gi] {
                        let h = &nf.gci[gi].1;
                        match h.len() {
                            0 => return CloseRes::Clash,
                            1 => add!(h[0]),
                            _ => pend.push(g),
                        }
                    }
                }
            }
            if !auto_checked && !self.empty_auto_inert.is_empty() {
                auto_checked = true;
                let mut auto_unit = false;
                for i_a in 0..self.empty_auto_inert.len() {
                    let (g, cand) = self.empty_auto_inert[i_a];
                    let h = &nf.gci[g as usize].1;
                    if h.iter().any(|&x| self.mark[x as usize] == st) {
                        continue;
                    }
                    if !self.is_forbid(cand, fst, st) && self.cmark[cand as usize] != st {
                        self.mark[cand as usize] = st;
                        for j in 0..self.conflict_peers[cand as usize].len() {
                            let p = self.conflict_peers[cand as usize][j];
                            if self.mark[p as usize] == st {
                                return CloseRes::Clash;
                            }
                            self.cmark[p as usize] = st;
                        }
                        t.push(cand);
                    } else {
                        pend.push(g);
                        auto_unit = true;
                    }
                }
                if auto_unit {
                    // let the unit propagation loop below inspect any fallback `g` pushed to `pend`
                }
            }
            // unit propagation on disjunctive GCIs with <= 1 unforbidden head
            let mut unit_added = false;
            for &g in &pend {
                let h = &nf.gci[g as usize].1;
                if h.iter().any(|&x| self.mark[x as usize] == st) {
                    continue;
                }
                let mut only = NONE;
                let mut cnt_u = 0usize;
                for &x in h {
                    if !self.is_forbid(x, fst, st) {
                        only = x;
                        cnt_u += 1;
                        if cnt_u > 1 {
                            break;
                        }
                    }
                }
                if cnt_u == 0 {
                    return CloseRes::Clash;
                }
                if cnt_u == 1 {
                    add!(only);
                    unit_added = true;
                }
            }
            if !unit_added {
                // If all triggered non-empty-body disjunctions are satisfied, batch-assign
                // inert heads of open empty-body disjunctions without branching.
                let has_open_non_empty = pend.iter().any(|&g| {
                    let (body, h) = &nf.gci[g as usize];
                    !body.is_empty() && !h.iter().any(|&x| self.mark[x as usize] == st)
                });
                if !has_open_non_empty {
                    let has_active_dreq = t.iter().any(|&a| self.dreq[a as usize] > 0);
                    let mut inert_added = false;
                    for i_p in 0..pend.len() {
                        let g = pend[i_p];
                        let (body, h) = &nf.gci[g as usize];
                        if !body.is_empty() || h.iter().any(|&x| self.mark[x as usize] == st) {
                            continue;
                        }
                        let mut best_inert: Option<(bool, u32)> = None;
                        for &cand in h {
                            if self.is_forbid(cand, fst, st) || self.cmark[cand as usize] == st {
                                continue;
                            }
                            let check_atom = |x: u32| -> bool {
                                let xu = x as usize;
                                !nf.named[xu]
                                    && !nf.is_nom[xu]
                                    && nf.ex_by.get(x).is_empty()
                                    && nf.ge_by.get(x).is_empty()
                                    && nf.all_by.get(x).is_empty()
                                    && !nf.has_le[xu]
                                    && self.dreq[xu] == 0
                                    && (!self.has_data[xu]
                                        || (!has_active_dreq
                                            || self.data.as_ref().map_or(false, |(d, _)| !d.datmost_by.contains_key(&x))))
                                    && self.bounce[xu].is_empty()
                                    && nf.gci_by_body.get(x).iter().all(|&gi| {
                                        let giu = gi as usize;
                                        let c_cur = if self.cstamp[giu] == st { self.cnt[giu] } else { 0 };
                                        c_cur + 1 < nf.body_len[giu]
                                    })
                            };
                            let cu = cand as usize;
                            let is_inert = check_atom(cand)
                                && self.self_push[cu]
                                    .iter()
                                    .all(|&c| !self.is_forbid(c, fst, st) && self.cmark[c as usize] != st && check_atom(c));
                            if is_inert {
                                let k = (self.has_data[cu], cand);
                                if best_inert.map_or(true, |b| k < b) {
                                    best_inert = Some(k);
                                }
                            }
                        }
                        if let Some((_, cand)) = best_inert {
                            add!(cand);
                            inert_added = true;
                        }
                    }
                    if inert_added {
                        continue;
                    }
                }
                break;
            }
        }
        if !pend.is_empty() && !self.check_atmost1_horn(&t) {
            return CloseRes::Clash;
        }
        // data requirements only grow with the type: prune a partial type without a data star
        if self.data.is_some() && !pend.is_empty() && t.iter().any(|&a| self.dreq[a as usize] > 0) {
            let mut ds: Vec<u32> = t.iter().copied().filter(|&a| self.has_data[a as usize]).collect();
            if !ds.is_empty() {
                ds.sort_unstable();
                if !self.has_data_star(ds) {
                    return CloseRes::Clash;
                }
            }
        }
        // select open disjunctive GCI: triggered non-empty-body clauses first, then MRV
        let mut open: Option<(bool, usize, u32)> = None;
        for &g in &pend {
            let (body, h) = &nf.gci[g as usize];
            if h.iter().any(|&x| self.mark[x as usize] == st) {
                continue;
            }
            let cnt_u = h.iter().filter(|&&x| !self.is_forbid(x, fst, st)).count();
            let key = (body.is_empty(), cnt_u, g);
            if open.map(|o| key < o).unwrap_or(true) {
                open = Some(key);
            }
        }
        if let Some((_, _, g)) = open {
            let heads0: Vec<u32> =
                nf.gci[g as usize].1.iter().copied().filter(|&h| !self.is_forbid(h, fst, st)).collect();
            // one-step lookahead: Horn consequences + triggered disjunctions of each head
            let mut keyed: Vec<((u32, usize, u32, usize, usize, u32), u32)> = Vec::with_capacity(heads0.len());
            for &h in &heads0 {
                let rk = self.rank(h);
                if heads0.len() == 1 {
                    keyed.push(((0, 0, rk, 0, 0, h), h));
                    continue;
                }
                let mut s2 = t.clone();
                s2.push(h);
                match self.horn_eval(&s2) {
                    None => continue,
                    Some((dirty, noms, new_disj, reqs)) => {
                        keyed.push((((rk >= 3 || noms > 0) as u32, dirty, rk, new_disj, reqs, h), h))
                    }
                }
            }
            keyed.sort();
            for (_, h) in keyed {
                let mut s2 = t.clone();
                s2.push(h);
                match self.close_from(&s2, depth + 1) {
                    CloseRes::Clash => continue,
                    r => return r,
                }
            }
            return CloseRes::Clash;
        }
        t.sort_unstable();
        let id = self.sets.intern(t);
        if !self.bad.is_empty() && self.bad.contains(&id) {
            return CloseRes::Clash;
        }
        if !self.succ_check(id) {
            return CloseRes::Clash;
        }
        if self.data.is_some() && self.sets.v[id as usize].iter().any(|&a| self.dreq[a as usize] > 0) {
            let ds: Vec<u32> = self.sets.v[id as usize]
                .iter()
                .copied()
                .filter(|&a| self.has_data[a as usize])
                .collect();
            if !self.has_data_star(ds) {
                return CloseRes::Clash;
            }
        }
        CloseRes::Ok(id)
    }

    /// Horn + unit propagation lookahead: None on a clash, else
    /// (dirty named classes, nominals, triggered disjunctions, existential obligations).
    fn horn_eval(&mut self, seed: &[u32]) -> Option<(usize, usize, usize, usize)> {
        self.runs += 1;
        let nf = self.nf;
        self.stamp = self.stamp.wrapping_add(1);
        if self.stamp == 0 {
            for x in self.mark.iter_mut() {
                *x = 0;
            }
            for x in self.cmark.iter_mut() {
                *x = 0;
            }
            for x in self.cstamp.iter_mut() {
                *x = 0;
            }
            self.stamp = 1;
        }
        let st = self.stamp;
        let fst = self.fstamp;
        let mut q: Vec<u32> = Vec::new();
        let mut vis: Vec<u32> = Vec::with_capacity(seed.len() + 16);
        let mut pend: Vec<u32> = Vec::new();
        let (mut dirty, mut noms, mut new_disj, mut reqs) = (0usize, 0usize, 0usize, 0usize);
        macro_rules! add {
            ($a:expr) => {{
                let a = $a;
                if self.mark[a as usize] != st {
                    if self.is_forbid(a, fst, st) {
                        return None;
                    }
                    self.mark[a as usize] = st;
                    for i in 0..self.conflict_peers[a as usize].len() {
                        let p = self.conflict_peers[a as usize][i];
                        if self.mark[p as usize] == st {
                            return None;
                        }
                        self.cmark[p as usize] = st;
                    }
                    if nf.is_nom[a as usize] {
                        noms += 1;
                    } else if nf.named[a as usize] && self.cur_target.binary_search(&a).is_err() {
                        dirty += 1;
                    }
                    for &(k, _, b) in nf.ge_by.get(a) {
                        if k > 1 && nf.is_nom[b as usize] {
                            return None;
                        }
                    }
                    reqs += nf.ex_by.get(a).len()
                        + nf.ge_by.get(a).len()
                        + self.dreq.get(a as usize).copied().unwrap_or(0) as usize;
                    vis.push(a);
                    q.push(a);
                }
            }};
        }
        for &g in &nf.gci_empty {
            let h = &nf.gci[g as usize].1;
            match h.len() {
                0 => return None,
                1 => add!(h[0]),
                _ => pend.push(g),
            }
        }
        for &a in seed {
            add!(a);
        }
        loop {
            while let Some(a) = q.pop() {
                for i in 0..self.self_push[a as usize].len() {
                    let c = self.self_push[a as usize][i];
                    add!(c);
                }
                for &g in nf.gci_by_body.get(a) {
                    let gi = g as usize;
                    if self.cstamp[gi] != st {
                        self.cstamp[gi] = st;
                        self.cnt[gi] = 0;
                    }
                    self.cnt[gi] += 1;
                    if self.cnt[gi] == nf.body_len[gi] {
                        let h = &nf.gci[gi].1;
                        match h.len() {
                            0 => return None,
                            1 => add!(h[0]),
                            _ => pend.push(g),
                        }
                    }
                }
            }
            let mut unit_added = false;
            for &g in &pend {
                let h = &nf.gci[g as usize].1;
                if h.iter().any(|&x| self.mark[x as usize] == st) {
                    continue;
                }
                let mut only = NONE;
                let mut cnt_u = 0usize;
                for &x in h {
                    if !self.is_forbid(x, fst, st) {
                        only = x;
                        cnt_u += 1;
                        if cnt_u > 1 {
                            break;
                        }
                    }
                }
                if cnt_u == 0 {
                    return None;
                }
                if cnt_u == 1 {
                    add!(only);
                    unit_added = true;
                }
            }
            if !unit_added {
                break;
            }
        }
        for &g in &pend {
            let (body, h) = &nf.gci[g as usize];
            if h.iter().any(|&x| self.mark[x as usize] == st) {
                continue;
            }
            if !body.is_empty() {
                new_disj += 1;
            }
            let mut all_nom = true;
            let mut all_dirty = true;
            let mut has_any = false;
            for &x in h {
                if self.is_forbid(x, fst, st) {
                    continue;
                }
                has_any = true;
                if !nf.is_nom[x as usize] {
                    all_nom = false;
                    if !(nf.named[x as usize] && self.cur_target.binary_search(&x).is_err()) {
                        all_dirty = false;
                    }
                }
            }
            if !has_any {
                return None;
            }
            if all_nom {
                noms += 1;
            } else if all_dirty {
                dirty += 1;
            }
        }
        if !self.check_atmost1_horn(&vis) {
            return None;
        }
        Some((dirty, noms, new_disj, reqs))
    }

    // ---------- graph ----------
    pub fn add_edge(&mut self, m: &mut Model, x: Id, y: Id, l: u32) {
        let l = if x == y { self.loop_lab(l) } else { l };
        let fl = self.flip(l);
        let ex = m.edge_label(x, y);
        match ex {
            Some(l0) => {
                if self.labs.subset(l, l0) {
                    return;
                }
                let u = self.lab_or(l0, l);
                m.update_edge(x, y, u);
                if x != y {
                    let fu = self.flip(u);
                    m.update_edge(y, x, fu);
                }
            }
            None => {
                m.push_edge(x, y, l);
                if x != y {
                    m.push_edge(y, x, fl);
                }
            }
        }
        // no requeue here: a reused neighbour changes neither type (`compatible`);
        // callers requeue where a type or a count can change
    }

    pub fn remove_edge(&mut self, m: &mut Model, x: Id, y: Id) {
        m.em(x).edges.retain(|e| e.0 != y);
        if x != y {
            m.em(y).edges.retain(|e| e.0 != x);
        }
        m.enqueue(x);
        m.enqueue(y);
    }

    /// Identify element `a` with `b` (b survives).
    pub fn merge(&mut self, m: &mut Model, a: Id, b: Id) {
        if a == b {
            return;
        }
        self.stats.merges += 1;
        let ea = m.elems[a as usize].clone();
        let ta = self.sets.get(ea.ty);
        {
            let eb = m.em(b);
            eb.pending.extend_from_slice(&ta);
            eb.pending.extend_from_slice(&ea.pending);
            if ea.nom {
                eb.nom = true;
            }
            if ea.pinned {
                eb.pinned = true;
            }
        }
        let fa = ea.forced;
        let fb = m.elems[b as usize].forced;
        let fu = self.sets.union(fb, fa);
        m.em(b).forced = fu;
        for &(z, _l) in &ea.edges {
            if z != a {
                m.em(z).edges.retain(|e| e.0 != a);
                m.enqueue(z);
            }
        }
        for &(z, l) in &ea.edges {
            let z2 = if z == a { b } else { z };
            self.add_edge(m, b, z2, l);
            m.enqueue(z2);
        }
        {
            let e = m.em(a);
            e.alive = false;
            e.edges.clear();
            e.pending.clear();
        }
        m.set_uf(a, b);
        let mut extra_merges: Vec<Id> = Vec::new();
        for &o in ta.iter() {
            if self.nf.is_nom[o as usize] {
                match m.nom_elem.get(&o).copied() {
                    Some(z) => {
                        let z = m.find(z);
                        if z == a || z == b {
                            m.set_nom(o, b);
                        } else if !extra_merges.contains(&z) {
                            extra_merges.push(z);
                        }
                    }
                    None => {
                        m.set_nom(o, b);
                    }
                }
            }
        }
        m.enqueue(b);
        for z in extra_merges {
            let b_cur = m.find(b);
            let z_cur = m.find(z);
            if b_cur != z_cur {
                self.merge(m, b_cur, z_cur);
            }
        }
    }

    fn count(&self, m: &Model, x: Id, r: u32, b: u32, exclude: Id) -> usize {
        let mut c = 0;
        for &(y, l) in &m.elems[x as usize].edges {
            if y != exclude && self.labs.has(l, r) && self.sets.has(m.elems[y as usize].ty, b) {
                c += 1;
            }
        }
        c
    }

    fn has_nbr(&self, m: &Model, x: Id, r: u32, b: u32) -> bool {
        m.elems[x as usize]
            .edges
            .iter()
            .any(|&(y, l)| self.labs.has(l, r) && self.sets.has(m.elems[y as usize].ty, b))
    }

    /// Can `y` serve as an `l`-neighbour of `x` without changing either type
    /// or breaking an at-most clause?
    pub fn compatible(&mut self, m: &Model, x: Id, y: Id, l: u32) -> bool {
        if x == y && !self.opt.loops {
            return false;
        }
        if self.nf.all.is_empty() && self.nf.le.is_empty() {
            return true;
        }
        let mut l2 = if x == y { self.loop_lab(l) } else { l };
        let existing = if self.nf.le.is_empty() { None } else { m.edge_label(x, y) };
        if let Some(l0) = existing {
            l2 = self.lab_or(l2, l0);
        }
        let tx = m.elems[x as usize].ty;
        let ty = m.elems[y as usize].ty;
        let f = self.fwd(tx, l2);
        if !self.sets.subset(f, ty) {
            return false;
        }
        let fl = self.flip(l2);
        let b = self.fwd(ty, fl);
        if !self.sets.subset(b, tx) {
            return false;
        }
        if self.nf.le.is_empty() || existing == Some(l2) {
            return true;
        }
        let nf = self.nf;
        // at-most at y over the new neighbour x
        let tys = self.sets.get(ty);
        for &a in tys.iter() {
            if !nf.has_le[a as usize] {
                continue;
            }
            for &(k, r, c) in nf.le_by.get(a) {
                if self.labs.has(fl, r) && self.sets.has(tx, c) && self.count(m, y, r, c, x) + 1 > k as usize {
                    return false;
                }
            }
        }
        let txs = self.sets.get(tx);
        for &a in txs.iter() {
            if !nf.has_le[a as usize] {
                continue;
            }
            for &(k, r, c) in nf.le_by.get(a) {
                if self.labs.has(l2, r) && self.sets.has(ty, c) && self.count(m, x, r, c, y) + 1 > k as usize {
                    return false;
                }
            }
        }
        true
    }

    /// Like `compatible`, but the universals of `y` may push names back into
    /// `x` (returned) as long as x's type still closes and pushes nothing new to `y`.
    fn compatible_push(&mut self, m: &Model, x: Id, y: Id, l: u32) -> Option<Vec<u32>> {
        if x == y && !self.opt.loops {
            return None;
        }
        let mut l2 = if x == y { self.loop_lab(l) } else { l };
        if let Some(l0) = m.edge_label(x, y) {
            l2 = self.lab_or(l2, l0);
        }
        let tx = m.elems[x as usize].ty;
        let ty = m.elems[y as usize].ty;
        if !m.elems[y as usize].pending.is_empty() {
            return None;
        }
        let f = self.fwd(tx, l2);
        if !self.sets.subset(f, ty) {
            return None;
        }
        let fl = self.flip(l2);
        let b = self.fwd(ty, fl);
        let back = minus_sorted(&self.sets.get(b), &self.sets.get(tx));
        if back.is_empty() {
            return if self.compatible(m, x, y, l) { Some(back) } else { None };
        }
        let nf = self.nf;
        if back.iter().any(|&a| nf.is_nom[a as usize] || nf.has_le[a as usize]) {
            return None;
        }
        let e = &m.elems[x as usize];
        let (fb, tg, nm, own) = (e.forbid, e.target, e.nom, e.owner);
        let s1 = self.sets.union_vec(tx, &back);
        let cr = if own == NONE {
            self.close_clean(s1, fb, tg, nm)
        } else {
            self.close(s1, fb, tg, nm)
        };
        let tx2 = match cr {
            CloseRes::Ok(t) => t,
            _ => return None,
        };
        if own == NONE
            && self.rowclasses != 0
            && self
                .sets
                .get(tx2)
                .iter()
                .any(|&c| self.is_rowclass[c as usize] && !self.sets.has(tg, c) && !self.sets.has(tx, c))
        {
            return None;
        }
        let f2 = self.fwd(tx2, l2);
        if !self.sets.subset(f2, ty) {
            return None;
        }
        if !nf.le.is_empty() && !self.atmost_ok(m, x, tx2, y, ty, l2) {
            return None;
        }
        Some(back)
    }

    /// Adding the edge x -l-> y (types tx, ty) exceeds no at-most clause at either end.
    fn atmost_ok(&mut self, m: &Model, x: Id, tx: u32, y: Id, ty: u32, l: u32) -> bool {
        let nf = self.nf;
        let fl = self.flip(l);
        let tys = self.sets.get(ty);
        for &a in tys.iter() {
            if !nf.has_le[a as usize] {
                continue;
            }
            for &(k, r, c) in nf.le_by.get(a) {
                if self.labs.has(fl, r) && self.sets.has(tx, c) && self.count(m, y, r, c, x) + 1 > k as usize {
                    return false;
                }
            }
        }
        let txs = self.sets.get(tx);
        for &a in txs.iter() {
            if !nf.has_le[a as usize] {
                continue;
            }
            for &(k, r, c) in nf.le_by.get(a) {
                if self.labs.has(l, r) && self.sets.has(ty, c) && self.count(m, x, r, c, y) + 1 > k as usize {
                    return false;
                }
            }
        }
        true
    }

    fn first_nom(&self, t: u32) -> Option<u32> {
        self.sets.get(t).iter().copied().find(|&a| self.nf.is_nom[a as usize])
    }

    /// Give `x` `need` more `r`-neighbours in `b`.
    fn satisfy(&mut self, m: &mut Model, x: Id, r: u32, b: u32, need: usize) -> Result<(), Fail> {
        let mut l = self.lab_of_role(r);
        let tx = m.elems[x as usize].ty;
        let f = self.fwd(tx, l);
        let mut seed = self.sets.union_vec(f, &[b]);
        // if x has `<= 1 r_max.c` with `r <= r_max` and `c` holds on every `r_max`-filler,
        // combine all non-nominal `ex_by` fillers on `x` under `r_max` into a single seed
        if need == 1 {
            let txs = self.sets.get(tx);
            let mut max_roles: Vec<(u32, u32)> = Vec::new();
            for &a in txs.iter() {
                if self.nf.has_le[a as usize] {
                    for &(k, r_max, c) in self.nf.le_by.get(a) {
                        if k == 1 && self.labs.has(l, r_max) {
                            let c_top = self.sets.has(f, c)
                                || self.nf.gci_empty.iter().any(|&g| self.nf.gci[g as usize].1 == [c]);
                            if c_top || b == c {
                                max_roles.push((r_max, c));
                            }
                        }
                    }
                }
            }
            if !max_roles.is_empty() {
                let mut extra_b = vec![b];
                let mut extra_r = vec![r];
                let mut nom_fillers: Vec<u32> = Vec::new();
                if self.nf.is_nom[b as usize] {
                    nom_fillers.push(b);
                }
                for &(yn, ln) in &m.elems[x as usize].edges {
                    let tyn = m.elems[yn as usize].ty;
                    let fits_yn = max_roles.iter().any(|&(r_max, c)| {
                        self.labs.has(ln, r_max)
                            && (self.sets.has(tyn, c)
                                || self.nf.gci_empty.iter().any(|&g| self.nf.gci[g as usize].1 == [c]))
                    });
                    if fits_yn {
                        if let Some(o_yn) = self.first_nom(tyn) {
                            nom_fillers.push(o_yn);
                            extra_b.push(o_yn);
                        }
                    }
                }
                for &a in txs.iter() {
                    for &(r2, b2) in self.nf.ex_by.get(a) {
                        let l2 = self.lab_of_role(r2);
                        let f2 = self.fwd(tx, l2);
                        let fits_max = max_roles.iter().any(|&(r_max, c)| {
                            self.labs.has(l2, r_max)
                                && (b2 == c
                                    || self.sets.has(f2, c)
                                    || self.nf.gci_empty.iter().any(|&g| self.nf.gci[g as usize].1 == [c]))
                        });
                        if fits_max {
                            if self.nf.is_nom[b2 as usize] {
                                nom_fillers.push(b2);
                            }
                            extra_b.push(b2);
                            extra_r.push(r2);
                        }
                    }
                }
                nom_fillers.sort_unstable();
                nom_fillers.dedup();
                if nom_fillers.len() <= 1 && extra_b.len() > 1 {
                    extra_b.sort_unstable();
                    extra_b.dedup();
                    let l_comb = self.upclose(&extra_r);
                    let f_comb = self.fwd(tx, l_comb);
                    let s_comb = self.sets.union_vec(f_comb, &extra_b);
                    let fl_comb = self.flip(l_comb);
                    let fb_comb = self.bwd_forbid(tx, fl_comb);
                    let nomok_c = !nom_fillers.is_empty();
                    let ok_comb = if fb_comb != 0 && matches!(self.close(s_comb, fb_comb, 0, nomok_c), CloseRes::Ok(_)) {
                        true
                    } else {
                        matches!(self.close(s_comb, 0, 0, nomok_c), CloseRes::Ok(_))
                    };
                    if ok_comb {
                        l = l_comb;
                        seed = s_comb;
                    }
                }
            } else if !self.nf.is_nom[b as usize]
                && txs.iter().any(|&a| {
                    self.nf.has_le[a as usize]
                        && self.nf.le_by.get(a).iter().any(|&(_, r_le, _)| self.labs.has(l, r_le))
                })
            {
                // combine non-nominal `ex_by` fillers on `x` for the exact same role `r`
                let mut same_b = vec![b];
                for &a in txs.iter() {
                    for &(r2, b2) in self.nf.ex_by.get(a) {
                        if r2 == r && b2 != b && !self.nf.is_nom[b2 as usize] {
                            same_b.push(b2);
                        }
                    }
                }
                if same_b.len() > 1 && same_b.len() <= 8 {
                    same_b.sort_unstable();
                    same_b.dedup();
                    let s_comb = self.sets.union_vec(f, &same_b);
                    let fl_comb = self.flip(l);
                    let fb_comb = self.bwd_forbid(tx, fl_comb);
                    let ok_comb = if matches!(self.close(s_comb, fb_comb, 0, false), CloseRes::Ok(_)) {
                        true
                    } else if !m.elems[x as usize].nom {
                        matches!(self.close(s_comb, 0, 0, false), CloseRes::Ok(_))
                    } else {
                        false
                    };
                    if ok_comb {
                        seed = s_comb;
                    }
                }
            }
        }
        if need == 1 {
            let nbrs: Vec<Id> = m.elems[x as usize].edges.iter().take(self.opt.reuse_scan).map(|e| e.0).collect();
            for yn in nbrs {
                let yn = m.find(yn);
                let ey = &m.elems[yn as usize];
                if !ey.alive || !self.sets.subset(seed, ey.ty) || !ey.pending.is_empty() {
                    continue;
                }
                if !self.nf.ge.is_empty() {
                    if let Some(l0) = m.edge_label(x, yn) {
                        if self.labs.has(l0, r) && self.sets.has(ey.ty, b) {
                            continue;
                        }
                    }
                }
                if self.compatible(m, x, yn, l) {
                    self.add_edge(m, x, yn, l);
                    self.stats.reused += 1;
                    return Ok(());
                }
            }
        }
        let fl = self.flip(l);
        let fb0 = self.sets.intern(self.le0_forbid(tx, l));
        let mut cap_v = Vec::new();
        if !self.nf.le.is_empty() {
            for &a in self.sets.get(tx).iter() {
                if self.nf.has_le[a as usize] {
                    for &(k_le, r_le, c_le) in self.nf.le_by.get(a) {
                        if k_le > 0 && self.labs.has(l, r_le) && self.count(m, x, r_le, c_le, NONE) >= k_le as usize {
                            cap_v.push(c_le);
                        }
                    }
                }
            }
            cap_v.sort_unstable();
            cap_v.dedup();
        }
        let cap_fb = self.sets.intern(cap_v);
        let nomseed = self.first_nom(seed);
        let (x_fb, x_tg, x_nm) = {
            let ex = &m.elems[x as usize];
            (ex.forbid, ex.target, ex.nom)
        };
        let close_succ = |en: &mut Self, s: u32, extra_fb: &[u32]| -> Result<u32, Fail> {
            let hard_fb0 = en.sets.union_vec(fb0, extra_fb);
            let hard_fb_cap = en.sets.union(hard_fb0, cap_fb);
            let mut hard_fb = hard_fb0;
            let cr0 = if hard_fb_cap != hard_fb0 {
                let cr_c = en.close(s, hard_fb_cap, 0, false);
                if matches!(cr_c, CloseRes::Ok(_)) {
                    hard_fb = hard_fb_cap;
                    cr_c
                } else {
                    en.close(s, hard_fb0, 0, false)
                }
            } else {
                en.close(s, hard_fb0, 0, false)
            };
            if let CloseRes::Ok(t0) = cr0 {
                let bk0 = en.fwd(t0, fl);
                if en.sets.subset(bk0, tx) {
                    return Ok(t0);
                }
            }
            if !matches!(cr0, CloseRes::Clash) {
                let fb = en.bwd_forbid(tx, fl);
                let fb_all = en.sets.union(fb, hard_fb);
                if fb_all != hard_fb {
                    if let CloseRes::Ok(t) = en.close(s, fb_all, 0, false) {
                        return Ok(t);
                    }
                    let fbs = en.sets.get(fb);
                    if fbs.len() > 1 && fbs.len() <= 32 && !fbs.iter().any(|&a| en.nf.is_nom[a as usize]) {
                        let h = fbs.len() / 2;
                        let fb1 = en.sets.union_vec(hard_fb, &fbs[..h]);
                        if let CloseRes::Ok(t) = en.close(s, fb1, 0, false) {
                            let bk1 = en.fwd(t, fl);
                            let u1 = en.sets.union(tx, bk1);
                            if en.sets.subset(bk1, tx) || matches!(en.close(u1, x_fb, x_tg, x_nm), CloseRes::Ok(_)) {
                                return Ok(t);
                            }
                        }
                        let fb2 = en.sets.union_vec(hard_fb, &fbs[h..]);
                        if let CloseRes::Ok(t) = en.close(s, fb2, 0, false) {
                            let bk2 = en.fwd(t, fl);
                            let u2 = en.sets.union(tx, bk2);
                            if en.sets.subset(bk2, tx) || matches!(en.close(u2, x_fb, x_tg, x_nm), CloseRes::Ok(_)) {
                                return Ok(t);
                            }
                        }
                    }
                }
            }
            match cr0 {
                CloseRes::Ok(mut t) => {
                    let mut cur_fb = hard_fb;
                    let mut hseed_opt: Option<Vec<u32>> = None;
                    for _ in 0..8 {
                        let bk = en.fwd(t, fl);
                        if en.sets.subset(bk, tx) {
                            return Ok(t);
                        }
                        let u = en.sets.union(tx, bk);
                        if matches!(en.close(u, x_fb, x_tg, x_nm), CloseRes::Ok(_)) {
                            return Ok(t);
                        }
                        let hseed = hseed_opt.get_or_insert_with(|| {
                            let mut hs: Vec<u32> = en.sets.get(s).to_vec();
                            for &g in &en.nf.gci_empty {
                                let h = &en.nf.gci[g as usize].1;
                                if h.len() == 1 && !hs.contains(&h[0]) {
                                    hs.push(h[0]);
                                }
                            }
                            let mut qi = 0;
                            while qi < hs.len() {
                                let a = hs[qi];
                                qi += 1;
                                for &c in &en.self_push[a as usize] {
                                    if !hs.contains(&c) {
                                        hs.push(c);
                                    }
                                }
                                for &gi in en.nf.gci_by_body.get(a) {
                                    let (body, head) = &en.nf.gci[gi as usize];
                                    if head.len() == 1 && body.iter().all(|x| hs.contains(x)) && !hs.contains(&head[0]) {
                                        hs.push(head[0]);
                                    }
                                }
                            }
                            hs.sort_unstable();
                            hs
                        });
                        let ts_s = en.sets.get(t);
                        let fl_s = en.labs.get(fl);
                        let mut bad_a = Vec::new();
                        for &a in ts_s.iter() {
                            if hseed.binary_search(&a).is_ok() {
                                continue;
                            }
                            for &(s_fl, c) in en.nf.all_by.get(a) {
                                if fl_s.binary_search(&s_fl).is_ok() && !en.sets.has(tx, c) {
                                    let uc = en.sets.union_vec(tx, &[c]);
                                    if matches!(en.close(uc, x_fb, x_tg, x_nm), CloseRes::Clash) {
                                        bad_a.push(a);
                                        break;
                                    }
                                }
                            }
                        }
                        if bad_a.is_empty() {
                            for &a in ts_s.iter() {
                                if hseed.binary_search(&a).is_ok() {
                                    continue;
                                }
                                if en.nf.all_by.get(a).iter().any(|&(s_fl, c)| fl_s.binary_search(&s_fl).is_ok() && !en.sets.has(tx, c)) {
                                    bad_a.push(a);
                                }
                            }
                        }
                        if bad_a.is_empty() {
                            break;
                        }
                        let next_fb = en.sets.union_vec(cur_fb, &bad_a);
                        if next_fb == cur_fb {
                            break;
                        }
                        cur_fb = next_fb;
                        match en.close(s, cur_fb, 0, false) {
                            CloseRes::Ok(t_next) => t = t_next,
                            _ => break,
                        }
                    }
                    Ok(t)
                }
                CloseRes::Clash => {
                    if en.debug {
                        eprintln!(
                            "debug: no successor type: x {} tx {} succ_ok {:?} r {} b {} seed {:?}",
                            x,
                            tx,
                            en.succ_ok.get(&tx),
                            r,
                            b,
                            en.sets.get(s)
                        );
                    }
                    Err(Fail::new("no type for a successor", vec![tx]))
                }
                CloseRes::Budget => Err(Fail::new("closure budget", vec![tx])),
            }
        };
        // Only forbid nominals on existing `r`-neighbours that ALREADY hold `b`
        let mut used_noms: Vec<u32> = Vec::new();
        if !self.nf.noms.is_empty() && (need > 1 || !self.nf.ge.is_empty()) {
            for &(yn, ln) in &m.elems[x as usize].edges {
                if self.labs.has(ln, r) && self.sets.has(m.elems[yn as usize].ty, b) {
                    for &a in self.sets.get(m.elems[yn as usize].ty).iter() {
                        if self.nf.is_nom[a as usize] {
                            used_noms.push(a);
                        }
                    }
                }
            }
            used_noms.sort_unstable();
            used_noms.dedup();
        }
        let mut t = if nomseed.is_some() {
            seed
        } else {
            close_succ(self, seed, &used_noms)?
        };
        let mut got = 0;
        while got < need {
            let Some(o) = self.first_nom(t) else { break };
            if used_noms.binary_search(&o).is_ok() {
                if nomseed.is_some() {
                    return Err(Fail::new("at-least on nominal", vec![tx]));
                }
                t = close_succ(self, seed, &used_noms)?;
                if self.first_nom(t).map(|o2| used_noms.binary_search(&o2).is_ok()).unwrap_or(false) {
                    return Err(Fail::new("at-least on nominal", vec![tx]));
                }
                continue;
            }
            let y = match m.nom_elem.get(&o) {
                Some(&y) => m.find(y),
                None => {
                    let fo = self.sets.intern(vec![o]);
                    let y = m.push_elem(Elem {
                        ty: 0,
                        forced: fo,
                        forbid: 0,
                        target: 0,
                        edges: Vec::new(),
                        pending: vec![o],
                        nom: true,
                        pinned: true,
                        owner: NONE,
                        alive: true,
                    });
                    m.set_nom(o, y);
                    y
                }
            };
            let ty_y = m.elems[y as usize].ty;
            let y_needs_seed = ty_y == 0 || !self.sets.subset(seed, ty_y);
            if y_needs_seed {
                let ss = self.sets.get(seed);
                m.em(y).pending.extend_from_slice(&ss);
            }
            let mut x_pushed = false;
            if ty_y != 0 {
                let bk = self.fwd(ty_y, fl);
                if bk != 0 && !self.sets.subset(bk, tx) {
                    let d = minus_sorted(&self.sets.get(bk), &self.sets.get(tx));
                    m.em(x).pending.extend_from_slice(&d);
                    x_pushed = true;
                }
            }
            self.add_edge(m, x, y, l);
            let y_has_le = ty_y != 0
                && !self.nf.le.is_empty()
                && self.sets.get(ty_y).iter().any(|&a| {
                    self.nf.has_le[a as usize]
                        && self.nf.le_by.get(a).iter().any(|&(k, r_le, c)| {
                            self.labs.has(fl, r_le)
                                && self.sets.has(tx, c)
                                && self.count(m, y, r_le, c, NONE) > k as usize
                        })
                });
            let x_has_le = !self.nf.le.is_empty()
                && self.sets.get(tx).iter().any(|&a| {
                    self.nf.has_le[a as usize]
                        && self.nf.le_by.get(a).iter().any(|&(k, r_le, c)| {
                            ty_y == 0
                                || (self.labs.has(l, r_le)
                                    && self.sets.has(ty_y, c)
                                    && self.count(m, x, r_le, c, NONE) > k as usize)
                        })
                });
            let f_tx_l = if ty_y != 0 { self.fwd(tx, l) } else { 0 };
            if y_needs_seed || y_has_le || (ty_y != 0 && !self.sets.subset(f_tx_l, ty_y)) {
                m.enqueue(y);
            }
            if x_pushed || x_has_le || ty_y == 0 {
                m.enqueue(x);
            }
            for &a in self.sets.get(t).iter() {
                if self.nf.is_nom[a as usize] {
                    used_noms.push(a);
                }
            }
            used_noms.sort_unstable();
            used_noms.dedup();
            got += 1;
            if got < need {
                if nomseed.is_some() {
                    return Err(Fail::new("at-least on nominal", vec![tx]));
                }
                t = close_succ(self, seed, &used_noms)?;
            }
        }
        if got == need {
            return Ok(());
        }
        // candidates: elements of type t or same seed
        let mut cands: Vec<Id> = Vec::new();
        for key in [t, seed | SEED_KEY] {
            if let Some(v) = m.typemap.get(&key) {
                cands.extend(v.iter().rev().take(self.opt.reuse_scan).copied());
            }
        }
        let mut picked: Vec<Id> = Vec::new();
        if !cands.is_empty() {
            for y in cands {
                if got == need {
                    break;
                }
                let y = m.find(y);
                if picked.contains(&y) {
                    continue;
                }
                let ey = &m.elems[y as usize];
                if !ey.alive || !self.sets.subset(seed, ey.ty) || !ey.pending.is_empty() {
                    continue;
                }
                if need > 1 || !self.nf.ge.is_empty() {
                    if let Some(l0) = m.edge_label(x, y) {
                        if self.labs.has(l0, r) && self.sets.has(ey.ty, b) {
                            continue;
                        }
                    }
                }
                if self.compatible(m, x, y, l) {
                    self.add_edge(m, x, y, l);
                    self.stats.reused += 1;
                    picked.push(y);
                    got += 1;
                }
            }
        }
        // second pass: an existing neighbour or an element created for the same seed,
        // even if it pushes names back into x (a fresh element for this seed would end
        // up pushing them too: without this, a chain of fresh elements never closes)
        if got < need {
            let mut cands2: Vec<Id> = Vec::new();
            if need == 1 {
                for &(yn, _) in m.elems[x as usize].edges.iter().take(self.opt.reuse_scan) {
                    let yn = m.find(yn);
                    if self.sets.subset(seed, m.elems[yn as usize].ty) {
                        cands2.push(yn);
                    }
                }
            }
            if let Some(v) = m.typemap.get(&(seed | SEED_KEY)) {
                cands2.extend(v.iter().rev().take(self.opt.reuse_scan).copied());
            }
            for y in cands2 {
                if got == need {
                    break;
                }
                let y = m.find(y);
                if y == x || !m.elems[y as usize].alive || picked.contains(&y) {
                    continue;
                }
                if let Some(l0) = m.edge_label(x, y) {
                    if self.labs.has(l0, r) && self.sets.has(m.elems[y as usize].ty, b) {
                        continue;
                    }
                }
                if let Some(back) = self.compatible_push(m, x, y, l) {
                    self.add_edge(m, x, y, l);
                    if !back.is_empty() {
                        m.em(x).pending.extend_from_slice(&back);
                        m.enqueue(x);
                    }
                    self.stats.reused += 1;
                    picked.push(y);
                    got += 1;
                }
            }
        }
        if self.debug && got < need {
            let c = self.dbg_created.entry(seed).or_insert(0);
            *c += 1;
            if *c == 1000 {
                // why did no candidate fit?
                let mut why = Vec::new();
                for key in [t, seed | SEED_KEY] {
                    if let Some(v) = m.typemap.get(&key) {
                        for &y in v.iter().rev().take(4) {
                            let y = m.find(y);
                            let ey = &m.elems[y as usize];
                            let tx = m.elems[x as usize].ty;
                            let f = self.fwd(tx, l);
                            let fl = self.flip(l);
                            let bk = self.fwd(ey.ty, fl);
                            let ok = self.compatible(m, x, y, l);
                            let ex = m.edge_label(x, y).map(|q| self.labs.get(q).to_vec());
                            let ey = &m.elems[y as usize];
                            why.push(format!(
                                "cand {} compat {} edge {:?} alive {} seed-in {} pend {} fwd-in {} back-in {} back {:?} tx-len {}",
                                y, ok, ex, ey.alive, self.sets.subset(seed, ey.ty), ey.pending.len(),
                                self.sets.subset(f, ey.ty), self.sets.subset(bk, tx),
                                minus_sorted(&self.sets.get(bk), &self.sets.get(tx)), self.sets.get(tx).len()
                            ));
                        }
                    }
                }
                eprintln!("debug: seed {:?} (role {}) created 1000 times; x {} type len {}; {:?}",
                    self.sets.get(seed), r, x, self.sets.get(m.elems[x as usize].ty).len(), why);
            }
        }
        while got < need {
            let y = m.push_elem(Elem {
                ty: t,
                forced: seed,
                forbid: 0,
                target: 0,
                edges: Vec::new(),
                pending: Vec::new(),
                nom: false,
                pinned: false,
                owner: x,
                alive: true,
            });
            self.stats.created += 1;
            m.tm_push(seed | SEED_KEY, y);
            self.add_edge(m, x, y, l);
            let bk = self.fwd(t, fl);
            if bk != 0 && !self.sets.subset(bk, tx) {
                let d = minus_sorted(&self.sets.get(bk), &self.sets.get(tx));
                m.em(x).pending.extend_from_slice(&d);
                m.enqueue(x);
            }
            m.enqueue(y);
            got += 1;
            if got < need && !self.nf.le.is_empty() && nomseed.is_none() {
                let mut added_cap = false;
                for &a in self.sets.get(tx).iter() {
                    if self.nf.has_le[a as usize] {
                        for &(k_le, r_le, c_le) in self.nf.le_by.get(a) {
                            if k_le > 0
                                && self.labs.has(l, r_le)
                                && self.sets.has(t, c_le)
                                && self.count(m, x, r_le, c_le, NONE) >= k_le as usize
                                && used_noms.binary_search(&c_le).is_err()
                            {
                                used_noms.push(c_le);
                                used_noms.sort_unstable();
                                added_cap = true;
                            }
                        }
                    }
                }
                if added_cap {
                    t = close_succ(self, seed, &used_noms)?;
                }
            }
        }
        Ok(())
    }

    /// Fold surplus neighbours of `x` in an at-most clause `<= k r.b`.
    fn fold(&mut self, m: &mut Model, x: Id, s: &[Id]) -> Result<(), Fail> {
        let tx = m.elems[x as usize].ty;
        let txs = self.sets.get(tx);
        let mut active_ge: Vec<(u32, u32, usize)> = Vec::new();
        for &a in txs.iter() {
            for &(k_ge, r_ge, b_ge) in self.nf.ge_by.get(a) {
                let c_ge = self.count(m, x, r_ge, b_ge, NONE);
                if c_ge <= k_ge as usize {
                    active_ge.push((r_ge, b_ge, c_ge));
                }
            }
        }
        let owner = m.elems[x as usize].owner;
        let mut y1s: Vec<Id> = s.iter().copied().filter(|&y| y != x).collect();
        y1s.sort_by_key(|&y| {
            let e = &m.elems[y as usize];
            (y == owner, e.nom, e.pinned, e.owner != x, e.edges.len() > 1)
        });
        for &y1 in &y1s {
            let e1 = &m.elems[y1 as usize];
            let (t1, f1, fb1, p1, n1, deg1) = (e1.ty, e1.forced, e1.forbid, e1.pinned, e1.nom, e1.edges.len());
            let l1 = match m.edge_label(x, y1) {
                Some(l) => l,
                None => continue,
            };
            let mut y2s: Vec<Id> = s.iter().copied().filter(|&y| y != y1).collect();
            y2s.sort_by_key(|&y| {
                let e = &m.elems[y as usize];
                (!self.sets.subset(t1, e.ty), e.pinned, e.nom, e.owner != x)
            });
            for &y2 in &y2s {
                let e2 = &m.elems[y2 as usize];
                let (t2, f2, fb, tg, nm, _p2, _deg2, own2) = (
                    e2.ty,
                    e2.forced,
                    e2.forbid,
                    e2.target,
                    e2.nom,
                    e2.pinned,
                    e2.edges.len(),
                    e2.owner,
                );
                let l2 = match m.edge_label(x, y2) {
                    Some(l) => l,
                    None => continue,
                };
                // do not fold two neighbours that both count toward an at-least bound on `x`
                // that is already at or below its minimum
                let breaks_ge = active_ge.iter().any(|&(r_ge, b_ge, _)| {
                    self.labs.has(l1, r_ge)
                        && self.sets.has(t1, b_ge)
                        && self.labs.has(l2, r_ge)
                        && self.sets.has(t2, b_ge)
                });
                if breaks_ge {
                    continue;
                }
                let fb_fold = if n1 { self.sets.union(fb, fb1) } else { fb };
                let nm_fold = nm || n1;
                let close_fold = |en: &mut Self, s: u32| -> Option<u32> {
                    let res = if own2 == NONE || n1 {
                        en.close_clean(s, fb_fold, tg, nm_fold)
                    } else {
                        en.close(s, fb_fold, tg, nm_fold)
                    };
                    match res {
                        CloseRes::Ok(t) => {
                            if nm_fold
                                && en.sets.get(t).iter().any(|&a| {
                                    en.nf.is_nom[a as usize]
                                        && !en.sets.has(t2, a)
                                        && !(n1 && en.sets.has(t1, a))
                                })
                            {
                                None
                            } else {
                                Some(t)
                            }
                        }
                        _ => None,
                    }
                };
                let u_full = self.sets.union(t2, t1);
                let mut t_new = if u_full == t2 {
                    Some(t2)
                } else {
                    close_fold(self, u_full)
                };
                if t_new.is_none() && !p1 && !n1 && deg1 <= 1 {
                    let u_f1 = self.sets.union(t2, f1);
                    t_new = close_fold(self, u_f1);
                    if t_new.is_none() {
                        let u_both = self.sets.union(f2, f1);
                        t_new = close_fold(self, u_both);
                    }
                }
                let Some(t_merged) = t_new else { continue };
                let f_merged = self.sets.union(f2, f1);
                self.stats.folds += 1;
                if n1 {
                    self.merge(m, y1, y2);
                    let y2_cur = m.find(y2);
                    {
                        let e = m.em(y2_cur);
                        e.ty = t_merged;
                        e.forced = f_merged;
                        e.pending.clear();
                    }
                    m.tm_push(t_merged, y2_cur);
                    m.enqueue(y2_cur);
                    m.enqueue(x);
                    return Ok(());
                }
                self.remove_edge(m, x, y1);
                if m.elems[y1 as usize].edges.is_empty() && !p1 && !n1 {
                    m.em(y1).alive = false;
                } else {
                    m.enqueue(y1);
                }
                {
                    let e = m.em(y2);
                    e.ty = t_merged;
                    e.forced = f_merged;
                }
                if t_merged != t2 {
                    m.tm_push(t_merged, y2);
                    let nb: Vec<Id> = m.elems[y2 as usize].edges.iter().map(|e| e.0).collect();
                    for z in nb {
                        m.enqueue(z);
                    }
                }
                self.add_edge(m, x, y2, l1);
                m.enqueue(y2);
                m.enqueue(x);
                return Ok(());
            }
        }
        Err(Fail::new("at-most: no fold possible", vec![m.elems[x as usize].ty]))
    }

    pub fn process(&mut self, m: &mut Model, x: Id) -> Result<(), Fail> {
        if !m.elems[x as usize].alive || m.uf[x as usize] != x {
            return Ok(());
        }
        let nf = self.nf;
        // 1. absorb pushed names
        if !m.elems[x as usize].pending.is_empty() {
            let mut p = std::mem::take(&mut m.em(x).pending);
            p.sort_unstable();
            p.dedup();
            let e = &m.elems[x as usize];
            let (ty0, forced0, forbid, target, nom, owner0) =
                (e.ty, e.forced, e.forbid, e.target, e.nom, e.owner);
            let tys = self.sets.get(ty0);
            p.retain(|a| tys.binary_search(a).is_err());
            if !p.is_empty() {
                let s1 = self.sets.union_vec(ty0, &p);
                let mut f1_extra = p.clone();
                for &a in tys.iter() {
                    if nf.is_nom[a as usize] {
                        f1_extra.push(a);
                    }
                }
                let f1 = self.sets.union_vec(forced0, &f1_extra);
                let r_s1 = if owner0 == NONE {
                    self.close_clean(s1, forbid, target, nom)
                } else {
                    self.close(s1, forbid, target, nom)
                };
                let t = match r_s1 {
                    CloseRes::Ok(mut t) => {
                        if owner0 == NONE
                            && self.rowclasses != 0
                            && self
                                .sets
                                .get(t)
                                .iter()
                                .any(|&b| self.is_rowclass[b as usize] && !self.sets.has(target, b) && !self.sets.has(ty0, b))
                        {
                            if let CloseRes::Ok(t_f1) = self.close_clean(f1, forbid, target, nom) {
                                let d_s1 = self
                                    .sets
                                    .get(t)
                                    .iter()
                                    .filter(|&&b| self.is_rowclass[b as usize] && !self.sets.has(target, b))
                                    .count();
                                let d_f1 = self
                                    .sets
                                    .get(t_f1)
                                    .iter()
                                    .filter(|&&b| self.is_rowclass[b as usize] && !self.sets.has(target, b))
                                    .count();
                                if d_f1 < d_s1 {
                                    self.stats.reclose_scratch += 1;
                                    t = t_f1;
                                }
                            }
                        }
                        t
                    }
                    CloseRes::Budget => return Err(Fail::new("closure budget", vec![ty0])),
                    CloseRes::Clash => {
                        self.stats.reclose_scratch += 1;
                        let r_f1 = if owner0 == NONE {
                            self.close_clean(f1, forbid, target, nom)
                        } else {
                            self.close(f1, forbid, target, nom)
                        };
                        match r_f1 {
                            CloseRes::Ok(t) => t,
                            CloseRes::Budget => return Err(Fail::new("closure budget", vec![ty0])),
                            CloseRes::Clash => {
                                let mut blame = Vec::new();
                                // the neighbours whose universals pushed the names
                                for &(y, l) in &m.elems[x as usize].edges.clone() {
                                    let ty_y = m.elems[y as usize].ty;
                                    let fl = self.flip(l);
                                    let f = self.fwd(ty_y, fl);
                                    let fs = self.sets.get(f);
                                    if fs.iter().any(|a| p.binary_search(a).is_ok())
                                        && !m.elems[y as usize].nom
                                        && !self.bad.contains(&ty_y)
                                    {
                                        blame.push(ty_y);
                                    }
                                }
                                if blame.is_empty() {
                                    blame.push(ty0);
                                }
                                return Err(Fail::new("clash when growing a type", blame));
                            }
                        }
                    }
                };
                {
                    let e = m.em(x);
                    e.ty = t;
                    e.forced = f1;
                }
                m.tm_push(t, x);
                let nb: Vec<Id> = m.elems[x as usize].edges.iter().map(|e| e.0).collect();
                for y in nb {
                    m.enqueue(y);
                }
                // nominal names pin the element
                let ts = self.sets.get(t);
                for &o in ts.iter() {
                    if !nf.is_nom[o as usize] {
                        continue;
                    }
                    match m.nom_elem.get(&o).copied() {
                        Some(y) => {
                            let y = m.find(y);
                            if y != x {
                                self.merge(m, x, y);
                                return Ok(());
                            }
                        }
                        None => {
                            m.set_nom(o, x);
                            let e = m.em(x);
                            e.nom = true;
                            e.pinned = true;
                        }
                    }
                }
            }
        }
        let tx = m.elems[x as usize].ty;
        let txs = self.sets.get(tx);
        // 2. universals to every neighbour
        if !nf.all.is_empty() && txs.iter().any(|&a| !nf.all_by.get(a).is_empty()) {
            let edges = m.elems[x as usize].edges.clone();
            for &(y, l) in &edges {
                let f = self.fwd(tx, l);
                if f == 0 {
                    continue;
                }
                let ty = m.elems[y as usize].ty;
                if !self.sets.subset(f, ty) {
                    let d = minus_sorted(&self.sets.get(f), &self.sets.get(ty));
                    m.em(y).pending.extend_from_slice(&d);
                    m.enqueue(y);
                }
            }
            if !m.elems[x as usize].pending.is_empty() {
                // a loop pushed into x itself
                m.enqueue(x);
                return Ok(());
            }
        }
        // 3. existentials and at-least (specific fillers before general fillers, non-self before self)
        let mut idx = NbrIdx::default();
        if !nf.le.is_empty() || !nf.ge.is_empty() {
            let mut obls: Vec<(bool, std::cmp::Reverse<(usize, u32, u32)>, bool, u32, u32, u32)> = Vec::new();
            for &a in txs.iter() {
                for &(r, b) in nf.ex_by.get(a) {
                    let is_self = self.sets.has(tx, b);
                    let spec = std::cmp::Reverse((nf.up[r as usize].len(), self.hclose_len[b as usize], 1));
                    obls.push((is_self, spec, false, 1, r, b));
                }
                for &(k, r, b) in nf.ge_by.get(a) {
                    let is_self = self.sets.has(tx, b);
                    let spec = std::cmp::Reverse((nf.up[r as usize].len(), self.hclose_len[b as usize], k));
                    obls.push((is_self, spec, true, k, r, b));
                }
            }
            obls.sort_unstable();
            let mut n_obls = 0usize;
            for (_, _, is_ge, k, r, b) in obls {
                n_obls += 1;
                if n_obls & 255 == 0 {
                    if self.mem_exceeded() {
                        return Err(Fail::new("memory cap (8 GB)", vec![]));
                    }
                    if let Some(d) = self.opt.deadline {
                        if Instant::now() > d {
                            return Err(Fail::new("time budget", vec![]));
                        }
                    }
                }
                if !is_ge {
                    let big = m.elems[x as usize].edges.len() > 8;
                    let ok = if big { idx.has(self, m, x, r, b) } else { self.has_nbr(m, x, r, b) };
                    if !ok {
                        self.satisfy(m, x, r, b, 1)?;
                    }
                } else {
                    let c = self.count(m, x, r, b, NONE);
                    if c < k as usize {
                        self.satisfy(m, x, r, b, k as usize - c)?;
                    }
                }
                if m.elems[x as usize].ty != tx
                    || !m.elems[x as usize].pending.is_empty()
                    || !m.elems[x as usize].alive
                {
                    m.enqueue(x);
                    return Ok(());
                }
            }
        } else {
            let mut n_obls = 0usize;
            for pass in [false, true] {
                for &a in txs.iter() {
                    for &(r, b) in nf.ex_by.get(a) {
                        if self.sets.has(tx, b) != pass {
                            continue;
                        }
                        n_obls += 1;
                        if n_obls & 255 == 0 {
                            if self.mem_exceeded() {
                                return Err(Fail::new("memory cap (8 GB)", vec![]));
                            }
                            if let Some(d) = self.opt.deadline {
                                if Instant::now() > d {
                                    return Err(Fail::new("time budget", vec![]));
                                }
                            }
                        }
                        let big = m.elems[x as usize].edges.len() > 8;
                        let ok = if big { idx.has(self, m, x, r, b) } else { self.has_nbr(m, x, r, b) };
                        if !ok {
                            self.satisfy(m, x, r, b, 1)?;
                        }
                    }
                    if m.elems[x as usize].ty != tx
                        || !m.elems[x as usize].pending.is_empty()
                        || !m.elems[x as usize].alive
                    {
                        m.enqueue(x);
                        return Ok(());
                    }
                }
            }
        }
        // 4. at-most
        for &a in txs.iter() {
            if !nf.has_le[a as usize] {
                continue;
            }
            for &(k, r, b) in nf.le_by.get(a) {
                let s: Vec<Id> = m.elems[x as usize]
                    .edges
                    .iter()
                    .filter(|&&(y, l)| self.labs.has(l, r) && self.sets.has(m.elems[y as usize].ty, b))
                    .map(|e| e.0)
                    .collect();
                if s.len() > k as usize {
                    self.fold(m, x, &s)?;
                    m.enqueue(x);
                    return Ok(());
                }
            }
        }
        Ok(())
    }

    pub fn saturate(&mut self, m: &mut Model) -> Result<(), Fail> {
        let mut steps: u64 = 0;
        while let Some(x) = m.pop() {
            self.process(m, x)?;
            steps += 1;
            self.stats.steps += 1;
            if steps > self.opt.step_budget {
                return Err(Fail::new("step budget", vec![]));
            }
            if m.elems.len() > self.opt.node_budget {
                return Err(Fail::new("node budget", vec![]));
            }
            if steps % 1024 == 0 {
                if self.mem_exceeded() {
                    return Err(Fail::new("memory cap (8 GB)", vec![]));
                }
                if let Some(d) = self.opt.deadline {
                    if Instant::now() > d {
                        return Err(Fail::new("time budget", vec![]));
                    }
                }
            }
        }
        Ok(())
    }

    /// Create an element whose closed type `t` has already been computed from `seed`.
    pub fn new_elem_closed(
        &mut self,
        m: &mut Model,
        seed: u32,
        t: u32,
        forbid: u32,
        target: u32,
        nom: bool,
    ) -> Id {
        let ts = self.sets.get(t);
        let existing_nom = ts.iter().any(|&o| self.nf.is_nom[o as usize] && m.nom_elem.contains_key(&o));
        if existing_nom {
            let y = m.push_elem(Elem {
                ty: 0,
                forced: seed,
                forbid,
                target,
                edges: Vec::new(),
                pending: ts.to_vec(),
                nom,
                pinned: true,
                owner: NONE,
                alive: true,
            });
            m.enqueue(y);
            return y;
        }
        let mut has_nom = nom;
        let mut nom_in_t: Vec<u32> = Vec::new();
        for &o in ts.iter() {
            if self.nf.is_nom[o as usize] {
                has_nom = true;
                nom_in_t.push(o);
            }
        }
        let forced_full = if nom_in_t.is_empty() {
            seed
        } else {
            self.sets.union_vec(seed, &nom_in_t)
        };
        let y = m.push_elem(Elem {
            ty: t,
            forced: forced_full,
            forbid,
            target,
            edges: Vec::new(),
            pending: Vec::new(),
            nom: has_nom,
            pinned: true,
            owner: NONE,
            alive: true,
        });
        for &o in ts.iter() {
            if self.nf.is_nom[o as usize] {
                m.set_nom(o, y);
            }
        }
        m.enqueue(y);
        y
    }

    /// A new element with forced names `seed`.
    pub fn new_elem(
        &mut self,
        m: &mut Model,
        seed: u32,
        forbid: u32,
        target: u32,
        nom: bool,
    ) -> Result<Id, Fail> {
        let t = match self.close_clean(seed, forbid, target, nom) {
            CloseRes::Ok(t) => t,
            CloseRes::Clash => return Err(Fail::new("clash in a seed type", vec![])),
            CloseRes::Budget => {
                let r = if self.mem_hit { "memory cap (8 GB)" } else { "closure budget" };
                return Err(Fail::new(r, vec![]));
            }
        };
        Ok(self.new_elem_closed(m, seed, t, forbid, target, nom))
    }
}
