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
        self.v[i as usize].clone()
    }
    #[inline]
    pub fn has(&self, i: u32, x: u32) -> bool {
        self.v[i as usize].binary_search(&x).is_ok()
    }
    pub fn subset(&self, a: u32, b: u32) -> bool {
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
        if a == b || b == 0 {
            return a;
        }
        if a == 0 {
            return b;
        }
        let v = merge_sorted(&self.v[a as usize], &self.v[b as usize]);
        self.intern(v)
    }
    pub fn union_vec(&mut self, a: u32, b: &[u32]) -> u32 {
        if b.is_empty() {
            return a;
        }
        let v = merge_sorted(&self.v[a as usize], b);
        self.intern(v)
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
        self.reason.contains("budget")
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
                j.saved.insert(i, self.elems[i as usize].clone());
            }
        }
        &mut self.elems[i as usize]
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
            uf_saved: Vec::new(),
            tm_added: Vec::new(),
            nom_saved: Vec::new(),
        });
    }
    pub fn in_txn(&self) -> bool {
        self.journal.is_some()
    }
    /// Pre-existing elements changed in the open transaction: (id, saved copy).
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
    pub fn queue_empty(&self) -> bool {
        self.queue.is_empty()
    }
    fn pop(&mut self) -> Option<Id> {
        let x = self.queue.pop_front()?;
        self.inq[x as usize] = false;
        Some(x)
    }
    pub fn canonical(&self) -> impl Iterator<Item = Id> + '_ {
        (0..self.elems.len() as Id).filter(move |&i| self.elems[i as usize].alive && self.uf[i as usize] == i)
    }
    pub fn edge_label(&self, x: Id, y: Id) -> Option<u32> {
        self.elems[x as usize].edges.iter().find(|e| e.0 == y).map(|e| e.1)
    }
}

#[derive(Clone)]
pub struct Opts {
    pub loops: bool,
    pub close_budget: u64,
    pub step_budget: u64,
    pub node_budget: usize,
    pub reuse_scan: usize,
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
            deadline: None,
        }
    }
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
    upto: usize,
}

impl NbrIdx {
    fn has(&mut self, en: &Engine, m: &Model, x: Id, r: u32, b: u32) -> bool {
        let edges = &m.elems[x as usize].edges;
        while self.upto < edges.len() {
            let (y, l) = edges[self.upto];
            for &rr in en.labs.v[l as usize].iter() {
                self.map.entry(rr).or_default().push(y);
            }
            self.upto += 1;
        }
        match self.map.get(&r) {
            Some(v) => v.iter().any(|&y| en.sets.has(m.elems[y as usize].ty, b)),
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
    memo: FxMap<(u32, u32, u32, bool), CloseRes>,
    pub bad: FxSet<u32>,
    mark: Vec<u32>,
    stamp: u32,
    cnt: Vec<u32>,
    cstamp: Vec<u32>,
    fmark: Vec<u32>,
    fstamp: u32,
    runs: u64,
    cur_target: Rc<[u32]>,
    cur_nomok: bool,
    pub opt: Opts,
    pub stats: Stats,
    pub debug: bool,
    dbg_created: FxMap<u32, u64>,
    /// data clauses: a closed type without a data star is a clash
    pub data: Option<(crate::data::DataNf, crate::data::Values)>,
    data_ok: FxMap<u32, bool>,
    /// one-step lookahead on successors: closed type -> its successor seeds close
    succ_ok: FxMap<u32, bool>,
    nest: u32,
    cur_forbid: u32,
}

impl<'a> Engine<'a> {
    pub fn new(nf: &'a Nf, opt: Opts) -> Engine<'a> {
        let mut labs = Sets::new();
        let lab_up: Vec<u32> = (0..2 * nf.m).map(|r| labs.intern(nf.up[r].clone())).collect();
        Engine {
            nf,
            sets: Sets::new(),
            labs,
            lab_flip: Vec::new(),
            lab_up,
            lab_union: FxMap::default(),
            fwd_cache: FxMap::default(),
            memo: FxMap::default(),
            bad: FxSet::default(),
            mark: vec![0; nf.n],
            stamp: 0,
            cnt: vec![0; nf.gci.len()],
            cstamp: vec![0; nf.gci.len()],
            fmark: vec![0; nf.n],
            fstamp: 0,
            runs: 0,
            cur_target: Rc::from(Vec::new()),
            cur_nomok: false,
            opt,
            stats: Stats::default(),
            debug: std::env::var("KM_HINTS_DEBUG").is_ok(),
            dbg_created: FxMap::default(),
            data: None,
            data_ok: FxMap::default(),
            succ_ok: FxMap::default(),
            nest: 0,
            cur_forbid: 0,
        }
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
        if let Some(&f) = self.fwd_cache.get(&(t, l)) {
            return f;
        }
        let ts = self.sets.get(t);
        let ls = self.labs.get(l);
        let mut out = Vec::new();
        for &a in ts.iter() {
            for &(s, c) in self.nf.all_by.get(a) {
                if ls.binary_search(&s).is_ok() {
                    out.push(c);
                }
            }
        }
        out.sort_unstable();
        out.dedup();
        let f = self.sets.intern(out);
        self.fwd_cache.insert((t, l), f);
        f
    }

    // ---------- closure ----------
    pub fn clear_memo(&mut self) {
        self.memo.clear();
        self.succ_ok.clear();
    }

    /// A closed type containing `seed`, avoiding `forbid` and the nogoods,
    /// preferring unnamed heads, then named heads in `target`.
    pub fn close(&mut self, seed: u32, forbid: u32, target: u32, nomok: bool) -> CloseRes {
        let key = (seed, forbid, target, nomok);
        if let Some(&r) = self.memo.get(&key) {
            // an entry made inside a cut-off lookahead may not have been checked
            if let CloseRes::Ok(t) = r {
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
        self.fstamp += 1;
        let fs = self.sets.get(forbid);
        for &a in fs.iter() {
            self.fmark[a as usize] = self.fstamp;
        }
        self.cur_target = self.sets.get(target);
        self.cur_nomok = nomok;
        self.cur_forbid = forbid;
        self.runs = 0;
        let s = self.sets.get(seed);
        let r = self.close_from(&s, 0);
        if self.nest < 2 {
            self.memo.insert(key, r);
        }
        r
    }

    /// Every existential of the closed type `t` has a successor seed that
    /// closes (one step; nested closures save and restore the outer state).
    fn succ_check(&mut self, t: u32) -> bool {
        if let Some(&b) = self.succ_ok.get(&t) {
            return b;
        }
        if self.nest >= 2 {
            return true;
        }
        let nf = self.nf;
        let ts = self.sets.get(t);
        let mut reqs: Vec<(u32, u32)> = Vec::new();
        for &a in ts.iter() {
            for &(r, b) in nf.ex_by.get(a) {
                reqs.push((r, b));
            }
            for &(_, r, b) in nf.ge_by.get(a) {
                reqs.push((r, b));
            }
        }
        if reqs.is_empty() {
            self.succ_ok.insert(t, true);
            return true;
        }
        // save the outer closure's state
        let (ft, tg, nk, runs, fst) = (self.cur_forbid, self.cur_target.clone(), self.cur_nomok, self.runs, self.fstamp);
        self.nest += 1;
        let mut ok = true;
        for (r, b) in reqs {
            let l = self.lab_of_role(r);
            let f = self.fwd(t, l);
            let seed = self.sets.union_vec(f, &[b]);
            if self.sets.get(seed).iter().any(|&o| nf.is_nom[o as usize]) {
                continue;
            }
            match self.close(seed, 0, 0, false) {
                CloseRes::Clash => {
                    ok = false;
                    break;
                }
                CloseRes::Ok(ts2) => {
                    // the successor's universals back into t must close with t
                    let fl = self.flip(l);
                    let bk = self.fwd(ts2, fl);
                    if !self.sets.subset(bk, t) {
                        let u = self.sets.union(t, bk);
                        if let CloseRes::Clash = self.close(u, ft, 0, nk) {
                            ok = false;
                            break;
                        }
                    }
                }
                CloseRes::Budget => {}
            }
        }
        self.nest -= 1;
        // restore: forbid marks, target, budget counter
        self.fstamp = fst.max(self.fstamp) + 1;
        let fs = self.sets.get(ft);
        for &a in fs.iter() {
            self.fmark[a as usize] = self.fstamp;
        }
        self.cur_forbid = ft;
        self.cur_target = tg;
        self.cur_nomok = nk;
        self.runs = runs;
        self.succ_ok.insert(t, ok);
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
        let nf = self.nf;
        self.stamp = self.stamp.wrapping_add(1);
        if self.stamp == 0 {
            for x in self.mark.iter_mut() {
                *x = 0;
            }
            for x in self.cstamp.iter_mut() {
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
                    self.mark[a as usize] = st;
                    if self.fmark[a as usize] == fst {
                        return CloseRes::Clash;
                    }
                    t.push(a);
                    q.push(a);
                }
            }};
        }
        for &g in &nf.gci_empty {
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
        while let Some(a) = q.pop() {
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
        // data requirements only grow with the type: prune a partial type without a data star
        if let Some((d, v)) = &self.data {
            if !pend.is_empty() {
                let mut ts = t.clone();
                ts.sort_unstable();
                if crate::data::star(d, v, &ts).is_none() {
                    return CloseRes::Clash;
                }
            }
        }
        // the first disjunctive gci whose head is not yet met
        let mut open: Option<u32> = None;
        for &g in &pend {
            let h = &nf.gci[g as usize].1;
            if !h.iter().any(|&x| self.mark[x as usize] == st) {
                open = Some(g);
                break;
            }
        }
        if let Some(g) = open {
            let heads0: Vec<u32> =
                nf.gci[g as usize].1.iter().copied().filter(|&h| self.fmark[h as usize] != fst).collect();
            // one-step lookahead: Horn consequences of each head
            let mut keyed: Vec<((u32, u32, usize, u32), u32)> = Vec::with_capacity(heads0.len());
            for &h in &heads0 {
                let rk = self.rank(h);
                if heads0.len() == 1 {
                    keyed.push(((0, 0, 0, rk), h));
                    continue;
                }
                let mut s2 = t.clone();
                s2.push(h);
                match self.horn_eval(&s2) {
                    None => continue,
                    Some((dirty, noms)) => keyed.push(((0, (rk >= 3 || noms > 0) as u32, dirty, rk), h)),
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
        if let Some((d, v)) = &self.data {
            let ok = match self.data_ok.get(&id) {
                Some(&b) => b,
                None => {
                    let b = crate::data::star(d, v, &self.sets.v[id as usize]).is_some();
                    self.data_ok.insert(id, b);
                    b
                }
            };
            if !ok {
                return CloseRes::Clash;
            }
        }
        CloseRes::Ok(id)
    }

    /// Horn propagation only: None on a clash, else (named names outside
    /// the current target, nominal names) among the consequences.
    fn horn_eval(&mut self, seed: &[u32]) -> Option<(usize, usize)> {
        self.runs += 1;
        let nf = self.nf;
        self.stamp = self.stamp.wrapping_add(1);
        if self.stamp == 0 {
            for x in self.mark.iter_mut() {
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
        let (mut dirty, mut noms) = (0usize, 0usize);
        macro_rules! add {
            ($a:expr) => {{
                let a = $a;
                if self.mark[a as usize] != st {
                    self.mark[a as usize] = st;
                    if self.fmark[a as usize] == fst {
                        return None;
                    }
                    if nf.is_nom[a as usize] {
                        noms += 1;
                    } else if nf.named[a as usize] && self.cur_target.binary_search(&a).is_err() {
                        dirty += 1;
                    }
                    q.push(a);
                }
            }};
        }
        for &g in &nf.gci_empty {
            let h = &nf.gci[g as usize].1;
            match h.len() {
                0 => return None,
                1 => add!(h[0]),
                _ => {}
            }
        }
        for &a in seed {
            add!(a);
        }
        while let Some(a) = q.pop() {
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
                        _ => {}
                    }
                }
            }
        }
        Some((dirty, noms))
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
                let e = m.em(x);
                for p in e.edges.iter_mut() {
                    if p.0 == y {
                        p.1 = u;
                    }
                }
                if x != y {
                    let fu = self.flip(u);
                    let e = m.em(y);
                    for p in e.edges.iter_mut() {
                        if p.0 == x {
                            p.1 = fu;
                        }
                    }
                }
            }
            None => {
                m.em(x).edges.push((y, l));
                if x != y {
                    m.em(y).edges.push((x, fl));
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
        for &(z, l) in &ea.edges {
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
        for &o in ta.iter() {
            if self.nf.is_nom[o as usize] {
                m.set_nom(o, b);
            }
        }
        m.enqueue(b);
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
        let mut l2 = if x == y { self.loop_lab(l) } else { l };
        let existing = m.edge_label(x, y);
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
        if existing.is_some() {
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
    /// `x` (returned) as long as x's type still closes.
    fn compatible_push(&mut self, m: &Model, x: Id, y: Id, l: u32) -> Option<Vec<u32>> {
        let tx = m.elems[x as usize].ty;
        let ty = m.elems[y as usize].ty;
        if !m.elems[y as usize].pending.is_empty() {
            return None;
        }
        let f = self.fwd(tx, l);
        if !self.sets.subset(f, ty) {
            return None;
        }
        let fl = self.flip(l);
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
        let (fb, tg, nm) = (e.forbid, e.target, e.nom);
        let s1 = self.sets.union_vec(tx, &back);
        let tx2 = match self.close(s1, fb, tg, nm) {
            CloseRes::Ok(t) => t,
            _ => return None,
        };
        if !nf.le.is_empty() && !self.atmost_ok(m, x, tx2, y, ty, l) {
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
        let l = self.lab_of_role(r);
        let tx = m.elems[x as usize].ty;
        let f = self.fwd(tx, l);
        let seed = self.sets.union_vec(f, &[b]);
        let nomseed = self.first_nom(seed);
        let t = if nomseed.is_some() {
            seed
        } else {
            match self.close(seed, 0, 0, false) {
                CloseRes::Ok(t) => t,
                CloseRes::Clash => {
                    if self.debug {
                        eprintln!("debug: no successor type: x {} tx {} succ_ok {:?} r {} b {} seed {:?}",
                            x, tx, self.succ_ok.get(&tx), r, b, self.sets.get(seed));
                    }
                    return Err(Fail::new("no type for a successor", vec![tx]));
                }
                CloseRes::Budget => return Err(Fail::new("closure budget", vec![tx])),
            }
        };
        if let Some(o) = self.first_nom(t) {
            let y = match m.nom_elem.get(&o) {
                Some(&y) => m.find(y),
                None => {
                    let fo = self.sets.intern(vec![o]);
                    let y = m.push_elem(Elem {
                        ty: fo,
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
            let ss = self.sets.get(seed);
            m.em(y).pending.extend_from_slice(&ss);
            self.add_edge(m, x, y, l);
            m.enqueue(y);
            m.enqueue(x);
            return Ok(());
        }
        let mut got = 0;
        // candidates: elements of type exactly t, and elements created for the
        // same seed (their type may have grown past t through their own successors)
        let mut cands: Vec<Id> = Vec::new();
        for key in [t, seed | SEED_KEY] {
            if let Some(v) = m.typemap.get(&key) {
                cands.extend(v.iter().rev().take(self.opt.reuse_scan).copied());
            }
        }
        if !cands.is_empty() {
            for y in cands {
                if got == need {
                    break;
                }
                let y = m.find(y);
                let ey = &m.elems[y as usize];
                if !ey.alive || !self.sets.subset(seed, ey.ty) || !ey.pending.is_empty() {
                    continue;
                }
                if need > 1 && m.edge_label(x, y).is_some() {
                    continue;
                }
                if self.compatible(m, x, y, l) {
                    self.add_edge(m, x, y, l);
                    self.stats.reused += 1;
                    got += 1;
                    if need > 1 {
                        // at-least: count again (the label may already cover r)
                        if self.count(m, x, r, b, NONE) >= need {
                            return Ok(());
                        }
                    }
                }
            }
        }
        // second pass: an element created for the same seed, even if it pushes
        // names back into x (a fresh element for this seed would end up pushing
        // them too: without this, a chain of fresh elements never closes)
        if got < need {
            if let Some(v) = m.typemap.get(&(seed | SEED_KEY)) {
                let cands: Vec<Id> = v.iter().rev().take(self.opt.reuse_scan).copied().collect();
                for y in cands {
                    if got == need {
                        break;
                    }
                    let y = m.find(y);
                    if y == x || !m.elems[y as usize].alive || (need > 1 && m.edge_label(x, y).is_some()) {
                        continue;
                    }
                    if let Some(back) = self.compatible_push(m, x, y, l) {
                        self.add_edge(m, x, y, l);
                        if !back.is_empty() {
                            m.em(x).pending.extend_from_slice(&back);
                            m.enqueue(x);
                        }
                        self.stats.reused += 1;
                        got += 1;
                    }
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
            m.enqueue(y);
            got += 1;
        }
        Ok(())
    }

    /// Fold surplus neighbours of `x` in an at-most clause `<= k r.b`.
    fn fold(&mut self, m: &mut Model, x: Id, s: &[Id]) -> Result<(), Fail> {
        let owner = m.elems[x as usize].owner;
        let mut y1s: Vec<Id> = s.iter().copied().filter(|&y| y != x).collect();
        y1s.sort_by_key(|&y| {
            let e = &m.elems[y as usize];
            (y == owner, e.nom, e.pinned, e.owner != x)
        });
        for &y1 in &y1s {
            let t1 = m.elems[y1 as usize].ty;
            let mut y2s: Vec<Id> = s.iter().copied().filter(|&y| y != y1).collect();
            y2s.sort_by_key(|&y| {
                let e = &m.elems[y as usize];
                (!self.sets.subset(t1, e.ty), e.pinned, e.nom, e.owner != x)
            });
            for &y2 in &y2s {
                let e2 = &m.elems[y2 as usize];
                let (t2, fb, tg, nm) = (e2.ty, e2.forbid, e2.target, e2.nom);
                let u = self.sets.union(t2, t1);
                if u != t2 {
                    if let CloseRes::Ok(_) = self.close(u, fb, tg, nm) {
                    } else {
                        continue;
                    }
                }
                let l1 = m.edge_label(x, y1).unwrap();
                self.stats.folds += 1;
                self.remove_edge(m, x, y1);
                self.add_edge(m, x, y2, l1);
                m.enqueue(x);
                let ts = self.sets.get(t1);
                m.em(y2).pending.extend_from_slice(&ts);
                m.enqueue(y2);
                m.enqueue(y1);
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
            let (ty0, forced0, forbid, target, nom) = (e.ty, e.forced, e.forbid, e.target, e.nom);
            let tys = self.sets.get(ty0);
            p.retain(|a| tys.binary_search(a).is_err());
            if !p.is_empty() {
                let s1 = self.sets.union_vec(ty0, &p);
                let f1 = self.sets.union_vec(forced0, &p);
                let t = match self.close(s1, forbid, target, nom) {
                    CloseRes::Ok(t) => t,
                    CloseRes::Budget => return Err(Fail::new("closure budget", vec![ty0])),
                    CloseRes::Clash => {
                        self.stats.reclose_scratch += 1;
                        match self.close(f1, forbid, target, nom) {
                            CloseRes::Ok(t) => t,
                            CloseRes::Budget => return Err(Fail::new("closure budget", vec![ty0])),
                            CloseRes::Clash => {
                                let mut blame = vec![ty0];
                                // the neighbours whose universals pushed the names
                                for &(y, l) in &m.elems[x as usize].edges.clone() {
                                    let ty_y = m.elems[y as usize].ty;
                                    let fl = self.flip(l);
                                    let f = self.fwd(ty_y, fl);
                                    let fs = self.sets.get(f);
                                    if fs.iter().any(|a| p.binary_search(a).is_ok()) {
                                        blame.push(ty_y);
                                    }
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
        // 2. universals to every neighbour
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
        // 3. existentials and at-least
        let txs = self.sets.get(tx);
        let mut idx = NbrIdx::default();
        let big = m.elems[x as usize].edges.len() > 8;
        for &a in txs.iter() {
            for &(r, b) in nf.ex_by.get(a) {
                let ok = if big { idx.has(self, m, x, r, b) } else { self.has_nbr(m, x, r, b) };
                if !ok {
                    self.satisfy(m, x, r, b, 1)?;
                }
            }
            for &(k, r, b) in nf.ge_by.get(a) {
                let c = self.count(m, x, r, b, NONE);
                if c < k as usize {
                    self.satisfy(m, x, r, b, k as usize - c)?;
                }
            }
            if m.elems[x as usize].ty != tx || !m.elems[x as usize].alive {
                m.enqueue(x);
                return Ok(());
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
            if steps % 4096 == 0 {
                if let Some(d) = self.opt.deadline {
                    if Instant::now() > d {
                        return Err(Fail::new("time budget", vec![]));
                    }
                }
            }
        }
        Ok(())
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
        let t = match self.close(seed, forbid, target, nom) {
            CloseRes::Ok(t) => t,
            CloseRes::Clash => return Err(Fail::new("clash in a seed type", vec![])),
            CloseRes::Budget => return Err(Fail::new("closure budget", vec![])),
        };
        // the type is set when the pending names are absorbed (step 1 of `process`)
        let y = m.push_elem(Elem {
            ty: 0,
            forced: seed,
            forbid,
            target,
            edges: Vec::new(),
            pending: self.sets.get(t).to_vec(),
            nom,
            pinned: true,
            owner: NONE,
            alive: true,
        });
        m.enqueue(y);
        Ok(y)
    }
}
