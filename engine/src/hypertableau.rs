//! HermiT-style hypertableau (Motik–Shearer–Horrocks, JAIR 2009), ported as a
//! distinct model-construction engine from the legacy `tableau.rs` paths.
//!
//! WHY THIS EXISTS. KM's frontend already emits HermiT-equivalent guarded
//! disjunctive DL-clauses, and `tableau.rs` already builds completion graphs.
//! What `tableau.rs` lacks vs HermiT — and what makes HermiT solve the live
//! `∀ + ⊔` disjunction family in well under a second where KM times out — is the
//! SEARCH discipline: dependency-directed backjumping, conflict-reason
//! propagation, anywhere blocking, and (the throughput half) delta-driven
//! incremental matching. This module ports those.
//!
//! Fragment: ALC(H). Number restrictions / nominals stay on `tableau.rs`;
//! `run_json` routes here only when `KM_HT` is set and the KB is ALC(H).
//!
//! INCR 1: DependencySet + Ext clash/extension manager.
//! INCR 2: hyperresolution matcher + saturation w/ unit prop.
//! INCR 3: existential expansion + blocking (ancestor-subset / anywhere-eq).
//! INCR 4: DFS with dependency-directed backjumping; `run_json` wiring.
//! INCR 5: DELTA-DRIVEN propagation — fact additions enqueue events; only
//!         clauses triggered by a newly-added fact are re-matched (anchored at
//!         that fact), instead of re-saturating the whole clause set each step.
//!         Unit-prop on a disjunct death is recovered by a cheap per-step scan
//!         of the (few) disjunctive clauses. Closes the per-step re-saturation
//!         cost the KM_HT_STATS diagnostic exposed (nodes=1-5, depth grows
//!         linearly, 0.2-1.0s/step from full re-matching).
//! INCR 7: SEARCH DISCIPLINE (HermiT's disjunct ordering by backtrack count).
//!         The family (5303/9024/12141) is search-bound: exponential program-
//!         order backtracking at the root, where HermiT finishes in ~2s. This
//!         adds VSIDS-style activity tracking (a disjunct's concept is bumped
//!         each time exploring it clashes), three env-gated orderings:
//!           KM_HT_ORD   1=least-failing-first, 2=most-failing-first (disjunct
//!                       order within a branch),
//!           KM_HT_PICK  1=most-constrained (fewest live), 2=highest-activity
//!                       (which pending disjunction to branch on),
//!           KM_HT_RESTART + KM_HT_RBASE  Luby restarts that preserve activity
//!                       across runs so the order improves each restart.
//!         All inert when unset: baseline search is byte-identical. This is pure
//!         scheduling over the same exhaustive backjumping DFS (answer-invariant,
//!         no calculus change, no Lean re-cert).

#![allow(dead_code)]

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

// INCR 7 diagnostics: matcher output volume (gated by KM_HT_STATS heartbeat).
static MATCH_TOT: AtomicU64 = AtomicU64::new(0);
static MATCH_MAX: AtomicU64 = AtomicU64::new(0);

use super::{Atom, CLit, Clause, Node, C, R, Var, X};

pub type Level = u32;

// =========================== DependencySet =================================

#[derive(Debug)]
pub struct DepNode {
    level: Level,
    rest: DepSet,
}
pub type DepSet = Option<Rc<DepNode>>;

#[inline]
pub fn dep_empty() -> DepSet {
    None
}
#[inline]
pub fn dep_max(d: &DepSet) -> Level {
    match d {
        None => 0,
        Some(n) => n.level,
    }
}
pub fn dep_contains(d: &DepSet, level: Level) -> bool {
    let mut cur = d;
    while let Some(n) = cur {
        if n.level == level {
            return true;
        }
        if n.level < level {
            return false;
        }
        cur = &n.rest;
    }
    false
}
pub fn dep_add(d: &DepSet, level: Level) -> DepSet {
    match d {
        None => Some(Rc::new(DepNode { level, rest: None })),
        Some(n) => {
            if level == n.level {
                d.clone()
            } else if level > n.level {
                Some(Rc::new(DepNode { level, rest: d.clone() }))
            } else {
                let tail = dep_add(&n.rest, level);
                Some(Rc::new(DepNode { level: n.level, rest: tail }))
            }
        }
    }
}
pub fn dep_union(a: &DepSet, b: &DepSet) -> DepSet {
    match (a, b) {
        (None, _) => b.clone(),
        (_, None) => a.clone(),
        (Some(na), Some(nb)) => {
            if na.level == nb.level {
                let tail = dep_union(&na.rest, &nb.rest);
                Some(Rc::new(DepNode { level: na.level, rest: tail }))
            } else if na.level > nb.level {
                let tail = dep_union(&na.rest, b);
                Some(Rc::new(DepNode { level: na.level, rest: tail }))
            } else {
                let tail = dep_union(a, &nb.rest);
                Some(Rc::new(DepNode { level: nb.level, rest: tail }))
            }
        }
    }
}
/// Number of decision levels in a dep set (its cardinality). Diagnostic use:
/// compares the true conflict size to the search depth (KM_HT_DEPSTATS).
pub fn dep_card(d: &DepSet) -> usize {
    let mut n = 0;
    let mut cur = d;
    while let Some(node) = cur {
        n += 1;
        cur = &node.rest;
    }
    n
}
pub fn dep_remove(d: &DepSet, level: Level) -> DepSet {
    match d {
        None => None,
        Some(n) => {
            if n.level == level {
                n.rest.clone()
            } else if n.level < level {
                d.clone()
            } else {
                let tail = dep_remove(&n.rest, level);
                Some(Rc::new(DepNode { level: n.level, rest: tail }))
            }
        }
    }
}

// ============================== Ext ========================================

enum Trail {
    Concept(Node, CLit),
    Edge(R, Node, Node),
    NewNode,
    /// eager mode: this node's deferred global disjunctions were fired; on
    /// backtrack the firing (and its pending disjunctions) is undone, so clear
    /// the flag to let it re-fire if the node becomes live again.
    GlobalsFired(Node),
}

/// A pending propagation event: a freshly added fact / node whose triggered
/// clauses have not yet been fired.
#[derive(Clone, Copy)]
enum Event {
    Concept(Node, CLit),
    Edge(R, Node, Node),
    NodeNew(Node),
}

/// A ground disjunction recorded when its clause body fully matched: the head's
/// concept disjuncts (all of them — liveness is recomputed on use) plus the body
/// DepSet and the trail length at recording (so backtracking drops it).
struct PendingDisj {
    disjuncts: Vec<(Node, CLit)>,
    bdep: DepSet,
    at: usize,
}

/// A deferred ∃-obligation `node ⊑ ∃r.fil` recorded when its clause body matched.
struct Oblig {
    n: Node,
    r: R,
    fil: CLit,
    dep: DepSet,
    at: usize,
}

pub struct Ext {
    concepts: Vec<HashMap<CLit, DepSet>>,
    out_edges: Vec<Vec<(R, Node, DepSet)>>,
    in_edges: Vec<Vec<(R, Node)>>,
    pred: Vec<Option<Node>>,
    blockable: Vec<bool>,
    /// eager mode: per-node flag — its deferred global ⊤-disjunctions have fired.
    globals_fired: Vec<bool>,
    /// KM_HT_BLOCKSKIP: per-node blocked snapshot, refreshed at each branch
    /// selection. A disjunction all of whose disjunct nodes are blocked is not
    /// branched (its blocker already witnesses it) — see `refresh_blocked`.
    blocked: Vec<bool>,
    /// KM_HT_BLOCKSKIP active: suppress nondeterministic branching on blocked
    /// nodes (sound + complete for the anywhere-blocked ALC(H) route).
    blockskip: bool,
    trail: Vec<Trail>,
    clash: Option<DepSet>,
    /// delta propagation worklist (drained by `Ht::propagate`).
    queue: Vec<Event>,
    /// ground disjunctions awaiting a branch (filled by `apply_head`).
    pending: Vec<PendingDisj>,
    /// ∃-obligations awaiting expansion (filled by `apply_head`).
    obligations: Vec<Oblig>,
    /// an out-of-ALC(H) head construct was seen ⇒ result is unsound, bail.
    unsupported: bool,

    // ---- incremental ("watch") disjunction bookkeeping (KM_HT_WATCH) ----
    /// active ⇒ maintain the indices below so disjunction unit-prop / branch
    /// detection is change-driven instead of an O(pending) per-step scan.
    watch: bool,
    /// disjunct (node, lit) ⇒ ids of pending disjunctions that contain it. A
    /// disjunction's status changes only when one of its disjuncts' lit or its
    /// complement is asserted / retracted, so those are the ids to re-check.
    lit_disj: HashMap<(Node, CLit), Vec<usize>>,
    /// disjunction ids whose status may have changed and must be re-evaluated.
    dirty: Vec<usize>,
    dirty_in: Vec<bool>,
    /// disjunction ids last seen as a >=2-live branch candidate (may be stale;
    /// re-evaluated on pop).
    open: Vec<usize>,
    open_in: Vec<bool>,

    /// per-node-id unique creation stamp (for sound learned-clause validity: a
    /// node id reused after backtracking gets a fresh uid, so a learned no-good
    /// referencing the old individual is recognised as stale). uid.len() is the
    /// high-water mark of created ids, never shrunk.
    uid: Vec<u64>,
    uid_next: u64,
    /// the node at which the most recent direct `c ∧ ¬c` clash was detected
    /// (KM_HT_LBLCACHE: lets the learner key the no-good on the clashing node's
    /// signature). `None` until a direct clash fires.
    clash_node: Option<Node>,
}

impl Ext {
    pub fn new() -> Ext {
        Ext {
            concepts: Vec::new(),
            out_edges: Vec::new(),
            in_edges: Vec::new(),
            pred: Vec::new(),
            blockable: Vec::new(),
            globals_fired: Vec::new(),
            blocked: Vec::new(),
            blockskip: std::env::var_os("KM_HT_BLOCKSKIP").is_some(),
            trail: Vec::new(),
            clash: None,
            queue: Vec::new(),
            pending: Vec::new(),
            obligations: Vec::new(),
            unsupported: false,
            watch: false,
            lit_disj: HashMap::new(),
            dirty: Vec::new(),
            dirty_in: Vec::new(),
            open: Vec::new(),
            open_in: Vec::new(),
            uid: Vec::new(),
            uid_next: 1,
            clash_node: None,
        }
    }

    #[inline]
    fn node_uid(&self, n: Node) -> u64 {
        self.uid.get(n).copied().unwrap_or(0)
    }
    /// A learned-clause literal `(n, uid)` is still valid iff node `n` exists and
    /// is the same individual it was when the clause was learned.
    #[inline]
    fn node_valid(&self, n: Node, uid: u64) -> bool {
        n < self.concepts.len() && self.uid.get(n).copied() == Some(uid)
    }

    /// Record a ground disjunction; under `watch`, index its disjuncts and queue
    /// it dirty so the incremental scan picks it up.
    fn push_disj(&mut self, disjuncts: Vec<(Node, CLit)>, bdep: DepSet) {
        let id = self.pending.len();
        let at = self.trail.len();
        if self.watch {
            for &(n, lit) in &disjuncts {
                self.lit_disj.entry((n, lit)).or_default().push(id);
            }
            self.dirty.push(id);
            self.dirty_in.push(true);
            self.open_in.push(false);
        }
        self.pending.push(PendingDisj { disjuncts, bdep, at });
    }

    /// Mark every disjunction touched by a change at `(n, lit)` (either the
    /// literal or its complement appears as a disjunct) for re-evaluation.
    fn mark_disj_dirty(&mut self, n: Node, lit: CLit) {
        if !self.watch {
            return;
        }
        let comp = CLit { neg: !lit.neg, c: lit.c };
        for key in [(n, lit), (n, comp)] {
            let len = self.lit_disj.get(&key).map_or(0, |v| v.len());
            for i in 0..len {
                let id = self.lit_disj[&key][i];
                if id < self.dirty_in.len() && !self.dirty_in[id] {
                    self.dirty_in[id] = true;
                    self.dirty.push(id);
                }
            }
        }
    }

    pub fn new_root(&mut self) -> Node {
        self.push_node(None, false)
    }
    pub fn new_node(&mut self, parent: Option<Node>) -> Node {
        self.push_node(parent, parent.is_some())
    }
    fn push_node(&mut self, parent: Option<Node>, blockable: bool) -> Node {
        let id = self.concepts.len();
        self.concepts.push(HashMap::new());
        self.out_edges.push(Vec::new());
        self.in_edges.push(Vec::new());
        self.pred.push(parent);
        self.blockable.push(blockable);
        self.globals_fired.push(false);
        self.trail.push(Trail::NewNode);
        self.queue.push(Event::NodeNew(id));
        // assign a fresh unique stamp to this (possibly reused) node id.
        let u = self.uid_next;
        self.uid_next += 1;
        if id < self.uid.len() {
            self.uid[id] = u;
        } else {
            self.uid.push(u);
        }
        id
    }

    #[inline]
    pub fn num_nodes(&self) -> usize {
        self.concepts.len()
    }
    #[inline]
    pub fn has_clash(&self) -> bool {
        self.clash.is_some()
    }
    pub fn clash_dep(&self) -> DepSet {
        self.clash.clone().unwrap_or(None)
    }
    pub fn dep_of(&self, node: Node, lit: CLit) -> Option<&DepSet> {
        self.concepts.get(node).and_then(|m| m.get(&lit))
    }
    pub fn has_concept(&self, node: Node, lit: CLit) -> bool {
        self.concepts.get(node).is_some_and(|m| m.contains_key(&lit))
    }

    /// Assert `lit` at `node`. Returns true iff freshly added (enqueues it).
    pub fn add_concept(&mut self, node: Node, lit: CLit, dep: &DepSet) -> bool {
        let comp = CLit { neg: !lit.neg, c: lit.c };
        if let Some(other) = self.concepts[node].get(&comp) {
            let cd = dep_union(dep, other);
            self.clash_node = Some(node);
            self.raise_clash(cd);
        }
        match self.concepts[node].get(&lit) {
            None => {
                self.concepts[node].insert(lit, dep.clone());
                self.trail.push(Trail::Concept(node, lit));
                self.queue.push(Event::Concept(node, lit));
                self.mark_disj_dirty(node, lit);
                true
            }
            Some(existing) => {
                if dep_max(dep) < dep_max(existing) {
                    self.concepts[node].insert(lit, dep.clone());
                }
                false
            }
        }
    }

    pub fn add_edge(&mut self, r: R, s: Node, t: Node, dep: &DepSet) {
        if self.out_edges[s].iter().any(|&(rr, tt, _)| rr == r && tt == t) {
            return;
        }
        self.out_edges[s].push((r, t, dep.clone()));
        self.in_edges[t].push((r, s));
        self.trail.push(Trail::Edge(r, s, t));
        self.queue.push(Event::Edge(r, s, t));
    }

    pub fn raise_clash(&mut self, dep: DepSet) {
        match &self.clash {
            Some(existing) if dep_max(existing) <= dep_max(&dep) => {}
            _ => self.clash = Some(dep),
        }
    }

    #[inline]
    pub fn mark(&self) -> usize {
        self.trail.len()
    }

    pub fn backtrack_to(&mut self, mark: usize) {
        while self.trail.len() > mark {
            match self.trail.pop().unwrap() {
                Trail::Concept(node, lit) => {
                    self.concepts[node].remove(&lit);
                    // a retracted fact can revive disjunctions it had satisfied
                    // or killed: re-dirty them.
                    self.mark_disj_dirty(node, lit);
                }
                Trail::Edge(r, s, t) => {
                    if let Some(pos) =
                        self.out_edges[s].iter().position(|&(rr, tt, _)| rr == r && tt == t)
                    {
                        self.out_edges[s].swap_remove(pos);
                    }
                    if let Some(pos) =
                        self.in_edges[t].iter().position(|&(rr, ss)| rr == r && ss == s)
                    {
                        self.in_edges[t].swap_remove(pos);
                    }
                }
                Trail::NewNode => {
                    self.concepts.pop();
                    self.out_edges.pop();
                    self.in_edges.pop();
                    self.pred.pop();
                    self.blockable.pop();
                    self.globals_fired.pop();
                }
                Trail::GlobalsFired(node) => {
                    if node < self.globals_fired.len() {
                        self.globals_fired[node] = false;
                    }
                }
            }
        }
        self.clash = None;
        // Pending events reference facts that may now be undone: drop them. The
        // facts present before `mark` were already fully propagated, and the
        // next assertion re-seeds the queue.
        self.queue.clear();
        // A ground disjunction / obligation recorded at trail length > mark had
        // at least one body fact among the undone suffix (else it would have
        // been recorded earlier), so it no longer holds: drop it. `pending` is
        // ordered by `at` ascending, so these form a suffix; pop it (unregistering
        // watch-index entries so reused node ids can't see stale mappings).
        while let Some(last) = self.pending.last() {
            if last.at <= mark {
                break;
            }
            let id = self.pending.len() - 1;
            let pd = self.pending.pop().unwrap();
            if self.watch {
                for (n, lit) in pd.disjuncts {
                    if let Some(v) = self.lit_disj.get_mut(&(n, lit)) {
                        if let Some(p) = v.iter().position(|&x| x == id) {
                            v.swap_remove(p);
                        }
                        if v.is_empty() {
                            self.lit_disj.remove(&(n, lit));
                        }
                    }
                }
                self.dirty_in.pop();
                self.open_in.pop();
            }
        }
        self.obligations.retain(|e| e.at <= mark);
    }
}

impl Default for Ext {
    fn default() -> Self {
        Ext::new()
    }
}

fn edge_dep(ext: &Ext, r: R, s: Node, t: Node) -> Option<DepSet> {
    ext.out_edges[s]
        .iter()
        .find(|&&(rr, tt, _)| rr == r && tt == t)
        .map(|(_, _, d)| d.clone())
}

fn has_rsucc(ext: &Ext, n: Node, r: R, fil: CLit) -> bool {
    ext.out_edges[n].iter().any(|&(rr, t, _)| rr == r && ext.has_concept(t, fil))
}

// ============================ Matching =====================================

fn atom_max_var(a: &Atom) -> Var {
    match *a {
        Atom::Concept { t, .. } => t,
        Atom::Role { s, t, .. } => s.max(t),
        Atom::Exists { t, .. } => t,
        Atom::Eq { s, t } => s.max(t),
    }
}
fn nvars_of(clause: &Clause) -> usize {
    let mut m = 0;
    for a in clause.body.iter().chain(clause.head.iter()) {
        m = m.max(atom_max_var(a));
    }
    (m as usize) + 1
}
fn sorted_body(body: &[Atom]) -> Vec<Atom> {
    let mut v = body.to_vec();
    v.sort_by_key(|a| (atom_max_var(a), matches!(a, Atom::Concept { .. }) as u8));
    v
}

type Subst = Vec<Option<Node>>;

/// X-anchored matcher (used by the full-scan callers: disjunction scan + ∃).
fn rec_match(
    ext: &Ext,
    atoms: &[Atom],
    i: usize,
    sigma: &mut Subst,
    dep: &DepSet,
    out: &mut Vec<(Subst, DepSet)>,
) {
    if i == atoms.len() {
        out.push((sigma.clone(), dep.clone()));
        return;
    }
    match &atoms[i] {
        Atom::Concept { lit, t } => {
            let v = *t as usize;
            if let Some(n) = sigma[v] {
                if let Some(d) = ext.dep_of(n, *lit) {
                    let nd = dep_union(dep, d);
                    rec_match(ext, atoms, i + 1, sigma, &nd, out);
                }
            }
        }
        Atom::Role { r, s, t } => {
            let sv = *s as usize;
            let tv = *t as usize;
            if let Some(sn) = sigma[sv] {
                if let Some(tn) = sigma[tv] {
                    if let Some((_, _, edep)) =
                        ext.out_edges[sn].iter().find(|&&(rr, tt, _)| rr == *r && tt == tn)
                    {
                        let nd = dep_union(dep, edep);
                        rec_match(ext, atoms, i + 1, sigma, &nd, out);
                    }
                } else {
                    for k in 0..ext.out_edges[sn].len() {
                        let (rr, tt, ref edep) = ext.out_edges[sn][k];
                        if rr == *r {
                            let nd = dep_union(dep, edep);
                            sigma[tv] = Some(tt);
                            rec_match(ext, atoms, i + 1, sigma, &nd, out);
                            sigma[tv] = None;
                        }
                    }
                }
            }
        }
        _ => {}
    }
}

fn match_body(ext: &Ext, body_sorted: &[Atom], nvars: usize, out: &mut Vec<(Subst, DepSet)>) {
    if body_sorted.is_empty() {
        for n in 0..ext.num_nodes() {
            let mut s = vec![None; nvars];
            s[X as usize] = Some(n);
            out.push((s, dep_empty()));
        }
        return;
    }
    for n in 0..ext.num_nodes() {
        let mut sigma = vec![None; nvars];
        sigma[X as usize] = Some(n);
        rec_match(ext, body_sorted, 0, &mut sigma, &dep_empty(), out);
    }
}

/// Flexible matcher: complete a partial substitution by repeatedly picking any
/// processable (some-variable-bound) atom, propagating bindings through role
/// edges in EITHER direction (out- or in-edges). Used by delta propagation,
/// where the anchored atom may bind a successor variable rather than X.
fn rec_match_flex(
    ext: &Ext,
    atoms: &[Atom],
    done: &mut [bool],
    sigma: &mut Subst,
    dep: &DepSet,
    out: &mut Vec<(Subst, DepSet)>,
) {
    // pick the first processable, not-done atom
    let mut pick = None;
    for (k, a) in atoms.iter().enumerate() {
        if done[k] {
            continue;
        }
        let proc = match a {
            Atom::Concept { t, .. } => sigma[*t as usize].is_some(),
            Atom::Role { s, t, .. } => sigma[*s as usize].is_some() || sigma[*t as usize].is_some(),
            _ => false,
        };
        if proc {
            pick = Some(k);
            break;
        }
    }
    let k = match pick {
        Some(k) => k,
        None => {
            if done.iter().all(|&d| d) {
                out.push((sigma.clone(), dep.clone()));
            }
            return;
        }
    };
    done[k] = true;
    match atoms[k] {
        Atom::Concept { lit, t } => {
            let n = sigma[t as usize].unwrap();
            if let Some(d) = ext.dep_of(n, lit) {
                let nd = dep_union(dep, d);
                rec_match_flex(ext, atoms, done, sigma, &nd, out);
            }
        }
        Atom::Role { r, s, t } => {
            let sv = s as usize;
            let tv = t as usize;
            match (sigma[sv], sigma[tv]) {
                (Some(sn), Some(tn)) => {
                    if let Some(ed) = edge_dep(ext, r, sn, tn) {
                        let nd = dep_union(dep, &ed);
                        rec_match_flex(ext, atoms, done, sigma, &nd, out);
                    }
                }
                (Some(sn), None) => {
                    for k2 in 0..ext.out_edges[sn].len() {
                        let (rr, tt, ref edep) = ext.out_edges[sn][k2];
                        if rr == r {
                            let nd = dep_union(dep, edep);
                            sigma[tv] = Some(tt);
                            rec_match_flex(ext, atoms, done, sigma, &nd, out);
                            sigma[tv] = None;
                        }
                    }
                }
                (None, Some(tn)) => {
                    for k2 in 0..ext.in_edges[tn].len() {
                        let (rr, ss) = ext.in_edges[tn][k2];
                        if rr == r {
                            if let Some(ed) = edge_dep(ext, r, ss, tn) {
                                let nd = dep_union(dep, &ed);
                                sigma[sv] = Some(ss);
                                rec_match_flex(ext, atoms, done, sigma, &nd, out);
                                sigma[sv] = None;
                            }
                        }
                    }
                }
                (None, None) => {}
            }
        }
        _ => {}
    }
    done[k] = false;
}

type ClauseRec = (Clause, Vec<Atom>, usize);

/// Apply the head of clause `cid` under a matched body substitution: unit-add a
/// forced concept, fold dead-disjunct reasons into its DepSet, raise a clash on
/// an empty live set / empty head, defer disjunctions and ∃-obligations.
fn apply_head(clauses: &[ClauseRec], ext: &mut Ext, cid: usize, sigma: &Subst, bdep: &DepSet) {
    let head = &clauses[cid].0.head;
    if head.is_empty() {
        ext.raise_clash(bdep.clone());
        return;
    }
    let mut satisfied = false;
    let mut dead_dep = dep_empty();
    let mut live: Vec<HeadItem> = Vec::new();
    let mut all_concepts: Vec<(Node, CLit)> = Vec::new();
    for h in head {
        match *h {
            Atom::Concept { lit, t } => {
                let n = sigma[t as usize].expect("head var bound by body");
                all_concepts.push((n, lit));
                if ext.has_concept(n, lit) {
                    satisfied = true;
                    break;
                }
                let comp = CLit { neg: !lit.neg, c: lit.c };
                if let Some(d) = ext.dep_of(n, comp) {
                    dead_dep = dep_union(&dead_dep, d);
                } else {
                    live.push(HeadItem::Concept(n, lit));
                }
            }
            Atom::Exists { r, fil, t } => {
                let n = sigma[t as usize].expect("head var bound by body");
                if has_rsucc(ext, n, r, fil) {
                    satisfied = true;
                    break;
                }
                live.push(HeadItem::Exists(n, r, fil));
            }
            Atom::Role { r, s, t } => {
                // role-hierarchy / chain / transitivity head: force the edge.
                let sn = sigma[s as usize].expect("head role src bound by body");
                let tn = sigma[t as usize].expect("head role dst bound by body");
                if edge_dep(ext, r, sn, tn).is_some() {
                    satisfied = true;
                    break;
                }
                live.push(HeadItem::Edge(r, sn, tn));
            }
            Atom::Eq { .. } => {
                // equality in the head (functionality / role-chain merge) is
                // genuinely out of the supported ALC(H) fragment: bail soundly.
                if std::env::var_os("KM_HT_TRACE").is_some() {
                    eprintln!("TR UNSUPPORTED: head Eq atom in clause cid={}", cid);
                }
                ext.unsupported = true;
            }
        }
    }
    if satisfied {
        return;
    }
    if live.is_empty() {
        ext.raise_clash(dep_union(bdep, &dead_dep));
        return;
    }
    if live.len() == 1 {
        match live[0] {
            HeadItem::Concept(n, lit) => {
                let d = dep_union(bdep, &dead_dep);
                ext.add_concept(n, lit, &d);
            }
            HeadItem::Exists(n, r, fil) => {
                let at = ext.mark();
                ext.obligations.push(Oblig { n, r, fil, dep: bdep.clone(), at });
            }
            HeadItem::Edge(r, s, t) => {
                // forced role edge (role inclusion / chain / transitivity).
                let d = dep_union(bdep, &dead_dep);
                ext.add_edge(r, s, t, &d);
            }
        }
    } else if live.iter().any(|h| matches!(h, HeadItem::Exists(..) | HeadItem::Edge(..))) {
        // a disjunction containing an ∃ or a role edge is out of the branchable
        // (ground concept-disjunction) fragment: bail soundly to the legacy path.
        if std::env::var_os("KM_HT_TRACE").is_some() {
            eprintln!("TR UNSUPPORTED: disjunctive head with exists/edge ({} live, cid={})", live.len(), cid);
        }
        ext.unsupported = true;
    } else {
        // >=2 live concepts: record the ground disjunction for branching. Store
        // all concept disjuncts (not just the currently-live ones); liveness is
        // recomputed when a branch is taken.
        ext.push_disj(all_concepts, bdep.clone());
    }
}

/// Fire clause `cid` whose sorted-body atom at `pos` is a Concept matching the
/// freshly added fact `(n, lit-at-pos)`; anchor there and complete the match.
fn fire_anchor_concept(clauses: &[ClauseRec], ext: &mut Ext, cid: usize, pos: usize, n: Node) {
    let body = &clauses[cid].1;
    let nv = clauses[cid].2;
    let (lit, v) = match body[pos] {
        Atom::Concept { lit, t } => (lit, t as usize),
        _ => return,
    };
    let dep0 = match ext.dep_of(n, lit) {
        Some(d) => d.clone(),
        None => return,
    };
    let mut sigma = vec![None; nv];
    sigma[v] = Some(n);
    let mut done = vec![false; body.len()];
    done[pos] = true;
    let mut matches: Vec<(Subst, DepSet)> = Vec::new();
    rec_match_flex(ext, body, &mut done, &mut sigma, &dep0, &mut matches);
    let ml = matches.len() as u64;
    MATCH_TOT.fetch_add(ml, Ordering::Relaxed);
    MATCH_MAX.fetch_max(ml, Ordering::Relaxed);
    for (s, d) in &matches {
        apply_head(clauses, ext, cid, s, d);
        if ext.has_clash() {
            return;
        }
    }
}

/// Fire clause `cid` whose sorted-body atom at `pos` is a Role matching the
/// freshly added edge `r(es,et)`; anchor there and complete the match.
fn fire_anchor_edge(clauses: &[ClauseRec], ext: &mut Ext, cid: usize, pos: usize, es: Node, et: Node) {
    let body = &clauses[cid].1;
    let nv = clauses[cid].2;
    let (r, sv, tv) = match body[pos] {
        Atom::Role { r, s, t } => (r, s as usize, t as usize),
        _ => return,
    };
    let dep0 = match edge_dep(ext, r, es, et) {
        Some(d) => d,
        None => return,
    };
    let mut sigma = vec![None; nv];
    sigma[sv] = Some(es);
    sigma[tv] = Some(et);
    let mut done = vec![false; body.len()];
    done[pos] = true;
    let mut matches: Vec<(Subst, DepSet)> = Vec::new();
    rec_match_flex(ext, body, &mut done, &mut sigma, &dep0, &mut matches);
    let ml = matches.len() as u64;
    MATCH_TOT.fetch_add(ml, Ordering::Relaxed);
    MATCH_MAX.fetch_max(ml, Ordering::Relaxed);
    for (s, d) in &matches {
        apply_head(clauses, ext, cid, s, d);
        if ext.has_clash() {
            return;
        }
    }
}

/// Fire an empty-body (global ⊤ ⊑ ...) clause on a freshly created node.
fn fire_global(clauses: &[ClauseRec], ext: &mut Ext, cid: usize, n: Node) {
    let nv = clauses[cid].2;
    let mut sigma = vec![None; nv];
    sigma[X as usize] = Some(n);
    apply_head(clauses, ext, cid, &sigma, &dep_empty());
}

// ============================== Blocking ===================================

fn label_subset(ext: &Ext, n: Node, m: Node) -> bool {
    ext.concepts[n].keys().all(|k| ext.concepts[m].contains_key(k))
}
fn ancestor_blocked(ext: &Ext, n: Node) -> bool {
    if !ext.blockable[n] {
        return false;
    }
    let mut cur = ext.pred[n];
    while let Some(m) = cur {
        if label_subset(ext, n, m) {
            return true;
        }
        cur = ext.pred[m];
    }
    false
}

// =============================== Ht ========================================

#[derive(Clone, Copy)]
pub struct GroundDisjunct {
    pub node: Node,
    pub lit: CLit,
}
struct GD {
    disjuncts: Vec<GroundDisjunct>,
    dep: DepSet,
}

/// A learned no-good: a set of decision literals whose simultaneous assertion led
/// to a clash. As a constraint it is the disjunction of their complements (at
/// least one decision must not hold). Each literal carries the node's uid so the
/// clause is ignored once that individual no longer exists (soundness). Two
/// watched literals (`w0`, `w1`, indices into `lits`) drive lazy maintenance.
struct LClause {
    lits: Vec<(Node, u64, CLit)>,
    w0: usize,
    w1: usize,
}
enum HeadItem {
    Concept(Node, CLit),
    Exists(Node, R, CLit),
    /// a forced role edge `r(s,t)` from a head Role atom (role hierarchy / chain
    /// / transitivity — the H in ALC(H)). Both endpoints are body-bound.
    Edge(R, Node, Node),
}
enum Out {
    Sat,
    Conflict(DepSet),
    /// restart budget hit: unwind to the top and re-run (activity preserved).
    Restart,
}
enum Scan {
    Sat,
    Clash,
    Unit,
    Branch(GD),
}

/// Result of evaluating one ground disjunction against the current model.
enum DEval {
    Satisfied,
    Clash(DepSet),
    Unit(Node, CLit, DepSet),
    Branch(Vec<GroundDisjunct>, DepSet),
}

/// KM_HT_BLOCKSKIP: a disjunction need not be branched if EVERY node carrying a
/// disjunct is blocked. Each blocked node n is label-subset of an unblocked
/// blocker m (anywhere blocking, ALC(H) no inverse); m sits on the frontier that
/// IS branched, so n reuses m's choice. Sound: were n's disjunction all-dead (a
/// clash), m's superset label would clash too, and m is branched. Complete: any
/// subsumption forced through n is also forced through m.
#[inline]
fn disj_all_blocked(ext: &Ext, id: usize) -> bool {
    ext.blockskip
        && ext.pending[id]
            .disjuncts
            .iter()
            .all(|&(n, _)| ext.blocked.get(n).copied().unwrap_or(false))
}

/// Evaluate pending disjunction `id`: is it satisfied, a clash (all disjuncts
/// dead), forced (one live ⇒ unit), or branchable (>=2 live)? Same formula as the
/// per-step scan, evaluated for a single disjunction.
fn eval_disj(ext: &Ext, id: usize) -> DEval {
    if disj_all_blocked(ext, id) {
        return DEval::Satisfied;
    }
    let pd = &ext.pending[id];
    let mut dead_dep = dep_empty();
    let mut live: Vec<GroundDisjunct> = Vec::new();
    for &(n, lit) in &pd.disjuncts {
        if ext.has_concept(n, lit) {
            return DEval::Satisfied;
        }
        let comp = CLit { neg: !lit.neg, c: lit.c };
        if let Some(d) = ext.dep_of(n, comp) {
            dead_dep = dep_union(&dead_dep, d);
        } else {
            live.push(GroundDisjunct { node: n, lit });
        }
    }
    let dep = dep_union(&pd.bdep, &dead_dep);
    match live.len() {
        0 => DEval::Clash(dep),
        1 => DEval::Unit(live[0].node, live[0].lit, dep),
        _ => DEval::Branch(live, dep),
    }
}

fn env_u8(key: &str, default: u8) -> u8 {
    std::env::var(key).ok().and_then(|s| s.parse().ok()).unwrap_or(default)
}

/// Luby sequence (1,1,2,1,1,2,4,1,...) — restart-interval multiplier; guarantees
/// the budget grows unboundedly, so the search stays complete.
fn luby(i: u64) -> u64 {
    let mut k = 1u64;
    while (1u64 << k) - 1 < i {
        k += 1;
    }
    if i == (1u64 << k) - 1 {
        1u64 << (k - 1)
    } else {
        luby(i - (1u64 << (k - 1)) + 1)
    }
}

/// Reusable scratch for the subset-blocking inverted index (concept-indexed
/// posting lists). Kept across `compute_blocked` calls to avoid re-allocating /
/// re-hashing a fresh map every call (blocking is the dominant per-test cost).
#[derive(Default)]
struct BlockBuf {
    /// encoded-literal `((c<<1)|neg)` → unblocked nodes carrying it, this call.
    lists: Vec<Vec<Node>>,
    /// encoded indices touched this call (so only those are cleared next call).
    touched: Vec<usize>,
}

pub struct Ht {
    clauses: Vec<ClauseRec>,
    /// body Concept atoms by literal: clauses triggered when that literal appears.
    concept_triggers: HashMap<CLit, Vec<(usize, usize)>>,
    /// body Role atoms by role.
    role_triggers: HashMap<R, Vec<(usize, usize)>>,
    /// empty-body (global) clauses, fired per node.
    global_clauses: Vec<usize>,
    /// the disjunctive subset of `global_clauses` (≥2 concept head atoms): a
    /// ⊤-headed disjunction fires on EVERY node. In eager mode these are NOT
    /// fired on a node until it is confirmed unblocked, so a blocked node never
    /// spawns their branch points (its blocker covers them) — the HermiT
    /// model-folding lever. `global_disj_set` is the same set for O(1) skip.
    global_disj: Vec<usize>,
    global_disj_set: HashSet<usize>,
    /// KM_HT_EAGER: defer global ⊤-disjunctions to unblocked nodes only.
    eager: bool,
    ext: Ext,
    anywhere: bool,
    /// blocking signature: 0=core (positive-concept equality, default), 1=subset
    /// (full-label superset), 2=eq (full-label equality). KM_HT_BLOCK overrides.
    block_mode: u8,
    cache: HashMap<u64, Vec<Node>>,
    steps: u64,
    backtracks: u64,
    /// backtracks that were genuine backjumps (clash dep did NOT contain the
    /// current level ⇒ skipped this branch point). If this is ≪ backtracks, the
    /// dependency sets are too coarse and search degrades to chronological.
    backjumps: u64,
    /// times the negate-tried-disjunct fact was actually asserted (KM_HT_NEGTRIED).
    negfired: u64,
    /// number of disjunction case-splits started (≡ HermiT branchPointsPushed) and
    /// the number of disjunct branches actually attempted (≡ model-search nodes).
    branch_pushes: u64,
    disjunct_tries: u64,
    /// KM_HT_PROF: total microseconds spent in `compute_blocked` (the per-step
    /// blocking recompute), to confirm whether it dominates the per-test wall.
    block_us: u128,
    /// reusable inverted-index scratch for subset blocking (see `BlockBuf`).
    block_buf: RefCell<BlockBuf>,
    stats: bool,
    hb: u64,
    tick: u64,
    cur_depth: Level,
    // INCR 7 — search discipline (all inert when ord/pick/restart are 0/off).
    /// per-concept clash activity (bumped when a disjunct of that concept clashes).
    activity: HashMap<C, u64>,
    ord_mode: u8,
    pick_mode: u8,
    do_restart: bool,
    rbase: u64,
    conflicts: u64,
    restart_limit: u64,
    luby_idx: u64,
    restarts: u64,
    start: Instant,
    trace: bool,
    /// force naive n² pairwise classification (default off ⇒ model-based pruning).
    naive: bool,
    /// incremental change-driven disjunction handling (KM_HT_WATCH).
    watch: bool,
    /// CDCL-style conflict-clause learning (KM_HT_LEARN).
    learn: bool,
    /// KM_HT_LEARN_NOSTALE (diagnostic, UNSOUND): ignore the node-uid staleness
    /// check in learned-clause BCP, so no-goods fire whenever the node IDs are in
    /// range (regardless of uid). Measures whether cross-recreation no-good
    /// transfer would cut backtracks — NOT for production (fires on wrong
    /// individuals).
    learn_nostale: bool,
    /// HermiT startNextChoice: on a disjunct clash, assert the complement of the
    /// tried disjunct (carrying the clash dep minus this branch level) before
    /// trying the next, so the remaining disjuncts unit-propagate against the
    /// known-false ones instead of re-expanding sibling subtrees (KM_HT_NEGTRIED).
    negtried: bool,
    /// decision literal asserted at each branch level (index = level); used to
    /// turn a clash dep-set into a learned no-good. Reset per dfs(0) run.
    decisions: Vec<(Node, u64, CLit)>,
    /// learned no-goods (persist across backtracks within one dfs(0) run).
    learned: Vec<LClause>,
    /// decision literal (node, lit) ⇒ learned clauses with that literal watched.
    lwatch: HashMap<(Node, CLit), Vec<usize>>,
    /// KM_HT_SATCACHE: persistent pool of node core-signatures that appeared in a
    /// COMPLETED clash-free model of some prior `consistent()` call. For the
    /// ALC(H) no-inverse/number/nominal fragment a node's satisfiability depends
    /// only on its (core) label, so a signature proven SAT once is SAT wherever it
    /// recurs — across every per-concept query rebuild. `compute_blocked` blocks a
    /// non-root node whose signature is pooled (it reuses that earlier model
    /// fragment), folding the 94 per-query model rebuilds against the consistency
    /// model. Sound on the same fragment Ht's core blocking already assumes.
    satcache: bool,
    sat_sigs: HashSet<Vec<u64>>,
    /// KM_HT_PHASE: label-keyed phase saving. `phase[c]` = was concept `c` true in
    /// the most recent clash-free model. `order_disjuncts` tries a disjunct whose
    /// concept was last-true first, so each per-query witness rebuild warm-starts
    /// from the consistency model's disjunct choices (Q6 vs DNA …) instead of
    /// re-searching from scratch — the model-find collapses toward a near-solution
    /// start. Persists across `consistent()` calls. Sound (only reorders a complete
    /// search; never changes SAT/UNSAT). Default off.
    phase_save: bool,
    phase: HashMap<C, bool>,
    /// KM_HT_LBLCACHE: signature-keyed conflict learning. Node-uid-keyed no-goods
    /// never refire on 5303 because the culprit nodes are recreated as different
    /// individuals; but the search re-derives the SAME tiny conflicts (card≈5.5)
    /// thousands of times. Re-keying each conflict literal on the deciding node's
    /// CORE-LABEL SIGNATURE (positive concepts) instead of its id makes the no-good
    /// recur across structurally-identical nodes. A learned no-good is a set of
    /// (sig, concept) choices; it fires (clash, no recursion) when all its choices
    /// are simultaneously active in the current branch assignment.
    lblng: bool,
    /// (sig, decision-concept) -> the branch level at which that choice is active.
    cur_choices: HashMap<(u64, CLit), Level>,
    /// core-signature of the deciding node, indexed by branch level.
    dec_sig: Vec<u64>,
    /// the (sig, concept) inserted into `cur_choices` at each branch level (for
    /// exact removal on backtrack); None if no choice recorded at that level.
    dec_choice: Vec<Option<(u64, CLit)>>,
    /// learned no-goods: sorted sets of (sig, concept) that jointly clash.
    lng: Vec<Vec<(u64, CLit)>>,
    /// (sig, concept) -> learned no-good ids containing it (watch index).
    lng_watch: HashMap<(u64, CLit), Vec<usize>>,
    lng_fires: u64,
    /// KM_HT_SATFOLD: model folding by SAT-superset completion. The disjunction
    /// blowup on 5303 is ~85 frontier nodes that share an 18-concept core and
    /// differ only by their exclusive-disjunct tag; each branches its ~17 global
    /// disjunctions. But a node's (un)satisfiability is label-determined for the
    /// ALC(H) no-inverse fragment, so if a node's label is a SUBSET of a label
    /// that already appeared in a completed clash-free model, the node can be
    /// COMPLETED to that label deterministically (assert the missing concepts) —
    /// its disjunctions become satisfied with NO branching, and the completion is
    /// independent of context (no inverse) so it never needs backtracking. This
    /// collapses the per-witness branch search toward HermiT's tiny model.
    satfold: bool,
    /// full (pos+neg) labels of nodes seen in completed clash-free models, sorted.
    sat_labels: Vec<Vec<CLit>>,
    /// smallest-literal watch index into `sat_labels` for the superset check.
    satfold_watch: HashMap<CLit, Vec<usize>>,
    satfold_hits: u64,
}

/// Contrapositive Horn clauses for clash clauses (KM_HT_CONTRA). A clash clause
/// `A1 ⊓ … ⊓ An ⊑ ⊥` (empty head, all-Concept body on one variable) entails its n
/// contrapositives `⋀_{j≠i} Aj → ¬Ai`. `Ht` only `raise_clash`es a clash clause
/// when *every* Ai is present (apply_head), so it never asserts `¬Ai`; yet its
/// disjunction handling (`eval_disj`, `apply_head`) decides a disjunct is *dead*
/// solely by its complement being present. The contrapositives feed exactly those
/// negative facts in through ordinary Horn firing, so unit propagation can fire on
/// complementary disjunctions and the negative branch's own consequences
/// (`¬A ⊑ ∃r.B`) get derived. Each added clause is entailed ⇒ sound.
fn contrapositives(clauses: &[Clause]) -> Vec<Clause> {
    let mut extra = Vec::new();
    for cl in clauses {
        if !cl.head.is_empty() || cl.body.len() < 2 {
            continue;
        }
        let mut lits: Vec<CLit> = Vec::with_capacity(cl.body.len());
        let mut var: Option<Var> = None;
        let mut ok = true;
        for a in &cl.body {
            match a {
                Atom::Concept { lit, t } => {
                    match var {
                        None => var = Some(*t),
                        Some(v) if v == *t => {}
                        _ => {
                            ok = false;
                            break;
                        }
                    }
                    lits.push(*lit);
                }
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            continue;
        }
        let v = var.unwrap();
        for i in 0..lits.len() {
            let body: Vec<Atom> = lits
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, l)| Atom::Concept { lit: *l, t: v })
                .collect();
            let comp = CLit { neg: !lits[i].neg, c: lits[i].c };
            extra.push(Clause { body, head: vec![Atom::Concept { lit: comp, t: v }] });
        }
    }
    extra
}

/// Trigger-keyed (binary/n-ary) absorption (KM_HT_TRIGABS). A global GCI clause
/// `⊤ ⊑ ¬C1 ⊔ … ⊔ ¬Ck ⊔ P1 ⊔ … ⊔ Pm` (empty body, head all-Concept on one
/// variable, k ≥ 1) is logically equivalent to the triggered implication
/// `C1 ⊓ … ⊓ Ck ⊑ P1 ⊔ … ⊔ Pm`. Moving the negated disjuncts into the body makes
/// the clause DORMANT until every Ci labels a node, instead of firing the
/// disjunction on EVERY node (Konclude `CTriggeredImplicationBinaryAbsorber` /
/// HermiT absorption — the documented anti-⊔-blowup device). This is the lever
/// for the live ∀+⊔ family, where ⊤-disjunctions otherwise re-branch on every
/// model node.
///
/// Sound + complete: a node missing some Ci already satisfies the `¬Ci` disjunct,
/// so the original clause is vacuous there and the dormant form loses nothing. A
/// purely positive disjunction `⊤ ⊑ P1 ⊔ … ⊔ Pm` (no negative disjunct) has no
/// such free disjunct and is left untouched (it genuinely must branch). Heads
/// containing non-Concept atoms (existential / role disjuncts) are also left
/// untouched (conservative). All-negative heads `⊤ ⊑ ¬C1 ⊔ … ⊔ ¬Ck` correctly
/// become the clash clause `C1 ⊓ … ⊓ Ck ⊑ ⊥`. Rewrites in place; returns count.
fn trigger_absorb(clauses: &mut [Clause]) -> usize {
    let mut count = 0usize;
    for cl in clauses.iter_mut() {
        if !cl.body.is_empty() || cl.head.is_empty() {
            continue;
        }
        // Head must be all-Concept atoms on a single variable, with ≥1 negative.
        let mut var: Option<Var> = None;
        let mut all_concept_one_var = true;
        let mut has_neg = false;
        for a in &cl.head {
            match a {
                Atom::Concept { lit, t } => {
                    match var {
                        None => var = Some(*t),
                        Some(v) if v == *t => {}
                        _ => {
                            all_concept_one_var = false;
                            break;
                        }
                    }
                    if lit.neg {
                        has_neg = true;
                    }
                }
                _ => {
                    all_concept_one_var = false;
                    break;
                }
            }
        }
        if !all_concept_one_var || !has_neg {
            continue;
        }
        // Move every negative concept disjunct ¬Ci into the body as +Ci.
        let mut new_body: Vec<Atom> = Vec::new();
        let mut new_head: Vec<Atom> = Vec::new();
        for a in &cl.head {
            if let Atom::Concept { lit, t } = a {
                if lit.neg {
                    new_body.push(Atom::Concept { lit: CLit { neg: false, c: lit.c }, t: *t });
                    continue;
                }
            }
            new_head.push(a.clone());
        }
        cl.body = new_body;
        cl.head = new_head;
        count += 1;
    }
    count
}

/// Build the clause records (sorted body + var count) for the Ht index.
fn mk_recs(clauses: &[Clause]) -> Vec<ClauseRec> {
    clauses
        .iter()
        .map(|c| {
            let sb = sorted_body(&c.body);
            let nv = nvars_of(c);
            (c.clone(), sb, nv)
        })
        .collect()
}

/// Common-disjunct harvest at the global (⊤) level (KM_HT_HARVEST). Konclude's
/// `initializeExtractDisjunctCommonConcept`: for a global disjunction
/// `⊤ ⊑ d1 ⊔ … ⊔ dk` (empty body, all-positive Concept disjuncts), any concept
/// `x` that is a *definite* (choice-free) consequence of EVERY live disjunct is a
/// consequence of the disjunction itself — so `⊤ ⊑ x` holds. Emitting those as
/// unconditional Horn facts lets the tableau derive them deterministically (and
/// fire clash clauses) instead of re-discovering them inside every branch on
/// every model node — the structural lever `docs/konclude-trace-5303.md`
/// identifies for the live ∀+⊔ family.
///
/// Soundness (fixed 2026-06-19 after the shared-model bug): `definite(c)` is
/// computed from an ISOLATED single-seed QoSat per disjunct concept, so no other
/// named seed shares the graph and the label is exactly c's forced closure (no
/// cross-concept contamination). The earlier shared-model version (one
/// saturation seeding ALL concepts) was UNSOUND — it injected non-entailed ⊤
/// facts (broke ore_ont_9024: 12 spurious + 458 lost subsumptions) because
/// `definite(di)` picked up facts that held only because OTHER seeds were in the
/// same graph. With isolated saturation each `definite(c)` is choice-free and the
/// ⋂ over live disjuncts is genuinely ⊤-entailed. A disjunct whose isolated seed
/// clashes (`node_unsat` at node 0) is dropped (sound: it can't be chosen).
/// Validate gold-clean before trusting. Returns the candidate `⊤ ⊑ x` clauses.
fn harvest_global(recs: &[ClauseRec]) -> Vec<Clause> {
    // Collect the global (⊤-headed, empty-body) all-positive disjunctions.
    let mut disjs: Vec<Vec<C>> = Vec::new();
    for (c, sb, _) in recs {
        if !sb.is_empty() {
            continue;
        }
        let mut disj: Vec<C> = Vec::new();
        let mut ok = true;
        for a in &c.head {
            match a {
                Atom::Concept { lit, .. } if !lit.neg => disj.push(lit.c),
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        if ok && disj.len() >= 2 {
            disjs.push(disj);
        }
    }
    if disjs.is_empty() {
        return Vec::new();
    }
    // definite(c): the forced consequences of an individual satisfying ONLY c,
    // from an ISOLATED single-seed saturation (no other named seed shares the
    // graph, so no cross-concept contamination — the soundness fix). Cached per
    // distinct disjunct concept. None ⇒ QoSat bailed (out of fragment) for that
    // seed, in which case we skip any disjunction mentioning it (conservative).
    let mut needed: HashSet<C> = HashSet::new();
    for d in &disjs {
        for &c in d {
            needed.insert(c);
        }
    }
    let mut definite: HashMap<C, Option<(HashSet<C>, bool)>> = HashMap::new();
    for &c in &needed {
        let mut qs = QoSat::new(recs);
        let g = qs.saturate_global(&[c]);
        if g.unsupported || g.label_pos.is_empty() {
            definite.insert(c, None);
        } else {
            // node 0 is the lone seed c; label_pos[0] is its forced closure.
            let dead = g.node_unsat.contains(&0);
            definite.insert(c, Some((g.label_pos[0].clone(), dead)));
        }
    }
    let mut emitted: HashSet<C> = HashSet::new();
    let mut extra: Vec<Clause> = Vec::new();
    for disj in &disjs {
        // Intersect the definite labels of the LIVE (satisfiable) disjuncts.
        let mut common: Option<HashSet<C>> = None;
        let mut bail = false;
        for &d in disj {
            match definite.get(&d) {
                Some(Some((lab, dead))) => {
                    if *dead {
                        continue; // dead disjunct: cannot be chosen
                    }
                    match &mut common {
                        None => common = Some(lab.clone()),
                        Some(cc) => cc.retain(|x| lab.contains(x)),
                    }
                }
                _ => {
                    bail = true; // unsupported seed ⇒ don't harvest this disjunction
                    break;
                }
            }
            if common.as_ref().map_or(false, |c| c.is_empty()) {
                break;
            }
        }
        if bail {
            continue;
        }
        if let Some(cc) = common {
            for x in cc {
                if emitted.insert(x) {
                    extra.push(Clause {
                        body: Vec::new(),
                        head: vec![Atom::Concept { lit: CLit::pos(x), t: X }],
                    });
                }
            }
        }
    }
    extra
}

// ====================== QuasiOrder shared-node saturation ====================
//
// Konclude/HermiT's non-branching saturation keeps ONE shared node per concept
// (existential successors reuse the filler concept's dedicated node), so the
// completion graph is bounded by #concepts — not model size. This is the
// structural lever `docs/konclude-trace-5303.md` identifies: KM's fresh-
// successor `park_fixpoint` still blows up on ∃-chain / transitive onts,
// whereas the shared-node model stays tiny and yields the possible-subsumer
// set + a sufficiency gate in O(#concepts) per query.
//
// `QoSat` is a self-contained worklist saturator over that shared-node model:
// Horn clauses propagate, ∃ heads route to the filler's shared node, role
// clauses (transitivity / chains) fire over the bounded edge set, and ≥2-live
// disjunctions are PARKED (never branched). A clash here means the parked
// over-approximation is inconsistent for the anchor node (NOT necessarily a
// KB-inconsistency verdict) — the caller falls back to the certified branching
// `consistent()` for the real sat/unsat decision. Sufficient (no open parked
// disjunction anchored at a node) ⇒ a genuine complete model of that node's
// seed concept exists ⇒ sat, no tableau test needed.
//
// The disjunct-common-concept harvest rule: a parked disjunction `D1 ⊔ ... ⊔ Dk`
// (all ≥2 live) anchored at `n` derives every literal common to the dedicated
// nodes `node(D1), ..., node(Dk)` into `n` (Konclude's
// `initializeExtractDisjunctCommonConcept`). Because `n` is the shared node of
// a concept `A`, the disjuncts `Di` are themselves named concepts with their own
// shared nodes carrying the `Di`-subsumer set; the intersection of those
// shared labels is exactly the set of `A`'s subsumers that hold *regardless* of
// which `Di` is true — the deterministic consequence. Re-running this as
// labels grow is a monotone fixpoint that closes the parked disjunctions'
// worth of consequences without a single branch. This is the structural
// mechanism the trace doc identifies as the reason Konclude opens ZERO
// branches on the live `∀ + ⊔` disjunction family: it harvests the common
// consequences through the parked disjunctions deterministically and never
// needs to case-split. A clash (a literal and its complement both in `n`)
// means this node cannot satisfy the KB — but, in the global model, a *clashed
// node* is NOT the same as a *clashed model*: a node is dead if and only if its
// own seed is inconsistent, and its clashes are local to it; other nodes keep
// their labels and verdicts. `node_unsat` tracks this.

struct QoSat<'a> {
    clauses: &'a [ClauseRec],
    label: Vec<HashSet<CLit>>,
    out_edges: Vec<Vec<(R, Node)>>,
    /// shared node for a concept literal (pos and neg both keyed).
    concept_node: HashMap<CLit, Node>,
    /// parked disjunctions: (node, clause_id); re-evaluated as labels grow.
    pending: Vec<(Node, usize)>,
    /// nodes whose own seed is unsatisfiable (local clash, not KB clash).
    node_unsat: HashSet<Node>,
    lit_work: Vec<(Node, CLit)>,
    edge_work: Vec<(Node, R, Node)>,
    node_work: Vec<Node>,
    concept_trig: HashMap<CLit, Vec<usize>>,
    role_clauses: Vec<usize>,
    global: Vec<usize>,
    unsupported: bool,
    open_disj: usize,
    /// trail for the residue-test DFS (branching over the shared model). Each
    /// entry records a mutation to undo on backtrack.
    trail: Vec<QoUndo>,
    tracing: bool,
}

/// undoable mutation for the residue-test DFS.
enum QoUndo {
    Lit(Node, CLit),
    Edge(Node, R, Node),
    NodeNew,
    Unsat(Node),
    Pending(usize), // pending grew to this len
    ConceptNode(CLit),
}

pub struct QoResult {
    pub unsupported: bool,
    pub clashed: bool,
    pub sufficient: bool,
    pub root_label: HashSet<C>,
}

/// Per-node model data after a global saturation: for each query concept `A`
/// the model supplies (a) a sat/unsat/clash verdict from `A`'s shared node,
/// (b) `A`'s possible-subsumer set = the positive concept ids in that node's
/// label, (c) a sufficiency flag (no open parked disjunction anchored there).
pub struct QoGlobalResult {
    pub unsupported: bool,
    pub node_unsat: HashSet<Node>,
    pub sufficient: Vec<bool>,
    pub open_disj_per_node: Vec<usize>,
    pub label_pos: Vec<HashSet<C>>,
}

const QO_NODE_CAP: usize = 8000;

impl<'a> QoSat<'a> {
    fn new(clauses: &'a [ClauseRec]) -> QoSat<'a> {
        let mut concept_trig: HashMap<CLit, Vec<usize>> = HashMap::new();
        let mut role_clauses = Vec::new();
        let mut global = Vec::new();
        for (cid, rec) in clauses.iter().enumerate() {
            let body = &rec.1;
            if body.is_empty() {
                global.push(cid);
                continue;
            }
            let has_role = body.iter().any(|a| matches!(a, Atom::Role { .. }));
            if has_role {
                role_clauses.push(cid);
            } else {
                for a in body {
                    if let Atom::Concept { lit, .. } = a {
                        concept_trig.entry(*lit).or_default().push(cid);
                    }
                }
            }
        }
        QoSat {
            clauses,
            label: Vec::new(),
            out_edges: Vec::new(),
            concept_node: HashMap::new(),
            pending: Vec::new(),
            node_unsat: HashSet::new(),
            lit_work: Vec::new(),
            edge_work: Vec::new(),
            node_work: Vec::new(),
            concept_trig,
            role_clauses,
            global,
            unsupported: false,
            open_disj: 0,
            trail: Vec::new(),
            tracing: false,
        }
    }

    fn new_node(&mut self) -> Node {
        let id = self.label.len();
        self.label.push(HashSet::new());
        self.out_edges.push(Vec::new());
        self.node_work.push(id);
        if self.tracing {
            self.trail.push(QoUndo::NodeNew);
        }
        id
    }

    /// The dedicated shared node for a concept literal: one node per `CLit`,
    /// reused on every reference. Created on first use and seeded with `lit`.
    fn concept_node_of(&mut self, lit: CLit) -> Node {
        if let Some(&n) = self.concept_node.get(&lit) {
            return n;
        }
        let n = self.new_node();
        self.concept_node.insert(lit, n);
        if self.tracing {
            self.trail.push(QoUndo::ConceptNode(lit));
        }
        // seed: the dedicated node of `A` (or `¬A`) carries `A` (resp. `¬A`).
        self.add_lit(n, lit);
        n
    }

    /// Assert `lit` at `n`. Returns false if a clash is raised at `n` (local —
    /// `n` is recorded unsat; the model keeps running for other nodes). No-ops
    /// if present. Routes through `node_alive` so a dead node stays inert.
    fn add_lit(&mut self, n: Node, lit: CLit) -> bool {
        if self.node_unsat.contains(&n) {
            return false;
        }
        let comp = CLit { neg: !lit.neg, c: lit.c };
        if self.label[n].contains(&comp) {
            self.kill_node(n);
            return false;
        }
        if self.label[n].insert(lit) {
            if self.tracing {
                self.trail.push(QoUndo::Lit(n, lit));
            }
            self.lit_work.push((n, lit));
        }
        true
    }

    /// Mark `n` unsat (local clash). Prune its parked disjunctions from the
    /// global `open_disj` count so sufficiency of *other* nodes is unaffected.
    fn kill_node(&mut self, n: Node) {
        if self.node_unsat.insert(n) {
            if self.tracing {
                self.trail.push(QoUndo::Unsat(n));
                return;
            }
            let mut i = 0;
            while i < self.pending.len() {
                if self.pending[i].0 == n {
                    self.pending.swap_remove(i);
                    self.open_disj = self.open_disj.saturating_sub(1);
                } else {
                    i += 1;
                }
            }
        }
    }

    fn ensure_filler(&mut self, lit: CLit) -> Node {
        self.concept_node_of(lit)
    }

    fn add_edge(&mut self, s: Node, r: R, t: Node) {
        if self.out_edges[s].iter().any(|(rr, tt)| *rr == r && *tt == t) {
            return;
        }
        self.out_edges[s].push((r, t));
        self.edge_work.push((s, r, t));
        if self.tracing {
            self.trail.push(QoUndo::Edge(s, r, t));
        }
    }

    /// Run the non-branching saturation fixpoint from a seeded root (node 0).
    /// Used only for the global-consistency probe (no per-concept nodes seeded).
    fn saturate(&mut self, seed: &[CLit]) -> QoResult {
        if self.label.is_empty() {
            self.new_node(); // root = node 0
        }
        let root = 0usize;
        for &lit in seed {
            if !self.add_lit(root, lit) {
                return self.finish(root);
            }
            self.concept_node.entry(lit).or_insert(root);
        }
        let mut guard = 0u64;
        loop {
            guard += 1;
            if guard > 50_000_000 || self.label.len() > QO_NODE_CAP {
                self.unsupported = true;
                return self.finish(root);
            }
            self.drain_work();
            if self.unsupported {
                return self.finish(root);
            }
            if self.lit_work.is_empty() && self.node_work.is_empty() && self.edge_work.is_empty() {
                self.harvest_all();
                if self.unsupported {
                    return self.finish(root);
                }
                self.eval_all_parked();
                if self.lit_work.is_empty() && self.node_work.is_empty() && self.edge_work.is_empty()
                {
                    break;
                }
            }
        }
        self.finish(root)
    }

    /// Global saturation: seed one shared node per named concept (positive
    /// polarity), run the deterministic fixpoint with the harvest rule, return
    /// per-node model data. This is Konclude's single non-branching pass.
    fn saturate_global(&mut self, named_concepts: &[C]) -> QoGlobalResult {
        for &c in named_concepts {
            self.concept_node_of(CLit::pos(c));
        }
        let mut guard = 0u64;
        loop {
            guard += 1;
            if guard > 50_000_000 || self.label.len() > QO_NODE_CAP {
                self.unsupported = true;
                return self.finish_global();
            }
            self.drain_work();
            if self.unsupported {
                return self.finish_global();
            }
            if self.lit_work.is_empty() && self.node_work.is_empty() && self.edge_work.is_empty() {
                self.harvest_all();
                if self.unsupported {
                    return self.finish_global();
                }
                self.eval_all_parked();
                if self.lit_work.is_empty() && self.node_work.is_empty() && self.edge_work.is_empty()
                {
                    break;
                }
            }
        }
        self.finish_global()
    }

    /// Drain all worklists once: literal-triggered clauses, new-node globals,
    /// edge-triggered role clauses, and harvest obligations.
    fn drain_work(&mut self) {
        while let Some((n, lit)) = self.lit_work.pop() {
            if self.node_unsat.contains(&n) {
                continue;
            }
            if let Some(trigs) = self.concept_trig.get(&lit).cloned() {
                for cid in trigs {
                    self.fire_concept_clause(cid, n);
                    if self.unsupported {
                        return;
                    }
                }
            }
            if !self.tracing {
                self.eval_parked_at(n);
            }
        }
        while let Some(n) = self.node_work.pop() {
            if self.node_unsat.contains(&n) {
                continue;
            }
            for cid in self.global.clone() {
                self.fire_concept_clause(cid, n);
                if self.unsupported {
                    return;
                }
            }
        }
        while let Some((s, r, t)) = self.edge_work.pop() {
            let rcs = self.role_clauses.clone();
            for cid in rcs {
                self.fire_role_clause(cid, s, r, t);
                if self.unsupported {
                    return;
                }
            }
        }
    }

    /// Harvest disjunct-common-concept consequences for ALL parked disjunctions
    /// (run at the fixpoint, when disjunct nodes are fully saturated, so the
    /// intersection is the true common-consequence set — never an
    /// over-approximation). The rule: a parked ≥2-live disjunction `D1..Dk` at
    /// `n` derives every literal common to `node(D1)..node(Dk)` into `n`.
    fn harvest_all(&mut self) {
        let parked: Vec<(Node, usize)> = self.pending.clone();
        for (n, cid) in parked {
            if self.node_unsat.contains(&n) {
                continue;
            }
            self.harvest_disj(n, cid);
            if self.unsupported {
                return;
            }
        }
    }

    /// For parked disjunction `cid` at `n`: intersect the positive labels of
    /// the dedicated nodes of all live disjuncts and add the intersection to
    /// `n`. The negative labels are intersected too (common negated
    /// consequences). Sound because the disjunction is still parked: whatever
    /// disjunct is eventually chosen, all of them carry the common label.
    fn harvest_disj(&mut self, n: Node, cid: usize) {
        let head = &self.clauses[cid].0.head;
        // collect live disjuncts (Concept only; Exists/Role park at apply_head
        // is satisfied-by-routing, so a parked disj is all Concept).
        let mut disj_nodes: Vec<(Node, CLit)> = Vec::new();
        for h in head {
            if let Atom::Concept { lit, t: _ } = h {
                if self.label[n].contains(lit) {
                    return; // satisfied — no longer parked
                }
                let comp = CLit { neg: !lit.neg, c: lit.c };
                if self.label[n].contains(&comp) {
                    continue; // dead disjunct
                }
                // live: its shared node carries the common-consequence set.
                disj_nodes.push((self.concept_node_of(*lit), *lit));
            }
        }
        if disj_nodes.len() < 2 {
            return; // 0 or 1 live — unit propagation handles it, not harvest.
        }
        // intersection of positive labels across all disjunct shared nodes.
        let mut common: Option<HashSet<CLit>> = None;
        for (dn, _) in &disj_nodes {
            if self.node_unsat.contains(dn) {
                return; // a dead disjunct node contributes nothing sound.
            }
            let lab = &self.label[*dn];
            match &mut common {
                None => common = Some(lab.iter().copied().collect()),
                Some(c) => c.retain(|x| lab.contains(x)),
            }
        }
        let common = match common {
            Some(c) if !c.is_empty() => c,
            _ => return,
        };
        for lit in common {
            if !self.label[n].contains(&lit)
                && !self.label[n].contains(&CLit { neg: !lit.neg, c: lit.c })
            {
                self.add_lit(n, lit);
            }
        }
    }

    /// Re-evaluate ALL parked disjunctions (global pass at fixpoint).
    fn eval_all_parked(&mut self) {
        let pend = self.pending.clone();
        for (n, _cid) in pend {
            self.eval_parked_at(n);
        }
    }

    fn finish(&self, root: Node) -> QoResult {
        let root_label: HashSet<C> = self
            .label
            .get(root)
            .map(|s| s.iter().filter(|k| !k.neg).map(|k| k.c).collect())
            .unwrap_or_default();
        QoResult {
            unsupported: self.unsupported,
            clashed: self.node_unsat.contains(&root),
            sufficient: !self.node_unsat.contains(&root) && self.open_disj == 0,
            root_label,
        }
    }

    fn finish_global(&self) -> QoGlobalResult {
        let nn = self.label.len();
        let mut sufficient = vec![false; nn];
        let mut open_disj_per_node = vec![0usize; nn];
        for &(n, _cid) in &self.pending {
            open_disj_per_node[n] = open_disj_per_node[n].saturating_add(1);
        }
        for n in 0..nn {
            sufficient[n] = !self.node_unsat.contains(&n) && open_disj_per_node[n] == 0;
        }
        let label_pos: Vec<HashSet<C>> = self
            .label
            .iter()
            .map(|s| s.iter().filter(|k| !k.neg).map(|k| k.c).collect())
            .collect();
        QoGlobalResult {
            unsupported: self.unsupported,
            node_unsat: self.node_unsat.clone(),
            sufficient,
            open_disj_per_node,
            label_pos,
        }
    }

    // ===================== residue SAT test (branching DFS) ====================
    //
    // After the global non-branching saturation, an insufficient anchor node
    // (open parked disjunctions) needs a real SAT verdict. Konclude runs that
    // test IN PLACE over the shared-node model: it branches ONLY the open
    // disjunctions in the anchor's reachable subtree, propagating through the
    // already-saturated shared nodes, with checkpoint/rollback per branch. This
    // is exponentially cheaper than rebuilding a fresh model-sized completion
    // graph (the legacy `consistent()` path), because the shared graph is
    // bounded by #concepts and only the ~15-20 open disjunctions branch.
    //
    // Soundness: the shared node for concept C represents "some individual
    // satisfying C"; its label is the complete consequence set of C (the global
    // saturation is a fixpoint). Branching an open disjunction D1⊔..⊔Dk at the
    // anchor asserts one disjunct Di — constructing a witness where the
    // anchor-individual satisfies Di (and inherits Di's saturated consequences).
    // A clash-free completion across all open disjunctions is a genuine model
    // (one witness per ∃ / per disjunction suffices for the SAT question); all
    // branches clashing ⇒ no model ⇒ unsat. This is the standard tableau SAT
    // test restricted to the shared abstraction, which is complete precisely
    // because the shared labels are the saturated consequence sets.

    fn checkpoint(&self) -> usize {
        self.trail.len()
    }

    fn rollback(&mut self, mark: usize) {
        while self.trail.len() > mark {
            match self.trail.pop().unwrap() {
                QoUndo::Lit(n, lit) => {
                    self.label[n].remove(&lit);
                }
                QoUndo::Edge(s, r, t) => {
                    if let Some(out) = self.out_edges.get_mut(s) {
                        out.retain(|(rr, tt)| !(*rr == r && *tt == t));
                    }
                }
                QoUndo::NodeNew => {
                    self.label.pop();
                    self.out_edges.pop();
                }
                QoUndo::Unsat(n) => {
                    self.node_unsat.remove(&n);
                }
                QoUndo::Pending(len) => {
                    self.pending.truncate(len);
                }
                QoUndo::ConceptNode(lit) => {
                    self.concept_node.remove(&lit);
                }
            }
        }
        // clear residual worklists (they reference undone state).
        self.lit_work.clear();
        self.node_work.clear();
        self.edge_work.clear();
    }

    /// BFS subtree from `root` over `out_edges` (root included).
    fn qo_subtree(&self, root: Node) -> HashSet<Node> {
        let mut seen = HashSet::new();
        let mut stack = vec![root];
        seen.insert(root);
        while let Some(n) = stack.pop() {
            for &(_, t) in &self.out_edges[n] {
                if seen.insert(t) {
                    stack.push(t);
                }
            }
        }
        seen
    }

    /// Branching fixpoint: drain + harvest + unit-prop until stable. Does NOT
    /// mutate `pending` (open disjunctions stay parked; the DFS resolves them).
    fn qo_fixpoint(&mut self) {
        let mut guard = 0u64;
        loop {
            guard += 1;
            if guard > 5_000_000 {
                self.unsupported = true;
                return;
            }
            self.drain_work();
            if self.unsupported {
                return;
            }
            if self.lit_work.is_empty() && self.node_work.is_empty() && self.edge_work.is_empty() {
                self.harvest_all();
                if self.unsupported {
                    return;
                }
                let made_unit = self.qo_unit_scan();
                if !made_unit
                    && self.lit_work.is_empty()
                    && self.node_work.is_empty()
                    && self.edge_work.is_empty()
                {
                    break;
                }
            }
        }
    }

    /// Scan parked disjunctions for unit-forced ones (exactly one live disjunct
    /// at its node) and assert that disjunct. Returns true if any was asserted.
    /// Leaves `pending` intact (the DFS will skip satisfied/open ones by re-scan).
    fn qo_unit_scan(&mut self) -> bool {
        let snap = self.pending.clone();
        let mut progress = false;
        for (n, cid) in snap {
            if self.node_unsat.contains(&n) {
                continue;
            }
            let head = &self.clauses[cid].0.head;
            let mut live: Vec<CLit> = Vec::new();
            let mut satisfied = false;
            for h in head {
                if let Atom::Concept { lit, t: _ } = h {
                    if self.label[n].contains(lit) {
                        satisfied = true;
                        break;
                    }
                    let comp = CLit { neg: !lit.neg, c: lit.c };
                    if self.label[n].contains(&comp) {
                        continue;
                    }
                    live.push(*lit);
                }
            }
            if satisfied || live.len() != 1 {
                continue;
            }
            self.add_lit(n, live[0]);
            progress = true;
        }
        progress
    }

    /// The open parked disjunctions anchored in `sub` (≥2 live, not satisfied).
    fn qo_open_in(&self, sub: &HashSet<Node>) -> Vec<(Node, usize)> {
        let mut out = Vec::new();
        for &(n, cid) in &self.pending {
            if !sub.contains(&n) || self.node_unsat.contains(&n) {
                continue;
            }
            let head = &self.clauses[cid].0.head;
            let mut live = 0usize;
            let mut satisfied = false;
            for h in head {
                if let Atom::Concept { lit, t: _ } = h {
                    if self.label[n].contains(lit) {
                        satisfied = true;
                        break;
                    }
                    let comp = CLit { neg: !lit.neg, c: lit.c };
                    if !self.label[n].contains(&comp) {
                        live += 1;
                    }
                }
            }
            if !satisfied && live >= 2 {
                out.push((n, cid));
            }
        }
        out
    }

    /// DFS: return true iff the anchor's subtree admits a clash-free completion.
    fn qo_branch_dfs(&mut self, sub: &HashSet<Node>, depth: u32, dl: Option<Instant>) -> bool {
        if depth > 64 {
            self.unsupported = true;
            return false;
        }
        if let Some(t) = dl {
            if Instant::now().duration_since(t).as_millis() > 4000 {
                self.unsupported = true;
                return false;
            }
        }
        self.qo_fixpoint();
        if self.unsupported {
            return false;
        }
        // anchor (any node in sub) clashing ⇒ this branch dead.
        for &n in sub {
            if self.node_unsat.contains(&n) {
                return false;
            }
        }
        let open = self.qo_open_in(sub);
        if open.is_empty() {
            return true; // clash-free complete model of the anchor
        }
        // branch the first open disjunction (fewest live would be better; keep
        // it simple for now — the harvest has already closed most).
        let (n, cid) = open[0];
        let head = &self.clauses[cid].0.head;
        let live: Vec<CLit> = head
            .iter()
            .filter_map(|h| {
                if let Atom::Concept { lit, t: _ } = h {
                    if self.label[n].contains(lit) {
                        return None;
                    }
                    let comp = CLit { neg: !lit.neg, c: lit.c };
                    if self.label[n].contains(&comp) {
                        return None;
                    }
                    return Some(*lit);
                }
                None
            })
            .collect();
        for lit in live {
            let mark = self.checkpoint();
            self.add_lit(n, lit);
            if self.qo_branch_dfs(sub, depth + 1, dl) {
                return true;
            }
            self.rollback(mark);
            if self.unsupported {
                return false;
            }
        }
        false
    }

    /// Residue SAT test over the shared model. `anchor` is the shared node of
    /// the concept under test; `extra` are additional literals to assert there
    /// (e.g. ¬B for the A⊑B test). Returns Some(true)=sat, Some(false)=unsat,
    /// None=unsupported/out-of-fragment/depth-bounded.
    fn qo_residue_test(&mut self, anchor: Node, extra: &[CLit]) -> Option<bool> {
        self.tracing = true;
        let dl = Some(Instant::now());
        let mark = self.checkpoint();
        for &lit in extra {
            if !self.add_lit(anchor, lit) {
                // immediate clash at anchor ⇒ unsat (the extra literals are
                // inconsistent with the anchor's saturated label).
                self.rollback(mark);
                self.tracing = false;
                return Some(false);
            }
        }
        let sub = self.qo_subtree(anchor);
        let r = self.qo_branch_dfs(&sub, 0, dl);
        let unsup = self.unsupported;
        self.rollback(mark);
        self.tracing = false;
        self.unsupported = false; // reset the branch-local flag
        if std::env::var_os("KM_HT_QOTRACE").is_some() {
            let dur = dl.unwrap().elapsed().as_millis();
            eprintln!("KM_HT [qo-residue] anchor={} extra={:?} -> r={} unsup={} {}ms", anchor, extra, r, unsup, dur);
        }
        if unsup {
            return None;
        }
        Some(r)
    }

    /// Fire an all-Concept-body clause at node `n` (body var X = n).
    fn fire_concept_clause(&mut self, cid: usize, n: Node) {
        let body = &self.clauses[cid].1;
        for a in body {
            if let Atom::Concept { lit, .. } = a {
                if !self.label[n].contains(lit) {
                    return;
                }
            } else {
                return;
            }
        }
        let mut sigma = vec![None; self.clauses[cid].2];
        sigma[X as usize] = Some(n);
        self.apply_head(cid, &sigma);
    }

    /// Fire a role-body clause, anchored at a freshly added edge (es, r, et).
    fn fire_role_clause(&mut self, cid: usize, es: Node, r: R, et: Node) {
        let body = &self.clauses[cid].1;
        let nv = self.clauses[cid].2;
        for (i, a) in body.iter().enumerate() {
            if let Atom::Role { r: ar, s, t } = a {
                if *ar != r {
                    continue;
                }
                let mut sigma = vec![None; nv];
                let mut done = vec![false; body.len()];
                if (sigma[*s as usize].is_none() || sigma[*s as usize] == Some(es))
                    && (sigma[*t as usize].is_none() || sigma[*t as usize] == Some(et))
                {
                    sigma[*s as usize] = Some(es);
                    sigma[*t as usize] = Some(et);
                    done[i] = true;
                    let mut out: Vec<Vec<Option<Node>>> = Vec::new();
                    self.match_body(body, &mut done, &mut sigma, &mut out);
                    for sgm in &out {
                        self.apply_head(cid, sgm);
                        if self.unsupported {
                            return;
                        }
                    }
                }
            }
        }
    }

    /// Recursive body matcher over the QoSat model (Concept + Role atoms).
    fn match_body(
        &self,
        body: &[Atom],
        done: &mut [bool],
        sigma: &mut Vec<Option<Node>>,
        out: &mut Vec<Vec<Option<Node>>>,
    ) {
        let k = match (0..body.len()).find(|&i| !done[i]) {
            Some(k) => k,
            None => {
                out.push(sigma.clone());
                return;
            }
        };
        done[k] = true;
        match &body[k] {
            Atom::Concept { lit, t } => {
                if let Some(n) = sigma[*t as usize] {
                    if !self.node_unsat.contains(&n) && self.label[n].contains(lit) {
                        self.match_body(body, done, sigma, out);
                    }
                }
            }
            Atom::Role { r, s, t } => match (sigma[*s as usize], sigma[*t as usize]) {
                (Some(sn), Some(tn)) => {
                    if self.out_edges[sn].iter().any(|(rr, tt)| *rr == *r && *tt == tn) {
                        self.match_body(body, done, sigma, out);
                    }
                }
                (Some(sn), None) => {
                    for &(rr, tt) in &self.out_edges[sn] {
                        if rr == *r {
                            sigma[*t as usize] = Some(tt);
                            self.match_body(body, done, sigma, out);
                            sigma[*t as usize] = None;
                        }
                    }
                }
                (None, Some(tn)) => {
                    for sn in 0..self.label.len() {
                        if self.out_edges[sn].iter().any(|(rr, tt)| *rr == *r && *tt == tn) {
                            sigma[*s as usize] = Some(sn);
                            self.match_body(body, done, sigma, out);
                            sigma[*s as usize] = None;
                        }
                    }
                }
                (None, None) => {}
            },
            _ => {}
        }
        done[k] = false;
    }

    /// Apply a clause's head under substitution `sigma`.
    fn apply_head(&mut self, cid: usize, sigma: &[Option<Node>]) {
        let head = &self.clauses[cid].0.head;
        if head.is_empty() {
            // empty head: clash at the anchor node.
            let n = sigma[X as usize].expect("X bound");
            self.kill_node(n);
            return;
        }
        let mut satisfied = false;
        let mut live: Vec<(Node, CLit)> = Vec::new();
        for h in head {
            match *h {
                Atom::Concept { lit, t } => {
                    let n = sigma[t as usize].expect("head var bound");
                    if self.node_unsat.contains(&n) {
                        continue;
                    }
                    if self.label[n].contains(&lit) {
                        satisfied = true;
                        break;
                    }
                    let comp = CLit { neg: !lit.neg, c: lit.c };
                    if self.label[n].contains(&comp) {
                        // dead disjunct
                    } else {
                        live.push((n, lit));
                    }
                }
                Atom::Exists { r, fil, t } => {
                    let n = sigma[t as usize].expect("head var bound");
                    if self.node_unsat.contains(&n) {
                        return;
                    }
                    let f = self.ensure_filler(fil);
                    if !self.out_edges[n].iter().any(|(rr, tt)| *rr == r && *tt == f) {
                        self.add_edge(n, r, f);
                    }
                    satisfied = true;
                    break;
                }
                Atom::Role { r, s, t } => {
                    let sn = sigma[s as usize].expect("head role src bound");
                    let tn = sigma[t as usize].expect("head role dst bound");
                    if !self.node_unsat.contains(&sn) {
                        self.add_edge(sn, r, tn);
                    }
                    satisfied = true;
                    break;
                }
                Atom::Eq { .. } => {
                    self.unsupported = true;
                    return;
                }
            }
        }
        if satisfied || self.unsupported {
            return;
        }
        let anchor = sigma[X as usize].expect("X bound");
        if live.is_empty() {
            self.kill_node(anchor);
            return;
        }
        if live.len() == 1 {
            self.add_lit(live[0].0, live[0].1);
            return;
        }
        // ≥2 live: park. Record and count as open.
        if self.tracing {
            self.trail.push(QoUndo::Pending(self.pending.len()));
        }
        self.pending.push((anchor, cid));
        self.open_disj += 1;
    }

    /// Re-evaluate parked disjunctions at `n`: a label change may have satisfied,
    /// unit-resolved, or all-refuted one. Maintains `open_disj`.
    fn eval_parked_at(&mut self, n: Node) {
        let mut i = 0;
        while i < self.pending.len() {
            if self.pending[i].0 != n || self.node_unsat.contains(&n) {
                i += 1;
                continue;
            }
            let cid = self.pending[i].1;
            let head = &self.clauses[cid].0.head;
            let mut satisfied = false;
            let mut live: Vec<CLit> = Vec::new();
            for h in head {
                if let Atom::Concept { lit, t: _ } = h {
                    if self.label[n].contains(lit) {
                        satisfied = true;
                        break;
                    }
                    let comp = CLit { neg: !lit.neg, c: lit.c };
                    if self.label[n].contains(&comp) {
                        continue;
                    }
                    live.push(*lit);
                }
            }
            if satisfied {
                self.pending.swap_remove(i);
                self.open_disj = self.open_disj.saturating_sub(1);
                continue;
            }
            if live.is_empty() {
                self.kill_node(n);
                return;
            }
            if live.len() == 1 {
                self.pending.swap_remove(i);
                self.open_disj = self.open_disj.saturating_sub(1);
                self.add_lit(n, live[0]);
                continue;
            }
            i += 1;
        }
    }
}

impl Ht {
    pub fn new(clauses: Vec<Clause>) -> Ht {
        let mut clauses = clauses;
        // KM_HT_TRIGABS: trigger-keyed binary absorption — rewrite global
        // ⊤-disjunctions with negated disjuncts into dormant triggered clauses so
        // they no longer fire on every node. Run BEFORE contrapositives so the
        // clash clauses freshly produced by all-negative heads get enriched too.
        if std::env::var_os("KM_HT_TRIGABS").is_some() {
            let absorbed = trigger_absorb(&mut clauses);
            if std::env::var_os("KM_HT_STATS").is_some() {
                eprintln!("KM_HT_STATS trigger_absorb absorbed={}", absorbed);
            }
        }
        // KM_HT_CONTRA: enrich clash clauses with their contrapositives so negative
        // literals propagate, feeding Ht's existing unit-propagation (eval_disj).
        if std::env::var_os("KM_HT_CONTRA").is_some() {
            let extra = contrapositives(&clauses);
            if std::env::var_os("KM_HT_STATS").is_some() {
                eprintln!("KM_HT_STATS contrapositives added={}", extra.len());
            }
            clauses.extend(extra);
        }
        let mut recs: Vec<ClauseRec> = mk_recs(&clauses);
        // KM_HT_HARVEST: inject global common-disjunct consequences as ⊤-facts so
        // the tableau derives them deterministically instead of re-branching them
        // on every node (the live ∀+⊔ family lever). Reuses only QoSat's sound
        // saturation, not its residue test.
        if std::env::var_os("KM_HT_HARVEST").is_some() {
            let extra = harvest_global(&recs);
            if std::env::var_os("KM_HT_STATS").is_some() {
                eprintln!("KM_HT_STATS harvest global_facts={}", extra.len());
            }
            if !extra.is_empty() {
                clauses.extend(extra);
                recs = mk_recs(&clauses);
            }
        }
        let mut concept_triggers: HashMap<CLit, Vec<(usize, usize)>> = HashMap::new();
        let mut role_triggers: HashMap<R, Vec<(usize, usize)>> = HashMap::new();
        let mut global_clauses = Vec::new();
        let mut global_disj = Vec::new();
        for (cid, rec) in recs.iter().enumerate() {
            if rec.1.is_empty() {
                global_clauses.push(cid);
                // disjunctive global = empty body + ≥2 concept head atoms (the
                // ⊤ ⊑ A ∨ B GCIs that fire and branch on every node).
                let nhc = rec.0.head.iter().filter(|a| matches!(a, Atom::Concept { .. })).count();
                if nhc >= 2 {
                    global_disj.push(cid);
                }
            }
            for (pos, a) in rec.1.iter().enumerate() {
                match *a {
                    Atom::Concept { lit, .. } => {
                        concept_triggers.entry(lit).or_default().push((cid, pos));
                    }
                    Atom::Role { r, .. } => {
                        role_triggers.entry(r).or_default().push((cid, pos));
                    }
                    _ => {}
                }
            }
        }
        let ht = Ht {
            clauses: recs,
            concept_triggers,
            role_triggers,
            global_disj_set: global_disj.iter().copied().collect(),
            global_disj,
            global_clauses,
            eager: std::env::var_os("KM_HT_EAGER").is_some(),
            ext: Ext::new(),
            anywhere: std::env::var_os("KM_HT_ANCESTOR_ONLY").is_none(),
            // default 1 = SUBSET anywhere blocking: empirically the only mode
            // that folds the disjunction-family models enough to terminate
            // (recovers 5303/12141/9024; core/eq fold too little and time out).
            // Sound + complete for ALC(H); with transitive roles it can be
            // incomplete (5303 drops 1 subsumption), so the router must withhold
            // KM_HT from onts with transitive roles. KM_HT_BLOCK overrides
            // (0=core, 2=full-eq).
            block_mode: if std::env::var_os("KM_HT_SUBSET_BLOCK").is_some() {
                1
            } else {
                env_u8("KM_HT_BLOCK", 1)
            },
            cache: HashMap::new(),
            steps: 0,
            backtracks: 0,
            backjumps: 0,
            negfired: 0,
            branch_pushes: 0,
            disjunct_tries: 0,
            block_us: 0,
            block_buf: RefCell::new(BlockBuf::default()),
            stats: std::env::var_os("KM_HT_STATS").is_some(),
            hb: std::env::var("KM_HT_HB").ok().and_then(|s| s.parse().ok()).unwrap_or(200_000),
            tick: 0,
            cur_depth: 0,
            activity: HashMap::new(),
            ord_mode: env_u8("KM_HT_ORD", 0),
            pick_mode: env_u8("KM_HT_PICK", 0),
            do_restart: std::env::var_os("KM_HT_RESTART").is_some(),
            rbase: std::env::var("KM_HT_RBASE").ok().and_then(|s| s.parse().ok()).unwrap_or(200),
            conflicts: 0,
            restart_limit: u64::MAX,
            luby_idx: 1,
            restarts: 0,
            start: Instant::now(),
            trace: std::env::var_os("KM_HT_TRACE").is_some(),
            naive: std::env::var_os("KM_HT_NAIVE").is_some(),
            // blockskip needs the full pending re-scan so a disjunction whose
            // node became unblocked is reconsidered (the watch path only revisits
            // dirty/open ids and could miss the unblock).
            watch: std::env::var_os("KM_HT_NO_WATCH").is_none()
                && std::env::var_os("KM_HT_BLOCKSKIP").is_none(),
            learn: std::env::var_os("KM_HT_LEARN").is_some(),
            learn_nostale: std::env::var_os("KM_HT_LEARN_NOSTALE").is_some(),
            negtried: std::env::var_os("KM_HT_NEGTRIED").is_some(),
            decisions: Vec::new(),
            learned: Vec::new(),
            lwatch: HashMap::new(),
            satcache: std::env::var_os("KM_HT_SATCACHE").is_some(),
            sat_sigs: HashSet::new(),
            phase_save: std::env::var_os("KM_HT_PHASE").is_some(),
            phase: HashMap::new(),
            lblng: std::env::var_os("KM_HT_LBLCACHE").is_some(),
            cur_choices: HashMap::new(),
            dec_sig: Vec::new(),
            dec_choice: Vec::new(),
            lng: Vec::new(),
            lng_watch: HashMap::new(),
            lng_fires: 0,
            satfold: std::env::var_os("KM_HT_SATFOLD").is_some(),
            sat_labels: Vec::new(),
            satfold_watch: HashMap::new(),
            satfold_hits: 0,
        };
        if ht.trace {
            let (mut hrole, mut heq, mut hexists, mut hdisj, mut hdisj_ex) = (0, 0, 0, 0, 0);
            for (c, _, _) in &ht.clauses {
                let nrole = c.head.iter().filter(|a| matches!(a, Atom::Role { .. })).count();
                let neq = c.head.iter().filter(|a| matches!(a, Atom::Eq { .. })).count();
                let nex = c.head.iter().filter(|a| matches!(a, Atom::Exists { .. })).count();
                if nrole > 0 { hrole += 1; }
                if neq > 0 { heq += 1; }
                if nex > 0 { hexists += 1; }
                if c.head.len() >= 2 { hdisj += 1; }
                if c.head.len() >= 2 && nex > 0 { hdisj_ex += 1; }
            }
            eprintln!(
                "TR CENSUS clauses={} head_role={} head_eq={} head_exists={} disj(>=2)={} disj_with_exists={}",
                ht.clauses.len(), hrole, heq, hexists, hdisj, hdisj_ex
            );
        }
        ht
    }

    #[inline]
    fn act_of(&self, c: C) -> u64 {
        *self.activity.get(&c).unwrap_or(&0)
    }

    /// Order disjuncts within a branch by clash activity (stable: ties keep
    /// program order, so ord_mode 0 is a no-op vs the baseline).
    fn order_disjuncts(&self, ds: &mut [GroundDisjunct]) {
        match self.ord_mode {
            1 => ds.sort_by_key(|d| self.act_of(d.lit.c)), // least-failing first
            2 => ds.sort_by_key(|d| std::cmp::Reverse(self.act_of(d.lit.c))), // most-failing first
            _ => {}
        }
        // KM_HT_PHASE: stable phase-saving pass — a disjunct whose concept was true
        // in the last model is tried first (warm-start toward a known model). Stable
        // so it only promotes phase-true disjuncts, preserving ord_mode's order
        // among ties. A positive literal whose concept was last-true is preferred;
        // a negative literal is preferred when its concept was last-FALSE.
        if self.phase_save {
            ds.sort_by_key(|d| {
                let last = self.phase.get(&d.lit.c).copied().unwrap_or(false);
                // preferred (key 0) when the literal agrees with the saved phase.
                let agrees = if d.lit.neg { !last } else { last };
                !agrees as u8
            });
        }
    }

    pub fn set_anywhere(&mut self, v: bool) {
        self.anywhere = v;
    }

    #[inline]
    fn heartbeat(&mut self, where_: &str) {
        self.tick += 1;
        if self.stats && self.tick % self.hb == 0 {
            // In-flight label-distinctness probe (KM_HT_LABELPROBE): how many of the
            // live nodes share an identical positive-concept label. distinct ≪ nodes
            // ⇒ heavy subtree redundancy that model/label caching would collapse;
            // distinct ≈ nodes ⇒ genuinely independent constraints (caching won't
            // help). Computed only at the heartbeat cadence, so the O(n·label) cost
            // is amortised.
            let (distinct, dup_max) = if std::env::var_os("KM_HT_LABELPROBE").is_some() {
                let nn = self.ext.num_nodes();
                let mut counts: HashMap<Vec<C>, u32> = HashMap::new();
                for n in 0..nn {
                    let mut s: Vec<C> = self.ext.concepts[n]
                        .keys()
                        .filter(|k| !k.neg)
                        .map(|k| k.c)
                        .collect();
                    s.sort_unstable();
                    *counts.entry(s).or_insert(0) += 1;
                }
                (counts.len(), counts.values().copied().max().unwrap_or(0))
            } else {
                (0, 0)
            };
            eprintln!(
                "KM_HT [{}] t_ms={} tick={} steps={} backtracks={} backjumps={} conflicts={} restarts={} nodes={} distinct_lbl={} dup_max={} depth={} pending={} oblig={} lng={} lng_fires={} mtot={} mmax={}",
                where_,
                self.start.elapsed().as_millis(),
                self.tick,
                self.steps,
                self.backtracks,
                self.backjumps,
                self.conflicts,
                self.restarts,
                self.ext.num_nodes(),
                distinct,
                dup_max,
                self.cur_depth,
                self.ext.pending.len(),
                self.ext.obligations.len(),
                self.lng.len(),
                self.lng_fires,
                MATCH_TOT.load(Ordering::Relaxed),
                MATCH_MAX.load(Ordering::Relaxed),
            );
            if self.satfold {
                eprintln!("KM_HT [satfold] labels={} hits={}", self.sat_labels.len(), self.satfold_hits);
            }
        }
    }

    fn label_hash(&self, n: Node) -> u64 {
        let mut h: u64 = 0;
        for k in self.ext.concepts[n].keys() {
            let mut x = (k.c as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
            if k.neg {
                x ^= 0xFFFF_FFFF_FFFF_FFFF;
            }
            h ^= x.rotate_left(17);
        }
        h
    }
    fn label_eq(&self, n: Node, m: Node) -> bool {
        let a = &self.ext.concepts[n];
        let b = &self.ext.concepts[m];
        a.len() == b.len() && a.keys().all(|k| b.contains_key(k))
    }
    fn is_blocked(&self, n: Node) -> bool {
        if !self.ext.blockable[n] {
            return false;
        }
        if !self.anywhere {
            return ancestor_blocked(&self.ext, n);
        }
        // single-node view of anywhere-subset blocking; `process_obligations`
        // uses the cheaper batch `compute_blocked` (this stays for completeness).
        self.compute_blocked()[n]
    }

    /// KM_HT_BLOCKSKIP: recompute the per-node blocked snapshot used to suppress
    /// branching on blocked nodes. Called once per branch selection (after the
    /// propagation fixpoint), so the snapshot reflects the current labels. Cheap:
    /// the same anywhere/ancestor computation `process_obligations` already runs.
    fn refresh_blocked(&mut self) {
        if !self.ext.blockskip {
            return;
        }
        self.ext.blocked = if self.anywhere {
            self.compute_blocked()
        } else {
            (0..self.ext.num_nodes())
                .map(|n| ancestor_blocked(&self.ext, n))
                .collect()
        };
    }

    /// Anywhere SUBSET blocking — the HermiT model-folding KM was missing.
    /// A blockable node `n` is blocked by ANY earlier node `m` (`m < n`, so no
    /// blocking cycles) whose concept label is a SUPERSET of `n`'s, where `m` is
    /// itself not blocked (a blocked node never blocks). Sound + complete for the
    /// ALC(H) fragment KM_HT routes to (no inverse roles / number / nominals).
    /// The old anywhere path keyed a hash cache on each node's CREATION-time
    /// (incomplete) label, so it never fired and the ∃-chains were never folded:
    /// 9024's model grew to 7559 nodes where HermiT folds it to 27. This forward
    /// pass collapses those models, cutting the branchable disjunction count by
    /// ~100x — the actual reason HermiT's per-test search is tiny.
    fn compute_blocked(&self) -> Vec<bool> {
        let nn = self.ext.num_nodes();
        let mut blocked = vec![false; nn];
        // CORE blocking (mode 0, default): equality on the POSITIVE concepts
        // only — the expansion-driving "core". KM's labels also carry negated
        // literals (¬B from the query / disjunction complements) and definers;
        // those only ever cause clashes (detected at assertion time), they do
        // not drive ∃/∀ expansion, so excluding them from the blocking signature
        // folds the model aggressively (toward HermiT's node count) while staying
        // complete for SH. SUBSET (mode 1) folds most but is incomplete with
        // transitive roles (dropped 1 subsumption on 5303). Full EQ (mode 2)
        // is complete but folds too little to terminate in time.
        let mode = self.block_mode;
        if mode == 0 || mode == 2 {
            // O(n) hashed equality blocking — HermiT's BlockingSignatureCache idea.
            // The equality modes block n by the FIRST earlier unblocked node with
            // an identical signature, so a hash on the signature replaces the
            // O(n²) pairwise scan with one pass (identical result; pure cost fix).
            // mode 2: full label (pos+neg); mode 0 (core): positive concepts only.
            // Signature key packs each literal as (c<<1)|neg, sorted for canonicity.
            let mut seen: HashSet<Vec<u64>> = HashSet::with_capacity(nn);
            for n in 0..nn {
                if !self.ext.blockable[n] {
                    continue;
                }
                let mut sig: Vec<u64> = self.ext.concepts[n]
                    .keys()
                    .filter(|k| mode == 2 || !k.neg)
                    .map(|k| ((k.c as u64) << 1) | (k.neg as u64))
                    .collect();
                sig.sort_unstable();
                // KM_HT_SATCACHE: a signature proven SAT in a prior completed model
                // blocks this node (it reuses that model fragment). Checked before
                // the within-model dedup so cross-test reuse fires even for the
                // first node carrying the signature in this build.
                if self.satcache && self.sat_sigs.contains(&sig) {
                    blocked[n] = true;
                    continue;
                }
                if !seen.insert(sig) {
                    // an earlier unblocked node already carries this signature
                    blocked[n] = true;
                }
            }
        } else if mode == 3 {
            // PAIRWISE (mode 3): HermiT anywhere pairwise blocking. Block n by the
            // FIRST earlier unblocked node with an identical triple
            // (core-label(n), core-label(pred n), roles on the pred→n edge).
            // Unlike full-equality (mode 2) this matches on the CORE plus the
            // parent context, so it folds the disjunction-family models like
            // subset does, while the parent+edge match keeps it complete under
            // transitive roles (the case subset drops) — sound+complete for SH
            // without inverse (guaranteed by ht_routable). Hashed O(n).
            const SEP: u64 = u64::MAX;
            let mut seen: HashSet<Vec<u64>> = HashSet::with_capacity(nn);
            for n in 0..nn {
                if !self.ext.blockable[n] {
                    continue;
                }
                let p = match self.ext.pred[n] {
                    Some(p) => p,
                    None => continue, // root has no parent edge; never blocked
                };
                let mut sig: Vec<u64> = Vec::new();
                let mut a: Vec<u64> = self.ext.concepts[n]
                    .keys()
                    .filter(|k| !k.neg)
                    .map(|k| (k.c as u64) << 1)
                    .collect();
                a.sort_unstable();
                sig.extend(a);
                sig.push(SEP);
                let mut b: Vec<u64> = self.ext.concepts[p]
                    .keys()
                    .filter(|k| !k.neg)
                    .map(|k| (k.c as u64) << 1)
                    .collect();
                b.sort_unstable();
                sig.extend(b);
                sig.push(SEP);
                let mut e: Vec<u64> = self.ext.in_edges[n]
                    .iter()
                    .filter(|(_, s)| *s == p)
                    .map(|(r, _)| *r as u64)
                    .collect();
                e.sort_unstable();
                e.dedup();
                sig.extend(e);
                if !seen.insert(sig) {
                    blocked[n] = true;
                }
            }
        } else if std::env::var_os("KM_HT_BLOCK_SLOW").is_some() {
            // mode 1 (subset), reference O(n²) scan — kept for result-identity
            // validation against the inverted-index fast path below.
            for n in 0..nn {
                if !self.ext.blockable[n] {
                    continue;
                }
                let ln = &self.ext.concepts[n];
                let lnlen = ln.len();
                for m in 0..n {
                    if blocked[m] {
                        continue;
                    }
                    let lm = &self.ext.concepts[m];
                    if lm.len() >= lnlen && ln.keys().all(|k| lm.contains_key(k)) {
                        blocked[n] = true;
                        break;
                    }
                }
            }
        } else {
            // mode 1 (subset), inverted-index fast path. A blockable node `n` is
            // blocked by an earlier UNBLOCKED node `m` whose label is a SUPERSET
            // of n's. `m ⊇ label(n)` iff `m` appears in the posting list of EVERY
            // concept of `n`, so the candidate set is the intersection of those
            // lists — and it cannot be larger than the SHORTEST one. We scan only
            // that rarest-concept list and verify the full superset. Posting lists
            // hold only earlier UNBLOCKED nodes, in id order (a blocked node never
            // blocks; m < n by construction). RESULT-IDENTICAL to the O(n²) scan.
            //
            // The index is a REUSED, concept-id-indexed flat vector (not a fresh
            // per-call HashMap): blocking is recomputed once per propagation pass
            // and was ~73% of the per-test wall, dominated by the per-call map
            // alloc + CLit hashing. The buffer is cleared by touched-slot only.
            let enc = |k: &CLit| -> usize { ((k.c as usize) << 1) | (k.neg as usize) };
            let mut bb = self.block_buf.borrow_mut();
            let BlockBuf { lists, touched } = &mut *bb;
            for &t in touched.iter() {
                lists[t].clear();
            }
            touched.clear();
            for n in 0..nn {
                let ln = &self.ext.concepts[n];
                if self.ext.blockable[n] && !ln.is_empty() {
                    let lnlen = ln.len();
                    // rarest concept of n ⇒ shortest candidate posting list.
                    let mut best: usize = usize::MAX;
                    let mut best_len = usize::MAX;
                    for k in ln.keys() {
                        let e = enc(k);
                        let l = lists.get(e).map_or(0, |v| v.len());
                        if l < best_len {
                            best_len = l;
                            best = e;
                        }
                    }
                    if let Some(cands) = lists.get(best) {
                        for &m in cands {
                            let lm = &self.ext.concepts[m];
                            if lm.len() >= lnlen && ln.keys().all(|k| lm.contains_key(k)) {
                                blocked[n] = true;
                                break;
                            }
                        }
                    }
                }
                if !blocked[n] {
                    for k in self.ext.concepts[n].keys() {
                        let e = enc(k);
                        if e >= lists.len() {
                            lists.resize_with(e + 1, Vec::new);
                        }
                        if lists[e].is_empty() {
                            touched.push(e);
                        }
                        lists[e].push(n);
                    }
                }
            }
        }
        if self.stats && nn > 200 {
            let nb = blocked.iter().filter(|b| **b).count();
            let blk = self.ext.blockable.iter().filter(|b| **b).count();
            eprintln!("KM_HT [blocking] mode={} nodes={} blockable={} blocked={} ({}%)",
                mode, nn, blk, nb, if nn > 0 { nb * 100 / nn } else { 0 });
        }
        blocked
    }

    /// Delta-driven saturation: drain the event queue, firing only the clauses
    /// triggered by each freshly added fact / node.
    fn propagate(&mut self) {
        while let Some(ev) = self.ext.queue.pop() {
            if self.ext.has_clash() {
                return;
            }
            self.heartbeat("prop");
            match ev {
                Event::Concept(n, lit) => {
                    if let Some(trigs) = self.concept_triggers.get(&lit) {
                        for i in 0..trigs.len() {
                            let (cid, pos) = trigs[i];
                            fire_anchor_concept(&self.clauses, &mut self.ext, cid, pos, n);
                            if self.ext.has_clash() {
                                return;
                            }
                        }
                    }
                    if self.learn {
                        self.learned_bcp(n, lit);
                    }
                }
                Event::Edge(r, s, t) => {
                    if let Some(trigs) = self.role_triggers.get(&r) {
                        for i in 0..trigs.len() {
                            let (cid, pos) = trigs[i];
                            fire_anchor_edge(&self.clauses, &mut self.ext, cid, pos, s, t);
                            if self.ext.has_clash() {
                                return;
                            }
                        }
                    }
                }
                Event::NodeNew(n) => {
                    for i in 0..self.global_clauses.len() {
                        let cid = self.global_clauses[i];
                        // eager: defer the ⊤-disjunctions; they are fired in
                        // `process_obligations` only on confirmed-unblocked nodes.
                        // The Horn globals still fire (they build the label that
                        // blocking and the deferred check depend on).
                        if self.eager && self.global_disj_set.contains(&cid) {
                            continue;
                        }
                        fire_global(&self.clauses, &mut self.ext, cid, n);
                        if self.ext.has_clash() {
                            return;
                        }
                    }
                }
            }
        }
    }

    /// Re-evaluate the recorded ground disjunctions (delta worklist, not a full
    /// clause scan): unit-propagate any whose live set collapsed to one, raise a
    /// clash on an empty live set, and return the first genuine >=2-way branch.
    /// Satisfied entries are skipped (kept, so backtracking can revive them).
    fn next_action_from_pending(&mut self) -> Scan {
        // KM_HT_BLOCKSKIP: refresh the blocked snapshot once for this branch
        // selection (no-op unless blockskip is on), then skip any disjunction all
        // of whose nodes are blocked.
        self.refresh_blocked();
        let mut branch: Option<GD> = None;
        let np = self.ext.pending.len();
        for i in 0..np {
            self.heartbeat("scan");
            if disj_all_blocked(&self.ext, i) {
                continue;
            }
            let m = self.ext.pending[i].disjuncts.len();
            let bdep = self.ext.pending[i].bdep.clone();
            let mut satisfied = false;
            let mut dead_dep = dep_empty();
            let mut live: Vec<GroundDisjunct> = Vec::new();
            for j in 0..m {
                let (n, lit) = self.ext.pending[i].disjuncts[j];
                if self.ext.has_concept(n, lit) {
                    satisfied = true;
                    break;
                }
                let comp = CLit { neg: !lit.neg, c: lit.c };
                if let Some(d) = self.ext.dep_of(n, comp) {
                    dead_dep = dep_union(&dead_dep, d);
                } else {
                    live.push(GroundDisjunct { node: n, lit });
                }
            }
            if satisfied {
                continue;
            }
            if live.is_empty() {
                self.ext.raise_clash(dep_union(&bdep, &dead_dep));
                return Scan::Clash;
            }
            if live.len() == 1 {
                let d = dep_union(&bdep, &dead_dep);
                if self.ext.add_concept(live[0].node, live[0].lit, &d) {
                    return Scan::Unit;
                }
            } else {
                // pick which pending disjunction to branch on (KM_HT_PICK).
                let take = match (&branch, self.pick_mode) {
                    (None, _) => true,
                    (Some(_), 0) => false, // baseline: first >=2-way branch
                    (Some(b), 1) => live.len() < b.disjuncts.len(), // most-constrained
                    (Some(b), 2) => {
                        // highest total clash activity (fail-fast on the hot one)
                        let s: u64 = live.iter().map(|d| self.act_of(d.lit.c)).sum();
                        let bs: u64 = b.disjuncts.iter().map(|d| self.act_of(d.lit.c)).sum();
                        s > bs
                    }
                    _ => false,
                };
                if take {
                    branch = Some(GD { disjuncts: live, dep: dep_union(&bdep, &dead_dep) });
                }
            }
        }
        match branch {
            Some(gd) => Scan::Branch(gd),
            None => Scan::Sat,
        }
    }

    /// Incremental disjunction handling (KM_HT_WATCH): only re-evaluate
    /// disjunctions touched by recent assertions/retractions (the `dirty` set),
    /// not all pending every step. Forced moves (clash/unit) returned eagerly;
    /// >=2-live disjunctions accumulate in `open`, from which a branch is chosen
    /// once the dirty set drains. Output is identical to the full scan (a unit is
    /// a unit regardless of visit order); only the cost changes (O(changes) vs
    /// O(pending) per step).
    fn next_action_incremental(&mut self) -> Scan {
        while let Some(id) = self.ext.dirty.pop() {
            if id >= self.ext.pending.len() {
                continue;
            }
            self.ext.dirty_in[id] = false;
            self.heartbeat("scan");
            match eval_disj(&self.ext, id) {
                DEval::Satisfied => {}
                DEval::Clash(dep) => {
                    self.ext.raise_clash(dep);
                    return Scan::Clash;
                }
                DEval::Unit(n, lit, dep) => {
                    if self.ext.add_concept(n, lit, &dep) {
                        return Scan::Unit;
                    }
                }
                DEval::Branch(_, _) => {
                    if !self.ext.open_in[id] {
                        self.ext.open_in[id] = true;
                        self.ext.open.push(id);
                    }
                }
            }
        }
        // fixpoint: choose a branch from the open candidates (re-evaluate to skip
        // entries that became satisfied / unit since being queued).
        while let Some(id) = self.ext.open.pop() {
            if id >= self.ext.pending.len() {
                continue;
            }
            self.ext.open_in[id] = false;
            match eval_disj(&self.ext, id) {
                DEval::Branch(live, dep) => return Scan::Branch(GD { disjuncts: live, dep }),
                DEval::Clash(dep) => {
                    self.ext.raise_clash(dep);
                    return Scan::Clash;
                }
                DEval::Unit(n, lit, dep) => {
                    if self.ext.add_concept(n, lit, &dep) {
                        return Scan::Unit;
                    }
                }
                DEval::Satisfied => {}
            }
        }
        Scan::Sat
    }

    /// Expand recorded ∃-obligations (delta worklist) on non-blocked nodes.
    /// Returns true if a successor was created (progress ⇒ re-propagate).
    fn process_obligations(&mut self) -> bool {
        let mut made = false;
        // Batch-compute blocking once per pass (cheap once the model is folded;
        // anywhere-subset for the default ALC(H) route, ancestor-only otherwise).
        let _bt0 = Instant::now();
        let blocked = if self.anywhere { Some(self.compute_blocked()) } else { None };
        self.block_us += _bt0.elapsed().as_micros();
        // EAGER (KM_HT_EAGER): fire the deferred global ⊤-disjunctions, but only on
        // nodes that are NOT blocked. A blocked node's ⊤-disjunctions are covered
        // by its blocker (anywhere blocking, ALC(H) no-inverse), so they never
        // need their own branch points — this is what keeps HermiT's model (and
        // its branch count) tiny. Because disjunct choices are not yet in the
        // label at this point, blocking compares Horn-only labels and folds more.
        if self.eager && !self.global_disj.is_empty() {
            let nn = self.ext.num_nodes();
            for n in 0..nn {
                if self.ext.globals_fired[n] {
                    continue;
                }
                let is_blk = match &blocked {
                    Some(b) => b[n],
                    None => ancestor_blocked(&self.ext, n),
                };
                if is_blk {
                    continue; // blocked: blocker covers its ⊤-disjunctions
                }
                self.ext.globals_fired[n] = true;
                self.ext.trail.push(Trail::GlobalsFired(n));
                for i in 0..self.global_disj.len() {
                    let cid = self.global_disj[i];
                    fire_global(&self.clauses, &mut self.ext, cid, n);
                }
                made = true;
                if self.ext.has_clash() {
                    return made;
                }
            }
        }
        let no = self.ext.obligations.len();
        for i in 0..no {
            let (n, r, fil, dep) = {
                let o = &self.ext.obligations[i];
                (o.n, o.r, o.fil, o.dep.clone())
            };
            let is_blk = match &blocked {
                Some(b) => b[n],
                None => ancestor_blocked(&self.ext, n),
            };
            if is_blk || has_rsucc(&self.ext, n, r, fil) {
                continue;
            }
            self.heartbeat("exp");
            let t = self.ext.new_node(Some(n));
            self.ext.add_edge(r, n, t, &dep);
            self.ext.add_concept(t, fil, &dep);
            made = true;
        }
        made
    }

    /// Wrap a base clash into an `Out`: count it and, if the restart budget is
    /// exhausted, signal a restart instead of the conflict (the activity learned
    /// so far survives and reorders the next run).
    #[inline]
    fn conflict_out(&mut self, cd: DepSet) -> Out {
        self.conflicts += 1;
        // KM_HT_DEPSTATS: sample the conflict-set size vs the search depth. If
        // card(cd) ≪ cur_depth, the path holds many levels irrelevant to this
        // clash ⇒ precise dependency-directed backjumping could skip them (big
        // win). If dep_max(cd) ≈ cur_depth and card(cd) is large, the deps are
        // already tight and the search is genuinely deep (precision won't help).
        if self.stats && std::env::var_os("KM_HT_DEPSTATS").is_some() && self.conflicts % 2000 == 0 {
            // dump the conflict's decision levels + their nodes: are the ~6 culprit
            // decisions at low/stable nodes (node-keyed learning suffices once
            // staleness is fixed) or scattered across recreated deep nodes
            // (label-keyed learning required)? Also the level spread vs depth.
            let mut lv: Vec<(Level, Node)> = Vec::new();
            let mut cur = &cd;
            while let Some(n) = cur {
                let l = n.level as usize;
                let nd = if l < self.decisions.len() { self.decisions[l].0 } else { usize::MAX };
                lv.push((n.level, nd));
                cur = &n.rest;
            }
            eprintln!(
                "KM_HT [depstats] conflicts={} cur_depth={} dep_max={} dep_card={} levels_nodes={:?}",
                self.conflicts, self.cur_depth, dep_max(&cd), dep_card(&cd), lv
            );
        }
        if self.learn {
            self.learn_clause(&cd);
        }
        if self.lblng {
            self.lng_learn(&cd);
        }
        if self.do_restart && self.conflicts >= self.restart_limit {
            return Out::Restart;
        }
        Out::Conflict(cd)
    }

    /// Core-label signature of `n`: a hash of its sorted POSITIVE concepts. Two
    /// structurally-identical nodes (same expansion-driving core) share a sig even
    /// when their node ids differ, so a conflict learned against one recurs against
    /// the other (KM_HT_LBLCACHE).
    fn core_sig(&self, n: Node) -> u64 {
        let mut v: Vec<C> = self
            .ext
            .concepts
            .get(n)
            .map(|m| m.keys().filter(|k| !k.neg).map(|k| k.c).collect())
            .unwrap_or_default();
        v.sort_unstable();
        let mut h: u64 = 0xcbf29ce484222325; // FNV-1a
        for c in v {
            for b in (c as u64).to_le_bytes() {
                h ^= b as u64;
                h = h.wrapping_mul(0x100000001b3);
            }
        }
        h
    }

    /// Remove the choice recorded at `level` from the active assignment.
    fn unrecord_choice(&mut self, level: Level) {
        let l = level as usize;
        if l < self.dec_choice.len() {
            if let Some(key) = self.dec_choice[l].take() {
                if self.cur_choices.get(&key) == Some(&level) {
                    self.cur_choices.remove(&key);
                }
            }
        }
    }

    /// After asserting the choice (sig, lit) at `level`, check whether any learned
    /// no-good is now fully active. Returns the conflict dep (the levels of the
    /// matched choices) if so — the branch is doomed without recursing.
    fn lng_fired(&mut self, sig: u64, lit: CLit) -> Option<DepSet> {
        let ids = self.lng_watch.get(&(sig, lit))?.clone();
        for cid in ids {
            let ng = &self.lng[cid];
            if ng.iter().all(|k| self.cur_choices.contains_key(k)) {
                let mut dep = dep_empty();
                for k in ng {
                    if let Some(&lv) = self.cur_choices.get(k) {
                        dep = dep_add(&dep, lv);
                    }
                }
                self.lng_fires += 1;
                return Some(dep);
            }
        }
        None
    }

    /// Learn a signature-keyed no-good from a clash dep: the set of (sig, concept)
    /// choices at the responsible decision levels. Recorded + watched by each
    /// element so it can fire when the same choices recur at structurally-identical
    /// nodes (different ids).
    fn lng_learn(&mut self, cd: &DepSet) {
        let mut ng: Vec<(u64, CLit)> = Vec::new();
        let mut cur = cd;
        while let Some(node) = cur {
            let l = node.level as usize;
            if l < self.dec_sig.len() && l < self.decisions.len() {
                let sig = self.dec_sig[l];
                let lit = self.decisions[l].2;
                if sig != 0 || self.decisions[l].1 != 0 {
                    ng.push((sig, lit));
                }
            }
            cur = &node.rest;
        }
        ng.sort_unstable_by_key(|&(s, l)| (s, l.c, l.neg as u8));
        ng.dedup();
        if ng.len() < 2 || ng.len() > 24 {
            return;
        }
        if self.lng.len() >= 300_000 {
            return;
        }
        let cid = self.lng.len();
        for &k in &ng {
            self.lng_watch.entry(k).or_default().push(cid);
        }
        self.lng.push(ng);
    }

    #[inline]
    fn record_decision(&mut self, level: Level, n: Node, lit: CLit) {
        let l = level as usize;
        if self.decisions.len() <= l {
            self.decisions.resize(l + 1, (0, 0, CLit { neg: false, c: 0 }));
        }
        self.decisions[l] = (n, self.ext.node_uid(n), lit);
        if self.lblng {
            if self.dec_sig.len() <= l {
                self.dec_sig.resize(l + 1, 0);
                self.dec_choice.resize(l + 1, None);
            }
            // drop any stale choice previously recorded at this level (sibling
            // disjunct retried) before installing the new one.
            self.unrecord_choice(level);
            let sig = self.core_sig(n);
            self.dec_sig[l] = sig;
            let key = (sig, lit);
            self.dec_choice[l] = Some(key);
            self.cur_choices.insert(key, level);
        }
    }

    /// Turn a clash dep-set (the set of decision levels responsible) into a
    /// learned no-good over the corresponding decision literals, with two watched
    /// literals registered. Sound: the conjunction of those decisions provably
    /// clashes, so the disjunction of their complements is entailed.
    fn learn_clause(&mut self, cd: &DepSet) {
        let mut lits: Vec<(Node, u64, CLit)> = Vec::new();
        let mut cur = cd;
        while let Some(node) = cur {
            let l = node.level as usize;
            if l < self.decisions.len() {
                let (n, u, lit) = self.decisions[l];
                // skip the default placeholder for levels with no recorded decision
                if u != 0 {
                    lits.push((n, u, lit));
                }
            }
            cur = &node.rest;
        }
        lits.sort_unstable_by_key(|&(n, u, l)| (n, u, l.c, l.neg as u8));
        lits.dedup();
        if lits.len() < 2 {
            return; // 0/1-literal no-goods aren't useful here (handled by depsets)
        }
        // cheap cap to bound memory / watch churn
        if self.learned.len() >= 200_000 {
            return;
        }
        let cid = self.learned.len();
        let k0 = (lits[0].0, lits[0].2);
        let k1 = (lits[1].0, lits[1].2);
        self.lwatch.entry(k0).or_default().push(cid);
        self.lwatch.entry(k1).or_default().push(cid);
        self.learned.push(LClause { lits, w0: 0, w1: 1 });
    }

    /// Learned-clause BCP: the decision literal `(n, lit)` was just asserted;
    /// re-examine learned clauses watching it (lazy two-watched-literals).
    fn learned_bcp(&mut self, n: Node, lit: CLit) {
        let ids = match self.lwatch.get(&(n, lit)) {
            Some(v) => v.clone(),
            None => return,
        };
        for cid in ids {
            if self.ext.has_clash() {
                return;
            }
            self.maintain_learned(cid, n, lit);
        }
    }

    /// `(n, lit)` (a watched literal of clause `cid`) just became asserted. Try to
    /// rewatch a non-asserted literal; if none, the clause is unit (force the
    /// other watch's complement) or violated (clash). Dormant if any literal's
    /// node is stale.
    fn maintain_learned(&mut self, cid: usize, n: Node, lit: CLit) {
        // identify which watch fired and the other watch.
        let (w_hit, w_other) = {
            let lc = &self.learned[cid];
            let (h0n, _, h0l) = lc.lits[lc.w0];
            if h0n == n && h0l == lit {
                (lc.w0, lc.w1)
            } else {
                (lc.w1, lc.w0)
            }
        };
        let nlits = self.learned[cid].lits.len();
        // dormant: any literal on a stale node ⇒ clause can never fire validly.
        // KM_HT_LEARN_NOSTALE (diagnostic, UNSOUND): relax to a range check only
        // (ignore uid), so a no-good fires when the node IDs are reused even by a
        // different individual — measures the would-be backtrack saving of
        // cross-recreation no-good transfer.
        for i in 0..nlits {
            let (ln, lu, _) = self.learned[cid].lits[i];
            let ok = if self.learn_nostale {
                ln < self.ext.concepts.len()
            } else {
                self.ext.node_valid(ln, lu)
            };
            if !ok {
                return;
            }
        }
        // asserted? = node valid (checked) and concept present.
        let asserted = |ext: &Ext, t: (Node, u64, CLit)| ext.has_concept(t.0, t.2);
        // try to find a replacement watch: a literal != w_other that is NOT asserted.
        for i in 0..nlits {
            if i == w_other || i == w_hit {
                continue;
            }
            let t = self.learned[cid].lits[i];
            if !asserted(&self.ext, t) {
                // move the hit watch to i; update lwatch index.
                let old_key = (n, lit);
                let new_key = (t.0, t.2);
                if let Some(v) = self.lwatch.get_mut(&old_key) {
                    if let Some(p) = v.iter().position(|&x| x == cid) {
                        v.swap_remove(p);
                    }
                }
                self.lwatch.entry(new_key).or_default().push(cid);
                if self.learned[cid].w0 == w_hit {
                    self.learned[cid].w0 = i;
                } else {
                    self.learned[cid].w1 = i;
                }
                return;
            }
        }
        // no replacement: clause is unit on w_other, or fully violated.
        let other = self.learned[cid].lits[w_other];
        let dep = self.learned_reason(cid, Some(w_other));
        if asserted(&self.ext, other) {
            // every decision literal holds ⇒ violated ⇒ clash.
            self.ext.raise_clash(dep);
        } else {
            // force the complement of the last free decision literal.
            let comp = CLit { neg: !other.2.neg, c: other.2.c };
            self.ext.add_concept(other.0, comp, &dep);
        }
    }

    /// Dep-set reason = union of the deps of the asserted decision literals (all
    /// of them, or all but `skip` for a unit derivation).
    fn learned_reason(&self, cid: usize, skip: Option<usize>) -> DepSet {
        let mut dep = dep_empty();
        let lc = &self.learned[cid];
        for (i, &(ln, _, ll)) in lc.lits.iter().enumerate() {
            if Some(i) == skip {
                continue;
            }
            if let Some(d) = self.ext.dep_of(ln, ll) {
                dep = dep_union(&dep, d);
            }
        }
        dep
    }

    fn dfs(&mut self, depth: Level) -> Out {
        loop {
            self.steps += 1;
            self.cur_depth = depth;
            self.heartbeat("dfs");
            if self.trace {
                eprintln!("TR dfs depth={} step={} pending={}", depth, self.steps, self.ext.pending.len());
            }
            self.propagate();
            if self.ext.has_clash() {
                if self.trace { eprintln!("TR prop-clash depth={}", depth); }
                return self.conflict_out(self.ext.clash_dep());
            }
            if self.process_obligations() {
                if self.trace { eprintln!("TR oblig-made depth={}", depth); }
                continue;
            }
            let action = if self.watch {
                self.next_action_incremental()
            } else {
                self.next_action_from_pending()
            };
            match action {
                Scan::Clash => {
                    if self.trace { eprintln!("TR scan-clash depth={}", depth); }
                    return self.conflict_out(self.ext.clash_dep());
                }
                Scan::Unit => {
                    if self.trace { eprintln!("TR scan-unit depth={}", depth); }
                    continue;
                }
                Scan::Sat => {
                    if self.trace { eprintln!("TR scan-sat depth={}", depth); }
                    return Out::Sat;
                }
                Scan::Branch(mut gd) => {
                    // KM_HT_SATFOLD: before branching, try to complete the live
                    // disjuncts' nodes from a cached clash-free model label. A
                    // completed node has all its disjunctions satisfied, so the
                    // branch is avoided — re-propagate and re-scan.
                    if self.satfold {
                        let mut nodes: Vec<Node> = gd.disjuncts.iter().map(|d| d.node).collect();
                        nodes.sort_unstable();
                        nodes.dedup();
                        let mut folded = false;
                        for nd in nodes {
                            if self.try_satfold(nd) {
                                folded = true;
                                if self.ext.has_clash() {
                                    break;
                                }
                            }
                        }
                        if folded {
                            continue;
                        }
                    }
                    let level = depth + 1;
                    if self.trace {
                        eprintln!("TR branch depth={} level={} ndisj={}", depth, level, gd.disjuncts.len());
                    }
                    self.order_disjuncts(&mut gd.disjuncts);
                    self.branch_pushes += 1;
                    let mut fail = dep_empty();
                    for (di, d) in gd.disjuncts.iter().enumerate() {
                        self.disjunct_tries += 1;
                        let mark = self.ext.mark();
                        let dep = dep_add(&gd.dep, level);
                        if self.trace {
                            eprintln!("TR try di={} node={} c={} neg={} mark={}", di, d.node, d.lit.c, d.lit.neg, mark);
                        }
                        if self.learn || self.lblng {
                            self.record_decision(level, d.node, d.lit);
                        }
                        self.ext.add_concept(d.node, d.lit, &dep);
                        // KM_HT_LBLCACHE: if this choice completes a learned
                        // signature-keyed no-good, the branch is doomed — treat it
                        // as an immediate conflict (with the no-good's level dep)
                        // instead of recursing into the same dead subtree.
                        let sub = if self.lblng && !self.ext.has_clash() {
                            let key = self.dec_choice.get(level as usize).and_then(|x| *x);
                            match key.and_then(|(s, l)| self.lng_fired(s, l)) {
                                Some(ngdep) => Out::Conflict(ngdep),
                                None => self.dfs(level),
                            }
                        } else {
                            self.dfs(level)
                        };
                        match sub {
                            Out::Sat => return Out::Sat,
                            Out::Restart => {
                                self.ext.backtrack_to(mark);
                                if self.lblng { self.unrecord_choice(level); }
                                return Out::Restart;
                            }
                            Out::Conflict(cd) => {
                                self.backtracks += 1;
                                // VSIDS-style: blame the disjunct we just tried.
                                if self.ord_mode != 0 || self.pick_mode == 2 {
                                    *self.activity.entry(d.lit.c).or_insert(0) += 1;
                                }
                                if self.trace {
                                    eprintln!("TR conflict di={} depth={} cd_max={} contains_level={}", di, depth, dep_max(&cd), dep_contains(&cd, level));
                                }
                                self.ext.backtrack_to(mark);
                                if !dep_contains(&cd, level) {
                                    self.backjumps += 1;
                                    if self.lblng { self.unrecord_choice(level); }
                                    return Out::Conflict(cd);
                                }
                                fail = dep_union(&fail, &cd);
                                // HermiT startNextChoice: D_di clashed under the other
                                // choices in cd, so ¬D_di holds under those choices.
                                // Assert it (dep = cd minus this branch level) so the
                                // remaining disjuncts unit-propagate against it instead
                                // of re-expanding the same subtree. The fact lands after
                                // `mark`, so it persists across the next iterations and
                                // is cleaned up when the caller backtracks past this
                                // disjunction. Sound: cd∖{level} ⊨ ¬D_di.
                                if self.negtried && di + 1 < gd.disjuncts.len() {
                                    let ndep = dep_remove(&cd, level);
                                    let comp = CLit { neg: !d.lit.neg, c: d.lit.c };
                                    self.negfired += 1;
                                    self.ext.add_concept(d.node, comp, &ndep);
                                    if self.ext.has_clash() {
                                        // ¬D_di immediately clashes ⇒ the disjunction is
                                        // unsat under the current outer choices.
                                        let cd2 = self.ext.clash_dep();
                                        self.ext.backtrack_to(mark);
                                        if self.lblng { self.unrecord_choice(level); }
                                        if !dep_contains(&cd2, level) {
                                            return Out::Conflict(cd2);
                                        }
                                        return Out::Conflict(dep_remove(&dep_union(&fail, &cd2), level));
                                    }
                                }
                            }
                        }
                    }
                    if self.trace { eprintln!("TR branch-exhausted depth={}", depth); }
                    if self.lblng { self.unrecord_choice(level); }
                    return Out::Conflict(dep_remove(&fail, level));
                }
            }
        }
    }

    pub fn consistent(&mut self, seed: &[CLit]) -> Option<bool> {
        // (Re)set the restart budget for this query; activity carries over from
        // prior queries (warm heuristic) and across restarts within this one.
        self.luby_idx = 1;
        self.restart_limit = if self.do_restart {
            self.conflicts + self.rbase
        } else {
            u64::MAX
        };
        // KM_HT_LBLCACHE: signature-keyed no-goods are independent of node ids /
        // Ext lifetime, so they accumulate across restarts within this query (CDCL).
        // Reset per query for soundness simplicity (a conflict is re-learnable).
        if self.lblng {
            self.lng.clear();
            self.lng_watch.clear();
            self.lng_fires = 0;
        }
        loop {
            self.ext = Ext::new();
            self.ext.watch = self.watch;
            self.cache.clear();
            // learned no-goods reference this run's node uids; reset per run.
            self.decisions.clear();
            self.learned.clear();
            self.lwatch.clear();
            // sig-keyed assignment state references this run's levels; reset it,
            // but keep `lng` (the learned no-goods) across restarts.
            self.cur_choices.clear();
            self.dec_sig.clear();
            self.dec_choice.clear();
            let root = self.ext.new_root();
            for &lit in seed {
                self.ext.add_concept(root, lit, &dep_empty());
            }
            match self.dfs(0) {
                Out::Restart => {
                    self.restarts += 1;
                    self.luby_idx += 1;
                    self.restart_limit = self.conflicts + self.rbase * luby(self.luby_idx);
                    // loop: re-run with preserved activity + grown budget.
                }
                other => {
                    if self.ext.unsupported {
                        return None;
                    }
                    let sat = matches!(other, Out::Sat);
                    // KM_HT_SATCACHE: pool the (core) signatures of this completed
                    // clash-free model's foldable nodes. Their satisfiability is
                    // label-determined (ALC(H) no-inverse), so they prune matching
                    // nodes in every later per-query rebuild. Only `blockable`
                    // nodes (the ∃-successors that blocking consults) are pooled;
                    // the root carries the query-specific seed and is never blocked.
                    if sat && self.satcache {
                        let full = self.block_mode == 2;
                        let nn = self.ext.num_nodes();
                        for n in 0..nn {
                            if !self.ext.blockable[n] {
                                continue;
                            }
                            let mut sig: Vec<u64> = self.ext.concepts[n]
                                .keys()
                                .filter(|k| full || !k.neg)
                                .map(|k| ((k.c as u64) << 1) | (k.neg as u64))
                                .collect();
                            sig.sort_unstable();
                            self.sat_sigs.insert(sig);
                        }
                    }
                    // KM_HT_PHASE: save the disjunct polarities of this model — every
                    // positive concept present was a satisfiable choice, so prefer it
                    // (true) next time; concepts seen nowhere stay default false.
                    if sat && self.phase_save {
                        let nn = self.ext.num_nodes();
                        for n in 0..nn {
                            for k in self.ext.concepts[n].keys() {
                                if !k.neg {
                                    self.phase.insert(k.c, true);
                                }
                            }
                        }
                    }
                    // KM_HT_SATFOLD: record the POSITIVE cores of this clash-free
                    // model's UNBLOCKED (fully-saturated, genuine-individual) nodes.
                    // Positive concepts are ENTAILED (query-independent), so a core
                    // is reusable across tests; negative literals (query ¬B,
                    // disjunction complements) are query-specific and excluded.
                    // `try_satfold` completes a node to such a core only when the
                    // core respects the node's own negatives, so injecting it is a
                    // sound model extension.
                    if sat && self.satfold {
                        let nn = self.ext.num_nodes();
                        let blocked = if self.anywhere { self.compute_blocked() } else { vec![false; nn] };
                        for n in 0..nn {
                            if blocked[n] {
                                continue;
                            }
                            let mut lab: Vec<CLit> = self.ext.concepts[n]
                                .keys()
                                .filter(|k| !k.neg)
                                .copied()
                                .collect();
                            if lab.len() < 2 || lab.len() > 80 {
                                continue;
                            }
                            lab.sort_unstable();
                            if self.sat_labels.len() >= 200_000 {
                                break;
                            }
                            let cid = self.sat_labels.len();
                            for &l in &lab {
                                self.satfold_watch.entry(l).or_default().push(cid);
                            }
                            self.sat_labels.push(lab);
                        }
                    }
                    return Some(sat);
                }
            }
        }
    }

    /// KM_HT_SATFOLD: if node `n`'s current label is a STRICT subset of a memoed
    /// clash-free model label `L`, complete `n` to `L` (assert the missing
    /// concepts) so its disjunctions are satisfied without branching. Sound for
    /// ALC(H) no-inverse: `n`'s satisfiability is label-determined and `L` is a
    /// clash-free completion whose successors are witnessed by the model `L` came
    /// from, so the completion never fails. Returns true if it completed `n`.
    fn try_satfold(&mut self, n: Node) -> bool {
        // positive core of n + the set of concepts n forbids (its negatives).
        let mut s: Vec<CLit> = Vec::new();
        let mut neg: HashSet<C> = HashSet::new();
        let mut dep = dep_empty();
        for (k, d) in &self.ext.concepts[n] {
            if k.neg {
                neg.insert(k.c);
            } else {
                s.push(*k);
                dep = dep_union(&dep, d);
            }
        }
        if s.is_empty() {
            return false;
        }
        s.sort_unstable();
        let key = s[0];
        let ids = match self.satfold_watch.get(&key) {
            Some(v) => v.clone(),
            None => return false,
        };
        for cid in ids {
            let l = &self.sat_labels[cid];
            if l.len() <= s.len() {
                continue;
            }
            // s ⊆ l (both sorted positive cores; merge-style subset check)
            let mut it = l.iter();
            let subset = s.iter().all(|x| it.by_ref().any(|y| y == x));
            if !subset {
                continue;
            }
            // the cached core must RESPECT n's negatives: no concept it would add
            // may be one n forbids (else the completion contradicts a ¬c at n and
            // the clash would be spurious — unsound). Skip such labels.
            if self.sat_labels[cid].iter().any(|x| neg.contains(&x.c)) {
                continue;
            }
            let missing: Vec<CLit> = self.sat_labels[cid]
                .iter()
                .copied()
                .filter(|x| !self.ext.concepts[n].contains_key(x))
                .collect();
            for lit in missing {
                self.ext.add_concept(n, lit, &dep);
                if self.ext.has_clash() {
                    return true; // genuine clash from saturating the core; dfs handles it
                }
            }
            self.satfold_hits += 1;
            return true;
        }
        false
    }

    /// Positive named concepts true at the root individual of the model left in
    /// `self.ext` by the most recent satisfiable `consistent` call. Used for
    /// model-based subsumer pruning.
    /// KM_HT_DUMPLABELS diagnostic: characterise the current model's node labels
    /// (positive concepts) to see why equality blocking does/doesn't fold it.
    fn dump_labels(&self) {
        let nn = self.ext.num_nodes();
        let mut sigs: Vec<Vec<C>> = Vec::with_capacity(nn);
        for n in 0..nn {
            let mut s: Vec<C> = self.ext.concepts[n].keys().filter(|k| !k.neg).map(|k| k.c).collect();
            s.sort_unstable();
            sigs.push(s);
        }
        let mut sizes: Vec<usize> = sigs.iter().map(|s| s.len()).collect();
        sizes.sort_unstable();
        let distinct: HashSet<&Vec<C>> = sigs.iter().collect();
        let blocked = if self.anywhere { self.compute_blocked() } else { vec![false; nn] };
        let nblk = blocked.iter().filter(|b| **b).count();
        let med = if sizes.is_empty() { 0 } else { sizes[sizes.len() / 2] };
        eprintln!(
            "KM_HT [dumplabels] nodes={} distinct_pos_labels={} blocked={} label_size(min/med/max)={}/{}/{}",
            nn, distinct.len(), nblk,
            sizes.first().copied().unwrap_or(0), med, sizes.last().copied().unwrap_or(0)
        );
        // UNBLOCKED nodes drive branching: how many DISTINCT labels among them,
        // and are they pairwise-incomparable (no subset relation ⇒ subset blocking
        // cannot fold them; the diversity comes from exclusive-disjunct choices)?
        let mut ublabels: Vec<&Vec<C>> = (0..nn).filter(|&n| !blocked[n]).map(|n| &sigs[n]).collect();
        ublabels.sort();
        ublabels.dedup();
        let ub_distinct = ublabels.len();
        let mut incomp = 0usize;
        let mut comp = 0usize;
        for i in 0..ublabels.len().min(60) {
            for j in (i + 1)..ublabels.len().min(60) {
                let (a, b) = (ublabels[i], ublabels[j]);
                let sub_ab = a.iter().all(|x| b.contains(x));
                let sub_ba = b.iter().all(|x| a.contains(x));
                if sub_ab || sub_ba { comp += 1; } else { incomp += 1; }
            }
        }
        eprintln!("KM_HT [dumplabels] unblocked_distinct={} pairs(comparable/incomparable)={}/{}",
            ub_distinct, comp, incomp);
        // smallest 8 unblocked labels (raw concept ids) to eyeball what differs.
        let mut by_size: Vec<&Vec<C>> = ublabels.clone();
        by_size.sort_by_key(|s| s.len());
        for s in by_size.iter().take(8) {
            eprintln!("KM_HT [dumplabels]   ub|{}| {:?}", s.len(), s);
        }
    }

    fn root_pos_label(&self) -> Vec<C> {
        self.node_pos_label(0)
    }

    /// Positive named concepts true at `n` in the current model.
    fn node_pos_label(&self, n: Node) -> Vec<C> {
        self.ext
            .concepts
            .get(n)
            .map(|m| m.keys().filter(|k| !k.neg).map(|k| k.c).collect())
            .unwrap_or_default()
    }

    /// All nodes reachable from `root` via role edges (BFS), `root` included.
    fn subtree_nodes(&self, root: Node) -> HashSet<Node> {
        let mut seen = HashSet::new();
        let mut stack = vec![root];
        seen.insert(root);
        while let Some(n) = stack.pop() {
            if let Some(out) = self.ext.out_edges.get(n) {
                for &(_, t, _) in out {
                    if seen.insert(t) {
                        stack.push(t);
                    }
                }
            }
        }
        seen
    }

    /// A pending disjunction is "open" iff it is not satisfied and has >=2 live
    /// disjuncts (i.e. it was parked during non-branching saturation). `root` is
    /// sufficient iff no open disjunction has a disjunct-node inside its subtree:
    /// then the parked model is already a complete clash-free model of `root`'s
    /// seed concept and no real tableau SAT test is needed (Konclude's
    /// "sufficient" node — the ~95% case).
    fn subtree_sufficient(&self, root: Node) -> bool {
        let sub = self.subtree_nodes(root);
        for pd in &self.ext.pending {
            let mut satisfied = false;
            let mut live = 0usize;
            let mut in_sub = false;
            for &(n, lit) in &pd.disjuncts {
                if sub.contains(&n) {
                    in_sub = true;
                }
                if self.ext.has_concept(n, lit) {
                    satisfied = true;
                    break;
                }
                let comp = CLit { neg: !lit.neg, c: lit.c };
                if self.ext.dep_of(n, comp).is_none() {
                    live += 1;
                }
            }
            if satisfied {
                continue;
            }
            if in_sub && live >= 2 {
                return false;
            }
        }
        true
    }

    pub fn classify(&mut self, queries: &[C]) -> Option<(bool, Vec<C>, Vec<(C, C)>)> {
        let global = self.consistent(&[])?;
        if !global {
            return Some((false, queries.to_vec(), Vec::new()));
        }
        if std::env::var_os("KM_HT_GLOBAL").is_some() {
            if self.trace { eprintln!("TR classify-return (global, consistent)"); }
            return Some((true, Vec::new(), Vec::new()));
        }
        // KM_HT_PAR=N (N>1): run the 94 per-concept SAT tests (Phase 1) and the
        // per-concept subsumption confirmations (Phase 2) across N OS threads. The
        // tests are independent (each `consistent` call builds its own `Ext`), and
        // the result is set-identical to the sequential run: a true subsumer of A
        // is in EVERY A-model's root label (so no candidate is lost regardless of
        // which model a worker finds), and Phase 2 only commits confirmed pairs.
        // No Lean re-cert: this is a scheduling change over the same exhaustive
        // per-test search (fixpoint-preserving). The default path (N=1) is
        // untouched. The cross-query heuristic caches (witreuse/satcache/satfold/
        // phase/lblcache) are per-worker, so they are inert under parallelism;
        // they are experimental and off in production.
        let par = std::env::var("KM_HT_PAR").ok().and_then(|s| s.parse::<usize>().ok()).unwrap_or(1);
        if par > 1 && !self.naive {
            return self.classify_parallel(queries, par);
        }
        let qset: HashSet<C> = queries.iter().copied().collect();
        let naive = self.naive;

        // Phase 1: per-concept satisfiability + capture the root label of one
        // model (the model-based subsumer candidate set). A true subsumer B of A
        // is in EVERY A-model's root label, so it is never pruned (complete);
        // the Phase-2 check keeps it sound. Output is identical to the naive n².
        let mut unsat = Vec::new();
        let mut sat_q = Vec::new();
        let mut labels: Vec<(C, Vec<C>)> = Vec::new();
        // KM_HT_WITREUSE: pseudo-model witness reuse across the per-concept queries.
        // In a COMPLETE clash-free model, any node carrying concept C already
        // carries every subsumer of C (C ⊑ B ⇒ every C-individual is a B-individual
        // ⇒ B holds at that node). So a node label containing C is a valid A-model
        // root label for A=C: it witnesses C SAT and over-approximates C's subsumers
        // (Phase-2 confirms, so soundness is unchanged). Recording the positive
        // labels of every node of each SAT model lets later query concepts that
        // already appear in some prior model skip their (often identical) witness
        // rebuild — the redundant hard witnesses (5303: many concepts give
        // byte-identical 8.8 s searches) collapse to one. Sound + result-identical;
        // only the number of Phase-1 sat-tests changes. Gated (default off).
        let witreuse = std::env::var_os("KM_HT_WITREUSE").is_some();
        let mut wit: HashMap<C, Vec<C>> = HashMap::new();
        let mut wit_hits = 0u64;
        for (qi, &a) in queries.iter().enumerate() {
            if witreuse {
                if let Some(lab) = wit.get(&a) {
                    // already witnessed SAT by a prior model that carries `a`.
                    sat_q.push(a);
                    if !naive {
                        labels.push((a, lab.clone()));
                    }
                    wit_hits += 1;
                    continue;
                }
            }
            let q0 = self.start.elapsed().as_millis();
            let bt0 = self.backtracks;
            let bj0 = self.backjumps;
            let nf0 = self.negfired;
            let bp0 = self.branch_pushes;
            let dt0 = self.disjunct_tries;
            let st0 = self.steps;
            let bu0 = self.block_us;
            let sat = self.consistent(&[CLit::pos(a)])?;
            if self.stats {
                let dt = self.start.elapsed().as_millis() - q0;
                if dt > 200 || qi % 100 == 0 {
                    eprintln!("KM_HT [classify-p1] qi={}/{} concept={} sat={} dt_ms={} block_ms={} nodes_last={} branch_pushes={} disjunct_tries={} backtracks={} backjumps={} negfired={} steps={}",
                        qi, queries.len(), a, sat, dt, (self.block_us - bu0) / 1000, self.ext.num_nodes(),
                        self.branch_pushes - bp0, self.disjunct_tries - dt0,
                        self.backtracks - bt0, self.backjumps - bj0, self.negfired - nf0,
                        self.steps - st0);
                }
            }
            if !sat {
                unsat.push(a);
            } else {
                sat_q.push(a);
                if !naive {
                    labels.push((a, self.root_pos_label()));
                }
                if witreuse {
                    // record this clash-free model's node labels so later query
                    // concepts present in it skip their rebuild. Only the FIRST
                    // model to carry a concept is kept (cheap, and any model's
                    // node label is a sound candidate set for that concept).
                    let nn = self.ext.num_nodes();
                    for n in 0..nn {
                        let lab = self.node_pos_label(n);
                        if lab.is_empty() {
                            continue;
                        }
                        for &c in &lab {
                            if qset.contains(&c) {
                                wit.entry(c).or_insert_with(|| lab.clone());
                            }
                        }
                    }
                }
            }
            // KM_HT_DUMPLABELS: one-shot dump of the first concept's model — node
            // count, distinct positive labels, size distribution, smallest labels.
            // Diagnostic for the HermiT model-fold gap (compare to HermitNodeLabels).
            if (qi == 0 || self.backtracks - bt0 > 5000) && std::env::var_os("KM_HT_DUMPLABELS").is_some() {
                eprintln!("KM_HT [dumplabels] FOR concept={} qi={} backtracks_here={}", a, qi, self.backtracks - bt0);
                self.dump_labels();
            }
        }
        if self.stats && witreuse {
            eprintln!("KM_HT [witreuse] queries={} reused={} built={}",
                queries.len(), wit_hits, queries.len() as u64 - wit_hits);
        }

        // Told subsumers (Mechanism 1, from the HermiT trace): structural
        // A(x) -> B(x) clauses give A ⊑ B with no tableau test. Skipping those
        // tests and propagating their transitive closure when a subsumption is
        // confirmed (A ⊑ B and B ⊑* X told ⇒ A ⊑ X) cuts the per-pair test count
        // while leaving the result set identical. Gated KM_HT_NO_TOLD.
        let use_told = std::env::var_os("KM_HT_NO_TOLD").is_none();
        let mut told: HashMap<C, Vec<C>> = HashMap::new();
        if use_told && !naive {
            for (c, _, _) in &self.clauses {
                if c.body.len() == 1 && c.head.len() == 1 {
                    if let (Atom::Concept { lit: lb, t: tb }, Atom::Concept { lit: lh, t: th }) =
                        (&c.body[0], &c.head[0])
                    {
                        if !lb.neg && !lh.neg && tb == th && lb.c != lh.c {
                            told.entry(lb.c).or_default().push(lh.c);
                        }
                    }
                }
            }
        }

        // Phase 2: confirm candidate subsumptions A ⊑ B.
        let mut subs = Vec::new();
        if naive {
            for &a in &sat_q {
                for &b in &sat_q {
                    if a != b && !self.consistent(&[CLit::pos(a), CLit::neg(b)])? {
                        subs.push((a, b));
                    }
                }
            }
        } else {
            let satset: HashSet<C> = sat_q.iter().copied().collect();
            // Multi-model pruning (HermiT QuasiOrderClassification, the
            // m_possibleSubsumptions.removeAll step). Every model of A built
            // during classification has A in its root label; any query concept
            // ABSENT from that label is witnessed non-subsumed (A ⊓ ¬C is
            // satisfiable in that model), so it can be dropped from A's candidate
            // set WITHOUT a test. Phase 1 supplies one A-model (`lab`); each
            // Phase-2 test that returns SAT (A ⋢ b) supplies a fresh A-model
            // whose root label shrinks the residual we still have to test. Sound
            // (only proven non-subsumers are removed) and output-identical to the
            // un-pruned run; it only changes which/how-many tests fire. Gated
            // KM_HT_MODELPRUNE for clean A/B. `tests` counts Phase-2 SAT calls so
            // KM_HT_STATS can report the per-classify test count (the HermiT
            // metric: O(classes), not O(classes^2)).
            let modelprune = std::env::var_os("KM_HT_MODELPRUNE").is_some();
            let mut tests: u64 = 0;
            for (a0, lab) in &labels {
                let a = *a0;
                // known = transitive closure of A's told subsumers (no test).
                let mut known: HashSet<C> = HashSet::new();
                let mut stack: Vec<C> = told.get(&a).cloned().unwrap_or_default();
                while let Some(x) = stack.pop() {
                    if known.insert(x) {
                        if let Some(v) = told.get(&x) {
                            stack.extend(v.iter().copied());
                        }
                    }
                }
                let mut local: Vec<C> = known
                    .iter()
                    .copied()
                    .filter(|b| *b != a && qset.contains(b) && satset.contains(b))
                    .collect();
                // candidates: model-label minus those already entailed by told.
                let mut cand: Vec<C> = lab
                    .iter()
                    .copied()
                    .filter(|b| {
                        *b != a && qset.contains(b) && satset.contains(b) && !known.contains(b)
                    })
                    .collect();
                cand.sort_unstable();
                cand.dedup();
                // `possible` is the live residual; SAT models prune it as we go.
                let mut possible: HashSet<C> =
                    if modelprune { cand.iter().copied().collect() } else { HashSet::new() };
                for b in cand {
                    if known.contains(&b) {
                        continue;
                    }
                    if modelprune && !possible.contains(&b) {
                        continue; // a prior A-model already witnessed A ⋢ b
                    }
                    tests += 1;
                    if !self.consistent(&[CLit::pos(a), CLit::neg(b)])? {
                        local.push(b);
                        known.insert(b);
                        // A ⊑ b and b ⊑* x (told) ⇒ A ⊑ x: record + skip its test.
                        let mut st: Vec<C> = told.get(&b).cloned().unwrap_or_default();
                        while let Some(x) = st.pop() {
                            if known.insert(x) {
                                if x != a && qset.contains(&x) && satset.contains(&x) {
                                    local.push(x);
                                }
                                if let Some(v) = told.get(&x) {
                                    st.extend(v.iter().copied());
                                }
                            }
                        }
                    } else if modelprune {
                        // SAT: this fresh A-model (A true, b false at root)
                        // excludes every query concept missing from its root
                        // label. Intersect the residual with it. True subsumers
                        // hold in every A-model, so they survive.
                        let m: HashSet<C> = self.root_pos_label().into_iter().collect();
                        possible.retain(|c| m.contains(c));
                    }
                }
                for b in local {
                    subs.push((a, b));
                }
            }
            if self.stats {
                eprintln!("KM_HT [classify-p2] modelprune={} sat_q={} phase2_tests={}",
                    modelprune, sat_q.len(), tests);
            }
        }
        if self.trace {
            eprintln!("TR classify-return (full) sat={} unsat={} subs={}", sat_q.len(), unsat.len(), subs.len());
        }
        Some((true, unsat, subs))
    }

    /// Multi-threaded sibling of `classify` (KM_HT_PAR>1). The global consistency
    /// check has already run in `classify`; here we parallelise the two
    /// per-concept loops. Each worker builds its own `Ht` (from a clone of the
    /// read-only clause set) so no mutable state is shared across threads — only
    /// `Vec<Clause>` (Send, no `Rc`) crosses a thread boundary; the `Rc`-backed
    /// `Ext` is created and dropped inside one thread. Result set-identical to the
    /// sequential path (see `classify`). Always non-naive, model-based pruning;
    /// the sequential modelprune/witreuse/etc. paths are not mirrored (off in
    /// production and either inert or order-dependent under parallelism).
    fn classify_parallel(&self, queries: &[C], par: usize) -> Option<(bool, Vec<C>, Vec<(C, C)>)> {
        use std::sync::atomic::{AtomicUsize, Ordering};
        let qset: HashSet<C> = queries.iter().copied().collect();
        let template: Vec<Clause> = self.clauses.iter().map(|(c, _, _)| c.clone()).collect();
        let anywhere = self.anywhere;
        let stats = self.stats;
        let nq = queries.len();
        let nthreads = par.min(nq).max(1);
        // Workers need a large stack: `dfs` recurses one frame per branch level,
        // and the disjunction search can dive ~thousands of levels deep (esp.
        // under ORD=1, which backtracks little but descends far). The main thread
        // has an 8 MB stack; spawned threads default to 2 MB and would overflow
        // (SIGABRT), so request a generous stack explicitly.
        const HT_WORKER_STACK: usize = 512 * 1024 * 1024;

        // ---- Phase 1: per-concept SAT + one model's root label. ----
        // Dynamic work-stealing: each worker builds ONE `Ht` and pulls the next
        // concept index from a shared atomic counter. This balances load across
        // wildly uneven per-concept costs (a couple of concepts dominate), which
        // static contiguous chunks do not — and reusing one `Ht` amortises setup
        // and preserves the per-worker activity/phase warm-start the sequential
        // path relies on. The result is set-identical (see `classify`).
        let next1 = AtomicUsize::new(0);
        let p1: Vec<Option<Vec<(C, bool, Vec<C>)>>> = std::thread::scope(|s| {
            let next1 = &next1;
            let handles: Vec<_> = (0..nthreads)
                .map(|_| {
                    let tmpl = template.clone();
                    std::thread::Builder::new()
                        .stack_size(HT_WORKER_STACK)
                        .spawn_scoped(s, move || -> Option<Vec<(C, bool, Vec<C>)>> {
                            let mut w = Ht::new(tmpl);
                            w.set_anywhere(anywhere);
                            let mut out = Vec::new();
                            loop {
                                let i = next1.fetch_add(1, Ordering::Relaxed);
                                if i >= nq {
                                    break;
                                }
                                let a = queries[i];
                                let sat = w.consistent(&[CLit::pos(a)])?;
                                let lab = if sat { w.root_pos_label() } else { Vec::new() };
                                out.push((a, sat, lab));
                            }
                            Some(out)
                        })
                        .expect("spawn HT phase-1 worker")
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let mut unsat = Vec::new();
        let mut sat_q = Vec::new();
        let mut labels: Vec<(C, Vec<C>)> = Vec::new();
        for part in p1 {
            for (a, sat, lab) in part? {
                if sat {
                    sat_q.push(a);
                    labels.push((a, lab));
                } else {
                    unsat.push(a);
                }
            }
        }

        // told subsumers (read-only; same construction as `classify`).
        let use_told = std::env::var_os("KM_HT_NO_TOLD").is_none();
        let mut told: HashMap<C, Vec<C>> = HashMap::new();
        if use_told {
            for (c, _, _) in &self.clauses {
                if c.body.len() == 1 && c.head.len() == 1 {
                    if let (Atom::Concept { lit: lb, t: tb }, Atom::Concept { lit: lh, t: th }) =
                        (&c.body[0], &c.head[0])
                    {
                        if !lb.neg && !lh.neg && tb == th && lb.c != lh.c {
                            told.entry(lb.c).or_default().push(lh.c);
                        }
                    }
                }
            }
        }
        let satset: HashSet<C> = sat_q.iter().copied().collect();

        // ---- Phase 2: confirm A ⊑ B, dynamic work-stealing over the labels. ----
        let nl = labels.len();
        let next2 = AtomicUsize::new(0);
        let p2: Vec<Option<Vec<(C, C)>>> = std::thread::scope(|s| {
            let (told, qset, satset, labels, next2) =
                (&told, &qset, &satset, &labels, &next2);
            let handles: Vec<_> = (0..nthreads.min(nl.max(1)))
                .map(|_| {
                    let tmpl = template.clone();
                    std::thread::Builder::new()
                        .stack_size(HT_WORKER_STACK)
                        .spawn_scoped(s, move || -> Option<Vec<(C, C)>> {
                            let mut w = Ht::new(tmpl);
                            w.set_anywhere(anywhere);
                            let mut subs = Vec::new();
                            loop {
                                let li = next2.fetch_add(1, Ordering::Relaxed);
                                if li >= nl {
                                    break;
                                }
                                let (a, lab) = &labels[li];
                                let a = *a;
                                let mut known: HashSet<C> = HashSet::new();
                                let mut stack: Vec<C> =
                                    told.get(&a).cloned().unwrap_or_default();
                                while let Some(x) = stack.pop() {
                                    if known.insert(x) {
                                        if let Some(v) = told.get(&x) {
                                            stack.extend(v.iter().copied());
                                        }
                                    }
                                }
                                let mut local: Vec<C> = known
                                    .iter()
                                    .copied()
                                    .filter(|b| *b != a && qset.contains(b) && satset.contains(b))
                                    .collect();
                                let mut cand: Vec<C> = lab
                                    .iter()
                                    .copied()
                                    .filter(|b| {
                                        *b != a
                                            && qset.contains(b)
                                            && satset.contains(b)
                                            && !known.contains(b)
                                    })
                                    .collect();
                                cand.sort_unstable();
                                cand.dedup();
                                for b in cand {
                                    if known.contains(&b) {
                                        continue;
                                    }
                                    if !w.consistent(&[CLit::pos(a), CLit::neg(b)])? {
                                        local.push(b);
                                        known.insert(b);
                                        let mut st: Vec<C> =
                                            told.get(&b).cloned().unwrap_or_default();
                                        while let Some(x) = st.pop() {
                                            if known.insert(x) {
                                                if x != a
                                                    && qset.contains(&x)
                                                    && satset.contains(&x)
                                                {
                                                    local.push(x);
                                                }
                                                if let Some(v) = told.get(&x) {
                                                    st.extend(v.iter().copied());
                                                }
                                            }
                                        }
                                    }
                                }
                                for b in local {
                                    subs.push((a, b));
                                }
                            }
                            Some(subs)
                        })
                        .expect("spawn HT phase-2 worker")
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let mut subs = Vec::new();
        for part in p2 {
            subs.extend(part?);
        }
        if stats {
            eprintln!(
                "KM_HT [classify-par] threads={} queries={} sat_q={} subs={}",
                nthreads, nq, sat_q.len(), subs.len()
            );
        }
        Some((true, unsat, subs))
    }

    /// KM_HT_QO: Konclude/HermiT `QuasiOrderClassification`. ONE non-branching
    /// global saturation (disjunctions parked, never case-split; common-concept
    /// consequences harvested through parked disjunctions deterministically)
    /// builds the shared-node model for the whole KB at once. From that single
    /// model we read off, for every query concept A: (a) sat/unsat (A's shared
    /// node is dead ⇒ unsat; sufficient ⇒ sat; otherwise the certified
    /// `consistent(&[A])` test decides), (b) the possible-subsumer set (the
    /// positive label of A's shared node — an over-approximation, so no
    /// subsumption is missed). Only the residual unknown subsumption pairs get
    /// real tableau SAT tests. This is the architecture both trace docs
    /// (`docs/konclude-trace-5303.md`, `docs/hermit-gap.md`) identify as the
    /// structural reason Konclude solves the live `∀ + ⊔` disjunction family in
    /// <0.2s with ZERO branches where KM's branching per-concept model build
    /// times out.
    ///
    /// Sound + complete on the ALC(H) fragment (the same fragment `Ht` covers):
    /// the parked global model under-approximates, but every sat/unsat and
    /// subsumption verdict is confirmed by either (a) a deterministic local
    /// clash at A's shared node (sound for unsat), (b) sufficiency (a genuine
    /// complete model of A, sound+complete), or (c) a real `consistent` tableau
    /// test (the certified branching path). `None` ⇒ an out-of-fragment
    /// construct was seen; the caller falls back.
    pub fn quasi_order_classify(&mut self, queries: &[C]) -> Option<(bool, Vec<C>, Vec<(C, C)>)> {
        let qset: HashSet<C> = queries.iter().copied().collect();

        // --- Collect the named concepts (positive-polarity shared nodes). ---
        let named_concepts: Vec<C> = queries.to_vec();

        // --- ONE global shared-node saturation with the harvest rule. We keep
        // `qs` alive across both phases: the residue SAT test (Phase 1 sat +
        // Phase 2 subsumption) branches the open disjunctions IN PLACE over
        // this saturated shared model, with trail rollback — the Konclude
        // architecture. No `self.consistent()` (the 671-node fresh rebuild) is
        // needed; `None` from a residue test ⇒ bail to the caller's fallback. ---
        let mut qs = QoSat::new(&self.clauses);
        let g = qs.saturate_global(&named_concepts);
        if g.unsupported {
            return None;
        }
        // The first `queries.len()` shared nodes are the seeded query concepts,
        // in order (saturate_global seeds them before any drain-induced node).
        let node_of: HashMap<C, Node> = queries
            .iter()
            .enumerate()
            .map(|(i, &c)| (c, i as Node))
            .collect();

        // --- Global consistency: if every query concept's shared node is dead
        // in the parked over-approximation, the KB is inconsistent (a clash in
        // the over-approximation is sound for unsat — no real model exists). ---
        let all_dead = !queries.is_empty()
            && queries.iter().all(|&a| qs.node_unsat.contains(&node_of[&a]));
        if all_dead {
            return Some((false, queries.to_vec(), Vec::new()));
        }
        if std::env::var_os("KM_HT_GLOBAL").is_some() {
            return Some((true, Vec::new(), Vec::new()));
        }

        // --- Told subsumers (Mechanism 1, free syntactic seeding). ---
        let use_told = std::env::var_os("KM_HT_NO_TOLD").is_none();
        let mut told: HashMap<C, Vec<C>> = HashMap::new();
        if use_told {
            for (c, _, _) in &self.clauses {
                if c.body.len() == 1 && c.head.len() == 1 {
                    if let (Atom::Concept { lit: lb, t: tb }, Atom::Concept { lit: lh, t: th }) =
                        (&c.body[0], &c.head[0])
                    {
                        if !lb.neg && !lh.neg && tb == th && lb.c != lh.c {
                            told.entry(lb.c).or_default().push(lh.c);
                        }
                    }
                }
            }
        }

        // --- Phase 1: read sat/unsat + possible off the global model; for
        // insufficient concepts run the residue SAT test over the shared model. ---
        let mut unsat: Vec<C> = Vec::new();
        let mut sat_q: Vec<C> = Vec::new();
        // possible[A] = candidate subsumers (over-approximation; true subsumers
        // are a subset, so no subsumption is missed).
        let mut possible: HashMap<C, HashSet<C>> = HashMap::new();
        // KM_HT_QO_TALLY: diagnostic — count dead/suff/insuff across ALL query
        // concepts WITHOUT running any residue test (so it never bails on the
        // first insufficient concept). Reveals how many concepts genuinely need
        // the expensive residue SAT test for this ont.
        let tally = std::env::var_os("KM_HT_QO_TALLY").is_some();
        if tally {
            let (mut nd, mut ns, mut ni) = (0u64, 0u64, 0u64);
            let mut open_hist: Vec<usize> = Vec::new();
            for &a in queries {
                let n = node_of[&a];
                if qs.node_unsat.contains(&n) {
                    nd += 1;
                } else if g.sufficient[n] {
                    ns += 1;
                } else {
                    ni += 1;
                    open_hist.push(g.open_disj_per_node[n]);
                }
            }
            open_hist.sort_unstable();
            let max_open = open_hist.last().copied().unwrap_or(0);
            let med_open = open_hist.get(open_hist.len() / 2).copied().unwrap_or(0);
            eprintln!(
                "KM_HT [qo-tally] queries={} dead={} suff={} insuff={} (insuff open: med={} max={})",
                queries.len(), nd, ns, ni, med_open, max_open
            );
            return Some((true, Vec::new(), Vec::new()));
        }
        for (qi, &a) in queries.iter().enumerate() {
            let n = node_of[&a];
            let dead = qs.node_unsat.contains(&n);
            let suff = g.sufficient[n];
            let open = g.open_disj_per_node[n];
            let lab = g.label_pos[n].clone();
            if self.stats {
                eprintln!("KM_HT [qo-p1] qi={}/{} a={} node={} dead={} suff={} open={} lab_sz={}",
                    qi, queries.len(), a, n, dead, suff, open, lab.len());
            }
            if dead {
                // parked-model clash ⇒ sound for unsat.
                unsat.push(a);
                continue;
            }
            if suff {
                // sufficient ⇒ a complete clash-free model of A exists ⇒ A sat.
                possible.insert(a, lab);
                sat_q.push(a);
                continue;
            }
            // insufficient (open>0): residue SAT test over the shared model.
            match qs.qo_residue_test(n, &[]) {
                None => return None,
                Some(false) => unsat.push(a),
                Some(true) => {
                    possible.insert(a, lab);
                    sat_q.push(a);
                }
            }
        }

        // --- Phase 2: residual subsumption tests, top-down with told-closure.
        // Each test is a residue SAT `A ⊓ ¬B` over A's shared node. ---
        let satset: HashSet<C> = sat_q.iter().copied().collect();
        let mut subs: Vec<(C, C)> = Vec::new();
        let mut tests: u64 = 0;
        for &a in &sat_q {
            let mut known: HashSet<C> = HashSet::new();
            let mut stack: Vec<C> = told.get(&a).cloned().unwrap_or_default();
            while let Some(x) = stack.pop() {
                if known.insert(x) {
                    if let Some(v) = told.get(&x) {
                        stack.extend(v.iter().copied());
                    }
                }
            }
            // known subsumers that are query concepts ⇒ recorded without a test.
            for b in known.iter().copied().filter(|b| *b != a && qset.contains(b) && satset.contains(b)) {
                subs.push((a, b));
            }
            // candidates = possible(a) minus known, restricted to query concepts.
            let mut cand: Vec<C> = possible
                .get(&a)
                .map(|s| {
                    s.iter()
                        .copied()
                        .filter(|b| *b != a && qset.contains(b) && satset.contains(b) && !known.contains(b))
                        .collect()
                })
                .unwrap_or_default();
            cand.sort_unstable();
            cand.dedup();
            let n_a = node_of[&a];
            for b in cand {
                if known.contains(&b) {
                    continue;
                }
                tests += 1;
                match qs.qo_residue_test(n_a, &[CLit::neg(b)]) {
                    None => return None,
                    Some(true) => {
                        // A ⊓ ¬B sat ⇒ A ⋢ B.
                    }
                    Some(false) => {
                        // A ⊓ ¬B unsat ⇒ A ⊑ B. Record + fold told-closure.
                        subs.push((a, b));
                        known.insert(b);
                        let mut st: Vec<C> = told.get(&b).cloned().unwrap_or_default();
                        while let Some(x) = st.pop() {
                            if known.insert(x) {
                                if x != a && qset.contains(&x) && satset.contains(&x) {
                                    subs.push((a, x));
                                }
                                if let Some(v) = told.get(&x) {
                                    st.extend(v.iter().copied());
                                }
                            }
                        }
                    }
                }
            }
        }
        if self.stats {
            eprintln!("KM_HT [qo-p2] sat_q={} phase2_tests={}", sat_q.len(), tests);
        }
        Some((true, unsat, subs))
    }

    /// Non-branching saturation fixpoint: propagate Horn clauses, expand
    /// existential obligations (under blocking), and unit-propagate forced
    /// disjuncts — but NEVER case-split a >=2-live disjunction (it is parked).
    /// Returns false if an out-of-ALC(H) construct sets `unsupported` (caller
    /// bails to the legacy path); true otherwise (the model may or may not have
    /// clashed — check `ext.has_clash()`).
    fn park_fixpoint(&mut self) -> bool {
        loop {
            self.propagate();
            if self.ext.unsupported {
                return false;
            }
            if self.ext.has_clash() {
                return true;
            }
            let made_oblig = self.process_obligations();
            if self.ext.unsupported {
                return false;
            }
            if self.ext.has_clash() {
                return true;
            }
            let made_unit = self.park_drain_units();
            if self.ext.unsupported {
                return false;
            }
            if !made_oblig && !made_unit {
                self.propagate();
                return !self.ext.unsupported;
            }
        }
    }

    /// Scan every recorded ground disjunction and assert the single live
    /// disjunct of any unit-forced one (cascading within `pending` until no new
    /// unit fires). >=2-live disjunctions are left in place (parked). Returns
    /// true if any unit was asserted (progress).
    fn park_drain_units(&mut self) -> bool {
        let mut progress = false;
        loop {
            let mut found_unit = false;
            let np = self.ext.pending.len();
            for i in 0..np {
                if self.ext.has_clash() {
                    return progress;
                }
                let (bdep, ndisj) = {
                    let pd = &self.ext.pending[i];
                    (pd.bdep.clone(), pd.disjuncts.len())
                };
                let mut satisfied = false;
                let mut dead_dep = dep_empty();
                let mut live: Vec<(Node, CLit)> = Vec::with_capacity(ndisj);
                for j in 0..ndisj {
                    let (n, lit) = self.ext.pending[i].disjuncts[j];
                    if self.ext.has_concept(n, lit) {
                        satisfied = true;
                        break;
                    }
                    let comp = CLit { neg: !lit.neg, c: lit.c };
                    if let Some(d) = self.ext.dep_of(n, comp) {
                        dead_dep = dep_union(&dead_dep, d);
                    } else {
                        live.push((n, lit));
                    }
                }
                if satisfied {
                    continue;
                }
                if live.is_empty() {
                    self.ext.raise_clash(dep_union(&bdep, &dead_dep));
                    return progress;
                }
                if live.len() == 1 {
                    let d = dep_union(&bdep, &dead_dep);
                    if self.ext.add_concept(live[0].0, live[0].1, &d) {
                        found_unit = true;
                        progress = true;
                        if self.ext.has_clash() {
                            return progress;
                        }
                    }
                }
                // >=2 live: park (skip — do not branch).
            }
            if !found_unit {
                break;
            }
        }
        progress
    }

    pub fn steps(&self) -> u64 {
        self.steps
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(neg: bool, c: C) -> CLit {
        CLit { neg, c }
    }
    fn con(neg: bool, c: C, t: Var) -> Atom {
        Atom::Concept { lit: CLit { neg, c }, t }
    }
    fn role(r: R, s: Var, t: Var) -> Atom {
        Atom::Role { r, s, t }
    }
    fn exists(r: R, neg: bool, c: C, t: Var) -> Atom {
        Atom::Exists { r, fil: CLit { neg, c }, t }
    }

    const A: C = 0;
    const B: C = 1;
    const D: C = 3;
    const R0: R = 0;

    #[test]
    fn depset_max_and_contains() {
        let d = dep_add(&dep_add(&dep_empty(), 3), 7);
        assert_eq!(dep_max(&d), 7);
        assert!(dep_contains(&d, 7) && dep_contains(&d, 3) && !dep_contains(&d, 5));
    }
    #[test]
    fn depset_union_and_remove() {
        let a = dep_add(&dep_add(&dep_empty(), 1), 4);
        let b = dep_add(&dep_add(&dep_empty(), 4), 8);
        let u = dep_union(&a, &b);
        for l in [1, 4, 8] {
            assert!(dep_contains(&u, l));
        }
        assert_eq!(dep_max(&dep_remove(&u, 8)), 4);
    }
    #[test]
    fn clash_union_dep_is_backjump_target() {
        let mut e = Ext::new();
        let n = e.new_root();
        e.add_concept(n, lit(false, 0), &dep_add(&dep_empty(), 5));
        e.add_concept(n, lit(true, 0), &dep_add(&dep_empty(), 2));
        assert!(e.has_clash());
        assert_eq!(dep_max(&e.clash_dep()), 5);
    }

    fn ht(cls: Vec<Clause>) -> Ht {
        Ht::new(cls)
    }

    #[test]
    fn clash_a_and_not_a() {
        assert_eq!(ht(vec![]).consistent(&[CLit::pos(A), CLit::neg(A)]), Some(false));
    }
    #[test]
    fn simple_sat() {
        assert_eq!(ht(vec![]).consistent(&[CLit::pos(A)]), Some(true));
    }
    #[test]
    fn existential_then_universal_clash() {
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A, X), role(R0, X, 1)], vec![con(true, B, 1)]),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(false));
    }
    #[test]
    fn existential_universal_consistent() {
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A, X), role(R0, X, 1)], vec![con(false, D, 1)]),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(true));
    }
    #[test]
    fn disjunction_unsat_both_branches_clash() {
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![con(false, B, X), con(false, D, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(true, D, X)]),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(false));
    }
    #[test]
    fn disjunction_one_branch_open() {
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![con(false, B, X), con(false, D, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(true));
    }
    #[test]
    fn unit_propagation_via_dead_disjunct() {
        // A ⊑ B ⊔ D, A ⊑ ¬B ⇒ D forced; {A,¬D} unsat. Exercises scan unit-prop.
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![con(false, B, X), con(false, D, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A), CLit::neg(D)]), Some(false));
    }
    #[test]
    fn horn_chain_delta() {
        // A→B, B→D ; {A,¬D} unsat — exercises delta trigger chaining.
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![con(false, B, X)]),
            Clause::new(vec![con(false, B, X)], vec![con(false, D, X)]),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A), CLit::neg(D)]), Some(false));
    }
    #[test]
    fn forall_propagation_delta_both_triggers() {
        // A ⊑ ∃r.B (succ gets B), B ⊑ C? no: A ⊑ ∀r.D and successor has B; check
        // ∀ fires whether the edge or the guard concept arrives first.
        // A→∃r.B ; A ∧ r(x,y) → D(y) ; D⊓B disjoint at y via D→¬B? use: A⊑∀r.¬B.
        const C2: C = 2;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A, X), role(R0, X, 1)], vec![con(false, C2, 1)]),
            Clause::new(vec![con(false, C2, X)], vec![con(true, B, X)]),
        ];
        // successor is B (from ∃) and C2 (from ∀), C2→¬B clashes ⇒ A unsat.
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(false));
    }
    #[test]
    fn infinite_chain_blocks_and_terminates() {
        let cls = vec![Clause::new(vec![con(false, A, X)], vec![exists(R0, false, A, X)])];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(true));
    }
    #[test]
    fn anywhere_blocking_also_terminates() {
        let cls = vec![Clause::new(vec![con(false, A, X)], vec![exists(R0, false, A, X)])];
        let mut t = ht(cls);
        t.set_anywhere(true);
        assert_eq!(t.consistent(&[CLit::pos(A)]), Some(true));
    }
    #[test]
    fn backjump_skips_irrelevant_branch() {
        const P: C = 6;
        const Q: C = 7;
        const R_: C = 8;
        let cls = vec![
            Clause::new(vec![con(false, P, X)], vec![con(false, Q, X), con(false, R_, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(false, B, X), con(false, D, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(true, D, X)]),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(P), CLit::pos(A)]), Some(false));
    }
    #[test]
    fn global_axiom_empty_body() {
        // ⊤ ⊑ B (empty body), ⊤ ⊑ ¬B ⇒ KB inconsistent (clash on the root node).
        let cls = vec![
            Clause::new(vec![], vec![con(false, B, X)]),
            Clause::new(vec![], vec![con(true, B, X)]),
        ];
        assert_eq!(ht(cls).consistent(&[]), Some(false));
    }
    #[test]
    fn luby_sequence_prefix() {
        let got: Vec<u64> = (1..=15).map(luby).collect();
        assert_eq!(got, vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]);
    }
    #[test]
    fn search_modes_answer_invariant() {
        // The unsat-both-branches and one-branch-open KBs must give the same
        // verdict under every ord/pick/restart setting (search is exhaustive).
        let unsat = || {
            vec![
                Clause::new(vec![con(false, A, X)], vec![con(false, B, X), con(false, D, X)]),
                Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
                Clause::new(vec![con(false, A, X)], vec![con(true, D, X)]),
            ]
        };
        let open = || {
            vec![
                Clause::new(vec![con(false, A, X)], vec![con(false, B, X), con(false, D, X)]),
                Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
            ]
        };
        for ord in [0u8, 1, 2] {
            for pick in [0u8, 1, 2] {
                for restart in [false, true] {
                    let mut tu = ht(unsat());
                    tu.ord_mode = ord;
                    tu.pick_mode = pick;
                    tu.do_restart = restart;
                    tu.rbase = 1; // force frequent restarts to exercise the loop
                    assert_eq!(
                        tu.consistent(&[CLit::pos(A)]),
                        Some(false),
                        "ord={ord} pick={pick} restart={restart}"
                    );
                    let mut to = ht(open());
                    to.ord_mode = ord;
                    to.pick_mode = pick;
                    to.do_restart = restart;
                    to.rbase = 1;
                    assert_eq!(
                        to.consistent(&[CLit::pos(A)]),
                        Some(true),
                        "ord={ord} pick={pick} restart={restart}"
                    );
                }
            }
        }
    }
    #[test]
    fn role_hierarchy_head_propagates_edge() {
        // A ⊑ ∃r.B ; r ⊑ s ; A ⊓ ∀s.¬B  ⇒  the r-successor (has B) also gets the
        // s-edge (head role atom), ∀s.¬B fires ¬B on it ⇒ clash ⇒ A unsat.
        const S: R = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![role(R0, X, 1)], vec![role(S, X, 1)]),
            Clause::new(vec![con(false, A, X), role(S, X, 1)], vec![con(true, B, 1)]),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(false));
    }
    #[test]
    fn role_hierarchy_head_consistent() {
        // same shape but ∀s.E (E ≠ ¬B): the successor gets B and E, no clash.
        const S: R = 1;
        const E: C = 4;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![role(R0, X, 1)], vec![role(S, X, 1)]),
            Clause::new(vec![con(false, A, X), role(S, X, 1)], vec![con(false, E, 1)]),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(true));
    }
    #[test]
    fn classify_basic_subsumption() {
        let cls = vec![Clause::new(vec![con(false, A, X)], vec![con(false, B, X)])];
        let (consistent, unsat, subs) = ht(cls).classify(&[A, B]).unwrap();
        assert!(consistent && unsat.is_empty());
        assert!(subs.contains(&(A, B)) && !subs.contains(&(B, A)));
    }
    #[test]
    fn watch_eq_scan_all_small_kbs() {
        // The incremental (watch) disjunction handling must give the same
        // consistency verdict as the full scan on every small KB above.
        let cases: Vec<(Vec<Clause>, Vec<CLit>, Option<bool>)> = vec![
            (vec![], vec![CLit::pos(A), CLit::neg(A)], Some(false)),
            (vec![], vec![CLit::pos(A)], Some(true)),
            (
                vec![
                    Clause::new(vec![con(false, A, X)], vec![con(false, B, X), con(false, D, X)]),
                    Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
                    Clause::new(vec![con(false, A, X)], vec![con(true, D, X)]),
                ],
                vec![CLit::pos(A)],
                Some(false),
            ),
            (
                vec![
                    Clause::new(vec![con(false, A, X)], vec![con(false, B, X), con(false, D, X)]),
                    Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
                ],
                vec![CLit::pos(A), CLit::neg(D)],
                Some(false),
            ),
            (
                vec![
                    Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
                    Clause::new(vec![con(false, A, X), role(R0, X, 1)], vec![con(true, B, 1)]),
                ],
                vec![CLit::pos(A)],
                Some(false),
            ),
            (
                vec![Clause::new(vec![con(false, A, X)], vec![exists(R0, false, A, X)])],
                vec![CLit::pos(A)],
                Some(true),
            ),
        ];
        for (cls, seed, want) in cases.iter() {
            let mut tw = ht(cls.clone());
            tw.watch = true;
            assert_eq!(tw.consistent(seed), *want, "watch-mode mismatch");
            // learning must also be answer-invariant.
            let mut tl = ht(cls.clone());
            tl.learn = true;
            assert_eq!(tl.consistent(seed), *want, "learn-mode mismatch");
            // and the two together.
            let mut twl = ht(cls.clone());
            twl.watch = true;
            twl.learn = true;
            assert_eq!(twl.consistent(seed), *want, "watch+learn mismatch");
        }
    }
    #[test]
    fn classify_model_based_eq_naive_chain() {
        // A ⊑ B ⊑ D ; classification must yield {A⊑B, A⊑D, B⊑D} and nothing
        // reversed, identically under model-based pruning and naive n².
        let cls = || {
            vec![
                Clause::new(vec![con(false, A, X)], vec![con(false, B, X)]),
                Clause::new(vec![con(false, B, X)], vec![con(false, D, X)]),
            ]
        };
        let (_, _, mut mb) = ht(cls()).classify(&[A, B, D]).unwrap();
        let mut tnaive = ht(cls());
        tnaive.naive = true;
        let (_, _, mut nv) = tnaive.classify(&[A, B, D]).unwrap();
        mb.sort();
        nv.sort();
        assert_eq!(mb, nv);
        assert!(mb.contains(&(A, B)) && mb.contains(&(A, D)) && mb.contains(&(B, D)));
        assert!(!mb.contains(&(B, A)) && !mb.contains(&(D, A)));
    }
}
