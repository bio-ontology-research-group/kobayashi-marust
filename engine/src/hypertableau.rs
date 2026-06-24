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

// KM_HT_NUMBER safety: a single clause body match (`rec_match_flex`) can blow up
// into an enormous join over a dense merged graph (the SHIQ ≤n / inverse path),
// which would hang. Under number-mode only, bound the recursion-step count per
// anchored fire; on overflow the matcher stops and the caller bails the whole HT
// run to `unsupported` (a sound fallback to CB — never a wrong answer). Production
// (number off) is untouched: the counter is not even incremented.
const RMF_STEP_CAP: u64 = 8_000_000;
// QoSat drain-loop step counters (KM_HT_TRACE diagnostics): lit-pops, node-pops
// (global ⊤-clause refiring), and edge-pops (role-clause firing). Split so a
// trace pinpoints which of the three loops dominates at the 73k-node scale.
static QO_DRAIN: AtomicU64 = AtomicU64::new(0);
static QO_NODE: AtomicU64 = AtomicU64::new(0);
static QO_EDGE: AtomicU64 = AtomicU64::new(0);
thread_local! {
    static RMF_STEPS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

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
    /// KM_HT_NUMBER: node `v` was folded into a survivor by a ≤n merge; on
    /// backtrack revive it (`merged[v] = None`). The copied concepts/edges are
    /// undone by their own (later) trail entries, so this restores the redirect.
    Merge(Node),
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
    in_edges: Vec<Vec<(R, Node, DepSet)>>,
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
    /// KM_HT_NUMBER: equality-head (≤n / functional) clauses merge nodes instead
    /// of bailing. `merged[v] = Some(u)` ⇒ node `v` was folded into survivor `u`
    /// (a ≤n merge); `resolve` follows the chain. Trail-recorded (`Trail::Merge`).
    number: bool,
    merged: Vec<Option<Node>>,
    merges: u64,

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

    /// KM_HT_INCRBLOCK: maintain a persistent inverted index for subset blocking
    /// (encoded-literal `(c<<1)|neg` → nodes carrying it), so `compute_blocked`
    /// QUERIES instead of rebuilding the index every call (the rebuild was ~73%
    /// of the per-test wall). Append on a fresh `add_concept`, pop on its
    /// trail-undo (LIFO-correct per literal). The index holds ALL nodes (blocked
    /// or not): a node is blocked iff some earlier node is a label-superset — if
    /// the only supersets are themselves blocked, their blocker is transitively a
    /// superset too, so the result is identical to the unblocked-only relation.
    incr_block: bool,
    block_index: Vec<Vec<Node>>,

    /// KM_HT_INCRBLOCK2: incremental subset blocking that is RESULT-IDENTICAL to
    /// the full per-pass scan but recomputes only the affected suffix. Blocking is
    /// strictly by an EARLIER node (`m < n`), so `blocked[n]` depends only on the
    /// labels of nodes `<= n`. Tracking `i2_lo` = the smallest node id whose label
    /// changed (a fresh `add_concept`, a new node, or a backtrack) since the last
    /// compute means a recompute only re-evaluates `i2_lo..nn` in id order — a
    /// forward pass over the suffix, equal to a full pass because every node `< lo`
    /// is unchanged (and so is its blocked status and list membership). In tableau
    /// the frontier (label growth + new nodes) sits at high ids, so the suffix is
    /// usually tiny; the full O(n) per-pass scan (~65% of the per-test wall on the
    /// disjunction family) collapses to O(changed). `i2_lists` holds only UNBLOCKED
    /// nodes per encoded literal (the candidate blockers), `i2_touched` the slots
    /// that ever received an entry (so a recompute clears `>= lo` cheaply).
    incr2: bool,
    i2_blocked: Vec<bool>,
    i2_lists: Vec<Vec<Node>>,
    /// Encoded-literal slots that ever received a posting (deduped via
    /// `i2_in_touched`), so a recompute clears/retains only non-empty slots instead
    /// of scanning the whole `i2_lists` table each of the ~250k passes.
    i2_touched: Vec<usize>,
    i2_in_touched: Vec<bool>,
    i2_lo: usize,
    i2_last_lo: usize,

    /// KM_HT_INCROBLIG: incremental ∃-obligation processing. The flat obligation
    /// loop in `process_obligations` re-scanned EVERY accumulated obligation on
    /// every saturation pass (240M iterations on 5303 = 72% of the wall once
    /// blocking was fixed). 92% of obligations sit on BLOCKED nodes and are merely
    /// skipped each pass — pure waste. `node_obligs[n]` indexes a node's obligation
    /// positions, so a pass iterates only the obligations of currently-UNBLOCKED
    /// nodes (the few that can actually expand). Indices into the flat `obligations`
    /// vec; pruned on backtrack to keep them valid under index reuse. Result is
    /// processed in index order (sorted), so it is identical to the flat scan.
    incroblig: bool,
    node_obligs: Vec<Vec<usize>>,
    /// Parallel to `obligations`: marks one as discharged (a successor exists), so
    /// even among unblocked nodes a satisfied obligation is skipped without an edge
    /// rescan. Cleared on backtrack (a removed edge can un-satisfy one → re-verify).
    oblig_sat: Vec<bool>,
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
            number: std::env::var_os("KM_HT_NUMBER").is_some(),
            merged: Vec::new(),
            merges: 0,
            watch: false,
            lit_disj: HashMap::new(),
            dirty: Vec::new(),
            dirty_in: Vec::new(),
            open: Vec::new(),
            open_in: Vec::new(),
            uid: Vec::new(),
            uid_next: 1,
            clash_node: None,
            incr_block: std::env::var_os("KM_HT_INCRBLOCK").is_some(),
            block_index: Vec::new(),
            incr2: std::env::var_os("KM_HT_INCRBLOCK2").is_some(),
            i2_blocked: Vec::new(),
            i2_lists: Vec::new(),
            i2_touched: Vec::new(),
            i2_in_touched: Vec::new(),
            i2_lo: 0,
            i2_last_lo: 0,
            incroblig: std::env::var_os("KM_HT_INCROBLIG").is_some(),
            node_obligs: Vec::new(),
            oblig_sat: Vec::new(),
        }
    }

    /// Note that node `n`'s label changed (or `n` is new): widen the dirty suffix
    /// so the next `i2_recompute` re-evaluates from here on. Cheap; the actual
    /// blocking work is deferred to the compute called once per saturation pass.
    #[inline]
    fn i2_note(&mut self, n: Node) {
        if self.incr2 && n < self.i2_lo {
            self.i2_lo = n;
        }
    }

    /// Is blockable node `n` blocked by an EARLIER unblocked node (subset blocking)?
    /// Candidates come from n's rarest concept's posting list (a superset must
    /// carry every concept of n); `i2_lists` holds only earlier unblocked nodes, so
    /// any `m < n` found is a valid blocker. Identical to the full-scan predicate.
    fn i2_blocked_by_earlier(&self, n: Node) -> bool {
        let ln = &self.concepts[n];
        if ln.is_empty() {
            return false;
        }
        let lnlen = ln.len();
        let mut best: &[Node] = &[];
        let mut best_len = usize::MAX;
        for k in ln.keys() {
            let e = Ext::enc_lit(*k);
            let l = self.i2_lists.get(e).map_or(0, |v| v.len());
            if l < best_len {
                best_len = l;
                best = self.i2_lists.get(e).map_or(&[], |v| v.as_slice());
            }
        }
        for &m in best {
            if m >= n {
                continue;
            }
            let lm = &self.concepts[m];
            if lm.len() >= lnlen && ln.keys().all(|k| lm.contains_key(k)) {
                return true;
            }
        }
        false
    }

    /// Recompute the subset-blocking snapshot incrementally and return it. Only the
    /// suffix `i2_lo..nn` is re-evaluated (see the `incr2` field doc): drop stale
    /// `>= lo` entries from the posting lists, reset `blocked[lo..]`, then a single
    /// forward pass classifies `lo..nn`, appending each unblocked node's concepts.
    fn i2_recompute(&mut self) -> Vec<bool> {
        let nn = self.num_nodes();
        let lo = self.i2_lo.min(nn);
        self.i2_last_lo = lo; // diagnostic: suffix size = nn - lo
        // Drop stale entries for re-evaluated nodes (id >= lo), touching only the
        // non-empty slots (scanning the whole table each pass was the dominant
        // blocking cost). Empty-but-touched slots are cheap (retain over 0 elems).
        if lo == 0 {
            for &e in &self.i2_touched {
                self.i2_lists[e].clear();
                self.i2_in_touched[e] = false;
            }
            self.i2_touched.clear();
        } else {
            for &e in &self.i2_touched {
                self.i2_lists[e].retain(|&x| x < lo);
            }
        }
        // Keep blocked[0..lo]; reset and recompute [lo..nn].
        self.i2_blocked.truncate(lo);
        self.i2_blocked.resize(nn, false);
        for n in lo..nn {
            let blk = self.blockable[n] && self.i2_blocked_by_earlier(n);
            self.i2_blocked[n] = blk;
            if !blk {
                // unblocked node: register it as a candidate blocker for later nodes.
                let keys: Vec<CLit> = self.concepts[n].keys().copied().collect();
                for k in keys {
                    let e = Ext::enc_lit(k);
                    if e >= self.i2_lists.len() {
                        self.i2_lists.resize_with(e + 1, Vec::new);
                    }
                    if e >= self.i2_in_touched.len() {
                        self.i2_in_touched.resize(e + 1, false);
                    }
                    if !self.i2_in_touched[e] {
                        self.i2_in_touched[e] = true;
                        self.i2_touched.push(e);
                    }
                    self.i2_lists[e].push(n);
                }
            }
        }
        self.i2_lo = usize::MAX;
        self.i2_blocked.clone()
    }

    /// Encode a literal as a flat index for `block_index`.
    #[inline]
    fn enc_lit(lit: CLit) -> usize {
        ((lit.c as usize) << 1) | (lit.neg as usize)
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
        self.merged.push(None);
        if self.incroblig {
            self.node_obligs.push(Vec::new());
        }
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
        self.i2_note(id);
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
                if self.incr_block {
                    let e = Ext::enc_lit(lit);
                    if e >= self.block_index.len() {
                        self.block_index.resize_with(e + 1, Vec::new);
                    }
                    self.block_index[e].push(node);
                }
                self.i2_note(node);
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
        self.in_edges[t].push((r, s, dep.clone()));
        self.trail.push(Trail::Edge(r, s, t));
        self.queue.push(Event::Edge(r, s, t));
    }

    /// Follow the ≤n merge chain to the surviving node (KM_HT_NUMBER). Identity
    /// when nothing is merged, so callers can resolve unconditionally.
    #[inline]
    pub fn resolve(&self, n: Node) -> Node {
        let mut x = n;
        while let Some(p) = self.merged[x] {
            x = p;
        }
        x
    }

    /// KM_HT_NUMBER: fold nodes `a` and `b` together (a ≤n / functional merge).
    /// The lower-id node survives (keeps the model closer to the root); the
    /// victim's concept label and incident edges are copied onto the survivor
    /// under the union of each fact's dep and the merge dependency `mdep`, then
    /// the victim is redirected (`merged[victim] = survivor`). All copies are
    /// ordinary trail-recorded `add_concept`/`add_edge`, so a `backtrack_to`
    /// undoes the whole merge. The merge dep `mdep` flows into every copied fact
    /// so a resulting clash backjumps past the cardinality clause that forced it.
    pub fn merge_into(&mut self, a: Node, b: Node, mdep: &DepSet) {
        let a = self.resolve(a);
        let b = self.resolve(b);
        if a == b {
            return;
        }
        let (survivor, victim) = if a <= b { (a, b) } else { (b, a) };
        self.merges += 1;
        if std::env::var_os("KM_HT_TRACE").is_some() && self.merges % 100_000 == 0 {
            eprintln!("MERGE count={} nodes={} trail={}", self.merges, self.concepts.len(), self.trail.len());
        }
        self.trail.push(Trail::Merge(victim));
        self.merged[victim] = Some(survivor);
        let cs: Vec<(CLit, DepSet)> =
            self.concepts[victim].iter().map(|(k, v)| (*k, v.clone())).collect();
        for (lit, d) in cs {
            let nd = dep_union(&d, mdep);
            self.add_concept(survivor, lit, &nd);
            if self.clash.is_some() {
                return;
            }
        }
        let oes: Vec<(R, Node, DepSet)> = self.out_edges[victim].clone();
        for (r, t, d) in oes {
            let t2 = self.resolve(t);
            let nd = dep_union(&d, mdep);
            self.add_edge(r, survivor, t2, &nd);
            if self.clash.is_some() {
                return;
            }
        }
        let ies: Vec<(R, Node, DepSet)> = self.in_edges[victim].clone();
        for (r, s, d) in ies {
            let s2 = self.resolve(s);
            let nd = dep_union(&d, mdep);
            self.add_edge(r, s2, survivor, &nd);
            if self.clash.is_some() {
                return;
            }
        }
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
        // Track the smallest node whose subset-blocking label changed (a concept
        // removed, or the node itself removed) so the incremental snapshot rebuilds
        // only the affected suffix [min_aff..nn] next pass — not the whole model.
        // Subset blocking is label-only, so edge/globals-fired undos don't matter.
        let mut min_aff = usize::MAX;
        while self.trail.len() > mark {
            match self.trail.pop().unwrap() {
                Trail::Concept(node, lit) => {
                    if node < min_aff {
                        min_aff = node;
                    }
                    self.concepts[node].remove(&lit);
                    if self.incr_block {
                        // LIFO: the most recent fresh add for this literal was this
                        // node, so it is the last element of its posting list.
                        let e = Ext::enc_lit(lit);
                        if let Some(v) = self.block_index.get_mut(e) {
                            debug_assert_eq!(v.last().copied(), Some(node));
                            v.pop();
                        }
                    }
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
                        self.in_edges[t].iter().position(|&(rr, ss, _)| rr == r && ss == s)
                    {
                        self.in_edges[t].swap_remove(pos);
                    }
                }
                Trail::NewNode => {
                    let id = self.concepts.len() - 1;
                    if id < min_aff {
                        min_aff = id;
                    }
                    self.concepts.pop();
                    self.out_edges.pop();
                    self.in_edges.pop();
                    self.pred.pop();
                    self.blockable.pop();
                    self.globals_fired.pop();
                    self.merged.pop();
                    if self.incroblig {
                        self.node_obligs.pop();
                    }
                }
                Trail::GlobalsFired(node) => {
                    if node < self.globals_fired.len() {
                        self.globals_fired[node] = false;
                    }
                }
                Trail::Merge(v) => {
                    if v < self.merged.len() {
                        self.merged[v] = None;
                    }
                }
            }
        }
        if self.incr2 {
            self.i2_lo = self.i2_lo.min(min_aff);
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
        if self.incroblig {
            // Obligations beyond the new length were dropped (and their indices may
            // be reused by later pushes), so drop dangling references to them.
            let nl = self.obligations.len();
            for v in self.node_obligs.iter_mut() {
                v.retain(|&i| i < nl);
            }
            // A removed edge can un-satisfy a surviving obligation; re-verify all.
            self.oblig_sat.truncate(nl);
            for b in self.oblig_sat.iter_mut() {
                *b = false;
            }
        }
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
    // KM_HT_NUMBER: bound the join to avoid a hang on an explosive match (see
    // RMF_STEP_CAP). On overflow stop enumerating; the caller detects it and bails.
    if ext.number {
        let over = RMF_STEPS.with(|c| {
            let v = c.get() + 1;
            c.set(v);
            v > RMF_STEP_CAP
        });
        if over {
            return;
        }
    }
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
                        let (rr, ss) = { let e = &ext.in_edges[tn][k2]; (e.0, e.1) };
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
    // KM_HT_NUMBER: equality-head clauses (≤n / functionality). A single Eq head
    // is a forced (unit) merge of the two role successors. Multiple Eq disjuncts
    // (≤n, n≥2) need a merge branch not yet implemented, so bail soundly there.
    if ext.number && head.iter().any(|h| matches!(h, Atom::Eq { .. })) {
        if head.len() == 1 {
            if let Atom::Eq { s, t } = head[0] {
                let sn = sigma[s as usize].expect("eq head src bound by body");
                let tn = sigma[t as usize].expect("eq head dst bound by body");
                ext.merge_into(sn, tn, bdep);
                return;
            }
        }
        ext.unsupported = true;
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
                let idx = ext.obligations.len();
                ext.obligations.push(Oblig { n, r, fil, dep: bdep.clone(), at });
                if ext.incroblig {
                    ext.node_obligs[n].push(idx);
                    ext.oblig_sat.push(false);
                }
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
    if ext.number {
        RMF_STEPS.with(|c| c.set(0));
    }
    rec_match_flex(ext, body, &mut done, &mut sigma, &dep0, &mut matches);
    if ext.number && RMF_STEPS.with(|c| c.get()) > RMF_STEP_CAP {
        if std::env::var_os("KM_HT_TRACE").is_some() {
            eprintln!("HUGEMATCH cid={} body_len={} join overflow -> bail unsupported", cid, body.len());
        }
        ext.unsupported = true;
        return;
    }
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
    if ext.number {
        RMF_STEPS.with(|c| c.set(0));
    }
    rec_match_flex(ext, body, &mut done, &mut sigma, &dep0, &mut matches);
    if ext.number && RMF_STEPS.with(|c| c.get()) > RMF_STEP_CAP {
        if std::env::var_os("KM_HT_TRACE").is_some() {
            eprintln!("HUGEMATCH cid={} body_len={} join overflow -> bail unsupported", cid, body.len());
        }
        ext.unsupported = true;
        return;
    }
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
    /// Concepts whose last per-concept QoSat saturation had a shared filler
    /// (in-degree ≥ 2 non-root node) and so may carry over-approximated subsumers.
    /// Set by `qo_classify_perconcept`, consumed by the verification pass.
    pc_tainted: Vec<C>,
    /// Candidate subsumptions `(A, B)` derived ONLY by the inverse-augmented
    /// (complete-but-unsound) per-concept saturation and NOT by the forward-only
    /// (sound) one. Each must be confirmed by the complete tableau before it is
    /// kept (sound) or dropped (the inverse over-derivation). Set by
    /// `qo_classify_perconcept`, consumed by the verification pass.
    pc_candidates: Vec<(C, C)>,
    /// Candidate unsatisfiable concepts seen only by the inverse-augmented run —
    /// confirmed with a complete consistency test before being trusted.
    pc_unsat_candidates: Vec<C>,
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
    /// KM_HT_PROF: cumulative microseconds in propagate() and in process_obligations
    /// (the latter inclusive of block_us), to split the per-test wall.
    prop_us: u128,
    oblig_us: u128,
    eager_us: u128,
    obligloop_us: u128,
    obl_iters: u64,
    i2_suf_sum: u128,
    i2_calls: u64,
    i2_full: u64,
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
    /// KM_HT_INCRBLOCK2_CHECK: validate each incremental blocking snapshot against
    /// the full per-pass scan (panics on any divergence). Diagnostic only.
    i2_check: bool,
    /// KM_HT_INCROBLIG: reused buffer for the unblocked-node obligation indices
    /// gathered each pass (sorted to index order for flat-scan-identical expansion).
    oblig_cand: Vec<usize>,
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
    /// `set_fast_tableau`: force the result-identical incremental blocking /
    /// obligation speedups on (re-applied after each per-run `Ext::new`), so
    /// model-builder workers run fast without the `KM_HT_INCRBLOCK2/INCROBLIG`
    /// env flags. Never changes results.
    force_fast: bool,
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

/// KM_HT_QO_INVCOMPOSE (lever 2): eliminate materialised reversed inverse edges by
/// RESOLVING each inverse-bridge clause into its consumers. For an inverse-
/// EQUIVALENT pair `(r,s)` — both `s(x,y)→r(y,x)` and `r(x,y)→s(y,x)` present —
/// every reversed `r`-edge is produced from a forward `s`-edge, so an NF4 consumer
/// `r(u,v) ⊓ D(v) → E(u)` is equivalent, over those reversed edges, to the forward
/// clause obtained by replacing `r(u,v)` with `s(v,u)`. We KEEP the original
/// consumer (it still fires over REAL `r`-edges from `∃r` heads), ADD the composed
/// forward variant (covering the reversed-edge contribution over real `s`-edges),
/// and DROP the two bridges — so the saturation never creates a reversed edge and
/// the inverse contribution becomes a forward ∀/range write the shared-node model
/// can fold per creation role. Applied only to pairs whose inverse-role body
/// occurrences are ALL single-role (no chain); any other pair keeps its bridges
/// unchanged. Sound: each composed clause is a resolvent of a bridge and a
/// consumer; dropping a bridge loses nothing because every reversed-edge consumer
/// has its forward composed counterpart and real (∃-created) edges are untouched.
fn compose_inverse(clauses: &[ClauseRec]) -> Vec<Clause> {
    // bridge `s(a,b) → r(b,a)` ⇒ r ⟸ s (a reversed r-edge comes from an s-edge).
    let mut bridge_src: HashMap<R, Vec<R>> = HashMap::new();
    let bridge_of = |c: &Clause| -> Option<(R, R)> {
        if c.body.len() == 1 && c.head.len() == 1 {
            if let (Atom::Role { r: sr, s: ba, t: bb }, Atom::Role { r: rr, s: hs, t: ht }) =
                (&c.body[0], &c.head[0])
            {
                if *hs == *bb && *ht == *ba && *sr != *rr {
                    return Some((*rr, *sr)); // r ⟸ s
                }
            }
        }
        None
    };
    for (c, _, _) in clauses {
        if let Some((r, s)) = bridge_of(c) {
            bridge_src.entry(r).or_default().push(s);
        }
    }
    // inverse-equivalent pairs: r⟸s AND s⟸r.
    let mut inv_of: HashMap<R, R> = HashMap::new();
    for (&r, ss) in &bridge_src {
        for &s in ss {
            if bridge_src.get(&s).map_or(false, |v| v.contains(&r)) {
                inv_of.insert(r, s);
            }
        }
    }
    // a pair is composable iff EVERY clause with r-or-s in its body is single-role.
    let mut bad: HashSet<R> = HashSet::new();
    for (c, _, _) in clauses {
        let roles: Vec<R> = c
            .body
            .iter()
            .filter_map(|a| if let Atom::Role { r, .. } = a { Some(*r) } else { None })
            .collect();
        if roles.len() > 1 {
            for r in roles {
                if inv_of.contains_key(&r) {
                    bad.insert(r);
                    if let Some(&s) = inv_of.get(&r) {
                        bad.insert(s);
                    }
                }
            }
        }
    }
    let composable = |r: R| inv_of.contains_key(&r) && !bad.contains(&r);
    if std::env::var_os("KM_HT_TRACE").is_some() {
        let n_bridges: usize = clauses.iter().filter(|(c, _, _)| bridge_of(c).is_some()).count();
        let n_inv = inv_of.len();
        let n_bad = bad.len();
        // single-role-body consumers of an inverse role (prop-shape ∀; composable)
        // vs multi-role-body consumers (chains; need the reversed edge).
        let mut single_cons = 0usize;
        let mut multi_cons = 0usize;
        for (c, _, _) in clauses {
            if bridge_of(c).is_some() {
                continue;
            }
            let rb: Vec<R> = c.body.iter().filter_map(|a| if let Atom::Role { r, .. } = a { Some(*r) } else { None }).collect();
            let touches_inv = rb.iter().any(|r| inv_of.contains_key(r));
            if touches_inv {
                if rb.len() == 1 {
                    single_cons += 1;
                } else {
                    multi_cons += 1;
                }
            }
        }
        eprintln!(
            "INVCOMPOSE-DIAG bridges={} inv_pairs={} bad_roles={} single_role_consumers={} multi_role_consumers={}",
            n_bridges, n_inv, n_bad, single_cons, multi_cons
        );
    }
    // One-directional bridge composition (covers e.g. 7914's 2 one-way bridges the
    // bidirectional `inv_of` misses). A consequent role `r` of a bridge `s(a,b)→r(b,a)`
    // whose edges come ONLY from that bridge (not otherwise produced) and that is only
    // single-role-consumed (never in a multi-role/chain body) can be composed away:
    // its single-role consumers fire over the forward `s`-edge swapped, and the bridge
    // is dropped — no reversed `r`-edge is ever created. Sound: `r`-edges are EXACTLY
    // the reversed `s`-edges when the bridge is `r`'s only producer.
    let mut multi_bodied: HashSet<R> = HashSet::new();
    let mut otherwise_produced: HashSet<R> = HashSet::new();
    for (c, _, _) in clauses {
        let is_bridge = bridge_of(c).is_some();
        let rb: Vec<R> = c.body.iter().filter_map(|a| if let Atom::Role { r, .. } = a { Some(*r) } else { None }).collect();
        if rb.len() > 1 {
            for r in rb {
                multi_bodied.insert(r);
            }
        }
        if !is_bridge {
            for h in &c.head {
                match h {
                    Atom::Role { r, .. } => { otherwise_produced.insert(*r); }
                    Atom::Exists { r, .. } => { otherwise_produced.insert(*r); }
                    _ => {}
                }
            }
        }
    }
    let mut oneway: HashMap<R, R> = HashMap::new();
    // KM_HT_QO_INVCHAIN (port #2, in-pass inverse for CHAIN consumers): relax the
    // single-role-body restriction. A consequent role `r` of a bridge `s(a,b)→r(b,a)`
    // whose r-edges come SOLELY from that one bridge (single source) and that is NOT
    // otherwise produced (no real `∃ r` / head `r` — so every r-edge is exactly a
    // reversed s-edge) can be composed away EVEN WHEN consumed in a multi-role/chain
    // body: replacing `r(u,v)` with `s(v,u)` in any body is sound (identical edge
    // set, the other body atoms unchanged), and the bridge is dropped so NO reversed
    // r-edge is ever materialised. This is exactly what 9724 needs — its 674
    // multi-role consumers were the only thing forcing 2.5M reversed edges. Without
    // INVCHAIN we keep the conservative single-role-only behaviour.
    let invchain = std::env::var_os("KM_HT_QO_INVCHAIN").is_some();
    // Gated behind KM_HT_QO_INVONEWAY / KM_HT_QO_INVCHAIN so neither can change the
    // established INVCOMPOSE (router) behaviour unless explicitly enabled.
    if std::env::var_os("KM_HT_QO_INVONEWAY").is_some() || invchain {
        for (&r, ss) in &bridge_src {
            if inv_of.contains_key(&r) && !invchain {
                continue; // bidirectional pair handled by `composable` below
            }
            // INVCHAIN relaxes the multi-role exclusion (the whole point of port #2);
            // INVONEWAY keeps it. `otherwise_produced` is a SOUNDNESS gate for both:
            // a real `∃ r` edge would be missed by the swap.
            if (!invchain && multi_bodied.contains(&r)) || otherwise_produced.contains(&r) {
                continue;
            }
            // single source: r-edges come solely from this one s-bridge.
            let mut uniq: Vec<R> = ss.clone();
            uniq.sort_unstable();
            uniq.dedup();
            if uniq.len() == 1 {
                oneway.insert(r, uniq[0]);
            }
        }
    }
    if std::env::var_os("KM_HT_TRACE").is_some() {
        eprintln!(
            "INVCOMPOSE-ONEWAY composing {} bridge roles (invchain={})",
            oneway.len(),
            invchain
        );
    }
    let mut out: Vec<Clause> = Vec::with_capacity(clauses.len() + clauses.len() / 4);
    for (c, _, _) in clauses {
        // drop a bridge whose pair we are composing (both directions).
        if let Some((r, s)) = bridge_of(c) {
            if composable(r) && composable(s) && inv_of.get(&r) == Some(&s) {
                continue;
            }
            if oneway.contains_key(&r) {
                continue; // one-directional: bridge dropped, consumers composed below
            }
        }
        out.push(c.clone());
        // add the composed forward variant for a single composable body role atom.
        let body_roles: Vec<(usize, R, Var, Var)> = c
            .body
            .iter()
            .enumerate()
            .filter_map(|(i, a)| {
                if let Atom::Role { r, s, t } = a {
                    Some((i, *r, *s, *t))
                } else {
                    None
                }
            })
            .collect();
        // General oneway/chain composition: if the body contains ANY oneway role
        // atom (single- or multi-role body), add a variant with EVERY oneway atom
        // swapped to its forward source edge `s(t,s)`. Sound because each such r is
        // purely virtual (single-source, not otherwise produced ⇒ all r-edges are
        // reversed s-edges); the original clause is kept but is dead (no real
        // r-edge survives the dropped bridge). This subsumes the old single-role
        // oneway branch and adds the multi-role/chain case (port #2).
        let has_oneway = body_roles.iter().any(|(_, r, _, _)| oneway.contains_key(r));
        if has_oneway {
            let mut nb = c.body.clone();
            for a in nb.iter_mut() {
                if let Atom::Role { r, s, t } = *a {
                    if let Some(&sv) = oneway.get(&r) {
                        *a = Atom::Role { r: sv, s: t, t: s };
                    }
                }
            }
            out.push(Clause { body: nb, head: c.head.clone() });
        }
        if body_roles.len() == 1 {
            let (idx, r, u, v) = body_roles[0];
            if composable(r) {
                let s = inv_of[&r];
                let mut nb = c.body.clone();
                // r(u,v) ⟸ s(v,u): fire the same consequence over the forward s-edge.
                nb[idx] = Atom::Role { r: s, s: v, t: u };
                out.push(Clause { body: nb, head: c.head.clone() });
            }
        }
    }
    out
}

/// Count clauses that are inverse/symmetric BRIDGES (single role head whose two
/// args are swapped relative to a body role atom: `R(s,t) → R'(t,s)`). The
/// forward-only QO pass (`skip_inverse = true`) DROPS such clauses, so a residual
/// bridge means the forward closure loses a real inverse contribution and a
/// "clean global pass" can no longer be trusted as COMPLETE. After
/// `compose_inverse` this should be 0 on a fully-composable ont (every inverse
/// consumer turned into a forward clause), which is the precondition for the
/// INVCOMPOSE + write-mode global pass to certify soundly.
fn count_inverse_bridges(clauses: &[ClauseRec]) -> usize {
    clauses
        .iter()
        .filter(|(c, _, _)| {
            !c.body.is_empty()
                && c.head.len() == 1
                && matches!(&c.head[0], Atom::Role { s: hs, t: ht, .. }
                    if c.body.iter().any(|a| matches!(a, Atom::Role { s, t, .. } if *s == *ht && *t == *hs)))
        })
        .count()
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
    /// Incoming-edge index per node: `in_edges[t]` holds `(role, source)` for
    /// every edge `(source, role, t)`. The elc-style backward-link index — lets
    /// the role-body matcher find a node's predecessors in O(in-degree) instead
    /// of scanning all nodes, the O(#nodes) cost that made QoSat diverge at the
    /// 73k-node scale (the `(None, Some(tn))` case in `match_body`).
    in_edges: Vec<Vec<(R, Node)>>,
    /// shared node for a concept literal (pos and neg both keyed).
    concept_node: HashMap<CLit, Node>,
    /// parked disjunctions: (node, clause_id); re-evaluated as labels grow.
    pending: Vec<(Node, usize)>,
    /// nodes whose own seed is unsatisfiable (local clash, not KB clash).
    node_unsat: HashSet<Node>,
    lit_work: Vec<(Node, CLit)>,
    edge_work: Vec<(Node, R, Node)>,
    node_work: Vec<Node>,
    /// Trigger-keyed role-clause re-fire worklist (the `complete_roles` engine).
    /// Entry `(cid, n)` means "role clause `cid` is guarded by a concept that
    /// just arrived at `n`, so re-anchor it on `n`'s incident edges." Replaces
    /// the blunt re-queue-all-incident-edges scheme: instead of re-firing EVERY
    /// role clause on every incident edge per literal insert, re-fire only the
    /// clauses whose body actually mentions the newly-inserted concept (elc's
    /// backward-link keying). This is what makes `complete_roles` affordable on
    /// 73k-node SRIF onts, so the global saturation can be a SOUND ELI saturator.
    guard_refire: Vec<(usize, Node)>,
    concept_trig: HashMap<CLit, Vec<usize>>,
    /// Role-body clauses with a single role atom `R(s,t)` whose ONLY adjacent
    /// concept guard sits on the TARGET var, keyed by `(R, that-guard)` — the elc
    /// NF4 `(role, filler-concept)` index. A fresh `R`-edge `(s,t)` fires only the
    /// clauses keyed by `(R, L)` for the concepts `L` actually in `label[t]`,
    /// instead of every clause that merely mentions `R` (the catastrophic
    /// O(#R-clauses)-per-edge cost: on 7581, role 1 has 109k body clauses, so the
    /// old per-edge clone+fire was billions of wasted matches).
    role_tgt_trig: HashMap<(R, CLit), Vec<usize>>,
    /// Same, for the role atom's SOURCE var (a guard on the predecessor).
    role_src_trig: HashMap<(R, CLit), Vec<usize>>,
    /// Role-body clauses with NO concept guard adjacent to their role atom (role
    /// hierarchy `R⊑S`, domain `R(x,y)→C(x)`, or multi-role chains): these depend
    /// only on the edge, so a fresh `R`-edge fires all of `role_noguard[R]`.
    role_noguard: HashMap<R, Vec<usize>>,
    /// elc backward-link rule for pure Horn NF4 `R(x,y) ⊓ D(y) → E(x)`: keyed by
    /// the filler concept `D`, gives `(role R, head E)`. Such a clause's
    /// consequence `E` depends only on `(R, label[filler])`, NOT on which
    /// predecessor `x` we are at — so instead of re-matching it on every one of
    /// the (millions of) incoming edges, we compute `E` ONCE when `D` reaches a
    /// filler node and broadcast it to that node's R-predecessors via `prop`.
    /// Clauses captured here are EXCLUDED from `role_tgt_trig`/`role_guard_trig`
    /// (they are handled solely by the backward-link machinery).
    prop_rule: HashMap<CLit, Vec<(R, CLit)>>,
    /// Materialised backward links: `prop[(R, T)]` is the set of literals every
    /// R-predecessor of node `T` must carry (accumulated as `T`'s label grows via
    /// `prop_rule`). A fresh edge `(X, R, T)` just unions `prop[(R,T)]` into `X` —
    /// O(consequences), no per-edge clause matching.
    prop: HashMap<(R, Node), Vec<CLit>>,
    /// FORWARD-broadcast analog of `prop_rule` (KM_HT_QO_FPROP). Captures the
    /// MIRROR Horn NF4 shape `R(sv,tv) ⊓ D(sv) → E(tv)`: a single role atom, one
    /// concept guard on the role's SOURCE var `sv`, one concept head on the
    /// role's TARGET var `tv`. This is exactly the shape `compose_inverse`
    /// produces when it resolves a bidirectional inverse bridge into a forward
    /// clause (`∃r.D⊑E` over an inverse role `r` becomes `s(v,u) ⊓ D(v) → E(u)`
    /// over the forward partner `s`, head on the s-target). Such a clause's
    /// consequence `E` for a successor depends only on `(R, label[source])`, NOT
    /// on which successor we reach — so it is broadcast forward ONCE per
    /// (source, role) instead of re-matched on every outgoing edge (the per-edge
    /// re-fire is exactly why bare KM_HT_QO_INVCOMPOSE diverged). Keyed by the
    /// source guard `D`; captured clauses are EXCLUDED from the other role
    /// indexes (handled solely by the forward-link machinery).
    fprop_rule: HashMap<CLit, Vec<(R, CLit)>>,
    /// Materialised forward links: `fprop[(R, S)]` is the set of literals every
    /// R-SUCCESSOR of node `S` must carry (accumulated as `S`'s label grows via
    /// `fprop_rule`). A fresh edge `(S, R, T)` just unions `fprop[(R,S)]` into
    /// `T` — O(consequences), no per-edge clause matching. The forward mirror of
    /// `prop`.
    fprop: HashMap<(R, Node), Vec<CLit>>,
    /// KM_HT_QO_FPROP: enable the forward-broadcast capture above. Default off
    /// (the standard backward-only `prop` path is unchanged when off).
    fprop_on: bool,
    /// KM_HT_QO_FCHECK: run the captured head-on-target (inverse-composed)
    /// clauses in CONTAINMENT-CHECK mode (Konclude G1/G3) instead of writing.
    /// MEASURED 2026-06-23: writing the composed head `E` to the shared
    /// successor node over-derives grossly (the forward mirror of the reversed-
    /// edge conflation — 7581 blows to 1.34 GB). Konclude never writes such an
    /// operand as a subsumer; it reads subsumers from self-nodes (G1) and uses
    /// the operand only to decide criticality (G3). So under `fcheck` the
    /// captured broadcast does NOT add `E` to the successor — it records a
    /// deferred obligation (`kp_check1`) that `kp_finalize` verifies against the
    /// forward closure. A still-missing obligation marks that node insufficient
    /// (`kp_insuff_nodes`). When NO obligation misses, the (sound) forward
    /// closure is certified COMPLETE — the inverse contributed nothing — and is
    /// returned directly. Implies `fprop_on` (it reuses the same capture).
    fcheck: bool,
    /// Role-body clauses indexed by each concept LITERAL guarding them — the
    /// `complete_roles` trigger index. When `lit` is asserted at a node, the
    /// clauses in `role_guard_trig[lit]` are the only role clauses whose
    /// firability could have changed, so only they are re-anchored on the node's
    /// incident edges (e.g. `D ⊓ R(x,y) → E(x)` from `D ⊑ ∀R⁻.E` is keyed by `D`,
    /// and re-fires when `D` reaches a node that already has an incoming `R`-edge).
    role_guard_trig: HashMap<CLit, Vec<usize>>,
    global: Vec<usize>,
    unsupported: bool,
    open_disj: usize,
    /// Nodes that received a ∀-style (non-anchor-var) concept head this
    /// saturation. Combined with in-degree ≥ 2 (shared filler) this is the
    /// precondition for cross-context pollution → taint the seed for re-verify.
    /// Only populated when `track_forall` is set (the verify path), so the fast
    /// path pays nothing.
    forall_nodes: HashSet<Node>,
    track_forall: bool,
    /// trail for the residue-test DFS (branching over the shared model). Each
    /// entry records a mutation to undo on backtrack.
    trail: Vec<QoUndo>,
    tracing: bool,
    /// When set, asserting a literal at `n` re-queues `n`'s incident edges so
    /// role-body clauses re-fire against the updated label. Without it a role
    /// clause (e.g. `∀r.C` = `Forall(x) ∧ r(x,y) → C(y)`) only fires when the
    /// EDGE is added, missing the case where the guard concept arrives at the
    /// node AFTER the edge — a completeness gap that does not matter for the
    /// over-approximating global probe (`saturate_global`, harvest) but is
    /// required for the per-concept gate to be a COMPLETE Horn-SRIF saturator.
    /// Off by default so `saturate_global` / M3 harvest behaviour is unchanged.
    complete_roles: bool,
    /// Node cap for `saturate` (single-seed). Default `QO_NODE_CAP` (tuned for
    /// the tiny 5303-family residue tests); the per-concept gate raises it since
    /// one concept's closure can legitimately span a large slice of the ontology.
    node_cap: usize,
    /// Konclude-style role-keyed range folding. A range/∀ write `R(x,y)→C(y)`
    /// must fold per the successor's CREATION ROLE, never onto a concept-only
    /// shared filler — the port of Konclude's
    /// `getRoleSuccessorALLConceptExtensionData(creationRole)`
    /// (CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp:960).
    /// `range_class[r]` is `r`'s effective-range class id (0 = no range; roles
    /// with identical effective range share an id, so range-free ∃ still share
    /// ONE filler node — the old behaviour). A filler for `∃r.B` is keyed by
    /// `(B, range_class[r])`, so an `r`-range write lands only on `r`-class
    /// fillers. This kills the cross-role filler pollution that produced the 106
    /// spurious subsumptions on 7581 (two roles' ranges landing on one shared
    /// `node(B)` and being misread for the wrong role).
    range_class: HashMap<R, u32>,
    /// Concept set per range class (index = class id; 0 = empty). A non-anchor
    /// concept write is SOUND iff the written literal is already in the target
    /// node's class set (so it was going to be forced there anyway); otherwise it
    /// is Konclude's "critical ALL" case and trips `qo_insufficient`.
    class_set: Vec<HashSet<CLit>>,
    /// Role-keyed filler nodes: `(filler-concept, range-class) → node`. Only used
    /// for classes ≠ 0; class-0 fillers share the concept self-node (unchanged).
    filler_node: HashMap<(CLit, u32), Node>,
    /// Per-node creation range-class (parallel to `label`); 0 for self/root nodes.
    node_range: Vec<u32>,
    /// Set when a role-conditional concept write (a ∀/range head on a non-anchor
    /// var) lands on a node whose creation class does not already cover it — the
    /// residue Konclude routes to the complete tableau
    /// (`isCriticalALLConceptDescriptorInsufficient`). The per-concept gate flags
    /// such seeds for sound re-verification; on a pure-range ont (7581) the
    /// role-keyed fillers absorb every range write, so this never fires.
    qo_insufficient: bool,
    /// KPSet (Konclude G2/G3 port, `KM_HT_QO_KPSET`). When set, inverse-bridge
    /// clauses are KEPT (their back-edges are created and recorded in
    /// `inv_edges`), but every concept-head write whose firing matched an
    /// inverse back-edge becomes a CONTAINMENT CHECK instead of a write — the
    /// port of Konclude's `isCriticalALLConceptDescriptorInsufficient`
    /// (CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp:3451):
    /// the would-be operand is never added to the (shared) target node; if the
    /// target already carries it (the forward closure forced it anyway) the
    /// check passes silently, otherwise `kp_insufficient` is raised and the
    /// concept is routed to the complete tableau. Because nothing is written
    /// across an inverse edge, the cross-concept shared-filler conflation (the
    /// 6.5M spurious facts on 7581) cannot form and the saturation stays
    /// forward-only fast — yet it is certified COMPLETE whenever no check missed
    /// (`!kp_insufficient`), which on 7581 is every concept (forward = gold).
    kpset: bool,
    /// Edges created by an inverse/symmetric bridge clause (`R(x,y) → S(y,x)`):
    /// the model-specific reversed back-edges. A rule firing anchored on such an
    /// edge has its concept-head writes turned into containment checks under
    /// `kpset`. Empty (and unused) when `kpset` is off.
    inv_edges: HashSet<(Node, R, Node)>,
    /// Clause ids of the inverse/symmetric bridge clauses (single role head with
    /// args swapped versus a body role atom). Populated in `new_opts`; used to
    /// tag the back-edges they create as `inv_edges`.
    inv_bridge_cid: HashSet<usize>,
    /// Raised (under `kpset`) when an inverse-anchored containment check missed:
    /// the inverse contribution would add a concept the forward closure did not
    /// derive, so this seed/concept is INSUFFICIENT and needs the complete
    /// tableau. Stays false on inverse-inert onts (7581) → forward label is the
    /// certified-complete answer.
    kp_insufficient: bool,
    /// Diagnostic count of inverse-anchored containment checks that missed
    /// (KM_HT_TRACE). Zero ⇒ inverse is non-load-bearing for this saturation.
    kp_miss: u64,
    /// Concepts that appear as a BODY GUARD in some clause (positive concept atom
    /// in a body). Konclude's saturation marks a node insufficient for an
    /// inverse/∀-propagated operand only when that operand can still TRIGGER
    /// something; an operand that never guards any clause body is inert (it can
    /// neither fire a forward rule nor — since subsumers are read from self-nodes,
    /// G1 — contribute a named subsumer), so a containment miss on it is NOT a
    /// completeness threat. `KM_HT_QO_KPGUARD` restricts `kp_insufficient` to
    /// guard-concept misses (sound: a non-guard operand dropped at a node loses
    /// nothing derivable). Built once in `new_opts`.
    kp_guard: std::rc::Rc<HashSet<C>>,
    kp_guard_only: bool,
    /// KM_HT_QO_SAT: Konclude-style separate role-keyed successor nodes. When set,
    /// `ensure_filler` ALWAYS allocates a fresh node keyed by `(filler-concept,
    /// role)` (never the concept's classification self-node, as it does when
    /// `range_class == 0`). Inverse/∀ writes then land on these successor nodes,
    /// never on a concept's self-node, so the self-node subsumer set (read for
    /// classification, G1) is never inverse-polluted — the structural precondition
    /// that lets the guard-criticality above be a sound completeness certificate.
    sat_mode: bool,
    /// Parallel to `label`: true for separate ∃-successor (filler) nodes created
    /// under `sat_mode`, false for concept self-nodes / root. An inverse write to a
    /// non-filler (self-node) is always insufficient; to a filler it follows the
    /// guard rule.
    is_filler: Vec<bool>,
    /// `sat_mode` role-keyed filler nodes: `(filler-concept, role) → node`.
    sat_filler: HashMap<(CLit, R), Node>,
    /// Deferred single-target containment checks `(node, lit)` collected during
    /// the saturation. Konclude runs the criticality test only AFTER the
    /// deterministic saturation reaches fixpoint (`checkCriticalIndividuals`), so
    /// a forward fact derived later still counts as present; checking eagerly
    /// would miss it spuriously. `kp_finalize` re-checks these against the final
    /// labels. Deduped (a `HashSet`) so the inverse firings don't blow it up.
    kp_check1: HashSet<(Node, CLit)>,
    /// Deferred multi-disjunct checks (an inverse-anchored disjunctive head):
    /// satisfied at fixpoint iff at least one `(node, lit)` is present.
    kp_checkn: Vec<Vec<(Node, CLit)>>,
    /// Nodes at which a containment check MISSED (per-node insufficiency, the
    /// Konclude granularity — a global bool defers the whole classification even
    /// when only shared-filler nodes are insufficient). A query concept whose
    /// self-node is not reverse-reachable from any of these is unaffected by the
    /// inverse and can be certified from the forward closure alone.
    kp_insuff_nodes: HashSet<Node>,
    /// KM_HT_QO_CARD: at-most / functional cardinality produces Eq-heads (a forced
    /// successor merge the shared-node saturation cannot represent). Instead of
    /// bailing the whole pass `unsupported` (legacy), mark the anchor node
    /// INSUFFICIENT and continue — Konclude's deferral — so the pass completes for
    /// every cardinality-unaffected concept and the per-node CLEAN split certifies
    /// them from the forward closure (the SHIF throughput onts: 9724 etc.).
    card_defer: bool,
    /// Per-branch DFS deadline (ms) and depth cap for `qo_branch_dfs`. Defaults
    /// match the historical hardcoded 4000ms / depth 64; the residue model-reuse
    /// (port #1) needs a more generous budget to complete the open core of a
    /// disjunction-heavy ont (7914: 67 disjunctions), tunable via KM_HT_QO_RES_MS.
    branch_ms: u128,
    branch_depth: u32,
    /// Set while a residue verify (`qo_residue_test`) is branching a subtree that
    /// touched a deferred-insufficient node (cardinality Eq-head / critical-ALL).
    /// The shared-model branch cannot decide such a concept soundly, so the test
    /// returns None (defer) instead of a possibly-wrong verdict.
    residue_tainted: bool,
    /// KM_HT_QO_RESIDUE_FORCE (DIAGNOSTIC, unsound): bypass the residue soundness
    /// gate and suppress tainting, so the residue model-reuse runs to completion
    /// even when an insufficient (∀/cardinality) core is present. Used only to
    /// MEASURE whether that core actually perturbs the final subsumptions for a
    /// given ont (diff vs gold). Never a production answer.
    residue_unsafe: bool,
}

/// undoable mutation for the residue-test DFS.
enum QoUndo {
    Lit(Node, CLit),
    Edge(Node, R, Node),
    NodeNew,
    Unsat(Node),
    Pending(usize), // pending grew to this len
    ConceptNode(CLit),
    Prop(R, Node, usize), // prop[(R,Node)] grew to this len
    Fprop(R, Node, usize), // fprop[(R,Node)] grew to this len
    Filler(CLit, u32),    // filler_node[(CLit, class)] was created
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
        QoSat::new_opts(
            clauses,
            std::env::var_os("KM_HT_QO_NOINV").is_some(),
            std::env::var_os("KM_HT_QO_FPROP").is_some(),
        )
    }

    /// `skip_inverse`: drop inverse/symmetric bridging clauses (a single role
    /// head with args SWAPPED relative to a body role atom). The shared-node
    /// saturation reads a successor's runtime label across such back-edges, which
    /// is a model-specific (unsound) read; a forward-only saturation
    /// (`skip_inverse = true`) is SOUND but may miss inverse-entailed
    /// subsumptions, so the per-concept gate runs both and verifies the
    /// difference with the complete tableau.
    fn new_opts(clauses: &'a [ClauseRec], skip_inverse: bool, fprop_on: bool) -> QoSat<'a> {
        // `fcheck` reuses the forward-broadcast capture but in containment-check
        // mode, so it implies `fprop_on`.
        let fcheck = std::env::var_os("KM_HT_QO_FCHECK").is_some();
        let fprop_on = fprop_on || fcheck;
        let mut concept_trig: HashMap<CLit, Vec<usize>> = HashMap::new();
        let mut role_tgt_trig: HashMap<(R, CLit), Vec<usize>> = HashMap::new();
        let mut role_src_trig: HashMap<(R, CLit), Vec<usize>> = HashMap::new();
        let mut role_noguard: HashMap<R, Vec<usize>> = HashMap::new();
        let mut role_guard_trig: HashMap<CLit, Vec<usize>> = HashMap::new();
        let mut prop_rule: HashMap<CLit, Vec<(R, CLit)>> = HashMap::new();
        // KM_HT_QO_NOPROP (diagnostic): route NF4 through the per-edge path instead
        // of the backward-link `prop` store, to isolate whether `prop` is a source
        // of over-approximation. Read once (not per clause).
        let no_prop = std::env::var_os("KM_HT_QO_NOPROP").is_some();
        let mut fprop_rule: HashMap<CLit, Vec<(R, CLit)>> = HashMap::new();
        let no_inv = skip_inverse;
        // Body-guard concepts: any concept id occurring in a clause BODY (either
        // polarity). An inverse/∀ operand that is NOT a body guard can trigger
        // nothing further, so a containment miss on it is inert (see `kp_guard`).
        let mut kp_guard_set: HashSet<C> = HashSet::new();
        for rec in clauses.iter() {
            for a in &rec.1 {
                if let Atom::Concept { lit, .. } = a {
                    kp_guard_set.insert(lit.c);
                }
            }
        }
        // --- Konclude role-keyed range folding setup. ------------------------
        // direct_range[r] = concepts a range/∀ clause `R(x,y)→C(y)` forces on any
        // r-successor when there is NO source-side guard (target guards are
        // filler-local, so the write is still purely role-conditional and folds
        // the same way). superrole[r] = direct super-roles from hierarchy clauses
        // `R(x,y)→S(x,y)`. The effective range of r folds in all super-role
        // ranges (a hierarchy S-edge fires range(S) at runtime, so the filler key
        // must account for it: same key ⇒ same forced label ⇒ sound sharing).
        let mut direct_range: HashMap<R, Vec<CLit>> = HashMap::new();
        let mut superrole: HashMap<R, Vec<R>> = HashMap::new();
        for rec in clauses.iter() {
            let body = &rec.1;
            let head = &rec.0.head;
            let roles: Vec<(R, Var, Var)> = body
                .iter()
                .filter_map(|a| match a {
                    Atom::Role { r, s, t } => Some((*r, *s, *t)),
                    _ => None,
                })
                .collect();
            if roles.len() != 1 || head.len() != 1 {
                continue;
            }
            let (r, sv, tv) = roles[0];
            match head[0] {
                Atom::Role { r: hr, s: hs, t: ht } if hs == sv && ht == tv => {
                    superrole.entry(r).or_default().push(hr);
                }
                Atom::Concept { lit, t } if t == tv => {
                    // range/∀ fold candidate: a concept head on the role TARGET
                    // var. Source-guarded (`D(sv) ⊓ R → C(tv)`) writes are
                    // predecessor-dependent — NOT role-foldable — so exclude them;
                    // they trip `qo_insufficient` at fire time (sound fallback).
                    let src_guard = body
                        .iter()
                        .any(|a| matches!(a, Atom::Concept { t, .. } if *t == sv));
                    if !src_guard {
                        direct_range.entry(r).or_default().push(lit);
                    }
                }
                _ => {}
            }
        }
        // effective range per role = direct ∪ transitive super-role direct.
        let mut all_roles: Vec<R> = direct_range.keys().copied().collect();
        for (r, sup) in &superrole {
            all_roles.push(*r);
            all_roles.extend(sup.iter().copied());
        }
        all_roles.sort_unstable();
        all_roles.dedup();
        // intern effective-range sets → class ids (0 = empty), so roles with the
        // same effective range share one filler-node class.
        let mut class_of_set: HashMap<Vec<CLit>, u32> = HashMap::new();
        let mut range_class: HashMap<R, u32> = HashMap::new();
        let mut class_set: Vec<HashSet<CLit>> = vec![HashSet::new()];
        let mut next_class: u32 = 1;
        for &r in &all_roles {
            let mut seen: Vec<R> = vec![r];
            let mut stack = vec![r];
            while let Some(x) = stack.pop() {
                if let Some(sup) = superrole.get(&x) {
                    for &s in sup {
                        if !seen.contains(&s) {
                            seen.push(s);
                            stack.push(s);
                        }
                    }
                }
            }
            let mut er: Vec<CLit> = Vec::new();
            for s in seen {
                if let Some(d) = direct_range.get(&s) {
                    er.extend(d.iter().copied());
                }
            }
            er.sort_unstable_by_key(|l| (l.c, l.neg));
            er.dedup();
            if er.is_empty() {
                continue;
            }
            let id = *class_of_set.entry(er.clone()).or_insert_with(|| {
                let c = next_class;
                next_class += 1;
                class_set.push(er.iter().copied().collect());
                c
            });
            range_class.insert(r, id);
        }
        let mut global = Vec::new();
        let mut inv_bridge_cid: HashSet<usize> = HashSet::new();
        for (cid, rec) in clauses.iter().enumerate() {
            let body = &rec.1;
            let head = &rec.0.head;
            if body.is_empty() {
                global.push(cid);
                continue;
            }
            let has_role = body.iter().any(|a| matches!(a, Atom::Role { .. }));
            if has_role {
                // Record inverse/symmetric bridge clauses (single role head whose
                // args are SWAPPED vs a body role atom) regardless of `no_inv`,
                // so the KPSet path can tag the back-edges they create as
                // `inv_edges` (containment-check, never write).
                if head.len() == 1 {
                    if let Atom::Role { s: hs, t: ht, .. } = head[0] {
                        if body
                            .iter()
                            .any(|a| matches!(a, Atom::Role { s, t, .. } if *s == ht && *t == hs))
                        {
                            inv_bridge_cid.insert(cid);
                        }
                    }
                }
                // KM_HT_QO_NOINV (diagnostic): skip inverse/symmetric bridging
                // clauses — a single role head whose args are SWAPPED relative to
                // a body role atom (`R(s,t) → R'(t,s)`). These create model-
                // specific back-edges into shared concept nodes; the NF4 rules
                // then read those shared labels across the back-edge, which is the
                // suspected source of the 7581 spurious subsumptions. Excluding
                // them from every role index makes them inert.
                if no_inv && inv_bridge_cid.contains(&cid) {
                    continue;
                }
                // elc backward-link capture: pure Horn NF4 `R(sv,tv) ⊓ D(tv) → E(sv)`
                // (body = exactly the role atom + one target-side concept guard,
                // head = exactly one concept on the role's SOURCE var). Its
                // consequence `E` for a predecessor depends only on `(R, D)`, so it
                // is handled by the `prop` broadcast, not per-edge matching. Such a
                // clause is EXCLUDED from the other role indexes (handled solely
                // here) to avoid double-firing.
                if !no_prop && body.len() == 2 && head.len() == 1 {
                    let role_atom = body.iter().find_map(|a| match a {
                        Atom::Role { r, s, t } => Some((*r, *s, *t)),
                        _ => None,
                    });
                    if let Some((r, sv, tv)) = role_atom {
                        let guard = body.iter().find_map(|a| match a {
                            Atom::Concept { lit, t } if *t == tv => Some(*lit),
                            _ => None,
                        });
                        let hd = match head[0] {
                            Atom::Concept { lit, t } if t == sv => Some(lit),
                            _ => None,
                        };
                        if let (Some(g), Some(e)) = (guard, hd) {
                            prop_rule.entry(g).or_default().push((r, e));
                            continue;
                        }
                    }
                }
                // FORWARD-broadcast capture (KM_HT_QO_FPROP), the mirror of the
                // `prop_rule` block above: pure Horn NF4 `R(sv,tv) ⊓ D(sv) → E(tv)`
                // — the role atom + ONE concept guard on the role's SOURCE var +
                // ONE concept head on the role's TARGET var. Its consequence `E`
                // for a successor depends only on `(R, D)`, so it is handled by the
                // `fprop` forward broadcast, not per-edge matching, and EXCLUDED
                // from the other role indexes. This is the shape `compose_inverse`
                // emits for resolved inverse bridges.
                if fprop_on && body.len() == 2 && head.len() == 1 {
                    let role_atom = body.iter().find_map(|a| match a {
                        Atom::Role { r, s, t } => Some((*r, *s, *t)),
                        _ => None,
                    });
                    if let Some((r, sv, tv)) = role_atom {
                        let guard = body.iter().find_map(|a| match a {
                            Atom::Concept { lit, t } if *t == sv => Some(*lit),
                            _ => None,
                        });
                        let hd = match head[0] {
                            Atom::Concept { lit, t } if t == tv => Some(lit),
                            _ => None,
                        };
                        if let (Some(g), Some(e)) = (guard, hd) {
                            fprop_rule.entry(g).or_default().push((r, e));
                            continue;
                        }
                    }
                }
                // Index this role clause by each DISTINCT concept guard in its
                // body, for `complete_roles` trigger-keyed re-firing (the
                // guard-arrives-after-edge half of completeness). Deduped per
                // (lit, cid).
                let mut lits_seen: Vec<CLit> = Vec::new();
                for a in body {
                    if let Atom::Concept { lit, .. } = a {
                        if !lits_seen.contains(lit) {
                            lits_seen.push(*lit);
                            role_guard_trig.entry(*lit).or_default().push(cid);
                        }
                    }
                }
                // Edge-add firing index (the elc NF4 keying): a single-role-atom
                // clause is anchored by ONE adjacent concept guard — preferring a
                // guard on the role atom's TARGET (the ∃-filler concept, the most
                // selective key), else the SOURCE; with no adjacent guard it goes
                // to `role_noguard` (fires on every edge of its role). A guard on
                // the OTHER side is re-checked by `match_body` when the clause
                // fires, so keying by one guard is sound (it can only fire when
                // that guard holds). Multi-role clauses (chains) go to
                // `role_noguard` for each distinct role — rare here, so the
                // unfiltered fire is acceptable.
                let role_atoms: Vec<(R, Var, Var)> = body
                    .iter()
                    .filter_map(|a| match a {
                        Atom::Role { r, s, t } => Some((*r, *s, *t)),
                        _ => None,
                    })
                    .collect();
                if role_atoms.len() == 1 {
                    let (r, sv, tv) = role_atoms[0];
                    let mut tgt_guard: Option<CLit> = None;
                    let mut src_guard: Option<CLit> = None;
                    for a in body {
                        if let Atom::Concept { lit, t } = a {
                            if *t == tv && tgt_guard.is_none() {
                                tgt_guard = Some(*lit);
                            } else if *t == sv && src_guard.is_none() {
                                src_guard = Some(*lit);
                            }
                        }
                    }
                    if let Some(l) = tgt_guard {
                        role_tgt_trig.entry((r, l)).or_default().push(cid);
                    } else if let Some(l) = src_guard {
                        role_src_trig.entry((r, l)).or_default().push(cid);
                    } else {
                        role_noguard.entry(r).or_default().push(cid);
                    }
                } else {
                    let mut roles_seen: Vec<R> = Vec::new();
                    for (r, _, _) in &role_atoms {
                        if !roles_seen.contains(r) {
                            roles_seen.push(*r);
                            role_noguard.entry(*r).or_default().push(cid);
                        }
                    }
                }
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
            in_edges: Vec::new(),
            concept_node: HashMap::new(),
            pending: Vec::new(),
            node_unsat: HashSet::new(),
            lit_work: Vec::new(),
            edge_work: Vec::new(),
            node_work: Vec::new(),
            guard_refire: Vec::new(),
            concept_trig,
            role_tgt_trig,
            role_src_trig,
            role_noguard,
            role_guard_trig,
            prop_rule,
            prop: HashMap::new(),
            fprop_rule,
            fprop: HashMap::new(),
            fprop_on,
            fcheck,
            forall_nodes: HashSet::new(),
            track_forall: false,
            global,
            unsupported: false,
            open_disj: 0,
            trail: Vec::new(),
            tracing: false,
            complete_roles: false,
            node_cap: QO_NODE_CAP,
            range_class,
            class_set,
            filler_node: HashMap::new(),
            node_range: Vec::new(),
            qo_insufficient: false,
            kpset: false,
            inv_edges: HashSet::new(),
            inv_bridge_cid,
            kp_insufficient: false,
            kp_miss: 0,
            kp_check1: HashSet::new(),
            kp_checkn: Vec::new(),
            kp_insuff_nodes: HashSet::new(),
            kp_guard: std::rc::Rc::new(kp_guard_set),
            kp_guard_only: std::env::var_os("KM_HT_QO_KPGUARD").is_some(),
            sat_mode: std::env::var_os("KM_HT_QO_SAT").is_some(),
            is_filler: Vec::new(),
            sat_filler: HashMap::new(),
            card_defer: std::env::var_os("KM_HT_QO_CARD").is_some(),
            branch_ms: std::env::var("KM_HT_QO_RES_MS")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(4000u128),
            branch_depth: std::env::var("KM_HT_QO_RES_DEPTH")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(64u32),
            residue_tainted: false,
            residue_unsafe: std::env::var_os("KM_HT_QO_RESIDUE_FORCE").is_some(),
        }
    }

    /// Clear the per-saturation model state (labels, edges, worklists, parked
    /// disjunctions, clashes, trail) while KEEPING the immutable clause indexes
    /// (`concept_trig`, the role_*_trig edge indexes, `global`) and config flags.
    /// Lets the
    /// per-concept gate run one fresh single-seed saturation per query concept
    /// without rebuilding the O(#clauses) indexes 73k times.
    fn reset(&mut self) {
        self.label.clear();
        self.out_edges.clear();
        self.in_edges.clear();
        self.concept_node.clear();
        self.pending.clear();
        self.node_unsat.clear();
        self.lit_work.clear();
        self.edge_work.clear();
        self.node_work.clear();
        self.guard_refire.clear();
        self.prop.clear();
        self.fprop.clear();
        self.forall_nodes.clear();
        self.filler_node.clear();
        self.node_range.clear();
        self.qo_insufficient = false;
        self.inv_edges.clear();
        self.kp_insufficient = false;
        self.kp_miss = 0;
        self.kp_check1.clear();
        self.kp_checkn.clear();
        self.kp_insuff_nodes.clear();
        self.is_filler.clear();
        self.sat_filler.clear();
        self.trail.clear();
        self.unsupported = false;
        self.open_disj = 0;
    }

    fn new_node(&mut self) -> Node {
        let id = self.label.len();
        self.label.push(HashSet::new());
        self.out_edges.push(Vec::new());
        self.in_edges.push(Vec::new());
        self.node_range.push(0);
        self.is_filler.push(false);
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
            // Completeness re-fire: a role-body clause guarded by `lit` on `n`
            // (a ∀-style guard, or an NF4 filler concept, or a `D ⊓ R(x,y) → E(x)`
            // from `D ⊑ ∀R⁻.E`) must re-fire now that `n` carries `lit`. Enqueue
            // only the clauses actually keyed by `lit` (trigger-keyed), to be
            // re-anchored on `n`'s incident edges when the worklist drains — not
            // every role clause on every incident edge. Bounded: only on a genuine
            // label insert, so finitely often per node. This is the elc
            // backward-link keying that makes `complete_roles` affordable at scale.
            if self.complete_roles {
                if let Some(cids) = self.role_guard_trig.get(&lit) {
                    for &cid in cids {
                        self.guard_refire.push((cid, n));
                    }
                }
            }
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

    /// The successor node for `∃r.fil`. For a range-free role (`range_class[r]
    /// == 0`) this is the concept self-node — the old behaviour, so range-free
    /// ontologies are byte-identical. For a role with a range it is a node keyed
    /// by `(fil, range_class[r])`, so `r`'s range writes fold onto an `r`-class
    /// filler and never pollute a different role's successor (Konclude's
    /// per-creation-role ALL-concept extension).
    fn ensure_filler(&mut self, r: R, fil: CLit) -> Node {
        // KM_HT_QO_SAT (Konclude separate successor): always a fresh node keyed by
        // (filler-concept, role), distinct from the concept's classification
        // self-node, so inverse/∀ writes never pollute the self-node subsumers.
        if self.sat_mode {
            if let Some(&n) = self.sat_filler.get(&(fil, r)) {
                return n;
            }
            let n = self.new_node();
            self.is_filler[n] = true;
            self.sat_filler.insert((fil, r), n);
            self.add_lit(n, fil);
            return n;
        }
        let cls = self.range_class.get(&r).copied().unwrap_or(0);
        if cls == 0 {
            return self.concept_node_of(fil);
        }
        if let Some(&n) = self.filler_node.get(&(fil, cls)) {
            return n;
        }
        let n = self.new_node();
        self.node_range[n] = cls;
        self.filler_node.insert((fil, cls), n);
        if self.tracing {
            self.trail.push(QoUndo::Filler(fil, cls));
        }
        self.add_lit(n, fil);
        n
    }

    fn add_edge(&mut self, s: Node, r: R, t: Node) {
        if self.out_edges[s].iter().any(|(rr, tt)| *rr == r && *tt == t) {
            return;
        }
        self.out_edges[s].push((r, t));
        self.in_edges[t].push((r, s));
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
            if guard > 50_000_000 || self.label.len() > self.node_cap {
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
        if self.kpset || self.fcheck {
            self.kp_finalize();
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
        // The shared-node model has one node per (named or anonymous) concept, so
        // the legitimate node count scales with the ontology, not a small constant.
        // QO_NODE_CAP (tuned for the tiny disjunction family) would bail instantly on
        // a real 70k-concept ontology. Scale the cap to the seeded concept count plus
        // generous headroom for ∃-filler / definer nodes.
        let cap = named_concepts.len().saturating_add(500_000).max(QO_NODE_CAP);
        let trace = std::env::var_os("KM_HT_TRACE").is_some();
        if trace {
            eprintln!(
                "QOSAT seeded named={} nodes_after_seed={} cap={}",
                named_concepts.len(),
                self.label.len(),
                cap
            );
        }
        let mut guard = 0u64;
        loop {
            guard += 1;
            if trace && guard % 100 == 0 {
                eprintln!(
                    "QOSAT guard={} nodes={} lit_work={} edge_work={} node_work={} pending={} open_disj={}",
                    guard, self.label.len(), self.lit_work.len(), self.edge_work.len(),
                    self.node_work.len(), self.pending.len(), self.open_disj
                );
            }
            if guard > 50_000_000 || self.label.len() > cap {
                if trace {
                    eprintln!("QOSAT BAIL unsupported guard={} nodes={}", guard, self.label.len());
                }
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
        if self.kpset || self.fcheck {
            self.kp_finalize();
        }
        self.finish_global()
    }

    /// Drain all worklists once: literal-triggered clauses, new-node globals,
    /// edge-triggered role clauses, and harvest obligations.
    fn drain_work(&mut self) {
        while let Some((n, lit)) = self.lit_work.pop() {
            let d = QO_DRAIN.fetch_add(1, Ordering::Relaxed);
            if d > 0 && d % 2_000_000 == 0 && std::env::var_os("KM_HT_TRACE").is_some() {
                eprintln!(
                    "QODRAIN steps={} nodes={} lit_work={} edge_work={} node_work={} pending={}",
                    d, self.label.len(), self.lit_work.len(), self.edge_work.len(),
                    self.node_work.len(), self.pending.len()
                );
            }
            if self.node_unsat.contains(&n) {
                continue;
            }
            // Fire the concept clauses triggered by `lit`. The trigger lists are
            // immutable after `new()`, but a per-pop `.clone()` of a hot lit's
            // list (some concepts trigger tens of thousands of clauses) was a
            // multi-GB allocation churn at the 2M-pop scale. Take the list out of
            // the map (O(1) move, no element copy), iterate, then restore it —
            // `fire_concept_clause` never touches `concept_trig`, so this is safe.
            if let Some(trigs) = self.concept_trig.remove(&lit) {
                for &cid in &trigs {
                    self.fire_concept_clause(cid, n);
                    if self.unsupported {
                        self.concept_trig.insert(lit, trigs);
                        return;
                    }
                }
                self.concept_trig.insert(lit, trigs);
            }
            // elc backward-link broadcast: `lit` arriving at `n` makes `n` a filler
            // whose R-predecessors inherit the NF4 head `e`. Record the link in
            // `prop[(r,n)]` (so edges added later inherit it) and push `e` to all
            // current R-predecessors. Computed once per (filler-concept, role),
            // never re-matched per incoming edge — the whole point of `prop`.
            if let Some(rules) = self.prop_rule.remove(&lit) {
                for &(r, e) in &rules {
                    let old_len = {
                        let entry = self.prop.entry((r, n)).or_default();
                        let ol = entry.len();
                        if !entry.contains(&e) {
                            entry.push(e);
                        }
                        ol
                    };
                    if self.tracing && self.prop[&(r, n)].len() != old_len {
                        self.trail.push(QoUndo::Prop(r, n, old_len));
                    }
                    let preds: Vec<Node> = self.in_edges[n]
                        .iter()
                        .filter(|(rr, _)| *rr == r)
                        .map(|(_, s)| *s)
                        .collect();
                    for x in preds {
                        // KPSet: an NF4 backward link across an inverse back-edge
                        // (x --r--> n) is a containment check, never a write.
                        let via_inv = self.kpset && self.inv_edges.contains(&(x, r, n));
                        self.kp_write(x, e, via_inv);
                        if self.unsupported {
                            self.prop_rule.insert(lit, rules);
                            return;
                        }
                    }
                }
                self.prop_rule.insert(lit, rules);
            }
            // Forward mirror of the backward-link broadcast above: `lit` arriving
            // at `n` makes `n` a SOURCE whose R-successors inherit the NF4 head `e`
            // (from `R(sv,tv) ⊓ lit(sv) → e(tv)`). Record the link in `fprop[(r,n)]`
            // (so edges added later inherit it) and push `e` to all current
            // R-successors. Computed once per (source-concept, role).
            if self.fprop_on {
                if let Some(rules) = self.fprop_rule.remove(&lit) {
                    for &(r, e) in &rules {
                        let old_len = {
                            let entry = self.fprop.entry((r, n)).or_default();
                            let ol = entry.len();
                            if !entry.contains(&e) {
                                entry.push(e);
                            }
                            ol
                        };
                        if self.tracing && self.fprop[&(r, n)].len() != old_len {
                            self.trail.push(QoUndo::Fprop(r, n, old_len));
                        }
                        let succs: Vec<Node> = self.out_edges[n]
                            .iter()
                            .filter(|(rr, _)| *rr == r)
                            .map(|(_, t)| *t)
                            .collect();
                        for t in succs {
                            self.fprop_emit(t, e);
                            if self.unsupported {
                                self.fprop_rule.insert(lit, rules);
                                return;
                            }
                        }
                    }
                    self.fprop_rule.insert(lit, rules);
                }
            }
            if !self.tracing {
                self.eval_parked_at(n);
            }
        }
        while let Some(n) = self.node_work.pop() {
            let e = QO_NODE.fetch_add(1, Ordering::Relaxed);
            if e > 0 && e % 200_000 == 0 && std::env::var_os("KM_HT_TRACE").is_some() {
                eprintln!(
                    "QONODE pops={} global_per_node={} edge_work={} node_work={}",
                    e, self.global.len(), self.edge_work.len(), self.node_work.len()
                );
            }
            if self.node_unsat.contains(&n) {
                continue;
            }
            // Fire every global ⊤-clause on the new node. Index loop, not
            // `self.global.clone()`: cloning the global list once per node was an
            // O(#nodes × |global|) allocation cost at the 73k-node scale.
            let glen = self.global.len();
            for gi in 0..glen {
                let cid = self.global[gi];
                self.fire_concept_clause(cid, n);
                if self.unsupported {
                    return;
                }
            }
        }
        while let Some((s, r, t)) = self.edge_work.pop() {
            let e = QO_EDGE.fetch_add(1, Ordering::Relaxed);
            if e > 0 && e % 200_000 == 0 && std::env::var_os("KM_HT_TRACE").is_some() {
                eprintln!(
                    "QOEDGE pops={} edge_work={} lit_work={} node_work={} nodes={}",
                    e, self.edge_work.len(), self.lit_work.len(),
                    self.node_work.len(), self.label.len()
                );
            }
            // Fire only the role-body clauses that mention this edge's exact
            // role `r`; a clause without `r` in its body is a guaranteed no-op
            // (no body role atom would anchor), so the role index drops only
            // no-ops — result-identical, and clones a tiny per-role bucket
            // instead of the whole role-clause list on every edge.
            // elc backward link: the fresh `r`-edge `(s,t)` inherits everything
            // `t`'s label has already broadcast for role `r` — O(consequences),
            // no clause matching. (The guard-arrives-after-edge direction is the
            // `prop_rule` push in the lit loop.)
            if let Some(es) = self.prop.get(&(r, t)) {
                let es: Vec<CLit> = es.clone();
                // KPSet: if this fresh edge is an inverse back-edge, the inherited
                // backward links are containment checks at `s`, never writes.
                let via_inv = self.kpset && self.inv_edges.contains(&(s, r, t));
                for e in es {
                    self.kp_write(s, e, via_inv);
                    if self.unsupported {
                        return;
                    }
                }
            }
            // Forward mirror: the fresh `r`-edge `(s,t)` inherits everything `s`'s
            // label has already broadcast forward for role `r` — the head-on-target
            // NF4 consequences land on the new successor `t`. O(consequences), no
            // clause matching. (The guard-arrives-after-edge direction is the
            // `fprop_rule` push in the lit loop.)
            if self.fprop_on {
                if let Some(es) = self.fprop.get(&(r, s)) {
                    let es: Vec<CLit> = es.clone();
                    for e in es {
                        self.fprop_emit(t, e);
                        if self.unsupported {
                            return;
                        }
                    }
                }
            }
            // Guard-filtered firing (elc NF4 keying): a fresh `r`-edge `(s,t)`
            // fires only (a) the guardless `r`-clauses, (b) source-guarded
            // clauses whose guard is present at `s`, (c) target-guarded clauses
            // whose guard is present at `t` — NOT every clause mentioning `r`.
            // (Pure Horn NF4 is handled by `prop` above, not here.) Gather first
            // (immutable borrows of the indexes + labels), then fire (mutable).
            // `match_body` re-verifies any non-keyed guard, so this is sound. The
            // guard-arrives-after-edge case is covered by `guard_refire`.
            let mut to_fire: Vec<usize> = Vec::new();
            if let Some(cids) = self.role_noguard.get(&r) {
                to_fire.extend_from_slice(cids);
            }
            if !self.role_src_trig.is_empty() {
                for &lit in &self.label[s] {
                    if let Some(cids) = self.role_src_trig.get(&(r, lit)) {
                        to_fire.extend_from_slice(cids);
                    }
                }
            }
            if !self.role_tgt_trig.is_empty() {
                for &lit in &self.label[t] {
                    if let Some(cids) = self.role_tgt_trig.get(&(r, lit)) {
                        to_fire.extend_from_slice(cids);
                    }
                }
            }
            for cid in to_fire {
                self.fire_role_clause(cid, s, r, t);
                if self.unsupported {
                    return;
                }
            }
        }
        // Trigger-keyed `complete_roles` re-firing: a guard concept arrived at a
        // node that may already have incident edges; re-anchor the keyed role
        // clause on every incident edge (both directions). `fire_role_clause`
        // re-checks the role + the concept guards, so this only derives genuinely
        // new consequences. This is the half of inverse/∀-role completeness that
        // edge-time firing misses (guard concept added AFTER the edge).
        while let Some((cid, n)) = self.guard_refire.pop() {
            if self.node_unsat.contains(&n) {
                continue;
            }
            let no = self.out_edges[n].len();
            for i in 0..no {
                let (r, t) = self.out_edges[n][i];
                self.fire_role_clause(cid, n, r, t);
                if self.unsupported {
                    return;
                }
            }
            let ni = self.in_edges[n].len();
            for i in 0..ni {
                let (r, s) = self.in_edges[n][i];
                self.fire_role_clause(cid, s, r, n);
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
                    if let Some(inc) = self.in_edges.get_mut(t) {
                        inc.retain(|(rr, ss)| !(*rr == r && *ss == s));
                    }
                }
                QoUndo::NodeNew => {
                    self.label.pop();
                    self.out_edges.pop();
                    self.in_edges.pop();
                    self.node_range.pop();
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
                QoUndo::Prop(r, n, len) => {
                    if let Some(v) = self.prop.get_mut(&(r, n)) {
                        v.truncate(len);
                    }
                }
                QoUndo::Fprop(r, n, len) => {
                    if let Some(v) = self.fprop.get_mut(&(r, n)) {
                        v.truncate(len);
                    }
                }
                QoUndo::Filler(fil, cls) => {
                    self.filler_node.remove(&(fil, cls));
                }
            }
        }
        // clear residual worklists (they reference undone state).
        self.lit_work.clear();
        self.node_work.clear();
        self.edge_work.clear();
        self.guard_refire.clear();
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
        if depth > self.branch_depth {
            self.unsupported = true;
            return false;
        }
        if let Some(t) = dl {
            if Instant::now().duration_since(t).as_millis() > self.branch_ms {
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
        self.residue_tainted = false;
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
        let tainted = self.residue_tainted;
        self.rollback(mark);
        self.tracing = false;
        self.unsupported = false; // reset the branch-local flag
        if std::env::var_os("KM_HT_QOTRACE").is_some() {
            let dur = dl.unwrap().elapsed().as_millis();
            eprintln!("KM_HT [qo-residue] anchor={} extra={:?} -> r={} unsup={} tainted={} {}ms", anchor, extra, r, unsup, tainted, dur);
        }
        if unsup || tainted {
            // could not decide soundly on the shared model ⇒ defer this concept.
            return None;
        }
        Some(r)
    }

    /// Port #1 — RESIDUE MODEL-REUSE. Complete the AFFECTED (residue) concepts on
    /// the ALREADY-BUILT shared model instead of re-saturating per concept or
    /// re-running a second global pass. Konclude builds ONE completion graph and
    /// branches only the open core; this mirrors that:
    ///
    ///   Phase 1 (model-reuse): branch the parked disjunctions ONCE to a single
    ///   clash-free completion of the whole model, and harvest, per affected
    ///   concept A, the CANDIDATE extra subsumers = query concepts in A's completed
    ///   label that the clean (pre-branching, deterministic) label did not already
    ///   carry. A real subsumer must appear in every completion, so it must appear
    ///   in this one — the single completion is a sound candidate FILTER.
    ///
    ///   Phase 2 (verify): for each candidate B, A ⊑ B iff A ⊓ ¬B is unsatisfiable;
    ///   test it with `qo_residue_test`, which branches only A's subtree on the
    ///   shared parked model (checkpoint/rollback, no rebuild). Also detect an
    ///   unsatisfiable A (inconsistent in every completion).
    ///
    /// SOUNDNESS GATE: the caller must only invoke this when the residue obstacle is
    /// PURE DISJUNCTION (no cardinality Eq-head deferrals, no ∀ shared-filler
    /// pollution) — then branching + label reads are sound. On any in-completion
    /// `unsupported` (depth/deadline/out-of-fragment) we return None ⇒ the caller
    /// defers to CB, so a partial residue never yields an unsound answer.
    fn qo_residue_classify(
        &mut self,
        affected: &[(C, Node)],
        g_label_pos: &[HashSet<C>],
        qset: &HashSet<C>,
    ) -> Option<(Vec<C>, Vec<(C, C)>)> {
        let trace = std::env::var_os("KM_HT_TRACE").is_some();
        let nn = self.label.len();
        self.tracing = true;
        // Phase 1: one global completion, shared across all affected reads.
        let all: HashSet<Node> = (0..nn).collect();
        let mark0 = self.checkpoint();
        let dl = Some(Instant::now());
        let sat = self.qo_branch_dfs(&all, 0, dl);
        if self.unsupported {
            self.rollback(mark0);
            self.tracing = false;
            self.unsupported = false;
            if trace {
                eprintln!("QORES phase1: global completion unsupported ⇒ defer");
            }
            return None;
        }
        let mut cand: Vec<(C, Node, Vec<C>)> = Vec::new();
        let mut tot_cand = 0usize;
        if sat {
            for &(a, na) in affected {
                let nai = na as usize;
                if nai >= nn {
                    continue;
                }
                let empty = HashSet::new();
                let clean = g_label_pos.get(nai).unwrap_or(&empty);
                let mut cs: Vec<C> = Vec::new();
                for &lit in &self.label[nai] {
                    if !lit.neg && lit.c != a && qset.contains(&lit.c) && !clean.contains(&lit.c) {
                        cs.push(lit.c);
                    }
                }
                tot_cand += cs.len();
                cand.push((a, na, cs));
            }
        }
        self.rollback(mark0);
        self.tracing = false;
        if trace {
            eprintln!(
                "QORES phase1: sat={} affected={} candidate_subs={}",
                sat,
                affected.len(),
                tot_cand
            );
        }
        // Phase 2: verify only the candidate EXTRAS by branching A's subtree.
        // Concepts with no candidate gained nothing from the disjunctions beyond
        // their (already-emitted) forward subsumers, so they need no test — this is
        // what keeps the residue pass from degenerating into a per-concept
        // re-saturation over all affected concepts. A subtree branch that touches a
        // deferred-insufficient (∀/cardinality) node returns None (tainted) unless
        // KM_HT_QO_RESIDUE_FORCE suppresses the taint for measurement.
        let mut subs: Vec<(C, C)> = Vec::new();
        let unsat: Vec<C> = Vec::new();
        let mut tested = 0usize;
        for (a, na, cs) in cand {
            if cs.is_empty() {
                continue;
            }
            for b in cs {
                tested += 1;
                let negb = CLit { neg: true, c: b };
                match self.qo_residue_test(na, &[negb]) {
                    Some(false) => subs.push((a, b)), // A ⊓ ¬B unsat ⇒ A ⊑ B
                    Some(true) => {}
                    None => return None,
                }
            }
        }
        if trace {
            eprintln!("QORES phase2: tests={} verified residue_subs={}", tested, subs.len());
        }
        Some((unsat, subs))
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
        // concept-body clauses have no role anchor ⇒ never an inverse edge.
        self.apply_head(cid, &sigma, false);
    }

    /// Fire a role-body clause, anchored at a freshly added edge (es, r, et).
    fn fire_role_clause(&mut self, cid: usize, es: Node, r: R, et: Node) {
        // KPSet (G2/G3): if the anchoring edge is an inverse-bridge back-edge,
        // this firing reads a successor's label across a model-specific reversed
        // edge — its head writes become containment checks (never written).
        let via_inv = self.kpset && self.inv_edges.contains(&(es, r, et));
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
                        self.apply_head(cid, sgm, via_inv);
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
                    // Predecessors of `tn` over role `r`, via the incoming-edge
                    // index — O(in-degree of tn), not O(#nodes). `in_edges[tn]`
                    // holds `(role, source)` for every edge into `tn`, so this
                    // enumerates exactly the same `sn` the full scan did.
                    for &(rr, sn) in &self.in_edges[tn] {
                        if rr == *r {
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

    /// Apply a clause's head under substitution `sigma`. `via_inv` is set
    /// (under `kpset`) when the firing was anchored on an inverse-bridge
    /// back-edge: the head is then a CONTAINMENT CHECK (Konclude's
    /// `isCriticalALLConceptDescriptorInsufficient`), never a write — see
    /// `kp_check_head`.
    fn apply_head(&mut self, cid: usize, sigma: &[Option<Node>], via_inv: bool) {
        let head = &self.clauses[cid].0.head;
        // KPSet G2/G3: an inverse-anchored firing must never write a consequence
        // into the (shared) model — it can only CHECK whether the consequence is
        // already forward-present; a miss marks the concept insufficient.
        if via_inv {
            self.kp_check_head(cid, sigma);
            return;
        }
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
                    // ∀-style write: a concept head on a NON-anchor var lands on a
                    // successor, not the clause's anchor. With role-keyed fillers
                    // such a write is SOUND iff `lit` is already in the target
                    // node's range class (i.e. its creation role's range forces it
                    // anyway). If not, this is Konclude's "critical ALL" case
                    // (`isCriticalALLConceptDescriptorInsufficient`): the write
                    // depends on how the node was reached, the shared model cannot
                    // represent it soundly, so flag the seed insufficient and let
                    // the caller re-verify it with the complete tableau. (Anchor
                    // heads — NF4 backward links, domain — are predecessor-keyed
                    // and never pollute.)
                    if t != X {
                        let cls = self.node_range[n] as usize;
                        let clean = cls != 0 && self.class_set[cls].contains(&lit);
                        if !clean {
                            self.qo_insufficient = true;
                            // KM_HT_QO_CARD per-node split: the write into successor
                            // `n` is model-specific (critical-ALL). Record `n` as
                            // insufficient so the affected-set reverse-reachability
                            // marks every concept whose model reaches `n`; CLEAN
                            // concepts (not reaching `n`) keep a sound label.
                            if self.card_defer {
                                self.kp_insuff_nodes.insert(n);
                            }
                            // A residue verify (tracing) that triggers a critical-ALL
                            // deferral cannot decide this concept soundly on the
                            // shared model ⇒ taint it so the test defers.
                            if self.tracing && !self.residue_unsafe {
                                self.residue_tainted = true;
                            }
                        }
                        if self.track_forall {
                            self.forall_nodes.insert(n);
                        }
                    }
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
                    let f = self.ensure_filler(r, fil);
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
                        // KPSet: tag the back-edge an inverse/symmetric bridge
                        // clause just created, so downstream rules firing across
                        // it become containment checks (never writes).
                        if self.kpset && self.inv_bridge_cid.contains(&cid) {
                            self.inv_edges.insert((sn, r, tn));
                        }
                    }
                    satisfied = true;
                    break;
                }
                Atom::Eq { .. } => {
                    // at-most / functional cardinality forces a successor merge the
                    // shared-node saturation cannot represent soundly. KM_HT_QO_CARD:
                    // mark the anchor node INSUFFICIENT (Konclude's deferral) and
                    // treat the head as satisfied (no write), so the pass completes
                    // for every other concept; the per-node split routes only the
                    // cardinality-affected concepts to the complete verify. Default
                    // (flag off): bail the whole pass `unsupported` (legacy — no
                    // regression on the non-SHIF onts).
                    if self.card_defer {
                        let anchor = sigma[X as usize].expect("X bound");
                        self.kp_insuff_nodes.insert(anchor);
                        self.qo_insufficient = true;
                        self.kp_insufficient = true;
                        // residue verify (tracing): a cardinality Eq-head merge cannot
                        // be decided soundly on the shared model ⇒ taint, test defers.
                        if self.tracing && !self.residue_unsafe {
                            self.residue_tainted = true;
                        }
                        satisfied = true;
                        break;
                    }
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

    /// KPSet containment check (port of Konclude's
    /// `isCriticalALLConceptDescriptorInsufficient`): the firing is anchored on
    /// an inverse-bridge back-edge, so its head must NEVER be written into the
    /// shared model. Instead, verify the head is already satisfied by the
    /// forward closure:
    ///   - all-Concept head ⇒ satisfied iff at least one head literal is already
    ///     present at its target node (the disjunction holds without a write);
    ///   - empty head (clash) / any ∃ or role head ⇒ cannot be containment-
    ///     checked, conservatively INSUFFICIENT.
    /// A miss raises `kp_insufficient` (the concept needs the complete tableau)
    /// and increments `kp_miss`; nothing is added, parked, or killed — so the
    /// inverse contribution can neither over-derive (sound) nor be silently
    /// dropped (complete via the insufficiency route). On an inverse-inert ont
    /// (7581) every head literal is already forward-present, so no check ever
    /// misses and the saturation stays forward-only fast + certified complete.
    fn kp_check_head(&mut self, cid: usize, sigma: &[Option<Node>]) {
        let head = &self.clauses[cid].0.head;
        let anchor = sigma[X as usize];
        if head.is_empty() {
            // an inverse-anchored clash cannot be trusted in the shared model.
            self.kp_insufficient = true;
            self.kp_miss += 1;
            if let Some(a) = anchor {
                self.kp_insuff_nodes.insert(a);
            }
            return;
        }
        let mut disj: Vec<(Node, CLit)> = Vec::new();
        for h in head {
            match *h {
                Atom::Concept { lit, t } => {
                    let n = sigma[t as usize].expect("head var bound");
                    if !self.node_unsat.contains(&n) && self.label[n].contains(&lit) {
                        return; // already satisfied — no obligation
                    }
                    // guard/self-node criticality: an absent operand matters for
                    // completeness only on a self-node, or (on a filler) if it is a
                    // body guard that could still trigger something.
                    let on_self = !(self.sat_mode && self.is_filler[n]);
                    if on_self || !self.kp_guard_only || self.kp_guard.contains(&lit.c) {
                        disj.push((n, lit));
                    }
                }
                // an ∃/role/eq head reached across an inverse edge would build new
                // structure the shared model cannot represent soundly ⇒ insufficient.
                _ => {
                    self.kp_insufficient = true;
                    self.kp_miss += 1;
                    if let Some(a) = anchor {
                        self.kp_insuff_nodes.insert(a);
                    }
                    return;
                }
            }
        }
        // not yet satisfied: defer to the fixpoint criticality pass.
        match disj.len() {
            // all absent operands are inert (non-guard fillers) ⇒ safe, no insufficiency.
            0 => {}
            1 => {
                self.kp_check1.insert(disj[0]);
            }
            _ => self.kp_checkn.push(disj),
        }
    }

    /// Forward-broadcast emit for a captured head-on-target clause. In write
    /// mode (`fprop_on`, not `fcheck`) it asserts `e` at the successor `t`. In
    /// containment-check mode (`fcheck`, Konclude G1/G3) it NEVER writes — it
    /// records a deferred obligation that `kp_finalize` verifies against the
    /// forward closure, so the inverse contribution can never pollute a node's
    /// (read-for-classification) label. A still-missing obligation marks the
    /// concept insufficient (routed to the complete tableau).
    fn fprop_emit(&mut self, t: Node, e: CLit) {
        if self.fcheck {
            if !self.node_unsat.contains(&t) && !self.label[t].contains(&e) {
                // Konclude G1 criticality (same refinement as `kp_write`): the
                // composed-clause head `e` lands on the role TARGET, which under
                // `sat_mode` is a separate ∃-filler node. A filler label is never
                // read as a named subsumer (G1), so a missing obligation there is
                // NOT a completeness threat UNLESS `e` is a body guard that could
                // still trigger a forward rule reaching a self-node. On a
                // self-node (`!is_filler`) the operand could be a named subsumer
                // read directly ⇒ always critical.
                let on_self = !(self.sat_mode && self.is_filler[t]);
                let critical =
                    on_self || !self.kp_guard_only || self.kp_guard.contains(&e.c);
                if critical {
                    self.kp_check1.insert((t, e));
                }
            }
        } else {
            self.add_lit(t, e);
        }
    }

    /// Either assert `lit` at `n` (normal) or, under KPSet when the write would
    /// cross an inverse back-edge (`via_inv`), defer a containment check instead:
    /// never write across the reversed edge. `kp_finalize` decides at fixpoint.
    /// Returns false only on a genuine clash from a real (non-inverse) write.
    fn kp_write(&mut self, n: Node, lit: CLit, via_inv: bool) -> bool {
        if self.kpset && via_inv {
            if !self.node_unsat.contains(&n) && !self.label[n].contains(&lit) {
                // Konclude criticality refinement: a containment miss matters for
                // COMPLETENESS only if the missed operand can still do something.
                //  - on a concept SELF-NODE (`!is_filler`): the operand could be a
                //    named subsumer read directly (G1), so always defer/insufficient.
                //  - on a separate ∃-filler (`sat_mode`): the operand affects named
                //    subsumers only by triggering a forward rule, i.e. only if it is
                //    a BODY GUARD. A non-guard operand at a filler is inert ⇒ safe to
                //    drop with no insufficiency.
                let on_self = !(self.sat_mode && self.is_filler[n]);
                let critical =
                    on_self || !self.kp_guard_only || self.kp_guard.contains(&lit.c);
                if critical {
                    self.kp_check1.insert((n, lit));
                }
            }
            return true;
        }
        self.add_lit(n, lit)
    }

    /// Fixpoint criticality pass (Konclude `checkCriticalIndividuals`): after the
    /// deterministic saturation has closed, re-check every deferred inverse-
    /// anchored containment obligation against the FINAL labels. A still-missing
    /// obligation means the inverse contribution would add something the forward
    /// closure never derived → `kp_insufficient` (route the concept to the
    /// complete tableau). On an inverse-inert ont every obligation is now present
    /// (the forward closure caught up), so nothing is flagged.
    fn kp_finalize(&mut self) {
        let c1 = std::mem::take(&mut self.kp_check1);
        for (n, lit) in c1 {
            if !self.node_unsat.contains(&n) && !self.label[n].contains(&lit) {
                self.kp_insufficient = true;
                self.kp_miss += 1;
                self.kp_insuff_nodes.insert(n);
            }
        }
        let cn = std::mem::take(&mut self.kp_checkn);
        for disj in cn {
            let sat = disj
                .iter()
                .any(|(n, lit)| !self.node_unsat.contains(n) && self.label[*n].contains(lit));
            if !sat {
                self.kp_insufficient = true;
                self.kp_miss += 1;
                // the obligation belongs to all its disjunct nodes (any could
                // have carried the operand); mark them affected.
                for (n, _) in &disj {
                    self.kp_insuff_nodes.insert(*n);
                }
            }
        }
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
    /// Recompute the tableau trigger indexes (`concept_triggers`,
    /// `role_triggers`, `global_clauses`, `global_disj`) from the CURRENT
    /// `self.clauses`. Must be called whenever `self.clauses` is replaced after
    /// construction (e.g. `KM_HT_QO_INVCOMPOSE` swaps in the composed clause
    /// set): the trigger lists hold `(cid, pos)` pairs that index into the clause
    /// records, so a stale index fires `fire_anchor_concept`/`_role` at an
    /// out-of-range `pos` against the new clauses and panics. Same logic as the
    /// inline build in `new`.
    fn rebuild_triggers(&mut self) {
        let mut concept_triggers: HashMap<CLit, Vec<(usize, usize)>> = HashMap::new();
        let mut role_triggers: HashMap<R, Vec<(usize, usize)>> = HashMap::new();
        let mut global_clauses = Vec::new();
        let mut global_disj = Vec::new();
        for (cid, rec) in self.clauses.iter().enumerate() {
            if rec.1.is_empty() {
                global_clauses.push(cid);
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
        self.global_disj_set = global_disj.iter().copied().collect();
        self.global_disj = global_disj;
        self.global_clauses = global_clauses;
        self.concept_triggers = concept_triggers;
        self.role_triggers = role_triggers;
    }

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
            pc_tainted: Vec::new(),
            pc_candidates: Vec::new(),
            pc_unsat_candidates: Vec::new(),
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
            prop_us: 0,
            oblig_us: 0,
            eager_us: 0,
            obligloop_us: 0,
            obl_iters: 0,
            i2_suf_sum: 0,
            i2_calls: 0,
            i2_full: 0,
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
            i2_check: std::env::var_os("KM_HT_INCRBLOCK2_CHECK").is_some(),
            oblig_cand: Vec::new(),
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
            force_fast: false,
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

    /// Turn on the RESULT-IDENTICAL tableau speedups (incremental suffix-only
    /// subset blocking + incremental ∃-obligation processing). These never change
    /// the answer — only how fast a `consistent` test runs — so it is always safe
    /// to enable them on a worker (e.g. the pseudo-model model-builders), without
    /// requiring `KM_HT_INCRBLOCK2` / `KM_HT_INCROBLIG` in the environment.
    pub fn set_fast_tableau(&mut self) {
        self.force_fast = true;
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
                    .filter(|(_, s, _)| *s == p)
                    .map(|(r, _, _)| *r as u64)
                    .collect();
                e.sort_unstable();
                e.dedup();
                sig.extend(e);
                if !seen.insert(sig) {
                    blocked[n] = true;
                }
            }
        } else if self.ext.incr_block {
            // mode 1 (subset), INCREMENTAL: query the persistent inverted index
            // (maintained in add_concept / backtrack_to) — no per-call rebuild.
            // A blockable node n is blocked iff some earlier node m<n is a
            // label-superset; candidates come from n's rarest concept's posting
            // list (m must carry every concept of n). Result-identical to the
            // O(n²) scan (the all-nodes index is sound: see Ext::block_index).
            let idx = &self.ext.block_index;
            for n in 0..nn {
                if !self.ext.blockable[n] {
                    continue;
                }
                let ln = &self.ext.concepts[n];
                if ln.is_empty() {
                    continue;
                }
                let lnlen = ln.len();
                // rarest concept of n ⇒ shortest candidate posting list.
                let mut best_len = usize::MAX;
                let mut best: &[Node] = &[];
                for k in ln.keys() {
                    let e = Ext::enc_lit(*k);
                    let l = idx.get(e).map_or(0, |v| v.len());
                    if l < best_len {
                        best_len = l;
                        best = idx.get(e).map_or(&[], |v| v.as_slice());
                    }
                }
                for &m in best {
                    if m >= n {
                        continue;
                    }
                    let lm = &self.ext.concepts[m];
                    if lm.len() >= lnlen && ln.keys().all(|k| lm.contains_key(k)) {
                        blocked[n] = true;
                        break;
                    }
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
        // KM_HT_NUMBER: a ≤n-merged victim is dead — exclude it (mark blocked so
        // it is neither expanded nor branched, and "a blocked node never blocks").
        if self.ext.number {
            for n in 0..nn {
                if self.ext.merged[n].is_some() {
                    blocked[n] = true;
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
        let blocked = if self.anywhere {
            // KM_HT_INCRBLOCK2: incremental subset-blocking (mode 1) — re-evaluate
            // only the changed suffix instead of all nodes every pass. Identical
            // result to the full scan; KM_HT_INCRBLOCK2_CHECK asserts it per pass.
            Some(if self.ext.incr2 && self.block_mode == 1 {
                let b = self.ext.i2_recompute();
                if self.stats {
                    self.i2_suf_sum += (b.len() - self.ext.i2_last_lo) as u128;
                    self.i2_calls += 1;
                    if self.ext.i2_last_lo == 0 {
                        self.i2_full += 1;
                    }
                }
                if self.i2_check {
                    let full = self.compute_blocked();
                    if full != b {
                        let fd = (0..b.len()).find(|&k| full[k] != b[k]);
                        panic!(
                            "i2 blocking mismatch: nn={} full_blk={} i2_blk={} first_diff={:?}",
                            b.len(),
                            full.iter().filter(|x| **x).count(),
                            b.iter().filter(|x| **x).count(),
                            fd
                        );
                    }
                }
                b
            } else {
                self.compute_blocked()
            })
        } else {
            None
        };
        self.block_us += _bt0.elapsed().as_micros();
        // EAGER (KM_HT_EAGER): fire the deferred global ⊤-disjunctions, but only on
        // nodes that are NOT blocked. A blocked node's ⊤-disjunctions are covered
        // by its blocker (anywhere blocking, ALC(H) no-inverse), so they never
        // need their own branch points — this is what keeps HermiT's model (and
        // its branch count) tiny. Because disjunct choices are not yet in the
        // label at this point, blocking compares Horn-only labels and folds more.
        let _et0 = Instant::now();
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
        self.eager_us += _et0.elapsed().as_micros();
        let _lt0 = Instant::now();
        let no = self.ext.obligations.len();
        if self.ext.incroblig {
            if let Some(b) = &blocked {
                // Gather obligations of currently-UNBLOCKED nodes only (blocked ones
                // are covered by their blocker), then process in INDEX order so the
                // expansion sequence — and the result — matches the flat scan.
                let mut cand = std::mem::take(&mut self.oblig_cand);
                cand.clear();
                for (n, blk) in b.iter().enumerate() {
                    if !*blk {
                        for &i in &self.ext.node_obligs[n] {
                            if !self.ext.oblig_sat[i] {
                                cand.push(i);
                            }
                        }
                    }
                }
                cand.sort_unstable();
                for &i in &cand {
                    if self.ext.oblig_sat[i] {
                        continue; // already discharged — no edge rescan
                    }
                    self.obl_iters += 1;
                    let (n, r, fil) = {
                        let o = &self.ext.obligations[i];
                        (o.n, o.r, o.fil)
                    };
                    if self.ext.merged[n].is_some() {
                        // victim of a ≤n merge: its ∃ was copied to the survivor.
                        self.ext.oblig_sat[i] = true;
                        continue;
                    }
                    if has_rsucc(&self.ext, n, r, fil) {
                        self.ext.oblig_sat[i] = true;
                        continue;
                    }
                    let dep = self.ext.obligations[i].dep.clone();
                    self.heartbeat("exp");
                    let t = self.ext.new_node(Some(n));
                    self.ext.add_edge(r, n, t, &dep);
                    self.ext.add_concept(t, fil, &dep);
                    self.ext.oblig_sat[i] = true;
                    made = true;
                }
                self.oblig_cand = cand;
            } else {
                // ancestor blocking (non-anywhere) — no per-node blocked snapshot,
                // fall back to the flat scan.
                for i in 0..no {
                    self.obl_iters += 1;
                    let (n, r, fil) = {
                        let o = &self.ext.obligations[i];
                        (o.n, o.r, o.fil)
                    };
                    if self.ext.merged[n].is_some() {
                        continue;
                    }
                    if ancestor_blocked(&self.ext, n) || has_rsucc(&self.ext, n, r, fil) {
                        continue;
                    }
                    let dep = self.ext.obligations[i].dep.clone();
                    self.heartbeat("exp");
                    let t = self.ext.new_node(Some(n));
                    self.ext.add_edge(r, n, t, &dep);
                    self.ext.add_concept(t, fil, &dep);
                    made = true;
                }
            }
        } else {
            for i in 0..no {
                self.obl_iters += 1;
                let (n, r, fil) = {
                    let o = &self.ext.obligations[i];
                    (o.n, o.r, o.fil)
                };
                if self.ext.merged[n].is_some() {
                    continue;
                }
                let is_blk = match &blocked {
                    Some(b) => b[n],
                    None => ancestor_blocked(&self.ext, n),
                };
                if is_blk || has_rsucc(&self.ext, n, r, fil) {
                    continue;
                }
                let dep = self.ext.obligations[i].dep.clone();
                self.heartbeat("exp");
                let t = self.ext.new_node(Some(n));
                self.ext.add_edge(r, n, t, &dep);
                self.ext.add_concept(t, fil, &dep);
                made = true;
            }
        }
        self.obligloop_us += _lt0.elapsed().as_micros();
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
            let _pt0 = Instant::now();
            self.propagate();
            self.prop_us += _pt0.elapsed().as_micros();
            if self.ext.has_clash() {
                if self.trace { eprintln!("TR prop-clash depth={}", depth); }
                return self.conflict_out(self.ext.clash_dep());
            }
            let _ot0 = Instant::now();
            let _made = self.process_obligations();
            self.oblig_us += _ot0.elapsed().as_micros();
            if _made {
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
            // `set_fast_tableau` override: force the result-identical incremental
            // blocking / obligation paths on even without the env flags (Ext::new
            // reads them from the environment, so re-apply after each rebuild).
            if self.force_fast {
                self.ext.incr2 = true;
                self.ext.incroblig = true;
            }
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

    /// Pseudo-model refutation support — the concept part of Konclude's
    /// `isPseudoModelSubsumerPossible` (COptimizedKPSetClassSubsumptionClassifier
    /// Thread.cpp:1626). Build ONE satisfiability model of `a` via
    /// `consistent(&[a])` and return the positive concepts true at its root: a
    /// genuine, INVERSE-AWARE model of `a`. A candidate subsumption `a ⊑ b` is
    /// then SOUNDLY refuted (`a ⋢ b`) iff `b` is absent from this set — `b` is
    /// false in a real model of `a`, so not every model of `a` satisfies `b`.
    /// Returns `None` when no usable model exists (out-of-fragment ⇒ defer, or
    /// `a` itself unsatisfiable ⇒ `a ⊑ b` holds trivially) — the caller keeps the
    /// candidate for the full tableau test, so completeness is preserved either
    /// way. This is the cheap gate that replaces a blowing-up `consistent(a ⊓ ¬b)`
    /// with a single (much easier) `consistent(a)` per concept.
    fn model_root_pos(&mut self, a: C) -> Option<HashSet<C>> {
        let _t0 = std::time::Instant::now();
        let r: Option<HashSet<C>> = match self.consistent(&[CLit::pos(a)]) {
            Some(true) => {
                // root = node 0; its label is `a`'s model assignment. Absent
                // positive concept ⇒ false at the root ⇒ a genuine countermodel.
                Some(self.ext.concepts[0].keys().filter(|k| !k.neg).map(|k| k.c).collect())
            }
            // unsat (a ⊑ ⊥ ⊑ b, keep) or unsupported (defer) ⇒ no refutation.
            _ => None,
        };
        if std::env::var_os("KM_HT_QO_PMTIME").is_some() {
            eprintln!(
                "PMMODEL a={} {:.3}s rootlen={}",
                a,
                _t0.elapsed().as_secs_f64(),
                r.as_ref().map(|s| s.len()).unwrap_or(0)
            );
        }
        r
    }

    pub fn classify(&mut self, queries: &[C]) -> Option<(bool, Vec<C>, Vec<(C, C)>)> {
        let global = self.consistent(&[])?;
        if !global {
            return Some((false, queries.to_vec(), Vec::new()));
        }
        // KM_HT_COREPROBE: feasibility probe for "build the deterministic core once".
        // Record the empty-seed (⊤+TBox) model's node label-signatures, then report
        // how much of each per-concept model is the SAME backbone (sharable). High
        // overlap ⇒ core-cloning saves; low overlap ⇒ each test's model is mostly
        // query-specific and cloning a core buys little.
        let core_sigs: Option<HashSet<Vec<C>>> = if std::env::var_os("KM_HT_COREPROBE").is_some() {
            let mut s: HashSet<Vec<C>> = HashSet::new();
            for n in 0..self.ext.num_nodes() {
                let mut v: Vec<C> =
                    self.ext.concepts[n].keys().filter(|k| !k.neg).map(|k| k.c).collect();
                v.sort_unstable();
                s.insert(v);
            }
            eprintln!(
                "KM_HT [coreprobe] empty_seed_nodes={} distinct_sigs={}",
                self.ext.num_nodes(),
                s.len()
            );
            Some(s)
        } else {
            None
        };
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
        // KM_HT_HORNFAST: a per-concept model that completed with ZERO branching is
        // the unique (deterministic) model of A, so its root label is A's EXACT
        // subsumer set — no Phase-2 confirmation needed (B subsumes A iff B holds in
        // every A-model; with one model that is just membership in its root label).
        // Concepts whose build branched still go through the sound Phase-2 confirm.
        // This is the sound, no-shared-filler route to classifying Horn/near-Horn
        // giants (e.g. ore_ont_7581) that the QoSat shared-node gate over-approximates.
        let hornfast = std::env::var_os("KM_HT_HORNFAST").is_some();
        let mut exact: HashSet<C> = HashSet::new();
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
            let pu0 = self.prop_us;
            let ou0 = self.oblig_us;
            let sat = self.consistent(&[CLit::pos(a)])?;
            if self.stats {
                let dt = self.start.elapsed().as_millis() - q0;
                if dt > 200 || qi % 100 == 0 {
                    eprintln!("KM_HT [classify-p1] qi={}/{} concept={} sat={} dt_ms={} block_ms={} prop_ms={} expand_ms={} nodes_last={} branch_pushes={} disjunct_tries={} backtracks={} backjumps={} negfired={} steps={}",
                        qi, queries.len(), a, sat, dt, (self.block_us - bu0) / 1000,
                        (self.prop_us - pu0) / 1000,
                        (self.oblig_us - ou0 - (self.block_us - bu0)) / 1000,
                        self.ext.num_nodes(),
                        self.branch_pushes - bp0, self.disjunct_tries - dt0,
                        self.backtracks - bt0, self.backjumps - bj0, self.negfired - nf0,
                        self.steps - st0);
                }
            }
            if let Some(core) = &core_sigs {
                if sat && qi < 8 {
                    let nn = self.ext.num_nodes();
                    let mut shared = 0usize;
                    for n in 0..nn {
                        let mut v: Vec<C> =
                            self.ext.concepts[n].keys().filter(|k| !k.neg).map(|k| k.c).collect();
                        v.sort_unstable();
                        if core.contains(&v) {
                            shared += 1;
                        }
                    }
                    eprintln!(
                        "KM_HT [coreprobe] concept={} nodes={} shared_with_core={} ({}%)",
                        a, nn, shared, if nn > 0 { 100 * shared / nn } else { 0 }
                    );
                }
            }
            if !sat {
                unsat.push(a);
            } else {
                sat_q.push(a);
                if !naive {
                    labels.push((a, self.root_pos_label()));
                    // branch-free build ⇒ this concept's root label is exact.
                    if hornfast && self.branch_pushes == bp0 {
                        exact.insert(a);
                    }
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
                // HORNFAST: branch-free build ⇒ unique model ⇒ root label is the
                // exact subsumer set; emit it without any Phase-2 SAT test.
                if hornfast && exact.contains(&a) {
                    for &b in lab {
                        if b != a && qset.contains(&b) && satset.contains(&b) {
                            subs.push((a, b));
                        }
                    }
                    continue;
                }
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
        if self.stats {
            let block_ms = self.block_us / 1000;
            let prop_ms = self.prop_us / 1000;
            let expand_ms = self.oblig_us.saturating_sub(self.block_us) / 1000;
            let tot = (block_ms + prop_ms + expand_ms).max(1);
            eprintln!(
                "KM_HT [classify-prof] steps={} block_ms={}({}%) prop_ms={}({}%) expand_ms={}({}%) eager_ms={} obligloop_ms={} obl_iters={}",
                self.steps,
                block_ms, 100 * block_ms / tot,
                prop_ms, 100 * prop_ms / tot,
                expand_ms, 100 * expand_ms / tot,
                self.eager_us / 1000, self.obligloop_us / 1000, self.obl_iters,
            );
            eprintln!(
                "KM_HT [classify-i2] calls={} full_rebuilds={} avg_suffix={} (vs ~node count)",
                self.i2_calls,
                self.i2_full,
                if self.i2_calls > 0 { self.i2_suf_sum / self.i2_calls as u128 } else { 0 },
            );
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
    /// KM_HT_QO_PC: per-concept saturation gate. For each query concept `A`, run
    /// a FRESH single-seed QoSat saturation (only `A` seeded), reusing the shared
    /// clause indexes via `reset()`. Read `A`'s verdict off that one model:
    ///   - clash at `A`'s node ⇒ `A ⊑ ⊥` (unsatisfiable);
    ///   - sufficient (no open parked disjunction) ⇒ `A`'s positive label is its
    ///     EXACT subsumer set (sound + complete on the Horn fragment, with
    ///     `complete_roles` re-firing role clauses for guard-after-edge);
    ///   - insufficient / unsupported (`Eq`-head, out-of-fragment, node cap) ⇒
    ///     return `None`, deferring to the caller's fallback (SOUND — never wrong,
    ///     just declines). On a Horn SRIF ont every concept is sufficient.
    /// Peak memory is one concept's closure (not the union of all 73k); total
    /// work is the sum of the per-concept closures, not the global node×clause
    /// cross-product that times `saturate_global` out.
    /// Konclude's single non-branching pass: ONE forward-only global saturation
    /// that seeds every query concept as its own self-node (with shared
    /// ∃-fillers), then reads each concept's sound subsumers directly off its
    /// self-node label — no per-concept re-saturation, no residue test. This is
    /// the 73k-saturations → 1 speedup that matches Konclude's architecture
    /// (`CCalculationTableauApproximationSaturationTaskHandleAlgorithm` =
    /// one approximation saturation, subsumers read per concept from its own
    /// node, `CPrecomputedSaturationSubsumerExtractor`).
    ///
    /// SOUND: forward-only (`skip_inverse = true`) drops the inverse-bridge
    /// back-edges, so the saturation never reads a successor's runtime label
    /// across a model-specific reversed edge — it never over-derives.
    ///
    /// COMPLETE *exactly when* the global pass is clean, i.e. it equals the
    /// per-concept forward-only gate. The only ways a shared filler node's label
    /// can pick up a seed-specific (cross-concept) literal are (a) an inverse
    /// back-edge — excluded by forward-only — and (b) a ∀/range concept head
    /// written onto a shared filler whose creation-role class does not already
    /// force it — which trips `qo_insufficient` (Konclude's
    /// `isCriticalALLConceptDescriptorInsufficient`). So when no node tripped
    /// `qo_insufficient`, no disjunction is parked (fully deterministic forward
    /// closure), and the pass did not bail (`unsupported`), every concept's
    /// self-node label is identical to its solo per-concept closure → reading it
    /// is sound *and* complete. Otherwise return `None` and let the caller fall
    /// back to the per-concept gate (which decides sufficiency per concept).
    fn qo_classify_global_fwd(&mut self, queries: &[C]) -> Option<(bool, Vec<C>, Vec<(C, C)>)> {
        let trace = std::env::var_os("KM_HT_TRACE").is_some();
        let qset: HashSet<C> = queries.iter().copied().collect();
        let mut qf = QoSat::new_opts(
            &self.clauses,
            true,
            std::env::var_os("KM_HT_QO_FPROP").is_some(),
        ); // forward-only ⇒ sound
        qf.complete_roles = true;
        let g = qf.saturate_global(queries);
        // Defer to the per-concept gate unless the single pass is fully clean:
        //  - `unsupported`: out-of-fragment / node-cap bail.
        //  - `qo_insufficient`: a ∀/range write polluted a shared filler, so a
        //    self-node label may carry a cross-concept literal — not safe to read.
        //  - any parked disjunction (`!pending.is_empty()`): the forward closure
        //    is not the whole story (a live ⊔), so a subsumer could be missed.
        // (For a Horn SRIF ont — 7581 — none of these fire, so the fast path is
        // taken and the per-concept gate is never reached.)
        if g.unsupported || qf.qo_insufficient || !qf.pending.is_empty() || qf.kp_insufficient {
            if trace {
                eprintln!(
                    "QOGF defer: unsupported={} insufficient={} pending={} kp_insufficient={} kp_miss={} insuff_nodes={}",
                    g.unsupported,
                    qf.qo_insufficient,
                    qf.pending.len(),
                    qf.kp_insufficient,
                    qf.kp_miss,
                    qf.kp_insuff_nodes.len()
                );
                // FCHECK per-node reachability probe: a query concept can still
                // certify from the forward closure iff its self-node cannot be
                // affected by any missed obligation. A missed `E(u)`, were it
                // present, would propagate from `u` BOTH backward (prop, to
                // predecessors via in_edges) AND forward (fprop, to successors via
                // out_edges); so the conservatively-affected set is the
                // bidirectional reachability closure of the insufficient nodes.
                // Count query concepts (nodes 0..|queries|) outside it.
                if qf.kp_insufficient && !qf.qo_insufficient && qf.pending.is_empty() {
                    let nn = qf.label.len();
                    let mut affected = vec![false; nn];
                    let mut stack: Vec<Node> = Vec::new();
                    for &n in &qf.kp_insuff_nodes {
                        if n < nn && !affected[n] {
                            affected[n] = true;
                            stack.push(n);
                        }
                    }
                    while let Some(n) = stack.pop() {
                        for &(_, p) in &qf.in_edges[n] {
                            if !affected[p] {
                                affected[p] = true;
                                stack.push(p);
                            }
                        }
                        for &(_, t) in &qf.out_edges[n] {
                            if !affected[t] {
                                affected[t] = true;
                                stack.push(t);
                            }
                        }
                    }
                    let clean = (0..queries.len().min(nn)).filter(|&i| !affected[i]).count();
                    eprintln!(
                        "QOGF fcheck per-node probe: {} / {} query concepts CLEAN (self-node not in the bidirectional closure of any insufficient node)",
                        clean,
                        queries.len()
                    );
                }
            }
            // KM_HT_QO_CARD per-node split on the FORWARD-ONLY pass (no inverse
            // back-edges are materialised, so the only insufficiencies are
            // cardinality Eq-heads and critical-∀ writes). A concept is AFFECTED iff
            // its self-node is in the BIDIRECTIONAL closure of any insufficient node
            // (a forced merge / ∀ pollutes both predecessors and successors). CLEAN
            // concepts keep the sound forward-only label, which — having reached no
            // insufficient node — is also complete. Emit them; defer only the rest.
            if qf.card_defer && !g.unsupported && qf.pending.is_empty() {
                let nn = qf.label.len();
                let mut affected = vec![false; nn];
                let mut stack: Vec<Node> = Vec::new();
                for &n in &qf.kp_insuff_nodes {
                    if n < nn && !affected[n] {
                        affected[n] = true;
                        stack.push(n);
                    }
                }
                while let Some(n) = stack.pop() {
                    for &(_, p) in &qf.in_edges[n] {
                        if !affected[p] {
                            affected[p] = true;
                            stack.push(p);
                        }
                    }
                    for &(_, t) in &qf.out_edges[n] {
                        if !affected[t] {
                            affected[t] = true;
                            stack.push(t);
                        }
                    }
                }
                let mut cs: Vec<(C, C)> = Vec::new();
                let mut cu: Vec<C> = Vec::new();
                let mut res = 0usize;
                for (i, &a) in queries.iter().enumerate() {
                    if i >= nn || affected[i] {
                        res += 1;
                        continue;
                    }
                    if g.node_unsat.contains(&i) {
                        cu.push(a);
                        continue;
                    }
                    for &b in &g.label_pos[i] {
                        if b != a && qset.contains(&b) {
                            cs.push((a, b));
                        }
                    }
                }
                if trace {
                    eprintln!(
                        "QOGF card-split: clean={} affected={} of {} clean_subs={} clean_unsat={} insuff_nodes={}",
                        queries.len() - res,
                        res,
                        queries.len(),
                        cs.len(),
                        cu.len(),
                        qf.kp_insuff_nodes.len()
                    );
                }
                if res == 0 {
                    let consistent = !(!queries.is_empty() && cu.len() == queries.len());
                    return Some((consistent, cu, cs));
                }
            }
            return None;
        }
        // INVCOMPOSE write-mode soundness guard. When the composed inverse clauses
        // are WRITTEN (fprop, not fcheck) into separate per-creation-role filler
        // nodes (sat_mode), the clean forward pass already INCLUDES the inverse
        // contribution, so it can certify complete WITHOUT the funnel — but ONLY if
        // composition was total. The forward-only pass drops every inverse BRIDGE
        // (`skip_inverse = true`); if any bridge survived `compose_inverse`
        // (a non-composable / one-directional inverse role), that contribution is
        // silently lost and a "clean" pass is NOT necessarily complete. So when
        // writing composed clauses, require zero residual inverse bridges; else
        // defer to the (sound) funnel.
        if qf.fprop_on && !qf.fcheck {
            let residual = count_inverse_bridges(&self.clauses);
            if residual > 0 {
                if trace {
                    eprintln!(
                        "QOGF defer: INVCOMPOSE write-mode but {} residual inverse bridges (composition not total) — cannot certify, funnel",
                        residual
                    );
                }
                return None;
            }
            if trace {
                eprintln!("QOGF INVCOMPOSE write-mode: 0 residual inverse bridges ⇒ certify safe");
            }
        }
        // `saturate_global` seeds the query concepts first, in order, so query
        // `queries[i]` is shared node `i` (same mapping the legacy global path uses).
        let node_of: HashMap<C, Node> =
            queries.iter().enumerate().map(|(i, &c)| (c, i as Node)).collect();
        let mut unsat: Vec<C> = Vec::new();
        let mut subs: Vec<(C, C)> = Vec::new();
        for &a in queries {
            let n = node_of[&a];
            if g.node_unsat.contains(&n) {
                unsat.push(a); // forward-only clash ⇒ sound unsat
                continue;
            }
            for &b in &g.label_pos[n] {
                if b != a && qset.contains(&b) {
                    subs.push((a, b)); // sound (forward-only never over-derives)
                }
            }
        }
        let consistent = !(!queries.is_empty() && unsat.len() == queries.len());
        if trace {
            eprintln!(
                "QOGF done subs={} unsat={} consistent={} nodes={}",
                subs.len(),
                unsat.len(),
                consistent,
                g.label_pos.len()
            );
        }
        // FCHECK (Konclude G1/G3 certification): the inverse-composed clauses ran
        // in containment-check mode and NO obligation missed (we passed the defer
        // gate, so `kp_insufficient` is false). That certifies the sound
        // forward-only closure is ALSO complete — the inverse contributed nothing
        // beyond what the forward closure already carries — so return it directly,
        // without the per-concept verify funnel.
        if qf.fcheck {
            if trace {
                eprintln!("QOGF fcheck CERTIFIED complete (kp_miss=0)");
            }
            return Some((consistent, unsat, subs));
        }
        // KM_HT_QO_VERIFY: certify completeness, cheaply. Forward-only `L` is sound
        // but may miss inverse-entailed subsumptions. A two-stage SOUND funnel:
        //   (1) STRUCTURAL suspect selection (no inverse saturation): a concept is a
        //       suspect iff its forward closure can REACH an edge on an
        //       inverse-having role. That is the only way inverse can affect its
        //       classification — the inverse back-edge `r⁻` is created from a forward
        //       `r`-edge, so any inverse-affected concept reaches an `r`-edge in the
        //       forward model. Sound over-approximation, O(nodes+edges); avoids the
        //       111s inverse-augmented global pass (measured) entirely. (Set
        //       `KM_HT_QO_GLOBALSEL` to use the older inverse-global selection.)
        //   (2) a per-concept (single-seed) inverse saturation runs ONLY on the
        //       suspects and de-conflates each to its TIGHT candidate set — a single
        //       seed cannot suffer the cross-concept filler conflation that bloated
        //       the global set (6.5M → 177 on 7581), so most suspects yield zero.
        // The caller then confirms each tight candidate `(A,B)` with the complete
        // tableau `consistent(A ⊓ ¬B)` (cheap: ~0.02–0.26s each). Result =
        // `L ∪ confirmed` = sound + complete. `KM_HT_QO_VERIFY_CAP` bounds the tight
        // candidate count (default 50000); overflow ⇒ defer (return None) rather
        // than run an unbounded verify.
        if std::env::var_os("KM_HT_QO_VERIFY").is_some() {
            let t_vp = std::time::Instant::now();
            // (1) structural suspects from the forward model `qf` (still in scope).
            let suspects: Vec<C> = if std::env::var_os("KM_HT_QO_GLOBALSEL").is_some() {
                // legacy: inverse-augmented global pass selects suspects (slow).
                let mut qg = QoSat::new_opts(
                    &self.clauses,
                    false,
                    std::env::var_os("KM_HT_QO_FPROP").is_some(),
                );
                qg.complete_roles = true;
                let gg = qg.saturate_global(queries);
                if gg.unsupported {
                    return None;
                }
                queries
                    .iter()
                    .copied()
                    .filter(|a| {
                        let n = node_of[a];
                        if g.node_unsat.contains(&n) {
                            return false;
                        }
                        let fwd = &g.label_pos[n];
                        gg.node_unsat.contains(&n)
                            || gg.label_pos[n].iter().any(|b| *b != *a && qset.contains(b) && !fwd.contains(b))
                    })
                    .collect()
            } else {
                // inverse-having roles: any role in an inverse-bridge clause (a single
                // role head whose args are swapped versus a body role atom).
                let mut inv_roles: HashSet<R> = HashSet::new();
                for rec in self.clauses.iter() {
                    let head = &rec.0.head;
                    if head.len() == 1 {
                        if let Atom::Role { r: hr, s: hs, t: ht } = &head[0] {
                            for a in &rec.1 {
                                if let Atom::Role { r, s, t } = a {
                                    if *s == *ht && *t == *hs {
                                        inv_roles.insert(*hr);
                                        inv_roles.insert(*r);
                                    }
                                }
                            }
                        }
                    }
                }
                // mark nodes incident to an inverse-role edge, then reverse-reach via
                // predecessors (`in_edges`) to mark every forward-ancestor.
                let nn = qf.label.len();
                let mut marked = vec![false; nn];
                let mut stack: Vec<Node> = Vec::new();
                for n in 0..nn {
                    let incident = qf.out_edges[n].iter().any(|(r, _)| inv_roles.contains(r))
                        || qf.in_edges[n].iter().any(|(r, _)| inv_roles.contains(r));
                    if incident {
                        marked[n] = true;
                        stack.push(n);
                    }
                }
                while let Some(n) = stack.pop() {
                    for &(_, p) in &qf.in_edges[n] {
                        if !marked[p] {
                            marked[p] = true;
                            stack.push(p);
                        }
                    }
                }
                queries
                    .iter()
                    .copied()
                    .filter(|a| {
                        let n = node_of[a];
                        !g.node_unsat.contains(&n) && marked[n]
                    })
                    .collect()
            };
            // inverse-induced unsat concepts are themselves structural suspects (their
            // model uses an inverse edge), so the per-concept clash check below catches
            // them — no separate inverse-global-unsat pass needed.
            let mut unsat_cands: Vec<C> = Vec::new();
            if trace {
                eprintln!(
                    "QOGF verify: {} suspect concepts [structural selection {:.2}s]",
                    suspects.len(),
                    t_vp.elapsed().as_secs_f64()
                );
            }
            let t_pc = std::time::Instant::now();
            // (2) per-concept inverse saturation on the suspects → tight candidates.
            let cap: usize = std::env::var("KM_HT_QO_VERIFY_CAP")
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or(50_000);
            let node_cap = queries.len().saturating_mul(4).saturating_add(500_000);
            // Parallel work-stealing per-concept inverse de-conflation: each worker
            // builds its own forward+inverse QoSat (borrowing the shared clause set)
            // and pulls the next suspect from an atomic counter. Single-seed
            // saturations are independent, so this scales near-linearly — the ~330s
            // sequential loop on 7581 (10635 suspects × ~31ms) drops to ~330/cores.
            // A worker returning `None` means a suspect's saturation went
            // out-of-fragment ⇒ the whole verify defers (sound: falls back).
            let par = std::env::var("KM_HT_PAR")
                .ok()
                .and_then(|s| s.parse::<usize>().ok())
                .unwrap_or(1)
                .max(1);
            let nthreads = par.min(suspects.len().max(1)).max(1);
            let next = std::sync::atomic::AtomicUsize::new(0);
            const QO_WORKER_STACK: usize = 256 * 1024 * 1024;
            let clauses_ref: &[ClauseRec] = &self.clauses;
            let suspects_ref = &suspects;
            let g_ref = &g;
            let node_of_ref = &node_of;
            let qset_ref = &qset;
            let parts: Vec<Option<(Vec<(C, C)>, Vec<C>)>> = std::thread::scope(|s| {
                let next = &next;
                let handles: Vec<_> = (0..nthreads)
                    .map(|_| {
                        std::thread::Builder::new()
                            .stack_size(QO_WORKER_STACK)
                            .spawn_scoped(s, move || -> Option<(Vec<(C, C)>, Vec<C>)> {
                                let mut qpc = QoSat::new_opts(
                                    clauses_ref,
                                    false,
                                    std::env::var_os("KM_HT_QO_FPROP").is_some(),
                                );
                                qpc.complete_roles = true;
                                qpc.node_cap = node_cap;
                                let mut c: Vec<(C, C)> = Vec::new();
                                let mut u: Vec<C> = Vec::new();
                                loop {
                                    let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                                    if i >= suspects_ref.len() {
                                        break;
                                    }
                                    let a = suspects_ref[i];
                                    qpc.reset();
                                    let r = qpc.saturate(&[CLit::pos(a)]);
                                    if r.unsupported {
                                        return None;
                                    }
                                    if r.clashed {
                                        u.push(a);
                                        continue;
                                    }
                                    let n = node_of_ref[&a];
                                    let fwd = &g_ref.label_pos[n];
                                    for &b in &r.root_label {
                                        if b != a && qset_ref.contains(&b) && !fwd.contains(&b) {
                                            c.push((a, b));
                                        }
                                    }
                                }
                                Some((c, u))
                            })
                            .expect("spawn per-concept inverse worker")
                    })
                    .collect();
                handles.into_iter().map(|h| h.join().unwrap()).collect()
            });
            let mut cands: Vec<(C, C)> = Vec::new();
            for part in parts {
                match part {
                    Some((c, u)) => {
                        cands.extend(c);
                        unsat_cands.extend(u);
                    }
                    None => return None, // a suspect went out-of-fragment ⇒ defer
                }
            }
            if cands.len() > cap {
                if trace {
                    eprintln!("QOGF verify: candidate set exceeded cap {} ⇒ defer", cap);
                }
                return None; // unbounded verify ⇒ defer rather than stall
            }
            if trace {
                eprintln!(
                    "QOGF verify: {} tight candidates after per-concept de-conflation, {} unsat candidates [per-concept-inverse {:.2}s]",
                    cands.len(),
                    unsat_cands.len(),
                    t_pc.elapsed().as_secs_f64()
                );
            }
            self.pc_candidates = cands;
            self.pc_unsat_candidates = unsat_cands;
        }
        Some((consistent, unsat, subs))
    }

    fn qo_classify_perconcept(&mut self, queries: &[C]) -> Option<(bool, Vec<C>, Vec<(C, C)>)> {
        let qset: HashSet<C> = queries.iter().copied().collect();
        let trace = std::env::var_os("KM_HT_TRACE").is_some();
        if trace {
            eprintln!("QOPC entry queries={} clauses={}", queries.len(), self.clauses.len());
        }
        let cap = queries.len().saturating_mul(4).saturating_add(500_000);
        // Two single-seed saturations per concept:
        //  - `qf` forward-only (inverse-bridge clauses dropped): SOUND. Reading a
        //    successor's runtime label is only justified across genuine forward
        //    ∃-edges, never across an inverse-induced back-edge, so this never
        //    over-derives — but it may MISS inverse-entailed subsumptions.
        //  - `qu` inverse-augmented: a COMPLETE superset (the old behaviour;
        //    sound only modulo the inverse over-derivation).
        // The truth is `qf ∪ verify(qu \ qf)`: the forward-only subsumers are
        // kept directly; the extra inverse-only ones are candidates the caller
        // confirms with the complete tableau. Sound + complete + general (no
        // ontology-specific assumption about whether inverse is load-bearing).
        // The forward-only saturation is the sound result and is returned by
        // default. The inverse-augmented superset is built + saturated ONLY when
        // the verify pass is enabled (`KM_HT_QO_VERIFY`), because it doubles the
        // saturation cost and its extra subsumptions are worthless without the
        // complete-tableau confirmation that the verify pass performs.
        let want_cands = std::env::var_os("KM_HT_QO_VERIFY").is_some();
        let mut qf = QoSat::new_opts(
            &self.clauses,
            true,
            std::env::var_os("KM_HT_QO_FPROP").is_some(),
        );
        qf.complete_roles = true;
        qf.node_cap = cap;
        let mut qu = QoSat::new_opts(
            &self.clauses,
            false,
            std::env::var_os("KM_HT_QO_FPROP").is_some(),
        );
        qu.complete_roles = true;
        qu.node_cap = cap;
        let mut unsat: Vec<C> = Vec::new();
        let mut subs: Vec<(C, C)> = Vec::new();
        let mut cands: Vec<(C, C)> = Vec::new();
        let mut unsat_cands: Vec<C> = Vec::new();
        for (i, &a) in queries.iter().enumerate() {
            qf.reset();
            let rf = qf.saturate(&[CLit::pos(a)]);
            if rf.unsupported {
                if trace {
                    eprintln!("QOPC bail (fwd) at {}/{} concept {}", i, queries.len(), a);
                }
                return None; // Eq-head / out-of-fragment / cap → defer
            }
            // A forward-only clash is a SOUND unsat (it never over-derives).
            // (Check clash before sufficiency: a clashed root may report
            // insufficient, but it is decided, not deferred.)
            if rf.clashed {
                unsat.push(a);
                continue;
            }
            if !rf.sufficient {
                if trace {
                    eprintln!("QOPC bail (insufficient) at {}/{} concept {}", i, queries.len(), a);
                }
                return None; // open parked disjunction → defer (sound)
            }
            let lset: HashSet<C> = rf.root_label.iter().copied().collect();
            for &b in &lset {
                if b != a && qset.contains(&b) {
                    subs.push((a, b)); // sound
                }
            }
            if want_cands {
                qu.reset();
                let ru = qu.saturate(&[CLit::pos(a)]);
                if ru.unsupported {
                    if trace {
                        eprintln!("QOPC bail (full) at {}/{} concept {}", i, queries.len(), a);
                    }
                    return None;
                }
                if ru.clashed && !rf.clashed {
                    unsat_cands.push(a); // inverse-only unsat → confirm with tableau
                } else if ru.sufficient {
                    for &b in &ru.root_label {
                        if b != a && qset.contains(&b) && !lset.contains(&b) {
                            cands.push((a, b)); // inverse-only subsumption → verify
                        }
                    }
                }
            }
            if trace && i > 0 && i % 5000 == 0 {
                eprintln!("QOPC {}/{} subs={} cands={} unsat={} ucands={}",
                    i, queries.len(), subs.len(), cands.len(), unsat.len(), unsat_cands.len());
            }
        }
        let consistent = !(!queries.is_empty() && unsat.len() == queries.len());
        if trace {
            eprintln!("QOPC done subs={} cands={} unsat={} ucands={} consistent={}",
                subs.len(), cands.len(), unsat.len(), unsat_cands.len(), consistent);
        }
        self.pc_candidates = cands;
        self.pc_unsat_candidates = unsat_cands;
        self.pc_tainted = Vec::new();
        Some((consistent, unsat, subs))
    }

    /// KPSet global gate (Konclude G2/G3 port, `KM_HT_QO_KPSET`). ONE
    /// inverse-AWARE global saturation in which every concept write that would
    /// cross an inverse-bridge back-edge is a CONTAINMENT CHECK, never a write
    /// (port of `isCriticalALLConceptDescriptorInsufficient`). When no check
    /// missed at the fixpoint (`!kp_insufficient`) and the pass is otherwise
    /// clean, each concept's self-node label is:
    ///   - SOUND — nothing was written across a model-specific reversed edge, so
    ///     no cross-concept shared-filler conflation (the 7581 6.5M pollution);
    ///   - COMPLETE — every inverse contribution was already forward-present (the
    ///     containment checks all passed), so dropping the inverse writes loses
    ///     nothing.
    /// = the certified sound+complete answer at forward-only speed (no per-
    /// candidate tableau verify). Otherwise (an inverse contribution was genuinely
    /// load-bearing, or a disjunction parked, or out of fragment) return `None`
    /// and fall through to the verify funnel — a sound fallback.
    fn qo_classify_kpset(&mut self, queries: &[C]) -> Option<(bool, Vec<C>, Vec<(C, C)>)> {
        let trace = std::env::var_os("KM_HT_TRACE").is_some();
        let qset: HashSet<C> = queries.iter().copied().collect();
        let mut qk = QoSat::new_opts(
            &self.clauses,
            false,
            std::env::var_os("KM_HT_QO_FPROP").is_some(),
        ); // KEEP inverse bridges
        qk.kpset = true;
        qk.complete_roles = true;
        let g = qk.saturate_global(queries);
        if g.unsupported || qk.kp_insufficient || qk.qo_insufficient || !qk.pending.is_empty() {
            // KM_HT_QO_CARD per-node split (study P2). When the ONLY obstacles are
            // insufficient nodes (cardinality Eq-heads / critical-ALL deferrals) —
            // not node-cap exhaustion (`unsupported`) nor a parked disjunction
            // (`pending`) — most concepts are still CLEAN: their self-node does not
            // forward-reach any insufficient node, so dropping the deferred writes
            // loses nothing for them and their saturated label is the exact,
            // complete subsumer set. Emit those directly; only the AFFECTED concepts
            // (whose model reaches an insufficient node) need the complete verify.
            // A concept is AFFECTED iff its self-node reverse-reaches an insufficient
            // node over `in_edges` (NF4/∀ propagate filler→predecessor up the forward
            // out-edges, so an insufficiency at `n` can only have polluted forward
            // ancestors of `n`).
            if qk.card_defer && !g.unsupported {
                let nn = qk.label.len();
                let mut affected = vec![false; nn];
                let mut stack: Vec<Node> = Vec::new();
                // Affected seeds = every node carrying a deferred obligation:
                //  - cardinality Eq-head / critical-∀ writes (kp_insuff_nodes),
                //  - inverse containment misses (kp_check_head also records these),
                //  - PARKED DISJUNCTION anchors: a node with an unresolved ⊔ has an
                //    incomplete label, so any concept whose model reaches it is
                //    affected. Seeding them lets the CLEAN bulk emit even while a
                //    small disjunction/cardinality core remains (the family members
                //    have a tiny hard core in a deterministic bulk).
                for &n in &qk.kp_insuff_nodes {
                    if n < nn && !affected[n] {
                        affected[n] = true;
                        stack.push(n);
                    }
                }
                for &(anchor, _cid) in &qk.pending {
                    if anchor < nn && !affected[anchor] {
                        affected[anchor] = true;
                        stack.push(anchor);
                    }
                }
                while let Some(n) = stack.pop() {
                    for &(_, p) in &qk.in_edges[n] {
                        if !affected[p] {
                            affected[p] = true;
                            stack.push(p);
                        }
                    }
                }
                let mut clean_subs: Vec<(C, C)> = Vec::new();
                let mut clean_unsat: Vec<C> = Vec::new();
                let mut residue: Vec<C> = Vec::new();
                let mut residue_nodes: Vec<(C, Node)> = Vec::new();
                for (i, &a) in queries.iter().enumerate() {
                    if i >= nn || affected[i] {
                        residue.push(a);
                        if i < nn {
                            residue_nodes.push((a, i as Node));
                            // An affected concept still has a SOUND forward lower
                            // bound: its self-node's deterministically-derived
                            // subsumers hold regardless of how the open disjunctions
                            // resolve (forward saturation is monotone). Emit those
                            // now; the residue model-reuse only adds the EXTRA
                            // disjunction-forced subsumers on top.
                            if g.node_unsat.contains(&i) {
                                clean_unsat.push(a); // forward clash ⇒ sound unsat
                            } else {
                                for &b in &g.label_pos[i] {
                                    if b != a && qset.contains(&b) {
                                        clean_subs.push((a, b));
                                    }
                                }
                            }
                        }
                        continue;
                    }
                    if g.node_unsat.contains(&i) {
                        clean_unsat.push(a); // forward clash is a sound unsat
                        continue;
                    }
                    for &b in &g.label_pos[i] {
                        if b != a && qset.contains(&b) {
                            clean_subs.push((a, b));
                        }
                    }
                }
                if trace {
                    eprintln!(
                        "QOKP card-split: clean={} affected(residue)={} of {} | clean_subs={} clean_unsat={} insuff_nodes={}",
                        queries.len() - residue.len(),
                        residue.len(),
                        queries.len(),
                        clean_subs.len(),
                        clean_unsat.len(),
                        qk.kp_insuff_nodes.len()
                    );
                }
                if residue.is_empty() {
                    // every query concept CLEAN ⇒ sound+complete from the single pass.
                    let consistent =
                        !(!queries.is_empty() && clean_unsat.len() == queries.len());
                    return Some((consistent, clean_unsat, clean_subs));
                }
                // Port #1 — RESIDUE MODEL-REUSE. Complete the affected concepts on
                // the shared model (one completion + per-subtree verify) instead of
                // deferring to a second global saturation / CB. SOUND only when the
                // residue obstacle is PURE DISJUNCTION: no cardinality Eq-head
                // deferrals (`kp_insuff_nodes` empty) and no ∀ shared-filler
                // pollution (`!qo_insufficient`). Otherwise the shared-model labels
                // and subtree branching are not trustworthy ⇒ keep deferring.
                if std::env::var_os("KM_HT_QO_RESIDUE").is_some()
                    && (qk.residue_unsafe
                        || (qk.kp_insuff_nodes.is_empty() && !qk.qo_insufficient))
                {
                    if let Some((res_unsat, res_subs)) =
                        qk.qo_residue_classify(&residue_nodes, &g.label_pos, &qset)
                    {
                        clean_subs.extend(res_subs);
                        clean_unsat.extend(res_unsat);
                        let consistent =
                            !(!queries.is_empty() && clean_unsat.len() == queries.len());
                        if trace {
                            eprintln!(
                                "QOKP residue model-reuse certified: total_subs={} total_unsat={}",
                                clean_subs.len(),
                                clean_unsat.len()
                            );
                        }
                        return Some((consistent, clean_unsat, clean_subs));
                    }
                    if trace {
                        eprintln!("QOKP residue model-reuse could not complete ⇒ defer");
                    }
                }
            }
            if trace {
                eprintln!(
                    "QOKP defer: unsupported={} kp_insufficient={} kp_miss={} qo_insufficient={} pending={} inv_edges={} insuff_nodes={}",
                    g.unsupported, qk.kp_insufficient, qk.kp_miss, qk.qo_insufficient,
                    qk.pending.len(), qk.inv_edges.len(), qk.kp_insuff_nodes.len()
                );
            }
            return None;
        }
        if trace {
            eprintln!(
                "QOKP certified sound+complete (kp_miss=0): inv_edges={} nodes={}",
                qk.inv_edges.len(),
                g.label_pos.len()
            );
        }
        let node_of: HashMap<C, Node> =
            queries.iter().enumerate().map(|(i, &c)| (c, i as Node)).collect();
        let mut unsat: Vec<C> = Vec::new();
        let mut subs: Vec<(C, C)> = Vec::new();
        for &a in queries {
            let n = node_of[&a];
            if g.node_unsat.contains(&n) {
                unsat.push(a);
                continue;
            }
            for &b in &g.label_pos[n] {
                if b != a && qset.contains(&b) {
                    subs.push((a, b));
                }
            }
        }
        let consistent = !(!queries.is_empty() && unsat.len() == queries.len());
        Some((consistent, unsat, subs))
    }

    pub fn quasi_order_classify(&mut self, queries: &[C]) -> Option<(bool, Vec<C>, Vec<(C, C)>)> {
        // KM_HT_QO_CERTIFY_ONLY (router mode): act as a sound certify-OR-DEFER
        // specialist. The hybrid (INVCOMPOSE+FPROP+SAT+KPSET) certifies the
        // Horn-inverse fragment fast (7581: 31s) but the funnel fallback inherits
        // pre-existing QO limitations (unsat under-detection etc.) — so in router
        // mode we NEVER run the funnel: kpset either certifies (return the sound
        // answer) or we DEFER (return None) and let the orchestrator's CB engine
        // decide. STRUCTURAL pre-gate: the hybrid only pays off when there is an
        // inverse contribution to compose, so defer immediately on a clause set
        // with no inverse bridge (a non-inverse ont gains nothing and would only
        // pay the INVCOMPOSE/sat_mode overhead — the corpus-validation cost cases
        // 11395/3905/3377 were exactly large non-certifying onts). Sound by
        // construction: a deferral yields no answer, so CB (sound+complete) is used.
        let certify_only = std::env::var_os("KM_HT_QO_CERTIFY_ONLY").is_some();
        if certify_only && count_inverse_bridges(&self.clauses) == 0 {
            if std::env::var_os("KM_HT_TRACE").is_some() {
                eprintln!("QO router: no inverse bridge ⇒ defer (not a hybrid candidate)");
            }
            return None;
        }
        // KM_HT_QO_INVCOMPOSE (lever 2): resolve bidirectional inverse bridges into
        // their consumers and drop the bridges, so NO reversed edge is ever created
        // — the inverse contribution becomes a forward ∀/range write. Applied to
        // the WHOLE clause set so both the QO gate AND `consistent()` (the
        // pseudo-model builders) avoid reversed-edge expansion + blocking. Sound
        // (the composed clauses are resolvents; real `∃`-created edges untouched).
        if std::env::var_os("KM_HT_QO_INVCOMPOSE").is_some() {
            let composed = compose_inverse(&self.clauses);
            if std::env::var_os("KM_HT_TRACE").is_some() {
                eprintln!(
                    "INVCOMPOSE: {} -> {} clauses",
                    self.clauses.len(),
                    composed.len()
                );
            }
            self.clauses = mk_recs(&composed);
            // The tableau trigger indexes were built in `new` from the ORIGINAL
            // clauses; rebuild them for the composed set so the per-concept verify
            // tableau (`consistent`) fires valid `(cid, pos)` anchors. Without this
            // `fire_anchor_concept` indexes a stale `pos` out of range and panics
            // (observed on ore_ont_10127 under the hybrid).
            self.rebuild_triggers();
        }
        // KM_HT_QO_KPSET: Konclude G2/G3 inverse-aware single pass — sound+complete
        // and forward-only-fast when no inverse contribution is load-bearing
        // (7581). Tried first; falls through to the gates below when it cannot
        // cleanly certify (a genuinely load-bearing inverse, parked disjunction,
        // or out-of-fragment construct).
        if std::env::var_os("KM_HT_QO_KPSET").is_some() {
            if let Some(r) = self.qo_classify_kpset(queries) {
                return Some(r);
            }
        }
        // Router mode: kpset did not certify (load-bearing residual inverse,
        // parked disjunction, or out-of-fragment) ⇒ DEFER rather than run the
        // (pre-existing-limitations) funnel. CB takes it from here.
        if certify_only {
            if std::env::var_os("KM_HT_TRACE").is_some() {
                eprintln!("QO router: kpset did not certify ⇒ defer to CB");
            }
            return None;
        }
        // KM_HT_QO_PC: the per-concept gate — instead of one global saturation
        // seeding all 73k concepts (whose node×clause cross-product is the wall
        // on big SRIF onts), run one fresh single-seed saturation per query and
        // read its subsumers off. See `qo_classify_perconcept`.
        if std::env::var_os("KM_HT_QO_PC").is_some() {
            // Konclude single-pass first: ONE forward-only global saturation,
            // subsumers read per concept off its own self-node. Returns `None`
            // (falls through to the per-concept gate) only when the global pass
            // can't cleanly decide — a parked disjunction, ∀/range filler
            // pollution, or an out-of-fragment bail. On a Horn SRIF ont (7581)
            // it always succeeds, replacing 73k saturations with one.
            // KM_HT_QO_NOGLOBAL forces the per-concept gate (diagnostic / A-B).
            let res = if std::env::var_os("KM_HT_QO_NOGLOBAL").is_none() {
                match self.qo_classify_global_fwd(queries) {
                    // global pass decided (and, under VERIFY, populated
                    // pc_candidates); fall through to the shared verify block.
                    Some(r) => Some(r),
                    // global pass could not cleanly decide ⇒ per-concept gate.
                    None => self.qo_classify_perconcept(queries),
                }
            } else {
                self.qo_classify_perconcept(queries)
            };
            // KM_HT_QO_VERIFY: confirm the inverse-only candidates with the
            // complete tableau. `qo_classify_perconcept` returns the SOUND
            // forward-only subsumers in `subs`; `pc_candidates` are the extra
            // subsumptions only the inverse-augmented run derived (a complete
            // superset). Each is real iff `A ⊓ ¬B` is unsatisfiable, so test it
            // with `consistent`: keep when entailed, drop the inverse
            // over-derivation otherwise. Likewise `pc_unsat_candidates` are
            // inverse-only unsat verdicts, confirmed with `consistent(A)`. Result
            // = forward-only ∪ confirmed candidates = SOUND + COMPLETE.
            if std::env::var_os("KM_HT_QO_VERIFY").is_some() {
                if let Some((_cons, mut unsat, mut subs)) = res {
                    let cands = std::mem::take(&mut self.pc_candidates);
                    let ucands = std::mem::take(&mut self.pc_unsat_candidates);
                    let trace = std::env::var_os("KM_HT_TRACE").is_some();
                    // KM_HT_QO_PMMERGE: Konclude pseudo-model refutation pre-filter
                    // (study P2). Each tight candidate `(A,B)` is an inverse-only
                    // possible subsumer; most are NOT real (on 7581 all 177 are
                    // spurious). Refute them WITHOUT the blowing-up `consistent(A ⊓
                    // ¬B)`: build ONE model per distinct `A` (`consistent(A)`, far
                    // easier than `A ⊓ ¬B`) and drop `(A,B)` when `B` is false in
                    // that model — a sound refutation (`B` false in a real model of
                    // `A` ⇒ `A ⋢ B`). Survivors (`B` present, so undecided) fall
                    // through to the full tableau verify below; for 7581 that set
                    // is ≈ 0, so the hard `A ⊓ ¬B` blowups are never reached.
                    let cands: Vec<(C, C)> = if std::env::var_os("KM_HT_QO_PMMERGE").is_some()
                        && !cands.is_empty()
                    {
                        let t_pm = std::time::Instant::now();
                        let mut distinct: Vec<C> = cands.iter().map(|(a, _)| *a).collect();
                        distinct.sort_unstable();
                        distinct.dedup();
                        let par = std::env::var("KM_HT_PAR")
                            .ok()
                            .and_then(|s| s.parse::<usize>().ok())
                            .unwrap_or(1)
                            .max(1);
                        let nthreads = par.min(distinct.len().max(1)).max(1);
                        // KM_HT_QO_PMCOMPOSE (lever 1×2): build the per-concept
                        // pseudo-model tableaux over the INVERSE-COMPOSED clause set
                        // (no reversed edges) so `consistent(A)` can use cheap subset
                        // blocking instead of inverse-aware pairwise blocking — the
                        // suspected cost of the slow (45-64s) deterministic model
                        // builds. Sound (composition is semantics-preserving), and
                        // scoped to the model builders only (the gate keeps the
                        // `prop`-optimised original clauses, since composition
                        // diverges the global gate saturation).
                        let template: Vec<Clause> =
                            if std::env::var_os("KM_HT_QO_PMCOMPOSE").is_some() {
                                compose_inverse(&self.clauses)
                            } else {
                                self.clauses.iter().map(|(c, _, _)| c.clone()).collect()
                            };
                        let anywhere = self.anywhere;
                        let next = std::sync::atomic::AtomicUsize::new(0);
                        const PMWORKER_STACK: usize = 512 * 1024 * 1024;
                        let distinct_ref = &distinct;
                        let parts: Vec<Vec<(C, Option<HashSet<C>>)>> = std::thread::scope(|s| {
                            let next = &next;
                            let handles: Vec<_> = (0..nthreads)
                                .map(|_| {
                                    let tmpl = template.clone();
                                    std::thread::Builder::new()
                                        .stack_size(PMWORKER_STACK)
                                        .spawn_scoped(s, move || -> Vec<(C, Option<HashSet<C>>)> {
                                            let mut w = Ht::new(tmpl);
                                            w.set_anywhere(anywhere);
                                            w.set_fast_tableau(); // result-identical speedups
                                            let mut out = Vec::new();
                                            loop {
                                                let i = next.fetch_add(
                                                    1,
                                                    std::sync::atomic::Ordering::Relaxed,
                                                );
                                                if i >= distinct_ref.len() {
                                                    break;
                                                }
                                                let a = distinct_ref[i];
                                                out.push((a, w.model_root_pos(a)));
                                            }
                                            out
                                        })
                                        .expect("spawn pmmerge worker")
                                })
                                .collect();
                            handles.into_iter().map(|h| h.join().unwrap()).collect()
                        });
                        let mut model: HashMap<C, Option<HashSet<C>>> = HashMap::new();
                        for part in parts {
                            for (a, m) in part {
                                model.insert(a, m);
                            }
                        }
                        let before = cands.len();
                        let filtered: Vec<(C, C)> = cands
                            .into_iter()
                            .filter(|(a, b)| match model.get(a) {
                                // A's model lacks B ⇒ B false in a model of A ⇒ refuted.
                                Some(Some(set)) => set.contains(b),
                                // no usable model (A unsat / out-of-fragment) ⇒ keep.
                                _ => true,
                            })
                            .collect();
                        if trace {
                            eprintln!(
                                "QOPC pmmerge: {} candidates -> {} survivors [{} A-models, {:.2}s, {} threads]",
                                before,
                                filtered.len(),
                                distinct.len(),
                                t_pm.elapsed().as_secs_f64(),
                                nthreads
                            );
                        }
                        filtered
                    } else {
                        cands
                    };
                    let t_v = std::time::Instant::now();
                    // Parallel candidate verification: the tight candidates are the
                    // HARD inverse-dependent pairs (each `consistent(A ⊓ ¬B)` ~1-2s on
                    // 7581, not the 0.02s median), so they dominate. Work-steal across
                    // per-thread `Ht` clones (the `classify_parallel` pattern):
                    // `consistent` mutates the Ht, so each worker owns one.
                    let par = std::env::var("KM_HT_PAR")
                        .ok()
                        .and_then(|s| s.parse::<usize>().ok())
                        .unwrap_or(1)
                        .max(1);
                    let nthreads = par.min(cands.len().max(1)).max(1);
                    let template: Vec<Clause> = self.clauses.iter().map(|(c, _, _)| c.clone()).collect();
                    let anywhere = self.anywhere;
                    let next = std::sync::atomic::AtomicUsize::new(0);
                    const VWORKER_STACK: usize = 512 * 1024 * 1024;
                    let cands_ref = &cands;
                    // per worker: (kept pairs, nkept, ndropped, nnone)
                    let parts: Vec<(Vec<(C, C)>, u64, u64, u64)> = std::thread::scope(|s| {
                        let next = &next;
                        let handles: Vec<_> = (0..nthreads)
                            .map(|_| {
                                let tmpl = template.clone();
                                std::thread::Builder::new()
                                    .stack_size(VWORKER_STACK)
                                    .spawn_scoped(s, move || -> (Vec<(C, C)>, u64, u64, u64) {
                                        let mut w = Ht::new(tmpl);
                                        w.set_anywhere(anywhere);
                                        w.set_fast_tableau(); // result-identical speedups
                                        let mut kept: Vec<(C, C)> = Vec::new();
                                        let (mut nk, mut nd, mut nn) = (0u64, 0u64, 0u64);
                                        loop {
                                            let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                                            if i >= cands_ref.len() {
                                                break;
                                            }
                                            let (a, b) = cands_ref[i];
                                            match w.consistent(&[CLit::pos(a), CLit::neg(b)]) {
                                                Some(false) => {
                                                    kept.push((a, b)); // A ⊓ ¬B unsat ⇒ A ⊑ B
                                                    nk += 1;
                                                }
                                                Some(true) => nd += 1, // satisfiable ⇒ A ⋢ B, drop
                                                None => {
                                                    kept.push((a, b)); // undecidable ⇒ keep (stay complete)
                                                    nn += 1;
                                                }
                                            }
                                        }
                                        (kept, nk, nd, nn)
                                    })
                                    .expect("spawn candidate-verify worker")
                            })
                            .collect();
                        handles.into_iter().map(|h| h.join().unwrap()).collect()
                    });
                    let (mut nkept, mut ndropped, mut nnone) = (0u64, 0u64, 0u64);
                    for (kept, nk, nd, nn) in parts {
                        subs.extend(kept);
                        nkept += nk;
                        ndropped += nd;
                        nnone += nn;
                    }
                    // inverse-only unsat candidates (usually empty) — sequential.
                    for a in ucands {
                        match self.consistent(&[CLit::pos(a)]) {
                            Some(false) => unsat.push(a), // confirmed unsatisfiable
                            Some(true) => {}              // satisfiable ⇒ inverse over-derivation
                            None => unsat.push(a),        // undecidable ⇒ keep (stay complete)
                        }
                    }
                    let consistent = !(!queries.is_empty() && unsat.len() == queries.len());
                    if trace {
                        eprintln!(
                            "QOPC verify: cand_kept={} cand_dropped={} none={} unsat={} [verify {:.2}s, {} threads]",
                            nkept, ndropped, nnone, unsat.len(), t_v.elapsed().as_secs_f64(), nthreads
                        );
                    }
                    return Some((consistent, unsat, subs));
                }
            }
            return res;
        }
        let qset: HashSet<C> = queries.iter().copied().collect();

        // --- Collect the named concepts (positive-polarity shared nodes). ---
        let named_concepts: Vec<C> = queries.to_vec();

        // --- ONE global shared-node saturation with the harvest rule. We keep
        // `qs` alive across both phases: the residue SAT test (Phase 1 sat +
        // Phase 2 subsumption) branches the open disjunctions IN PLACE over
        // this saturated shared model, with trail rollback — the Konclude
        // architecture. No `self.consistent()` (the 671-node fresh rebuild) is
        // needed; `None` from a residue test ⇒ bail to the caller's fallback. ---
        if std::env::var_os("KM_HT_TRACE").is_some() {
            eprintln!("QOC entry queries={} clauses={}", queries.len(), self.clauses.len());
        }
        let mut qs = QoSat::new(&self.clauses);
        // Sound ELI saturation: re-fire role/∀ clauses when their guard concept
        // arrives at a node that already has the relevant edge. Without this the
        // global pass misses inverse (∀R⁻) and ∀-role consequences whenever the
        // guard is derived after the edge — an incompleteness on SRIF onts. Made
        // affordable by the trigger-keyed `role_guard_trig` re-fire (see add_lit);
        // KM_HT_QO_NOCOMPLETE restores the old edge-time-only firing for A/B.
        qs.complete_roles = std::env::var_os("KM_HT_QO_NOCOMPLETE").is_none();
        if std::env::var_os("KM_HT_TRACE").is_some() {
            eprintln!("QOC QoSat::new done, calling saturate_global");
        }
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
    fn inverse_role_propagates_universal_back() {
        // r and s = r⁻ with the cb_to_ht bridging clauses. A ⊑ ∃r.B and
        // B ⊑ ∀r⁻.¬A: the r-successor's back r⁻-edge to the root forces ¬A at
        // the root, which carries A ⇒ {A} is unsat. Verifies that an inverse
        // edge is materialised (bridging clause fires on the ∃-created edge) and
        // that a ∀ over the inverse role propagates back along it.
        const S: R = 1; // r⁻
        let cls = vec![
            // A ⊑ ∃r.B
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            // bridging: r(x,y) → r⁻(y,x)
            Clause::new(vec![role(R0, X, 1)], vec![role(S, 1, X)]),
            // bridging: r⁻(x,y) → r(y,x)
            Clause::new(vec![role(S, X, 1)], vec![role(R0, 1, X)]),
            // B ⊑ ∀r⁻.¬A  ==  B(x) ∧ r⁻(x,y) → ¬A(y)
            Clause::new(vec![con(false, B, X), role(S, X, 1)], vec![con(true, A, 1)]),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(false));
    }
    #[test]
    fn inverse_role_consistent_without_clash() {
        // Same shape, but the back-propagated universal is ∀r⁻.¬D and D never
        // holds at the root, so no clash ⇒ {A} is consistent. Guards against a
        // spurious inverse clash (over-propagation).
        const S: R = 1; // r⁻
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![role(R0, X, 1)], vec![role(S, 1, X)]),
            Clause::new(vec![role(S, X, 1)], vec![role(R0, 1, X)]),
            Clause::new(vec![con(false, B, X), role(S, X, 1)], vec![con(true, D, 1)]),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(true));
    }
    #[test]
    fn functional_merge_forces_clash() {
        // KM_HT_NUMBER: r functional (≤1 r): r(x,y1) ∧ r(x,y2) → y1 = y2.
        // A ⊑ ∃r.B, A ⊑ ∃r.C, B ⊓ C ⊑ ⊥. The two distinct r-successors are
        // merged by the functional clause; the survivor then carries both B and
        // C, which clash ⇒ {A} unsat. Verifies the Eq-head node-merge primitive
        // (copies the victim's label onto the survivor, with the merge dep).
        const C2: C = 2; // C, disjoint from B
        // Harmless to leave set for the test binary: only Eq-head clauses consult
        // `number`, and no other test uses Eq heads.
        std::env::set_var("KM_HT_NUMBER", "1");
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, C2, X)]),
            // functional r: r(x,y1) ∧ r(x,y2) → y1 = y2
            Clause::new(vec![role(R0, X, 1), role(R0, X, 2)], vec![Atom::Eq { s: 1, t: 2 }]),
            // B ⊓ C ⊑ ⊥
            Clause::new(vec![con(false, B, X), con(false, C2, X)], vec![]),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(false));
    }
    #[test]
    fn merge_inverse_existential_terminates() {
        // Functional r merges A's two r-successors; the merged node carries B,
        // which fires ∃ over the inverse role s=r⁻, and the bridging clauses
        // re-materialise edges. Exercises merge × inverse × ∃-over-inverse
        // together — must terminate (the back-edge to the root satisfies ∃s.A).
        std::env::set_var("KM_HT_NUMBER", "1");
        const S: R = 1; // r⁻
        const C2: C = 2;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, C2, X)]),
            // r functional
            Clause::new(vec![role(R0, X, 1), role(R0, X, 2)], vec![Atom::Eq { s: 1, t: 2 }]),
            // inverse bridging r <-> s
            Clause::new(vec![role(R0, X, 1)], vec![role(S, 1, X)]),
            Clause::new(vec![role(S, X, 1)], vec![role(R0, 1, X)]),
            // B ⊑ ∃s.A : the merged node spawns an r-predecessor labelled A
            Clause::new(vec![con(false, B, X)], vec![exists(S, false, A, X)]),
        ];
        let _ = ht(cls).consistent(&[CLit::pos(A)]);
    }
    #[test]
    fn functional_merge_consistent_when_compatible() {
        // Same functional r, but the two successors carry B and D which are NOT
        // disjoint, so the merge yields a consistent survivor ⇒ {A} sat. Guards
        // against a spurious merge clash.
        std::env::set_var("KM_HT_NUMBER", "1");
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, D, X)]),
            Clause::new(vec![role(R0, X, 1), role(R0, X, 2)], vec![Atom::Eq { s: 1, t: 2 }]),
        ];
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

    #[test]
    fn qosat_edge_index_role_chain() {
        // Drives BOTH elc-style edge indexes in QoSat saturation:
        //  - the role_*_trig edge indexes: a fresh r-edge fires only the guardless
        //    r-clauses (transitivity) plus the target-guarded join clause keyed by
        //    G, not every role clause.
        //  - in_edges: the (None, Some) predecessor branch of match_body, hit
        //    when transitivity anchors its SECOND atom r(y,z) on a new edge and
        //    must find the predecessor x with r(x,y) via the incoming index.
        // A ⊑ ∃r.B, B ⊑ ∃r.G, r∘r ⊑ r, r(x,z) ⊓ G(z) ⊑ H.  Seeding A builds the
        // shared chain  node(A) --r--> node(B) --r--> node(G);  transitivity
        // derives node(A) --r--> node(G) (this is the in_edges-driven step), and
        // the join clause then puts H on node(A). The result is exact (Horn, no
        // parked disjunction), so it is a faithful check that the indexed
        // saturation derives the same closure the full scan would.
        const G: C = 4;
        const H: C = 5;
        let y: Var = 1;
        let z: Var = 2;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, B, X)], vec![exists(R0, false, G, X)]),
            Clause::new(vec![role(R0, X, y), role(R0, y, z)], vec![role(R0, X, z)]),
            Clause::new(vec![role(R0, X, z), con(false, G, z)], vec![con(false, H, X)]),
        ];
        let recs = mk_recs(&cls);
        let mut qs = QoSat::new(&recs);
        let g = qs.saturate_global(&[A]);
        assert!(!g.unsupported, "saturation must converge in-fragment");
        let na = qs.concept_node[&CLit::pos(A)];
        assert!(
            g.label_pos[na].contains(&H),
            "H must be derived at node(A) via the transitive r-chain"
        );
    }

    #[test]
    fn qosat_global_inverse_complete() {
        // GLOBAL saturation as a SOUND ELI saturator (the 7581 path).
        // A ⊑ ∃r.B, B ⊑ D, and D ⊑ ∀r⁻.E encoded as  D(y) ⊓ r(x,y) → E(x).
        // Seeding all concepts builds the shared edge node(A) --r--> node(B);
        // D reaches node(B) via B ⊑ D, i.e. AFTER the edge exists, so E only
        // reaches node(A) (the r-predecessor) if the D-guarded backward clause
        // re-fires on the incoming edge — exactly the trigger-keyed
        // `complete_roles` mechanism. Horn, so the closure is exact.
        const E: C = 7;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, B, X)], vec![con(false, D, X)]),
            Clause::new(vec![con(false, D, y), role(R0, X, y)], vec![con(false, E, X)]),
        ];
        let recs = mk_recs(&cls);
        // WITH complete_roles: the inverse consequence E reaches node(A).
        let mut qs = QoSat::new(&recs);
        qs.complete_roles = true;
        let g = qs.saturate_global(&[A, B, D, E]);
        assert!(!g.unsupported, "in-fragment SRIF saturation must converge");
        let na = qs.concept_node[&CLit::pos(A)];
        assert!(
            g.label_pos[na].contains(&E),
            "E (D ⊑ ∀r⁻.E, backward over the A→B edge) must reach node(A)"
        );
        // node(B) itself is not an r-predecessor of a D-node here, so it has D
        // but not E — guards must propagate only along real edges, not spuriously.
        let nb = qs.concept_node[&CLit::pos(B)];
        assert!(g.label_pos[nb].contains(&D));
        assert!(!g.label_pos[nb].contains(&E), "E must not appear without an r-edge");
    }

    #[test]
    fn qosat_prop_broadcast_shared() {
        // Backward-link broadcast to MULTIPLE shared predecessors. A1 ⊑ ∃r.B,
        // A2 ⊑ ∃r.B, B ⊑ D, and R(x,y) ⊓ D(y) → E(x). The consequence E is
        // computed ONCE at node(B) (the filler) and broadcast to both A1 and A2;
        // node(B) itself never gets E. This is the elc per-(role,filler) sharing
        // that replaces re-matching the NF4 clause on every incoming edge.
        const A2: C = 10;
        const E: C = 7;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A2, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, B, X)], vec![con(false, D, X)]),
            Clause::new(vec![con(false, D, y), role(R0, X, y)], vec![con(false, E, X)]),
        ];
        let recs = mk_recs(&cls);
        let mut qs = QoSat::new(&recs);
        qs.complete_roles = true;
        let g = qs.saturate_global(&[A, A2, B, D, E]);
        assert!(!g.unsupported);
        let na = qs.concept_node[&CLit::pos(A)];
        let na2 = qs.concept_node[&CLit::pos(A2)];
        let nb = qs.concept_node[&CLit::pos(B)];
        assert!(g.label_pos[na].contains(&E), "A1 must get E via prop broadcast");
        assert!(g.label_pos[na2].contains(&E), "A2 must get E via prop broadcast");
        assert!(!g.label_pos[nb].contains(&E));
    }

    #[test]
    fn qosat_fprop_forward_broadcast() {
        // Forward-broadcast mirror of `qosat_prop_broadcast_shared`. The
        // head-on-TARGET Horn NF4 `R(sv,tv) ⊓ D(sv) → E(tv)` (the shape
        // `compose_inverse` emits) must land `E` on the role-SUCCESSOR, broadcast
        // once per (source, role), and reach a successor whether the guard `D`
        // arrives before or after the edge. Setup: A ⊑ ∃r.B, A ⊑ D, and the
        // head-on-target clause. E must appear at node(B) (A's r-successor), NOT
        // at node(A). With fprop OFF the same clause would instead set
        // qo_insufficient (a head on a non-anchor var), so this also confirms the
        // capture routes it away from the per-edge `apply_head` path.
        const E: C = 7;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(false, D, X)]),
            // R(X,y) ⊓ D(X) → E(y): guard D on the role SOURCE, head E on TARGET.
            Clause::new(vec![con(false, D, X), role(R0, X, y)], vec![con(false, E, y)]),
        ];
        let recs = mk_recs(&cls);
        let mut qs = QoSat::new_opts(&recs, false, true); // fprop_on = true
        qs.complete_roles = true;
        let g = qs.saturate_global(&[A, B, D, E]);
        assert!(!g.unsupported);
        assert!(!qs.qo_insufficient, "fprop capture must route the head-on-target clause away from apply_head");
        let na = qs.concept_node[&CLit::pos(A)];
        let nb = qs.concept_node[&CLit::pos(B)];
        assert!(g.label_pos[nb].contains(&E), "B (A's r-successor) must get E via fprop forward broadcast");
        assert!(!g.label_pos[na].contains(&E), "A (the source) must NOT get E");
    }

    #[test]
    fn qopc_range_no_cross_role_pollution() {
        // The 7581 soundness bug, minimised. Two roles each with a range write to
        // the SAME filler concept B:
        //   A  ⊑ ∃R0.B,  A2 ⊑ ∃R1.B,  range(R0)=Cr,  range(R1)=Cs,
        //   ∃R0.Cs ⊑ Spur   (spurious if B's R0-successor wrongly carries Cs),
        //   ∃R0.Cr ⊑ Good   (legitimate: B's R0-successor genuinely carries Cr).
        // Concept-keyed fillers share one node(B) that accumulates BOTH Cr and Cs,
        // so `∃R0.Cs ⊑ Spur` fires for A — UNSOUND. Role-keyed fillers give A an
        // R0-class filler (Cr only) and A2 an R1-class filler (Cs only), so Spur
        // never fires while Good still does.
        const A2: C = 10;
        const CR: C = 4;
        const CS: C = 5;
        const SPUR: C = 6;
        const GOOD: C = 7;
        const R1: R = 1;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A2, X)], vec![exists(R1, false, B, X)]),
            Clause::new(vec![role(R0, X, y)], vec![con(false, CR, y)]),
            Clause::new(vec![role(R1, X, y)], vec![con(false, CS, y)]),
            Clause::new(vec![role(R0, X, y), con(false, CS, y)], vec![con(false, SPUR, X)]),
            Clause::new(vec![role(R0, X, y), con(false, CR, y)], vec![con(false, GOOD, X)]),
        ];
        let mut ht = ht(cls);
        let (cons, _unsat, subs) = ht
            .qo_classify_perconcept(&[A, A2, B, CR, CS, SPUR, GOOD])
            .unwrap();
        assert!(cons);
        assert!(
            subs.contains(&(A, GOOD)),
            "A ⊑ Good must hold (R0-range Cr reaches B's R0-filler)"
        );
        assert!(
            !subs.contains(&(A, SPUR)),
            "A ⊑ Spur is the cross-role range pollution — must NOT be derived"
        );
    }

    // ---- Per-concept QoSat gate (KM_HT_QO_PC) ----

    #[test]
    fn qopc_subsumption_chain() {
        // A ⊑ B ⊑ D: per-concept gate yields {A⊑B, A⊑D, B⊑D}, nothing reversed.
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![con(false, B, X)]),
            Clause::new(vec![con(false, B, X)], vec![con(false, D, X)]),
        ];
        let mut ht = ht(cls);
        let (cons, unsat, mut subs) = ht.qo_classify_perconcept(&[A, B, D]).unwrap();
        subs.sort();
        assert!(cons && unsat.is_empty());
        assert_eq!(subs, vec![(A, B), (A, D), (B, D)]);
    }

    #[test]
    fn qopc_role_guard_after_edge_complete() {
        // Completeness under guard-after-edge: A ⊑ ∃r.B, A ⊑ Guard,
        // Guard(x) ⊓ r(x,y) ⊑ E. The role clause must fire whichever of the
        // edge / the guard concept lands at A first ⇒ A ⊑ E and A ⊑ Guard.
        const GUARD: C = 6;
        const E: C = 7;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(false, GUARD, X)]),
            Clause::new(vec![con(false, GUARD, X), role(R0, X, y)], vec![con(false, E, X)]),
        ];
        let mut ht = ht(cls);
        let (_, _, subs) = ht.qo_classify_perconcept(&[A, B, GUARD, E]).unwrap();
        assert!(subs.contains(&(A, E)), "A ⊑ E must be derived (guard-after-edge)");
        assert!(subs.contains(&(A, GUARD)));
    }

    #[test]
    fn qopc_transitive_chain() {
        // Same closure as qosat_edge_index_role_chain, via the per-concept path:
        // A ⊑ ∃r.B, B ⊑ ∃r.G, r∘r ⊑ r, r(x,z) ⊓ G(z) ⊑ H ⇒ A ⊑ H.
        const G: C = 4;
        const H: C = 5;
        let y: Var = 1;
        let z: Var = 2;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, B, X)], vec![exists(R0, false, G, X)]),
            Clause::new(vec![role(R0, X, y), role(R0, y, z)], vec![role(R0, X, z)]),
            Clause::new(vec![role(R0, X, z), con(false, G, z)], vec![con(false, H, X)]),
        ];
        let mut ht = ht(cls);
        let (_, _, subs) = ht.qo_classify_perconcept(&[A, H]).unwrap();
        assert!(subs.contains(&(A, H)), "A ⊑ H via transitive r-chain (per-concept)");
    }

    #[test]
    fn qopc_unsat_concept() {
        // A ⊑ B and A ⊑ ¬B ⇒ A unsatisfiable; B stays satisfiable; KB consistent.
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![con(false, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
        ];
        let mut ht = ht(cls);
        let (cons, unsat, _) = ht.qo_classify_perconcept(&[A, B]).unwrap();
        assert!(cons);
        assert_eq!(unsat, vec![A]);
    }

    #[test]
    fn qopc_functional_eq_bails() {
        // Functional r with two distinct r-successors forces an Eq head, which
        // QoSat has no merge for ⇒ the per-concept gate bails to fallback (None),
        // soundly (it declines rather than answers wrong).
        const C1: C = 8;
        const C2: C = 9;
        let y: Var = 1;
        let z: Var = 2;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, C1, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, C2, X)]),
            Clause::new(vec![role(R0, X, y), role(R0, X, z)], vec![Atom::Eq { s: y, t: z }]),
        ];
        let mut ht = ht(cls);
        assert_eq!(ht.qo_classify_perconcept(&[A, C1, C2]), None);
    }

    // ---- KPSet inverse-aware gate (KM_HT_QO_KPSET, Konclude G2/G3 port) ----

    #[test]
    fn kpset_inert_inverse_certifies() {
        // The 7581 shape with a NON-load-bearing inverse:
        //   A ⊑ ∃r1.B,  r1(x,y) → r2(y,x)  (back-edge node(B) --r2--> A),
        //   A ⊑ D,  ∃r2.D ⊑ E              (would WRITE E onto the shared node(B)),
        //   B ⊑ E                          (E is ALREADY forward-present at node(B)).
        // The inverse-anchored write of E to node(B) is a containment check that
        // PASSES (E already there) ⇒ kp_miss = 0 ⇒ the gate CERTIFIES (returns
        // Some) with the real subsumers and no spurious A⊑E pollution.
        const R1: R = 1;
        const R2: R = 2;
        const E: C = 7;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R1, false, B, X)]),
            Clause::new(vec![role(R1, X, y)], vec![role(R2, y, X)]), // inverse bridge
            Clause::new(vec![con(false, A, X)], vec![con(false, D, X)]),
            Clause::new(vec![role(R2, X, y), con(false, D, y)], vec![con(false, E, X)]), // ∃r2.D ⊑ E
            Clause::new(vec![con(false, B, X)], vec![con(false, E, X)]), // B ⊑ E (forward)
        ];
        let mut ht = ht(cls);
        let (cons, _unsat, subs) = ht
            .qo_classify_kpset(&[A, B, D, E])
            .expect("inert inverse must certify (Some)");
        assert!(cons);
        assert!(subs.contains(&(B, E)), "B ⊑ E is real (forward) and must be kept");
        assert!(subs.contains(&(A, D)), "A ⊑ D (forward) must be kept");
        assert!(
            !subs.contains(&(A, E)),
            "A ⊑ E is not entailed and must NOT be derived"
        );
    }

    #[test]
    fn kpset_loadbearing_inverse_defers_not_oversderive() {
        // Same shape WITHOUT the forward B ⊑ E: the inverse-anchored write of E
        // onto the shared node(B) is NOT forward-present, so the containment
        // check MISSES ⇒ kp_insufficient ⇒ the gate DECLINES (None) rather than
        // deriving the spurious B ⊑ E. This is the 7581 pollution caught soundly:
        // never written, routed to the complete tableau instead.
        const R1: R = 1;
        const R2: R = 2;
        const E: C = 7;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R1, false, B, X)]),
            Clause::new(vec![role(R1, X, y)], vec![role(R2, y, X)]), // inverse bridge
            Clause::new(vec![con(false, A, X)], vec![con(false, D, X)]),
            Clause::new(vec![role(R2, X, y), con(false, D, y)], vec![con(false, E, X)]), // ∃r2.D ⊑ E
        ];
        let mut ht = ht(cls);
        assert!(
            ht.qo_classify_kpset(&[A, B, D, E]).is_none(),
            "load-bearing/spurious inverse must defer (None), never over-derive B⊑E"
        );
    }

    #[test]
    fn pmmerge_model_root_refutes_nonsubsumer() {
        // Konclude pseudo-model refutation (concept part). A ⊑ B; CC unrelated.
        // consistent(&[A])'s root model FORCES B (A⊑B) but not CC, so the model
        // refutes the candidate A⊑CC (CC absent ⇒ A ⋢ CC) and cannot refute A⊑B
        // (B present ⇒ falls through to the full tableau, which confirms it).
        const CC: C = 7;
        let cls = vec![Clause::new(vec![con(false, A, X)], vec![con(false, B, X)])];
        let mut ht = ht(cls);
        let m = ht.model_root_pos(A).expect("A is satisfiable");
        assert!(m.contains(&B), "B forced in A's model (A⊑B) ⇒ NOT refutable");
        assert!(!m.contains(&CC), "CC absent in A's model ⇒ refutes A⊑CC");
    }
}
