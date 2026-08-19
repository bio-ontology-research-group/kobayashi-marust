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

// KM_HT_QO_SPLIT (port #2) diagnostics: redirects performed, ∀-critical
// insufficiency inserts (the share that split could in principle remove), and
// cardinality Eq-head insufficiency inserts (the separate cardinality-merge gap).
/// Debug formatter for a clause Atom (residue histogram diagnostic).
fn fmt_atom_dbg(a: &Atom) -> String {
    match a {
        Atom::Concept { lit, t } => {
            format!("{}C{}@{}", if lit.neg { "¬" } else { "" }, lit.c, t)
        }
        Atom::Role { r, s, t } => format!("R{}({},{})", r, s, t),
        Atom::Exists { r, fil, t } => {
            format!("∃R{}.{}C{}@{}", r, if fil.neg { "¬" } else { "" }, fil.c, t)
        }
        Atom::Eq { s, t } => format!("Eq({},{})", s, t),
    }
}

/// KM_HT_QO_NODECERTAIN: build `cid → ⋂-closure D of its disjuncts` for the given
/// concept-level disjunction clause ids. `closure(h)` is `h`'s forward saturation
/// label; `D = ⋂_h closure(h)` is the set true in EVERY branch. A disjunction whose
/// intersection is just the disjuncts themselves (or empty) carries no extra certain
/// consequence and is omitted. The closures are computed once per unique disjunct
/// head with a single reused `QoSat`.
fn build_nodecertain_map(
    clauses: &[ClauseRec],
    cids: &HashSet<usize>,
    fprop: bool,
    cap: usize,
) -> HashMap<usize, Vec<C>> {
    // unique disjunct heads across all concept-level disjunctions
    let mut heads: Vec<C> = Vec::new();
    {
        let mut seen: HashSet<C> = HashSet::new();
        for &cid in cids {
            for a in clauses[cid].0.head.iter() {
                if let Atom::Concept { lit, .. } = a {
                    if !lit.neg && seen.insert(lit.c) {
                        heads.push(lit.c);
                    }
                }
            }
        }
    }
    let mut closure: HashMap<C, HashSet<C>> = HashMap::new();
    let mut qf = QoSat::new_opts(clauses, true, fprop);
    qf.complete_roles = true;
    qf.node_cap = cap;
    for &h in &heads {
        qf.reset();
        let rf = qf.saturate(&[CLit::pos(h)]);
        let lab: HashSet<C> = rf.root_label.into_iter().collect();
        closure.insert(h, lab);
    }
    let mut out: HashMap<usize, Vec<C>> = HashMap::new();
    for &cid in cids {
        let hs: Vec<C> = clauses[cid]
            .0
            .head
            .iter()
            .filter_map(|a| match a {
                Atom::Concept { lit, .. } if !lit.neg => Some(lit.c),
                _ => None,
            })
            .collect();
        if hs.len() < 2 {
            continue;
        }
        let mut d: HashSet<C> = match closure.get(&hs[0]) {
            Some(c) => c.clone(),
            None => continue,
        };
        for h in &hs[1..] {
            match closure.get(h) {
                Some(c) => d.retain(|x| c.contains(x)),
                None => {
                    d.clear();
                    break;
                }
            }
        }
        // drop the disjunct heads themselves (already handled by the clause)
        for h in &hs {
            d.remove(h);
        }
        if !d.is_empty() {
            out.insert(cid, d.into_iter().collect());
        }
    }
    out
}

static DBG_SPLIT: AtomicU64 = AtomicU64::new(0);
static DBG_PM_COUNT: AtomicU64 = AtomicU64::new(0);
static DBG_PM_MAXNODES: AtomicU64 = AtomicU64::new(0);
static DBG_PM_TOTNODES: AtomicU64 = AtomicU64::new(0);
static DBG_PM_TOTCONC: AtomicU64 = AtomicU64::new(0);
static DBG_PM_MAXCONC: AtomicU64 = AtomicU64::new(0);
static DBG_FORALL_INSUFF: AtomicU64 = AtomicU64::new(0);
static DBG_CARD_INSUFF: AtomicU64 = AtomicU64::new(0);
// KM_HT_QO_CARDMERGE: count of forced successor merges actually performed.
static DBG_CARDMERGE: AtomicU64 = AtomicU64::new(0);
// Why a forced Eq fell through to the card_defer fallback instead of merging.
static DBG_EQ_NONFILLER: AtomicU64 = AtomicU64::new(0); // a successor is not a filler
static DBG_EQ_NOROLE: AtomicU64 = AtomicU64::new(0); // eq_merge_role None (shape)
static DBG_EQ_UNSAT: AtomicU64 = AtomicU64::new(0); // a successor already unsat (killed merge)
static DBG_EQ_OTHER: AtomicU64 = AtomicU64::new(0); // empty seed / budget
                                                    // harvest churn probe: total harvest_disj calls vs those that added ZERO lits (re-scan waste)
static DBG_HARVEST_DISJ: AtomicU64 = AtomicU64::new(0);
static DBG_HARVEST_NOOP: AtomicU64 = AtomicU64::new(0);
// QO-saturation work-volume probe (gated on `KM_HT_QO_EDGEPROBE`, off by default so
// production pays nothing — every increment sits behind the cached `edgeprobe` bool).
// These locate where a non-converging giant (14817/9663/...) burns its time: which
// per-step primitive dominates, and whether labels bloat. Reusable for any QO
// throughput tuning, not just the edge loop. `KM_HT_QO_EDGEPROBE=<n>` sets the
// QOEDGE print interval (default 2000); the counters print in the QOEDGE/QOGRFIRE
// trace lines under `KM_HT_TRACE`.
static DBG_FRC: AtomicU64 = AtomicU64::new(0); // fire_role_clause calls
static DBG_MATCH: AtomicU64 = AtomicU64::new(0); // match_body recursive calls
static DBG_APPLY: AtomicU64 = AtomicU64::new(0); // apply_head calls
static DBG_FPROPE: AtomicU64 = AtomicU64::new(0); // fprop_emit calls
static DBG_KPW: AtomicU64 = AtomicU64::new(0); // kp_write calls
static DBG_ADDLIT: AtomicU64 = AtomicU64::new(0); // add_lit calls (true inserts + noops)
static DBG_GRFIRE: AtomicU64 = AtomicU64::new(0); // guard_refire pops processed
static DBG_TRIGSCAN: AtomicU64 = AtomicU64::new(0); // lits scanned in src/tgt-trig to_fire build
static DBG_MAXLABEL: AtomicU64 = AtomicU64::new(0); // max label size seen in a to_fire scan
static DBG_EVALSCAN: AtomicU64 = AtomicU64::new(0); // total `pending` entries scanned by eval_parked_at
static DBG_KILLSCAN: AtomicU64 = AtomicU64::new(0); // total `pending` entries scanned by kill_node
static DBG_KILLS: AtomicU64 = AtomicU64::new(0); // kill_node calls (node clashes)

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

use super::{Atom, CLit, Clause, Node, Var, C, R, X};

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

/// Transitively close a confirmed subsumption relation `A ⊑ B`.
///
/// Phase 2 tests only the candidates in each concept's single captured model
/// root label (plus a told-clause closure). A true subsumer that is inferred
/// (e.g. via domain/range, not a structural `A(x)→B(x)` clause) and is absent
/// from that one model's label is never a candidate, so `A ⊑ B ⊑ C` can yield
/// `A ⊑ B` and `B ⊑ C` while dropping the entailed `A ⊑ C` (ore_ont_7499: 3297
/// such pairs to the BFO/CHEBI upper ontology). Closing the relation restores
/// them.
///
/// Unconditionally sound: subsumption is transitive, so every added pair is
/// already entailed by `subs`; it only ADDS pairs and never removes one, so an
/// already-closed (correct) output is returned unchanged and no unsound pair can
/// be introduced unless `subs` already contained one. Runs on the (small) set of
/// query concepts the HT classifies, not the full signature.
pub fn transitive_close_subs(subs: Vec<(C, C)>) -> Vec<(C, C)> {
    let mut sup: HashMap<C, HashSet<C>> = HashMap::new();
    for (a, b) in &subs {
        sup.entry(*a).or_default().insert(*b);
    }
    let keys: Vec<C> = sup.keys().copied().collect();
    let mut changed = true;
    while changed {
        changed = false;
        for &a in &keys {
            let bs: Vec<C> = sup[&a].iter().copied().collect();
            let mut add: Vec<C> = Vec::new();
            for b in bs {
                if let Some(bsup) = sup.get(&b) {
                    for &c in bsup {
                        if c != a && !sup[&a].contains(&c) {
                            add.push(c);
                        }
                    }
                }
            }
            if !add.is_empty() {
                let e = sup.get_mut(&a).unwrap();
                for c in add {
                    e.insert(c);
                }
                changed = true;
            }
        }
    }
    let mut out: Vec<(C, C)> = Vec::new();
    for (a, bs) in &sup {
        for &b in bs {
            out.push((*a, b));
        }
    }
    if std::env::var_os("KM_HT_STATS").is_some() {
        eprintln!("KM_HT [close-subs] in={} out={}", subs.len(), out.len());
    }
    out
}

pub fn dep_add(d: &DepSet, level: Level) -> DepSet {
    match d {
        None => Some(Rc::new(DepNode { level, rest: None })),
        Some(n) => {
            if level == n.level {
                d.clone()
            } else if level > n.level {
                Some(Rc::new(DepNode {
                    level,
                    rest: d.clone(),
                }))
            } else {
                let tail = dep_add(&n.rest, level);
                Some(Rc::new(DepNode {
                    level: n.level,
                    rest: tail,
                }))
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
                Some(Rc::new(DepNode {
                    level: na.level,
                    rest: tail,
                }))
            } else if na.level > nb.level {
                let tail = dep_union(&na.rest, b);
                Some(Rc::new(DepNode {
                    level: na.level,
                    rest: tail,
                }))
            } else {
                let tail = dep_union(a, &nb.rest);
                Some(Rc::new(DepNode {
                    level: nb.level,
                    rest: tail,
                }))
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
                Some(Rc::new(DepNode {
                    level: n.level,
                    rest: tail,
                }))
            }
        }
    }
}

// ============================== Ext ========================================

#[derive(Clone)]
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
    /// Nominals: a node was recorded as a carrier of nominal concept `c`; on
    /// backtrack pop the (LIFO-last) entry of `nom_carriers[c]`.
    NomCarrier(C),
    /// KM_HT_CARD: a distinct (inequality) edge `a≠b` was recorded; on backtrack
    /// drop the (LIFO-last) entry from both `distinct[a]` and `distinct[b]`.
    Distinct(Node, Node),
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
#[derive(Clone)]
struct PendingDisj {
    disjuncts: Vec<(Node, CLit)>,
    bdep: DepSet,
    at: usize,
}

/// A deferred qualified-cardinality choice, branched at the dfs fixpoint like a
/// `PendingDisj`. `at` = trail length at recording, so a backtrack past the
/// matching body drops it (suffix pop, like `pending`). Two head shapes share
/// this record:
///   - pure ≤n AtMost: head `⋁ Eq(yi,yj)` fired with n+1 distinct r-successors in
///     the filler; exactly one candidate `pairs` entry must be identified
///     (merged). `concepts` is empty.
///   - ≥n recognition: head `Q ∨ ⋁ Eq(yi,yj)` (the contrapositive of `≥n r.F ⊑ Q`)
///     fired with n distinct r-successors in F. The branch either asserts the
///     recognized concept `Q` (a `concepts` entry) OR identifies one of the
///     candidate successor pairs. `concepts` holds the recognized literal(s).
/// A branch option is thus "assert a live concept" or "merge a live pair";
/// liveness (concept present/dead, pair already merged) is recomputed at branch
/// time, so the stored sets are the full original disjuncts.
#[derive(Clone)]
struct MergeDisj {
    concepts: Vec<(Node, CLit)>,
    pairs: Vec<(Node, Node)>,
    bdep: DepSet,
    at: usize,
}

/// KM_HT_CARD: a first-class qualified number restriction, the faithful Konclude
/// representation (`CCATLEAST` / `CCATMOST` concepts) rather than KM's clausified
/// `⋁ Eq` pigeonhole. A fresh marker concept id `c` carries the restriction onto
/// a node's label; when `c` is added, `apply_atleast` / `apply_atmost` fire on
/// `(node, role, filler, n)`. Built once (`card_defs`), keyed by marker concept.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CardKind {
    /// `≥n role.filler` (Konclude `applyATLEASTRule`).
    Min,
    /// `≤n role.filler` (Konclude `applyATMOSTRule`).
    Max,
}

#[derive(Clone, Copy, Debug)]
struct CardDef {
    kind: CardKind,
    n: u32,
    role: R,
    filler: CLit,
}

/// A deferred ∃-obligation `node ⊑ ∃r.fil` recorded when its clause body matched.
#[derive(Clone)]
struct Oblig {
    n: Node,
    r: R,
    fil: CLit,
    dep: DepSet,
    at: usize,
}

/// KM_HT_CARD: a deferred number-restriction obligation recorded when its marker
/// concept landed on node `n`. For `≥bound` (Konclude `applyATLEASTRule`) the
/// blocking-aware obligation pass creates the missing pairwise-distinct
/// `role.filler` successors; for `≤bound` (`applyATMOSTRule`) the `Scan::Sat`
/// step qualifies (choose) and merges excess `role.filler` successors. Like
/// `Oblig`, dropped as a trail-ordered suffix on backtrack (`at`).
#[derive(Clone)]
struct CardReq {
    n: Node,
    role: R,
    filler: CLit,
    bound: u32,
    dep: DepSet,
    at: usize,
}

#[derive(Clone)]
pub struct Ext {
    concepts: Vec<HashMap<CLit, DepSet>>,
    /// Dense encoded-literal membership used only by the subset-blocking hot
    /// path. `concepts` remains authoritative (and retains dependencies); this
    /// shadow turns repeated hash probes into contiguous word operations.
    block_bits: Option<Vec<Vec<u64>>>,
    out_edges: Vec<Vec<(R, Node, DepSet)>>,
    in_edges: Vec<Vec<(R, Node, DepSet)>>,
    /// KM_HT_CARD: inequality / distinct edges (Konclude `CDistinctHash`). Two
    /// nodes asserted DISTINCT (created pairwise-distinct by `≥n`, or carrying
    /// distinct nominals) may NOT be merged: a `≤n` merge that would identify a
    /// distinct pair is a CLASH (Konclude `isIndividualNodesMergeable` returns
    /// false on a distinct edge). Symmetric: `distinct[a]` holds `(b, dep)` and
    /// vice-versa. Trail-recorded (`Trail::Distinct`) so a backtrack drops it;
    /// `merge_into` re-targets a victim's distinct edges onto the survivor.
    distinct: Vec<Vec<(Node, DepSet)>>,
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
    /// ≤n qualified-cardinality merge choices awaiting a branch (KM_HT_QMERGE).
    pending_merge: Vec<MergeDisj>,
    /// KM_HT_QMERGE: enable the n≥2 qualified ≤n merge branch (apply_head). When
    /// off, an n≥2 AtMost head bails `unsupported` (the prior behaviour).
    qmerge: bool,
    /// ∃-obligations awaiting expansion (filled by `apply_head`).
    obligations: Vec<Oblig>,
    /// KM_HT_CARD: deferred `≥n` obligations (Konclude `applyATLEASTRule`).
    card_min: Vec<CardReq>,
    /// KM_HT_CARD: deferred `≤n` obligations (Konclude `applyATMOSTRule`).
    card_max: Vec<CardReq>,
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

    /// Incremental PAIRWISE (mode-3) blocking — the equality-signature analogue of
    /// the i2_* subset path, for the inverse-safe route (SHIQ). A node is blocked
    /// by the FIRST earlier node sharing its triple signature
    /// `(core(n), core(pred n), pred→n edge roles)`; `i3_sig` maps that signature
    /// to its owning (unblocked) node, `i3_node_sig` records each node's registered
    /// signature so a recompute can un-register the changed suffix. Shares `i2_lo`/
    /// `i2_last_lo`/`i2_blocked` with the subset path (one block mode is live per
    /// run). `block3` makes `add_edge` widen the dirty suffix, since unlike subset
    /// blocking a mode-3 signature also depends on the parent edge.
    i3_sig: HashMap<Vec<u64>, Node>,
    i3_node_sig: Vec<Option<Vec<u64>>>,
    block3: bool,

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

    /// Nominals (O): the set of concept ids that denote singletons `{o}`. When a
    /// node freshly gains a positive nominal concept it is recorded as a carrier;
    /// `process_nominals` deterministically merges all carriers of one nominal into
    /// the lowest-id survivor (the o-rule). Sound + complete for SHOQ (nominals +
    /// number, no inverse); SHOIQ additionally needs the NN-rule (not yet here).
    nominals: HashSet<C>,
    /// Per-nominal carrier nodes (append-only within a branch; popped on backtrack
    /// via `Trail::NomCarrier`). Entries may be stale post-merge — `resolve` folds
    /// them and `process_nominals` dedups the resolved survivors.
    nom_carriers: HashMap<C, Vec<Node>>,
}

impl Ext {
    pub fn new() -> Ext {
        Ext {
            concepts: Vec::new(),
            block_bits: None,
            out_edges: Vec::new(),
            in_edges: Vec::new(),
            distinct: Vec::new(),
            pred: Vec::new(),
            blockable: Vec::new(),
            globals_fired: Vec::new(),
            blocked: Vec::new(),
            blockskip: std::env::var_os("KM_HT_BLOCKSKIP").is_some(),
            trail: Vec::new(),
            clash: None,
            queue: Vec::new(),
            pending: Vec::new(),
            pending_merge: Vec::new(),
            qmerge: std::env::var_os("KM_HT_QMERGE").is_some(),
            obligations: Vec::new(),
            card_min: Vec::new(),
            card_max: Vec::new(),
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
            i3_sig: HashMap::new(),
            i3_node_sig: Vec::new(),
            block3: false,
            incroblig: std::env::var_os("KM_HT_INCROBLIG").is_some(),
            node_obligs: Vec::new(),
            oblig_sat: Vec::new(),
            nominals: HashSet::new(),
            nom_carriers: HashMap::new(),
        }
    }

    fn enable_block_bits(&mut self) {
        debug_assert!(self.concepts.is_empty());
        self.block_bits = Some(Vec::new());
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
            if lm.len() >= lnlen
                && self.block_bits.as_ref().unwrap()[n]
                    .iter()
                    .enumerate()
                    .all(|(word, &need)| {
                        need & !self.block_bits.as_ref().unwrap()[m]
                            .get(word)
                            .copied()
                            .unwrap_or(0)
                            == 0
                    })
            {
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
                // Nodes are registered by the forward pass in strictly increasing
                // id order. Entries invalidated by a suffix recomputation therefore
                // form one contiguous tail; find its boundary instead of scanning
                // and copying the stable prefix on every blocking pass.
                debug_assert!(self.i2_lists[e].is_sorted());
                let keep = self.i2_lists[e].partition_point(|&x| x < lo);
                self.i2_lists[e].truncate(keep);
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
                // Borrow the concept map and posting-list fields separately so this
                // hot loop does not allocate a temporary key vector for every node.
                let concepts = &self.concepts[n];
                let lists = &mut self.i2_lists;
                let in_touched = &mut self.i2_in_touched;
                let touched = &mut self.i2_touched;
                for &k in concepts.keys() {
                    let e = Ext::enc_lit(k);
                    if e >= lists.len() {
                        lists.resize_with(e + 1, Vec::new);
                    }
                    if e >= in_touched.len() {
                        in_touched.resize(e + 1, false);
                    }
                    if !in_touched[e] {
                        in_touched[e] = true;
                        touched.push(e);
                    }
                    lists[e].push(n);
                }
            }
        }
        self.i2_lo = usize::MAX;
        self.i2_blocked.clone()
    }

    /// The mode-3 pairwise blocking signature of node `n` with parent `p`:
    /// `core(n) · SEP · core(p) · SEP · sorted-deduped roles on the p→n edge`,
    /// where `core` is the positive concepts encoded `(c<<1)`. Shared by the
    /// full-scan `compute_blocked` and the incremental `i3_recompute` so the two
    /// are identical by construction.
    fn i3_signature(&self, n: Node, p: Node) -> Vec<u64> {
        const SEP: u64 = u64::MAX;
        let mut sig: Vec<u64> = Vec::new();
        let mut a: Vec<u64> = self.concepts[n]
            .keys()
            .filter(|k| !k.neg)
            .map(|k| (k.c as u64) << 1)
            .collect();
        a.sort_unstable();
        sig.extend(a);
        sig.push(SEP);
        let mut b: Vec<u64> = self.concepts[p]
            .keys()
            .filter(|k| !k.neg)
            .map(|k| (k.c as u64) << 1)
            .collect();
        b.sort_unstable();
        sig.extend(b);
        sig.push(SEP);
        let mut e: Vec<u64> = self.in_edges[n]
            .iter()
            .filter(|(_, s, _)| *s == p)
            .map(|(r, _, _)| *r as u64)
            .collect();
        e.sort_unstable();
        e.dedup();
        sig.extend(e);
        sig
    }

    /// FULL-label BIDIRECTIONAL pairwise signature — the sound SHIQ double-blocking
    /// key (block_mode 4) and the cross-query saturation cache key (KM_HT_SATCACHE3).
    /// Differs from `i3_signature` (positive-core, sound only for SH WITHOUT inverse)
    /// in two ways the SHIQ pairwise-blocking theorem (Horrocks/Sattler/Tobies)
    /// requires once inverse roles are present:
    ///  - FULL labels (pos+neg, `(c<<1)|neg`): a node's negative concepts constrain
    ///    the unraveling, so blocking must match them (positive-core would let a
    ///    block skip a forbidden-concept clash — unsound, and the cross-query reuse
    ///    cannot tell two differently-forbidden contexts apart).
    ///  - BOTH edge directions between `n` and its parent `p`: with inverse the
    ///    connecting edge carries roles each way (`p→n` in `in_edges[n]`, `n→p` in
    ///    `out_edges[n]`), and the pairwise condition is on that whole edge. Forward
    ///    roles are tagged `r<<1`, backward roles `(r<<1)|1`, so the two directions
    ///    never alias.
    fn i3_signature_full(&self, n: Node, p: Node) -> Vec<u64> {
        const SEP: u64 = u64::MAX;
        let mut sig: Vec<u64> = Vec::new();
        let mut a: Vec<u64> = self.concepts[n]
            .keys()
            .map(|k| ((k.c as u64) << 1) | (k.neg as u64))
            .collect();
        a.sort_unstable();
        sig.extend(a);
        sig.push(SEP);
        let mut b: Vec<u64> = self.concepts[p]
            .keys()
            .map(|k| ((k.c as u64) << 1) | (k.neg as u64))
            .collect();
        b.sort_unstable();
        sig.extend(b);
        sig.push(SEP);
        let mut e: Vec<u64> = Vec::new();
        // forward p→n roles (tag 0)
        e.extend(
            self.in_edges[n]
                .iter()
                .filter(|(_, s, _)| *s == p)
                .map(|(r, _, _)| (*r as u64) << 1),
        );
        // backward n→p roles (tag 1) — the inverse direction of the same edge
        e.extend(
            self.out_edges[n]
                .iter()
                .filter(|(_, t, _)| *t == p)
                .map(|(r, _, _)| ((*r as u64) << 1) | 1),
        );
        e.sort_unstable();
        e.dedup();
        sig.extend(e);
        sig
    }

    /// Incremental pairwise (mode-3) blocking: re-evaluate only the changed suffix
    /// `i2_lo..nn`, identical in result to the full mode-3 scan in `compute_blocked`
    /// (KM_HT_INCRBLOCK2_CHECK asserts it per pass). A signature depends only on
    /// nodes `<= n` (the node, its parent `< n`, the parent edge), so the same
    /// suffix invariant as the subset path holds: keep `i3_sig` registrations for
    /// nodes `< lo`, un-register the changed/removed suffix, re-classify `lo..nn`
    /// in id order. A node is blocked by the FIRST earlier node owning its
    /// signature.
    fn i3_recompute(&mut self) -> Vec<bool> {
        let nn = self.num_nodes();
        let lo = self.i2_lo.min(nn);
        self.i2_last_lo = lo;
        // Un-register the signatures of nodes `>= lo` (their labels/edges may have
        // changed; ids beyond `nn` are leftovers from a backtrack). Only the owner
        // of a signature holds the map slot, so removing owners `>= lo` is safe —
        // any same-signature node `< lo` would be the owner instead.
        let old = self.i3_node_sig.len();
        for n in lo..old {
            if let Some(s) = self.i3_node_sig[n].take() {
                if self.i3_sig.get(&s) == Some(&n) {
                    self.i3_sig.remove(&s);
                }
            }
        }
        self.i2_blocked.truncate(lo);
        self.i2_blocked.resize(nn, false);
        self.i3_node_sig.resize(nn, None);
        for n in lo..nn {
            self.i3_node_sig[n] = None;
            let p = match (self.blockable[n], self.pred[n]) {
                (true, Some(p)) => p,
                _ => {
                    // root / non-blockable node never blocked, never a blocker.
                    self.i2_blocked[n] = false;
                    continue;
                }
            };
            let sig = self.i3_signature(n, p);
            match self.i3_sig.get(&sig) {
                Some(&m) if m < n => self.i2_blocked[n] = true,
                _ => {
                    self.i2_blocked[n] = false;
                    self.i3_sig.entry(sig.clone()).or_insert(n);
                    self.i3_node_sig[n] = Some(sig);
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
        self.pending.push(PendingDisj {
            disjuncts,
            bdep,
            at,
        });
    }

    /// Record a ≤n qualified-cardinality merge choice (KM_HT_QMERGE), branched at
    /// the dfs fixpoint. `at` lets a backtrack drop it as a trail-ordered suffix.
    fn push_merge(&mut self, pairs: Vec<(Node, Node)>, bdep: DepSet) {
        self.push_card(Vec::new(), pairs, bdep);
    }

    /// Record a deferred cardinality choice with both concept-recognition
    /// disjuncts (`concepts`, the `Q` of a `≥n r.F ⊑ Q` head) and merge candidates
    /// (`pairs`). Branched at the dfs fixpoint (`branch_merge`), where each option
    /// is either "assert a live concept" or "merge a live pair".
    fn push_card(&mut self, concepts: Vec<(Node, CLit)>, pairs: Vec<(Node, Node)>, bdep: DepSet) {
        let at = self.trail.len();
        self.pending_merge.push(MergeDisj {
            concepts,
            pairs,
            bdep,
            at,
        });
    }

    /// Mark every disjunction touched by a change at `(n, lit)` (either the
    /// literal or its complement appears as a disjunct) for re-evaluation.
    fn mark_disj_dirty(&mut self, n: Node, lit: CLit) {
        if !self.watch {
            return;
        }
        let comp = CLit {
            neg: !lit.neg,
            c: lit.c,
        };
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
        if let Some(block_bits) = &mut self.block_bits {
            block_bits.push(Vec::new());
        }
        self.out_edges.push(Vec::new());
        self.in_edges.push(Vec::new());
        self.distinct.push(Vec::new());
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
        self.concepts
            .get(node)
            .is_some_and(|m| m.contains_key(&lit))
    }

    /// Assert `lit` at `node`. Returns true iff freshly added (enqueues it).
    pub fn add_concept(&mut self, node: Node, lit: CLit, dep: &DepSet) -> bool {
        let comp = CLit {
            neg: !lit.neg,
            c: lit.c,
        };
        if let Some(other) = self.concepts[node].get(&comp) {
            let cd = dep_union(dep, other);
            self.clash_node = Some(node);
            self.raise_clash(cd);
        }
        match self.concepts[node].get(&lit) {
            None => {
                self.concepts[node].insert(lit, dep.clone());
                if let Some(block_bits) = &mut self.block_bits {
                    let e = Ext::enc_lit(lit);
                    let word = e >> 6;
                    if word >= block_bits[node].len() {
                        block_bits[node].resize(word + 1, 0);
                    }
                    block_bits[node][word] |= 1u64 << (e & 63);
                }
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
                // Nominals: a fresh positive nominal concept makes `node` a carrier
                // of that singleton. Recorded (trail-popped on backtrack); the
                // deterministic merge is deferred to `process_nominals`.
                if !lit.neg && self.nominals.contains(&lit.c) {
                    self.nom_carriers.entry(lit.c).or_default().push(node);
                    self.trail.push(Trail::NomCarrier(lit.c));
                }
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
        if self.out_edges[s]
            .iter()
            .any(|&(rr, tt, _)| rr == r && tt == t)
        {
            return;
        }
        self.out_edges[s].push((r, t, dep.clone()));
        self.in_edges[t].push((r, s, dep.clone()));
        self.trail.push(Trail::Edge(r, s, t));
        self.queue.push(Event::Edge(r, s, t));
        // A mode-3 (pairwise) signature depends on the parent→node edge roles, so a
        // new edge into `t` can change `t`'s blocking signature: widen the suffix.
        if self.block3 {
            self.i2_note(t);
        }
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

    /// KM_HT_CARD: assert `a ≠ b` (Konclude `createIndividualsDistinct`). Records
    /// the inequality on both nodes' `distinct` lists under `dep`, trail-recorded.
    /// Idempotent (a re-asserted pair is ignored). Resolves through merges first,
    /// so an inequality always names live survivors.
    pub fn add_distinct(&mut self, a: Node, b: Node, dep: &DepSet) {
        let a = self.resolve(a);
        let b = self.resolve(b);
        if a == b {
            // a≠a is an immediate contradiction (Konclude clashes a self-distinct).
            self.raise_clash(dep.clone());
            return;
        }
        if self.distinct[a].iter().any(|&(x, _)| x == b) {
            return;
        }
        self.distinct[a].push((b, dep.clone()));
        self.distinct[b].push((a, dep.clone()));
        self.trail.push(Trail::Distinct(a, b));
    }

    /// KM_HT_CARD: if `a` and `b` are asserted distinct, return the witnessing
    /// inequality's dependency (so a merge-clash backjumps past the `≥n`/nominal
    /// choice that separated them); `None` if they may still be merged.
    pub fn are_distinct(&self, a: Node, b: Node) -> Option<DepSet> {
        let a = self.resolve(a);
        let b = self.resolve(b);
        if a == b {
            return None;
        }
        self.distinct[a]
            .iter()
            .find(|&&(x, _)| x == b)
            .map(|(_, d)| d.clone())
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
        // Konclude `isIndividualNodesMergeable`: a distinct (inequality) edge
        // between the pair makes the merge a CLASH — the ≤n cannot identify two
        // provably-distinct successors. Backjump past both the merge cause and
        // the inequality witness.
        if let Some(dd) = self.are_distinct(a, b) {
            self.raise_clash(dep_union(mdep, &dd));
            return;
        }
        let (survivor, victim) = if a <= b { (a, b) } else { (b, a) };
        self.merges += 1;
        if std::env::var_os("KM_HT_TRACE").is_some() && self.merges % 100_000 == 0 {
            eprintln!(
                "MERGE count={} nodes={} trail={}",
                self.merges,
                self.concepts.len(),
                self.trail.len()
            );
        }
        self.trail.push(Trail::Merge(victim));
        self.merged[victim] = Some(survivor);
        let cs: Vec<(CLit, DepSet)> = self.concepts[victim]
            .iter()
            .map(|(k, v)| (*k, v.clone()))
            .collect();
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
        // Konclude `mergeIndividualNodeInto` distinct-edge propagation: every node
        // the victim was distinct from is now distinct from the survivor. If the
        // survivor was itself distinct from the victim we already clashed above;
        // a victim distinct from the survivor's own identity (`d2 == survivor`)
        // would be a self-distinct, which `add_distinct` turns into a clash.
        let dvs: Vec<(Node, DepSet)> = self.distinct[victim].clone();
        for (d, dd) in dvs {
            let d2 = self.resolve(d);
            let nd = dep_union(&dd, mdep);
            self.add_distinct(survivor, d2, &nd);
            if self.clash.is_some() {
                return;
            }
        }
    }

    /// The nominal o-rule (deterministic, no branch): for each nominal concept,
    /// merge every distinct carrier into the lowest-id survivor — a singleton `{o}`
    /// has exactly one element, so any two `__nom__o` carriers denote it. Returns
    /// true iff a merge happened (the caller re-propagates); a clash during a merge
    /// sets `self.clash` and returns true. The merge dep is the union of the two
    /// carriers' nominal-membership deps, so a resulting clash backjumps past the
    /// choices that put `{o}` on both. Sound + complete for SHOQ.
    fn process_nominals(&mut self) -> bool {
        if self.nominals.is_empty() {
            return false;
        }
        let mut changed = false;
        let noms: Vec<C> = self.nominals.iter().copied().collect();
        for c in noms {
            let carriers = match self.nom_carriers.get(&c) {
                Some(v) if v.len() >= 2 => v.clone(),
                _ => continue,
            };
            let mut survs: Vec<Node> = carriers.iter().map(|&n| self.resolve(n)).collect();
            survs.sort_unstable();
            survs.dedup();
            if survs.len() < 2 {
                continue;
            }
            let lit = CLit { neg: false, c };
            let keep = survs[0];
            for &o in &survs[1..] {
                if self.resolve(keep) == self.resolve(o) {
                    continue;
                }
                let dk = self.concepts[self.resolve(keep)]
                    .get(&lit)
                    .cloned()
                    .unwrap_or(None);
                let dobj = self.concepts[o].get(&lit).cloned().unwrap_or(None);
                let mdep = dep_union(&dk, &dobj);
                self.merge_into(keep, o, &mdep);
                changed = true;
                if self.clash.is_some() {
                    return true;
                }
            }
        }
        changed
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
                    if let Some(block_bits) = &mut self.block_bits {
                        let e = Ext::enc_lit(lit);
                        block_bits[node][e >> 6] &= !(1u64 << (e & 63));
                    }
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
                    if let Some(pos) = self.out_edges[s]
                        .iter()
                        .position(|&(rr, tt, _)| rr == r && tt == t)
                    {
                        self.out_edges[s].swap_remove(pos);
                    }
                    if let Some(pos) = self.in_edges[t]
                        .iter()
                        .position(|&(rr, ss, _)| rr == r && ss == s)
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
                    if let Some(block_bits) = &mut self.block_bits {
                        block_bits.pop();
                    }
                    self.out_edges.pop();
                    self.in_edges.pop();
                    self.distinct.pop();
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
                Trail::NomCarrier(c) => {
                    if let Some(v) = self.nom_carriers.get_mut(&c) {
                        v.pop();
                    }
                }
                Trail::Distinct(a, b) => {
                    // LIFO: this `a≠b` was the most recent distinct entry pushed
                    // onto both lists, so it is each list's last element.
                    if a < self.distinct.len() {
                        if let Some(p) = self.distinct[a].iter().rposition(|&(x, _)| x == b) {
                            self.distinct[a].swap_remove(p);
                        }
                    }
                    if b < self.distinct.len() {
                        if let Some(p) = self.distinct[b].iter().rposition(|&(x, _)| x == a) {
                            self.distinct[b].swap_remove(p);
                        }
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
        // ≤n merge choices, like `pending`, are recorded in trail order, so the
        // entries past `mark` form a suffix whose matching body has been undone.
        while let Some(last) = self.pending_merge.last() {
            if last.at <= mark {
                break;
            }
            self.pending_merge.pop();
        }
        self.obligations.retain(|e| e.at <= mark);
        self.card_min.retain(|e| e.at <= mark);
        self.card_max.retain(|e| e.at <= mark);
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

impl Ext {
    /// Turn a completed clash-free branch into a fixed model that can be checked
    /// against an enlarged clause set.
    ///
    /// The old branch choices are witnesses, not consequences of the new
    /// ontology.  They are therefore retained as ordinary facts with empty
    /// dependency sets.  Old pending work and branch journals are discarded,
    /// then every retained node, concept, and edge is replayed through the new
    /// trigger indexes.  If that fixed witness cannot be extended, the caller
    /// must run a fresh search; a replay clash is never an UNSAT certificate.
    fn prepare_addition_replay(&mut self) {
        for label in &mut self.concepts {
            for dependency in label.values_mut() {
                *dependency = dep_empty();
            }
        }
        for edges in &mut self.out_edges {
            for (_, _, dependency) in edges {
                *dependency = dep_empty();
            }
        }
        for edges in &mut self.in_edges {
            for (_, _, dependency) in edges {
                *dependency = dep_empty();
            }
        }
        for distinct in &mut self.distinct {
            for (_, dependency) in distinct {
                *dependency = dep_empty();
            }
        }

        self.trail.clear();
        self.clash = None;
        self.clash_node = None;
        self.queue.clear();
        self.pending.clear();
        self.pending_merge.clear();
        self.obligations.clear();
        self.card_min.clear();
        self.card_max.clear();
        self.unsupported = false;

        self.lit_disj.clear();
        self.dirty.clear();
        self.dirty_in.clear();
        self.open.clear();
        self.open_in.clear();

        self.block_index.clear();
        self.i2_blocked.clear();
        self.i2_lists.clear();
        self.i2_touched.clear();
        self.i2_in_touched.clear();
        self.i2_lo = 0;
        self.i2_last_lo = 0;
        self.i3_sig.clear();
        self.i3_node_sig.clear();
        self.node_obligs.clear();
        self.node_obligs.resize_with(self.concepts.len(), Vec::new);
        self.oblig_sat.clear();
        self.globals_fired.fill(false);
        self.blocked.fill(false);
        self.nom_carriers.clear();

        // `block_index` and nominal carriers are normally maintained only by
        // fresh `add_concept` calls. Replay queues existing facts directly, so
        // reconstruct those auxiliary indexes from the retained labels.
        for (node, label) in self.concepts.iter().enumerate() {
            for &literal in label.keys() {
                if self.incr_block {
                    let encoded = Ext::enc_lit(literal);
                    if encoded >= self.block_index.len() {
                        self.block_index.resize_with(encoded + 1, Vec::new);
                    }
                    self.block_index[encoded].push(node);
                }
                if !literal.neg && self.nominals.contains(&literal.c) {
                    self.nom_carriers.entry(literal.c).or_default().push(node);
                }
            }
        }

        // Replaying the complete fact base is deliberately redundant.  Duplicate
        // insertions are ignored by Ext, while every newly installed trigger sees
        // every old premise at least once.
        for node in 0..self.concepts.len() {
            self.queue.push(Event::NodeNew(node));
            let concepts: Vec<CLit> = self.concepts[node].keys().copied().collect();
            self.queue
                .extend(concepts.into_iter().map(|lit| Event::Concept(node, lit)));
            let edges: Vec<(R, Node)> = self.out_edges[node]
                .iter()
                .map(|(role, target, _)| (*role, *target))
                .collect();
            self.queue.extend(
                edges
                    .into_iter()
                    .map(|(role, target)| Event::Edge(role, node, target)),
            );
        }
    }

    fn edge_count(&self) -> usize {
        self.out_edges.iter().map(Vec::len).sum()
    }
}

fn edge_dep(ext: &Ext, r: R, s: Node, t: Node) -> Option<DepSet> {
    ext.out_edges[s]
        .iter()
        .find(|&&(rr, tt, _)| rr == r && tt == t)
        .map(|(_, _, d)| d.clone())
}

fn has_rsucc(ext: &Ext, n: Node, r: R, fil: CLit) -> bool {
    ext.out_edges[n]
        .iter()
        .any(|&(rr, t, _)| rr == r && ext.has_concept(t, fil))
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

/// Eliminate positive equality atoms from a clause body by identifying their
/// variables throughout the clause. For universally quantified clauses,
/// `x = y ∧ B(x,y) → H(x,y)` is equivalent to `B(x,x) → H(x,x)`.
/// Equality-only bodies otherwise have no concept or role event to wake them.
fn eliminate_body_equalities(clause: &mut Clause) {
    let equalities: Vec<(Var, Var)> = clause
        .body
        .iter()
        .filter_map(|atom| match atom {
            Atom::Eq { s, t } => Some((*s, *t)),
            _ => None,
        })
        .collect();
    if equalities.is_empty() {
        return;
    }
    let count = nvars_of(clause);
    let mut parent: Vec<usize> = (0..count).collect();
    fn root(parent: &mut [usize], mut node: usize) -> usize {
        while parent[node] != node {
            parent[node] = parent[parent[node]];
            node = parent[node];
        }
        node
    }
    for (left, right) in equalities {
        let left = root(&mut parent, left as usize);
        let right = root(&mut parent, right as usize);
        if left != right {
            let (representative, other) = if left < right {
                (left, right)
            } else {
                (right, left)
            };
            parent[other] = representative;
        }
    }
    for variable in 0..count {
        parent[variable] = root(&mut parent, variable);
    }
    let rename = |variable: &mut Var| *variable = parent[*variable as usize] as Var;
    let rename_atom = |atom: &mut Atom| match atom {
        Atom::Concept { t, .. } | Atom::Exists { t, .. } => rename(t),
        Atom::Role { s, t, .. } | Atom::Eq { s, t } => {
            rename(s);
            rename(t);
        }
    };
    for atom in &mut clause.body {
        rename_atom(atom);
    }
    for atom in &mut clause.head {
        rename_atom(atom);
    }
    clause.body.retain(|atom| !matches!(atom, Atom::Eq { .. }));
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
                    if let Some((_, _, edep)) = ext.out_edges[sn]
                        .iter()
                        .find(|&&(rr, tt, _)| rr == *r && tt == tn)
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
                        let (rr, ss) = {
                            let e = &ext.in_edges[tn][k2];
                            (e.0, e.1)
                        };
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
    // KM_HT_NUMBER: equality-head clauses (qualified cardinality). Two head shapes
    // are handled uniformly as a deferred cardinality choice:
    //   - all-Eq head `⋁ Eq(yi,yj)`            = ≤n AtMost merge (identify a pair).
    //   - mixed concept+Eq head `Q ∨ ⋁ Eq`     = ≥n recognition (`≥n r.F ⊑ Q`,
    //     i.e. the contrapositive `¬Q ⊑ ≤(n-1) r.F`): assert `Q`, or merge a pair.
    // A single live option is a unit (a forced merge, or — when ¬Q is fixed and
    // exactly one pair survives — the AtMost merge); ≥2 live options branch
    // (`branch_merge`) under KM_HT_QMERGE. The branch's concept disjunct is the
    // Konclude at-least/at-most recognition that earlier bailed `unsupported`.
    if ext.number && head.iter().any(|h| matches!(h, Atom::Eq { .. })) {
        // Recognized concept disjuncts (the `Q`): satisfied ⇒ done; dead (¬Q
        // present) ⇒ fold its reason; else a live branch option.
        let mut dead = dep_empty();
        let mut concepts: Vec<(Node, CLit)> = Vec::new();
        for h in head {
            if let Atom::Concept { lit, t } = *h {
                let n = ext.resolve(sigma[t as usize].expect("recognition head var bound by body"));
                if ext.has_concept(n, lit) {
                    return;
                }
                let comp = CLit {
                    neg: !lit.neg,
                    c: lit.c,
                };
                if let Some(d) = ext.dep_of(n, comp) {
                    dead = dep_union(&dead, d);
                } else {
                    concepts.push((n, lit));
                }
            }
        }
        // Candidate merge pairs. A pair already identified ⇒ the cardinality
        // bound already holds ⇒ no choice needed.
        let mut pairs: Vec<(Node, Node)> = Vec::new();
        for h in head {
            if let Atom::Eq { s, t } = *h {
                let sn = ext.resolve(sigma[s as usize].expect("eq head src bound by body"));
                let tn = ext.resolve(sigma[t as usize].expect("eq head dst bound by body"));
                if sn == tn {
                    return;
                }
                pairs.push(if sn <= tn { (sn, tn) } else { (tn, sn) });
            }
        }
        pairs.sort_unstable();
        pairs.dedup();
        let bdep2 = dep_union(bdep, &dead);
        // pairs is non-empty here (the head has an Eq atom and none is already
        // identified), so there is always ≥1 option — a merge is always available,
        // hence no immediate clash (a forbidden merge clashes later via the ≥m
        // distinctness clauses). One option ⇒ unit; ≥2 ⇒ deferred branch.
        match concepts.len() + pairs.len() {
            0 | 1 => {
                if let Some(&(n, lit)) = concepts.first() {
                    ext.add_concept(n, lit, &bdep2);
                } else if let Some(&(a, b)) = pairs.first() {
                    ext.merge_into(a, b, &bdep2);
                }
            }
            _ => {
                if ext.qmerge {
                    ext.push_card(concepts, pairs, bdep2);
                } else {
                    ext.unsupported = true;
                }
            }
        }
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
                let comp = CLit {
                    neg: !lit.neg,
                    c: lit.c,
                };
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
                ext.obligations.push(Oblig {
                    n,
                    r,
                    fil,
                    dep: bdep.clone(),
                    at,
                });
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
    } else if live
        .iter()
        .any(|h| matches!(h, HeadItem::Exists(..) | HeadItem::Edge(..)))
    {
        // a disjunction containing an ∃ or a role edge is out of the branchable
        // (ground concept-disjunction) fragment: bail soundly to the legacy path.
        if std::env::var_os("KM_HT_TRACE").is_some() {
            eprintln!(
                "TR UNSUPPORTED: disjunctive head with exists/edge ({} live, cid={})",
                live.len(),
                cid
            );
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
            eprintln!(
                "HUGEMATCH cid={} body_len={} join overflow -> bail unsupported",
                cid,
                body.len()
            );
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
fn fire_anchor_edge(
    clauses: &[ClauseRec],
    ext: &mut Ext,
    cid: usize,
    pos: usize,
    es: Node,
    et: Node,
) {
    let body = &clauses[cid].1;
    let nv = clauses[cid].2;
    let (r, sv, tv) = match body[pos] {
        Atom::Role { r, s, t } => (r, s as usize, t as usize),
        _ => return,
    };
    // A self-loop body atom `r(x,x)` (sv == tv, same variable) is only witnessed by a
    // SELF edge `r(es,es)`. Anchoring it on a non-self edge `r(es,et)` with es != et
    // would bind the single var inconsistently (the second `sigma[sv]=Some(et)` just
    // overwrote the first), silently dropping the es==et constraint and matching
    // r(x,x) against a non-self edge — UNSOUND (e.g. ObjectHasSelf's `Q_15→r(x,x)` /
    // its converse `r(x,x)→Q_15` wrongly fires on an inverse-derived r(n3,n1), forcing
    // the located-in occupant spatial → false clash on 10908). Require es == et.
    if sv == tv && es != et {
        return;
    }
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
            eprintln!(
                "HUGEMATCH cid={} body_len={} join overflow -> bail unsupported",
                cid,
                body.len()
            );
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
    ext.concepts[n]
        .keys()
        .all(|k| ext.concepts[m].contains_key(k))
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
/// One branch option of a deferred cardinality choice (`branch_merge`): assert a
/// recognized concept (`≥n` recognition's `Q`) or identify a candidate pair.
#[derive(Clone, Copy)]
enum MergeChoice {
    Concept(Node, CLit),
    Merge(Node, Node),
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

#[derive(Clone, Copy, serde::Serialize)]
struct LeanHtLit {
    concept: usize,
    neg: bool,
}

#[derive(Clone, serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum LeanHtAtom {
    Concept { literal: LeanHtLit, node: usize },
    Role { role: usize, source: usize, target: usize },
    Exists_ { role: usize, filler: LeanHtLit, node: usize },
    Eq { left: usize, right: usize },
}

#[derive(Clone, serde::Serialize)]
struct LeanHtClause {
    body: Vec<LeanHtAtom>,
    head: Vec<LeanHtAtom>,
}

#[derive(serde::Serialize)]
struct LeanHtLabel {
    node: usize,
    literal: LeanHtLit,
}

#[derive(serde::Serialize)]
struct LeanHtEdge {
    role: usize,
    source: usize,
    target: usize,
}

#[derive(serde::Serialize)]
struct LeanHtObligation {
    role: usize,
    filler: LeanHtLit,
    node: usize,
}

#[derive(serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum LeanHtRefutationTree {
    Clash,
    Branch {
        clause: usize,
        assignment: Vec<usize>,
        children: Vec<LeanHtRefutationTree>,
    },
    Witness {
        source: usize,
        target: usize,
        role: usize,
        filler: LeanHtLit,
        child: Box<LeanHtRefutationTree>,
    },
}

#[derive(Clone, Copy, serde::Serialize)]
struct LeanHtEquality {
    left: usize,
    right: usize,
}

#[derive(serde::Serialize)]
struct LeanHtEqState {
    labels: Vec<LeanHtLabel>,
    edges: Vec<LeanHtEdge>,
    obligations: Vec<LeanHtObligation>,
    equalities: Vec<LeanHtEquality>,
    representatives: Vec<usize>,
    representative_paths: Vec<Vec<usize>>,
}

#[derive(serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum LeanHtEqRefutationTree {
    Clash,
    Branch {
        clause: usize,
        assignment: Vec<usize>,
        children: Vec<(LeanHtEqState, LeanHtEqRefutationTree)>,
    },
    Witness {
        source: usize,
        target: usize,
        role: usize,
        filler: LeanHtLit,
        child: Box<LeanHtEqRefutationTree>,
    },
}

#[derive(serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum LeanHtEqEvidence {
    Sat,
    Unsat { tree: LeanHtEqRefutationTree },
    Subsumption {
        root: usize,
        sub: usize,
        sup: usize,
        tree: LeanHtEqRefutationTree,
    },
    UnsatisfiableConcept {
        root: usize,
        concept: usize,
        tree: LeanHtEqRefutationTree,
    },
    NonSubsumption {
        root: usize,
        sub: usize,
        sup: usize,
    },
    SatisfiableConcept {
        root: usize,
        concept: usize,
    },
}

#[derive(serde::Serialize)]
struct LeanHtEqCertificate {
    version: usize,
    node_count: usize,
    concept_count: usize,
    role_count: usize,
    variable_count: usize,
    ontology: Vec<LeanHtClause>,
    state: LeanHtEqState,
    evidence: LeanHtEqEvidence,
}

#[derive(serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum LeanHtEvidence {
    Sat,
    Unsat { tree: LeanHtRefutationTree },
    Subsumption {
        root: usize,
        sub: usize,
        sup: usize,
        tree: LeanHtRefutationTree,
    },
    UnsatisfiableConcept {
        root: usize,
        concept: usize,
        tree: LeanHtRefutationTree,
    },
    NonSubsumption {
        root: usize,
        sub: usize,
        sup: usize,
    },
    SatisfiableConcept {
        root: usize,
        concept: usize,
    },
}

#[derive(serde::Serialize)]
struct LeanHtCertificate {
    version: usize,
    node_count: usize,
    concept_count: usize,
    role_count: usize,
    variable_count: usize,
    ontology: Vec<LeanHtClause>,
    labels: Vec<LeanHtLabel>,
    edges: Vec<LeanHtEdge>,
    obligations: Vec<LeanHtObligation>,
    evidence: LeanHtEvidence,
}

struct LeanHtRefutationState {
    labels: HashSet<(Node, CLit)>,
    label_order: Vec<(Node, CLit)>,
    edges: HashSet<(R, Node, Node)>,
    edge_order: Vec<(R, Node, Node)>,
    obligations: HashSet<(R, CLit, Node)>,
    obligation_order: Vec<(R, CLit, Node)>,
    equalities: Vec<(Node, Node)>,
    active_nodes: usize,
}

impl LeanHtRefutationState {
    fn root(labels: &[(Node, CLit)]) -> Self {
        Self {
            labels: labels.iter().copied().collect(),
            label_order: labels.to_vec(),
            edges: HashSet::new(),
            edge_order: Vec::new(),
            obligations: HashSet::new(),
            obligation_order: Vec::new(),
            equalities: Vec::new(),
            active_nodes: 1,
        }
    }

    fn representatives_and_paths(&self, node_count: usize) -> (Vec<Node>, Vec<Vec<Node>>) {
        debug_assert!(node_count >= self.active_nodes);
        let mut parent: Vec<Node> = (0..node_count).collect();
        fn find(parent: &mut [Node], mut node: Node) -> Node {
            while parent[node] != node {
                node = parent[node];
            }
            node
        }
        for &(left, right) in &self.equalities {
            let left_root = find(&mut parent, left);
            let right_root = find(&mut parent, right);
            if left_root != right_root {
                let representative = left_root.min(right_root);
                let other = left_root.max(right_root);
                parent[other] = representative;
            }
        }
        let representatives: Vec<Node> = (0..node_count)
            .map(|node| find(&mut parent, node))
            .collect();
        let mut adjacency = vec![Vec::<Node>::new(); node_count];
        for &(left, right) in &self.equalities {
            adjacency[left].push(right);
            adjacency[right].push(left);
        }
        let paths = (0..node_count)
            .map(|source| {
                let target = representatives[source];
                if source == target {
                    return Vec::new();
                }
                let mut predecessor = vec![None; node_count];
                let mut queue = std::collections::VecDeque::from([source]);
                predecessor[source] = Some(source);
                while let Some(node) = queue.pop_front() {
                    if node == target {
                        break;
                    }
                    for &next in &adjacency[node] {
                        if predecessor[next].is_none() {
                            predecessor[next] = Some(node);
                            queue.push_back(next);
                        }
                    }
                }
                debug_assert!(predecessor[target].is_some());
                let mut reversed = Vec::new();
                let mut node = target;
                while node != source {
                    reversed.push(node);
                    node = predecessor[node].expect("union path must use recorded equalities");
                }
                reversed.reverse();
                reversed
            })
            .collect();
        (representatives, paths)
    }

    fn equivalent(&self, left: Node, right: Node) -> bool {
        if left == right {
            return true;
        }
        let (representatives, _) = self.representatives_and_paths(self.active_nodes);
        representatives[left] == representatives[right]
    }

    fn equality_wire_state(&self, node_count: usize) -> LeanHtEqState {
        let (representatives, representative_paths) =
            self.representatives_and_paths(node_count);
        LeanHtEqState {
            labels: self
                .label_order
                .iter()
                .map(|&(node, literal)| LeanHtLabel {
                    node,
                    literal: Ht::lean_wire_lit(literal),
                })
                .collect(),
            edges: self
                .edge_order
                .iter()
                .map(|&(role, source, target)| LeanHtEdge {
                    role: role as usize,
                    source,
                    target,
                })
                .collect(),
            obligations: self
                .obligation_order
                .iter()
                .map(|&(role, filler, node)| LeanHtObligation {
                    role: role as usize,
                    filler: Ht::lean_wire_lit(filler),
                    node,
                })
                .collect(),
            equalities: self
                .equalities
                .iter()
                .rev()
                .map(|&(left, right)| LeanHtEquality { left, right })
                .collect(),
            representatives,
            representative_paths,
        }
    }

    fn holds(&self, atom: &Atom, assignment: &[Node]) -> bool {
        match atom {
            Atom::Concept { lit, t } => self.labels.contains(&(assignment[*t as usize], *lit)),
            Atom::Role { r, s, t } => self.edges.contains(&(
                *r,
                assignment[*s as usize],
                assignment[*t as usize],
            )),
            Atom::Exists { r, fil, t } => {
                self.obligations
                    .contains(&(*r, *fil, assignment[*t as usize]))
            }
            Atom::Eq { s, t } => self.equivalent(
                assignment[*s as usize],
                assignment[*t as usize],
            ),
        }
    }

    fn insert(&mut self, atom: &Atom, assignment: &[Node]) -> bool {
        match atom {
            Atom::Concept { lit, t } => {
                let fact = (assignment[*t as usize], *lit);
                if self.labels.insert(fact) {
                    self.label_order.insert(0, fact);
                    true
                } else {
                    false
                }
            }
            Atom::Role { r, s, t } => {
                let fact = (*r, assignment[*s as usize], assignment[*t as usize]);
                if self.edges.insert(fact) {
                    self.edge_order.insert(0, fact);
                    true
                } else {
                    false
                }
            }
            Atom::Exists { r, fil, t } => {
                let fact = (*r, *fil, assignment[*t as usize]);
                if self.obligations.insert(fact) {
                    self.obligation_order.insert(0, fact);
                    true
                } else {
                    false
                }
            }
            Atom::Eq { s, t } => {
                let left = assignment[*s as usize];
                let right = assignment[*t as usize];
                if self.equivalent(left, right) {
                    false
                } else {
                    self.equalities.push((left, right));
                    true
                }
            }
        }
    }

    fn remove(&mut self, atom: &Atom, assignment: &[Node]) {
        match atom {
            Atom::Concept { lit, t } => {
                let fact = (assignment[*t as usize], *lit);
                self.labels.remove(&fact);
                debug_assert_eq!(self.label_order.first(), Some(&fact));
                self.label_order.remove(0);
            }
            Atom::Role { r, s, t } => {
                let fact = (*r, assignment[*s as usize], assignment[*t as usize]);
                self.edges.remove(&fact);
                debug_assert_eq!(self.edge_order.first(), Some(&fact));
                self.edge_order.remove(0);
            }
            Atom::Exists { r, fil, t } => {
                let fact = (*r, *fil, assignment[*t as usize]);
                self.obligations.remove(&fact);
                debug_assert_eq!(self.obligation_order.first(), Some(&fact));
                self.obligation_order.remove(0);
            }
            Atom::Eq { s, t } => {
                let expected = (assignment[*s as usize], assignment[*t as usize]);
                let removed = self.equalities.pop();
                debug_assert_eq!(removed, Some(expected));
            }
        }
    }

    fn clashes(&self) -> bool {
        self.labels.iter().any(|(node, literal)| {
            self.labels.iter().any(|(other, candidate)| {
                candidate.c == literal.c
                    && candidate.neg != literal.neg
                    && self.equivalent(*node, *other)
            })
        })
    }

    fn witness_for(&self, role: R, filler: CLit, source: Node) -> bool {
        self.edges.iter().any(|&(candidate_role, candidate_source, target)| {
            candidate_role == role
                && candidate_source == source
                && self.labels.contains(&(target, filler))
        })
    }
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
        let comp = CLit {
            neg: !lit.neg,
            c: lit.c,
        };
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
    std::env::var(key)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
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

/// Persistent named-individual state.  `consistent` rebuilds `Ext` for every
/// taxonomy probe/restart, so source ABox roots cannot live only in one model.
#[derive(Clone, Default)]
struct NativeAboxState {
    /// `(singleton proxy concepts, asserted normalized concept markers)`.
    individuals: Vec<(Vec<C>, Vec<C>)>,
    /// Pairs of indices into `individuals`.
    different: Vec<(usize, usize)>,
    /// `(role, source index, target index)`.
    role_assertions: Vec<(R, usize, usize)>,
}

/// Opaque clash-free completion graph retained by the incremental HT adapter.
///
/// A snapshot is only a SAT witness for the exact clause/id layout that created
/// it.  [`Ht::resume_satisfiable_model`] accepts it for an enlarged layout only
/// after the adapter has proved that all old concept ids, role ids, and compiled
/// clauses are stable prefixes.  The snapshot is never used as an UNSAT proof.
#[derive(Clone)]
pub struct HtModelSnapshot {
    ext: Ext,
}

impl HtModelSnapshot {
    pub fn root_positive_label(&self) -> Vec<C> {
        self.ext
            .concepts
            .first()
            .map(|label| {
                let mut concepts: Vec<C> = label
                    .keys()
                    .filter(|literal| !literal.neg)
                    .map(|literal| literal.c)
                    .collect();
                concepts.sort_unstable();
                concepts.dedup();
                concepts
            })
            .unwrap_or_default()
    }

    pub fn edge_count(&self) -> usize {
        self.ext.edge_count()
    }
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
    /// Complete-answer-or-defer SHOIQ certificate. The missing NN/NI rule can
    /// matter only when completion folds a blockable predecessor chain into a
    /// nominal along a number role. The certified route checks that premise
    /// once on the completed clash-free graph and declines when it occurs.
    cert_no_blocking: bool,
    /// Roles occurring in an equality-head (at-most/functionality) clause.
    /// Used only by the SHOIQ complete-answer-or-defer certificate.
    cert_number_roles: HashSet<R>,
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
    /// KM_HT_SATCACHE3: cross-query SATURATION CACHE for the SOUND mode-3 (pairwise)
    /// route — the mode the inverse/number targets (10908/7914/9724/15672) require.
    /// `satcache`/`satfold` are inert here: they fire only for block_mode 0/1/2 and
    /// key on positive cores, which is unsound under inverse (a node clash-free in
    /// query X can carry a forbidden concept in query Y; a positive-core block would
    /// skip its clash). This cache pools the FULL-label pairwise signature
    /// (`i3_signature_full`: pos+neg core(n) + core(pred) + edge-roles) of UNBLOCKED
    /// clash-free nodes from completed models. A later mode-3 node whose full
    /// signature is pooled is blocked: its (label, parent-context) was witnessed
    /// consistent by a fully-expanded subtree, and the full label (incl. negatives)
    /// guarantees that witness respects this query's forbidden concepts too. Sound
    /// on the same SHIQ fragment within-query mode-3 blocking is sound on, lifted
    /// cross-query. Default OFF (opt-in, validated vs gold before any promotion).
    satcache3: bool,
    sat_sigs3: HashSet<Vec<u64>>,
    sc3_pooled: u64,
    /// KM_HT_BLOCK=5: Konclude `isLabelConceptOptimizedBlocking` port (B1 subset +
    /// B2a ∀-operand-on-predecessor; see docs/KONCLUDE-BLOCKING-SPEC.md). `forall_idx`
    /// maps a (body-concept, role) to the head concepts of every ∀-clause
    /// `C0(x) ∧ r(x,y) → D(y)` — KM's clause-world encoding of "∀r.D with C0 in the
    /// label". B2a consults it: for each ∀r.D the blocker w' carries, the predecessor
    /// v must already carry D. Built once at construction.
    forall_idx: HashMap<(CLit, R), Vec<CLit>>,
    /// KM_HT_CARD: first-class qualified number restrictions, keyed by their
    /// marker concept (see `CardDef`). The faithful Konclude `applyATLEASTRule` /
    /// `applyATMOSTRule` fire when a marker concept lands on a node, instead of
    /// KM's clausified `⋁ Eq` merge. Empty unless `card` is on.
    card_defs: HashMap<C, CardDef>,
    /// KM_HT_CARD master switch: route number restrictions through the Konclude
    /// number rules (`card_defs`) rather than the legacy `KM_HT_NUMBER` Eq-merge.
    card: bool,
    /// KM_HT_CARD_RECOG: propagation-based `≤n` RECOGNITION. Replaces the frontend's
    /// per-node `⊤→Q∨NQ` excluded-middle recognition (which branches on every node
    /// and causes disjunction non-convergence on cardinality giants) with a
    /// deterministic counting rule run at `Scan::Sat` (`card_recog_step`). The
    /// clausal excluded middle is dropped by cb_to_ht when this is set.
    card_recog: bool,
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
    /// `set_qmerge`: force the n≥2 qualified ≤n merge branch on (re-applied after
    /// each per-run `Ext::new`), independent of the KM_HT_QMERGE env flag.
    force_qmerge: bool,
    /// `set_number`: force the qualified-cardinality (≤n / ≥n / functional)
    /// equality-head handling on (re-applied after each per-run `Ext::new`),
    /// independent of the KM_HT_NUMBER env flag. Set from the input's `number`
    /// flag so a number KB routed to the fast Ht actually runs the cardinality
    /// rules instead of bailing `unsupported`.
    force_number: bool,
    /// full (pos+neg) labels of nodes seen in completed clash-free models, sorted.
    sat_labels: Vec<Vec<CLit>>,
    /// smallest-literal watch index into `sat_labels` for the superset check.
    satfold_watch: HashMap<CLit, Vec<usize>>,
    satfold_hits: u64,
    /// Nominals (O) passed from `run_json` (`set_nominals`); re-applied to
    /// `ext.nominals` after each per-query `Ext::new` (which resets it). Empty ⇒
    /// the o-rule is inert.
    nom_set: Vec<C>,
    /// Exact source ABox roots/edges/inequalities, recreated for every query and
    /// restart.  Negative role assertions are exact guarded clash clauses in the
    /// immutable clause template and therefore do not need mutable side state.
    native_abox: NativeAboxState,
    /// Role chains `R1∘R2⊑R` (incl. transitive `R∘R⊑R`) received via `set_chains`
    /// side-data, passed to each QoSat worker via `install_edge_compose` for the
    /// faithful Konclude role-automaton edge composition (KM_QO_EDGE_COMPOSE).
    /// The raw chain axioms are filtered from the clause stream by the frontend
    /// (`is_chain_axiom`), so QoSat cannot detect them from its clause set — the
    /// chain info MUST reach it through this side channel.
    qo_edge_chains: Vec<(R, R, R)>,
    /// Forward/backward chain-composition indexes for the Ht propagate loop
    /// (KM_QO_EDGE_COMPOSE on the complete-tableau path).  Populated in
    /// `set_chains`; fired on each `Event::Edge` in `propagate`.  Bounded by the
    /// Ht's blocking (the tableau model is finite), unlike the shared-filler
    /// QoSat where the same composition cascades.
    ht_chain_fwd: HashMap<R, Vec<(R, R)>>,
    ht_chain_bwd: HashMap<R, Vec<(R, R)>>,
    /// Ht-only `__cmpp__` clauses (transitive-chain compose, generated in
    /// `set_chains` via `ht_transitive_chain_compose`).  Stored SEPARATELY from
    /// `self.clauses` so the QoSat forward pass (which reads `&self.clauses`)
    /// never sees them — they cascade on the shared-filler model.  The Ht residue
    /// workers extend their template with these clauses (bounded by blocking).
    ht_tcc_clauses: Vec<Clause>,
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
            let comp = CLit {
                neg: !lits[i].neg,
                c: lits[i].c,
            };
            extra.push(Clause {
                body,
                head: vec![Atom::Concept { lit: comp, t: v }],
            });
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
                    new_body.push(Atom::Concept {
                        lit: CLit {
                            neg: false,
                            c: lit.c,
                        },
                        t: *t,
                    });
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

/// Index the ∀-clauses for Konclude optimized blocking B2a (KM_HT_BLOCK=5). A
/// universal `C0 ⊑ ∀r.D` is clausified to `C0(x) ∧ r(x,y) → D(y)`: body is exactly
/// one Concept on the role SOURCE var and one Role atom, head is a single Concept on
/// the role TARGET var. We key by `(C0-literal, r)` and collect the head literal `D`,
/// so blocking can ask "what does ∀r carry for a node whose label has C0?". Clauses
/// of any other shape (chains, ≥2 body roles, disjunctive/empty heads) are skipped —
/// B2a only needs the simple single-step universals. See docs/KONCLUDE-BLOCKING-SPEC.md.
fn index_forall(clauses: &[Clause]) -> HashMap<(CLit, R), Vec<CLit>> {
    let mut idx: HashMap<(CLit, R), Vec<CLit>> = HashMap::new();
    for c in clauses {
        if c.body.len() != 2 || c.head.len() != 1 {
            continue;
        }
        let (dlit, dvar) = match c.head[0] {
            Atom::Concept { lit, t } => (lit, t),
            _ => continue,
        };
        let mut c0: Option<(CLit, Var)> = None;
        let mut role: Option<(R, Var, Var)> = None;
        for a in &c.body {
            match *a {
                Atom::Concept { lit, t } => c0 = Some((lit, t)),
                Atom::Role { r, s, t } => role = Some((r, s, t)),
                _ => {}
            }
        }
        if let (Some((c0lit, c0v)), Some((r, rs, rt))) = (c0, role) {
            // C0 on the role source, D on the role target, distinct vars.
            if c0v == rs && dvar == rt && rs != rt {
                idx.entry((c0lit, r)).or_default().push(dlit);
            }
        }
    }
    idx
}

/// Faithful port of Konclude's chain-unfolding (generateRoleChainAutomatConcept)
/// for the Ht complete-tableau path.  For each ∀R.C clause `D(x) ∧ R(x,y) →
/// C(y)` and each chain R1∘R2⊑R (with R a creation role, per
/// CExtractPropagationIntoCreationDirectionPreProcess), emit:
///   `D(x) ∧ R1(x,y) → M2(y)`   (carry ∀R2.C marker across R1)
///   `M2(x) ∧ R2(x,y) → C(y)`   (M2 fires C on R2-successors)
/// M2 is a fresh marker concept.  Sound (R1∘R2⊑R ⟹ ∀R.C ⊑ ∀R1.∀R2.C).
fn ht_chain_unfolding_clauses(
    clauses: &[Clause],
    chains: &[(R, R, R)],
    transitive: &[R],
) -> Vec<Clause> {
    use std::collections::{HashMap, HashSet};
    if chains.is_empty() {
        return Vec::new();
    }
    let transitive: HashSet<R> = transitive.iter().copied().collect();
    let mut superrole: HashMap<R, Vec<R>> = HashMap::new();
    // sub-role S⊑R from single-role-body/head clauses (these are NOT raw chain
    // axioms; they're the normal role-hierarchy clauses, kept in the clause set)
    for c in clauses {
        let body = &c.body;
        let head = &c.head;
        if body.len() == 1
            && head.len() == 1
            && matches!(body[0], Atom::Role { .. })
            && matches!(head[0], Atom::Role { .. })
        {
            if let (Atom::Role { r: sr, .. }, Atom::Role { r: hr, .. }) = (&body[0], &head[0]) {
                if sr != hr {
                    superrole.entry(*sr).or_default().push(*hr);
                }
            }
        }
    }
    // creation roles (roles with some ∃R.D exists-head) + super-role closure
    let mut creation_roles: HashSet<R> = HashSet::new();
    for c in clauses {
        for a in &c.head {
            if let Atom::Exists { r, .. } = a {
                creation_roles.insert(*r);
            }
        }
    }
    let creation_closure: HashSet<R> = {
        let mut out = HashSet::new();
        for &r in &creation_roles {
            let mut st = vec![r];
            while let Some(u) = st.pop() {
                if out.insert(u) {
                    for &v in superrole.get(&u).map(|x| x.as_slice()).unwrap_or(&[]) {
                        st.push(v);
                    }
                }
            }
        }
        out
    };
    let super_close = |r: R| -> HashSet<R> {
        let mut out = HashSet::new();
        out.insert(r);
        let mut st = vec![r];
        while let Some(u) = st.pop() {
            for &v in superrole.get(&u).map(|x| x.as_slice()).unwrap_or(&[]) {
                if out.insert(v) {
                    st.push(v);
                }
            }
        }
        out
    };
    // max concept id (allocate fresh markers past it)
    let mut maxc: C = 0;
    for c in clauses {
        for a in c.body.iter().chain(c.head.iter()) {
            match a {
                Atom::Concept { lit, .. } => maxc = maxc.max(lit.c + 1),
                Atom::Exists { fil, .. } => maxc = maxc.max(fil.c + 1),
                _ => {}
            }
        }
    }
    let mut next_marker: C = maxc;
    // ∀R.C clauses: D(x) ∧ R(x,y) → C(y)  (one concept on source, one role, one concept on target)
    // Collect (D, R, C) for creation-role R only.
    let mut forall_clauses: Vec<(CLit, R, CLit)> = Vec::new();
    for c in clauses {
        let body = &c.body;
        let head = &c.head;
        if body.len() != 2 || head.len() != 1 {
            continue;
        }
        let mut src_con: Option<CLit> = None;
        let mut role: Option<(R, Var, Var)> = None;
        for a in body {
            match a {
                Atom::Concept { lit, t } if *t == X => src_con = Some(*lit),
                Atom::Role { r, s, t } => role = Some((*r, *s, *t)),
                _ => {}
            }
        }
        let (r, rs, rt) = match role {
            Some(r) => r,
            None => continue,
        };
        if let (Some(d), Atom::Concept { lit: e, t: et }) = (src_con, &head[0]) {
            if rs == X && *et == rt && rs != rt && creation_closure.contains(&r) {
                forall_clauses.push((d, r, *e));
            }
        }
    }
    // emit chain-unfolding clauses
    let mut out: Vec<Clause> = Vec::new();
    let mut chain_markers: HashMap<(R, CLit, CLit), C> = HashMap::new();
    for (d, r, e) in &forall_clauses {
        for &(r1, r2, u) in chains.iter() {
            if !super_close(u).contains(r) {
                continue;
            }
            // M2 = marker for ∀R2.E
            let m2 = *chain_markers.entry((r2, *d, *e)).or_insert_with(|| {
                let id = next_marker;
                next_marker += 1;
                // M2(x) ∧ R2(x,y) → E(y): M2 fires E on R2-successors
                out.push(Clause {
                    body: vec![
                        Atom::Concept {
                            lit: CLit::pos(id),
                            t: X,
                        },
                        Atom::Role { r: r2, s: X, t: 1 },
                    ],
                    head: vec![Atom::Concept { lit: *e, t: 1 }],
                });
                id
            });
            // D(x) ∧ R1(x,y) → M2(y): carry M2 across R1
            out.push(Clause {
                body: vec![
                    Atom::Concept { lit: *d, t: X },
                    Atom::Role { r: r1, s: X, t: 1 },
                ],
                head: vec![Atom::Concept {
                    lit: CLit::pos(m2),
                    t: 1,
                }],
            });
        }
    }
    let _ = transitive; // (transitive self-loop handled by existing __trans__ clauses)
    out
}

/// Ht-only port of `transitive_chain_compose_clauses` (frontend preprocess.rs).
/// Generates the `__cmpp__` mid-marker clauses that propagate a transitive
/// marker `__trans__T__C` (= P) through a chain `R∘S⊑T` (T transitive):
///   S(X,Z) ∧ P(Z) → M(X)      (S-edge + P on target ⇒ mid marker M on source)
///   R(X,Y) ∧ M(Y) → P(X)      (R-edge + M on target ⇒ P on source)
/// plus the `__cmpc__` variant (S-edge + the C_i operands on target ⇒ M2; R-edge
/// + M2 ⇒ P).  This is Konclude's role-automaton state propagation expressed as
/// Horn clauses — bounded by the finite marker set, NOT edge composition (which
/// cascades on the shared-filler QoSat).  Installed Ht-only via `set_chains` so
/// the QoSat forward pass never sees these clauses (no cascade); the Ht residue
/// (with blocking) derives the chain subsumptions.
fn ht_transitive_chain_compose(
    clauses: &[Clause],
    chains: &[(R, R, R)],
    transitive: &[R],
) -> Vec<Clause> {
    let trans: HashSet<R> = transitive.iter().copied().collect();
    if trans.is_empty() || chains.is_empty() {
        return Vec::new();
    }
    // sub-role hierarchy R⊑S from single-role-body→role-head clauses.
    let mut sub_super: HashMap<R, Vec<R>> = HashMap::new();
    for c in clauses {
        if c.body.len() == 1 && c.head.len() == 1 {
            if let (Atom::Role { r: u, s: us, t: ut }, Atom::Role { r: v, s: vs, t: vt }) =
                (&c.body[0], &c.head[0])
            {
                if us == vs && ut == vt && us != ut && u != v {
                    sub_super.entry(*u).or_default().push(*v);
                }
            }
        }
    }
    fn super_trans(
        u: R,
        sub_super: &HashMap<R, Vec<R>>,
        trans: &HashSet<R>,
        seen: &mut HashSet<R>,
    ) -> Option<R> {
        if trans.contains(&u) {
            return Some(u);
        }
        if !seen.insert(u) {
            return None;
        }
        for v in sub_super.get(&u).map(|x| x.as_slice()).unwrap_or(&[]) {
            if let Some(t) = super_trans(*v, sub_super, trans, seen) {
                return Some(t);
            }
        }
        None
    }
    // seen_p: for each clause R(X,Y) ∧ C1(Y) ∧ ... → P(X) where R is transitive,
    // key (R, sorted [C1,...]) → P (the head CLit).  P is the __trans__R__C marker.
    let mut seen_p: HashMap<(R, Vec<CLit>), CLit> = HashMap::new();
    for c in clauses {
        let roles: Vec<&Atom> = c
            .body
            .iter()
            .filter(|a| matches!(a, Atom::Role { .. }))
            .collect();
        if roles.len() != 1 {
            continue;
        }
        if let Atom::Role { r, s, t } = roles[0] {
            if !trans.contains(r) || *s != X {
                continue;
            }
            let yt = *t;
            if yt == X {
                continue;
            }
            let mut c_on_y: Vec<CLit> = c
                .body
                .iter()
                .filter_map(|a| match a {
                    Atom::Concept { lit, t } if *t == yt => Some(*lit),
                    _ => None,
                })
                .collect();
            c_on_y.sort();
            c_on_y.dedup();
            if c_on_y.is_empty() || c.head.is_empty() {
                continue;
            }
            if !c
                .head
                .iter()
                .all(|h| matches!(h, Atom::Concept { t, .. } if *t == X))
            {
                continue;
            }
            if let Atom::Concept { lit: p, .. } = &c.head[0] {
                seen_p.entry((*r, c_on_y)).or_insert(*p);
            }
        }
    }
    if seen_p.is_empty() {
        return Vec::new();
    }
    // fresh marker ids past the max concept id
    let mut maxc: C = 0;
    for c in clauses {
        for a in c.body.iter().chain(c.head.iter()) {
            if let Atom::Concept { lit, .. } = a {
                maxc = maxc.max(lit.c + 1);
            }
        }
    }
    let mut next_marker: C = maxc;
    let y: Var = 1;
    let z: Var = 2;
    let mut out: Vec<Clause> = Vec::new();
    // mid-marker maps keyed by (s, P) / (s, operands) so repeated chains share
    let mut mid_p: HashMap<(R, CLit), C> = HashMap::new();
    let mut mid_c: HashMap<(R, Vec<CLit>), C> = HashMap::new();
    for &(r, s, u) in chains {
        let mut seen2 = HashSet::new();
        let t = match super_trans(u, &sub_super, &trans, &mut seen2) {
            Some(t) => t,
            None => continue,
        };
        for ((pt, c_on_y), p) in &seen_p {
            if *pt != t {
                continue;
            }
            // __cmpp variant: S(X,Z) ∧ P(Z) → M(X) ; R(X,Y) ∧ M(Y) → P(X)
            let m = *mid_p.entry((s, *p)).or_insert_with(|| {
                let id = next_marker;
                next_marker += 1;
                out.push(Clause {
                    body: vec![
                        Atom::Role { r: s, s: X, t: z },
                        Atom::Concept { lit: *p, t: z },
                    ],
                    head: vec![Atom::Concept {
                        lit: CLit::pos(id),
                        t: X,
                    }],
                });
                id
            });
            out.push(Clause {
                body: vec![
                    Atom::Role { r, s: X, t: y },
                    Atom::Concept {
                        lit: CLit::pos(m),
                        t: y,
                    },
                ],
                head: vec![Atom::Concept { lit: *p, t: X }],
            });
            // __cmpc variant: S(X,Z) ∧ ⋀C_i(Z) → M2(X) ; R(X,Y) ∧ M2(Y) → P(X)
            let key = (s, c_on_y.clone());
            let m2 = *mid_c.entry(key).or_insert_with(|| {
                let id = next_marker;
                next_marker += 1;
                let mut body1: Vec<Atom> = vec![Atom::Role { r: s, s: X, t: z }];
                for ci in c_on_y {
                    body1.push(Atom::Concept { lit: *ci, t: z });
                }
                out.push(Clause {
                    body: body1,
                    head: vec![Atom::Concept {
                        lit: CLit::pos(id),
                        t: X,
                    }],
                });
                id
            });
            out.push(Clause {
                body: vec![
                    Atom::Role { r, s: X, t: y },
                    Atom::Concept {
                        lit: CLit::pos(m2),
                        t: y,
                    },
                ],
                head: vec![Atom::Concept { lit: *p, t: X }],
            });
        }
    }
    out
}

/// `s(a,b) → r(b,a)` (single role body, single role head, swapped variables,
/// distinct roles). cb_to_ht emits these (with the `inverse` TInput flag often left
/// false), so the flag is unreliable — detect inverse structurally instead. Used to
/// auto-select Konclude optimized blocking (mode 5), which is sound under inverse,
/// over the subset default (mode 1, unsound under inverse). Mirrors `bridge_of`
/// inside `compose_inverse`.
fn has_inverse_bridge(clauses: &[Clause]) -> bool {
    clauses.iter().any(|c| {
        if c.body.len() == 1 && c.head.len() == 1 {
            if let (
                Atom::Role {
                    r: sr,
                    s: ba,
                    t: bb,
                },
                Atom::Role {
                    r: rr,
                    s: hs,
                    t: ht,
                },
            ) = (&c.body[0], &c.head[0])
            {
                return *hs == *bb && *ht == *ba && *sr != *rr;
            }
        }
        false
    })
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
            if let (
                Atom::Role {
                    r: sr,
                    s: ba,
                    t: bb,
                },
                Atom::Role {
                    r: rr,
                    s: hs,
                    t: ht,
                },
            ) = (&c.body[0], &c.head[0])
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
            .filter_map(|a| {
                if let Atom::Role { r, .. } = a {
                    Some(*r)
                } else {
                    None
                }
            })
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
        let n_bridges: usize = clauses
            .iter()
            .filter(|(c, _, _)| bridge_of(c).is_some())
            .count();
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
            let rb: Vec<R> = c
                .body
                .iter()
                .filter_map(|a| {
                    if let Atom::Role { r, .. } = a {
                        Some(*r)
                    } else {
                        None
                    }
                })
                .collect();
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
        let rb: Vec<R> = c
            .body
            .iter()
            .filter_map(|a| {
                if let Atom::Role { r, .. } = a {
                    Some(*r)
                } else {
                    None
                }
            })
            .collect();
        if rb.len() > 1 {
            for r in rb {
                multi_bodied.insert(r);
            }
        }
        if !is_bridge {
            for h in &c.head {
                match h {
                    Atom::Role { r, .. } => {
                        otherwise_produced.insert(*r);
                    }
                    Atom::Exists { r, .. } => {
                        otherwise_produced.insert(*r);
                    }
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
            out.push(Clause {
                body: nb,
                head: c.head.clone(),
            });
        }
        if body_roles.len() == 1 {
            let (idx, r, u, v) = body_roles[0];
            if composable(r) {
                let s = inv_of[&r];
                let mut nb = c.body.clone();
                // r(u,v) ⟸ s(v,u): fire the same consequence over the forward s-edge.
                nb[idx] = Atom::Role { r: s, s: v, t: u };
                out.push(Clause {
                    body: nb,
                    head: c.head.clone(),
                });
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
                        head: vec![Atom::Concept {
                            lit: CLit::pos(x),
                            t: X,
                        }],
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
    /// Optional membership index for the adjacency lists. The vectors remain
    /// authoritative for traversal; this only replaces the linear duplicate
    /// scan in `add_edge`.
    edge_seen: HashSet<(Node, R, Node)>,
    edge_seen_on: bool,
    /// shared node for a concept literal (pos and neg both keyed).
    concept_node: HashMap<CLit, Node>,
    /// parked disjunctions: (node, clause_id); re-evaluated as labels grow.
    pending: Vec<(Node, usize)>,
    /// P0 (Konclude per-node critical queue): `pending_by_node[n]` holds the
    /// INDICES into `pending` of the disjunctions parked at node `n`. Lets
    /// `eval_parked_at(n)` and `kill_node(n)` touch only `n`'s parked entries
    /// instead of scanning the whole `pending` Vec — the O(|pending|) → O(deg(n))
    /// fix (|pending| reaches 763k on 14817: the 13 global ⊤-disjunctions × 58k
    /// nodes). Maintained ONLY in the non-tracing global precompute; the residue
    /// DFS (tracing) keeps its small linear scan + length-truncate undo untouched,
    /// so this is inert there. Kept in sync with `pending` via `pending_remove`.
    pending_by_node: Vec<Vec<usize>>,
    /// nodes whose own seed is unsatisfiable (local clash, not KB clash).
    node_unsat: HashSet<Node>,
    lit_work: Vec<(Node, CLit)>,
    edge_work: Vec<(Node, R, Node)>,
    node_work: Vec<Node>,
    /// Edge-pop budget: bail `unsupported` once this many edge-work items have been
    /// processed in the current saturation. The node cap cannot bound the
    /// ∀-pollution edge cascade (nodes stay fixed while edges blow to millions),
    /// so a per-concept model that explodes must fail-fast here to the blocking
    /// tableau instead of stalling inside one `drain_work`. `u64::MAX` = no bound
    /// (the default for the global/complete passes). Set via QoSat field.
    edge_budget: u64,
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
    /// elc NF1 fast path (`KM_HT_QO_FASTIMPL`): clauses of the simple Horn shape
    /// `C(x) → D(x)` (one concept body atom on the anchor, one concept head atom on
    /// the anchor) are the bulk of a near-EL ontology (ore_ont_14817: 83% of
    /// 272545 clauses). Firing them through `fire_concept_clause` allocates a
    /// substitution vector and runs the full `apply_head` machinery per call (5.1M
    /// calls). Index them as `C → [D…]` and apply directly with `add_lit` when `C`
    /// arrives — result-identical (apply_head of a single concept head IS add_lit),
    /// no allocation. These clauses are then EXCLUDED from `concept_trig`.
    simple_impl: HashMap<CLit, Vec<CLit>>,
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
    /// KM_HT_QO_KPWRITE (lever C, the faithful Konclude `applyALLRule` backward
    /// write). The pure-CHECK `kpset` above DEFERS every inverse-anchored operand,
    /// which on a pervasive-inverse Horn giant (9724: 66M back-edge writes) marks
    /// ~every concept insufficient ⇒ global deferral ⇒ timeout. Konclude does NOT
    /// defer the backward contribution: `applyALLRule` (:6143) WRITES the ∀R⁻
    /// operands to the genuine R-predecessors via `backPropHash`
    /// (`addConceptFilteredToIndividual(op, backPropIndiNode)`, :6167). That is
    /// SOUND — every R-predecessor of the (shared) filler really does entail the
    /// operand by ∀-semantics (X ⊑ ∃R.D, D ⊑ ∀R⁻.E ⟹ X ⊑ E). So under `kpwrite`
    /// an inverse-anchored write whose target is a real SELF/named node (`on_self`,
    /// not a shared ∃-filler) is performed as a real `add_lit` write that
    /// propagates forward — exactly Konclude's backward write. Only a SHARED-FILLER
    /// target stays a containment check (reading a filler's label as a named
    /// subsumer would conflate the context-specific filler with the concept — the
    /// 7581 pollution this whole mechanism exists to prevent). Net: the pervasive
    /// sound inverse propagation certifies in the single forward pass.
    kpwrite: bool,
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
    /// KM_RSUCC: enable the transitive+inverse reconstruction insufficiency
    /// post-pass (see `reach_by_role`).
    rsucc: bool,
    /// KM_RSUCC: per role `R`, the reachability concepts `C` propagated by a
    /// `C(y) ∧ R(x,y) → C(x)` clause; used to flag shared fillers whose
    /// predecessor carries `C` across an inverse back-edge.
    reach_by_role: std::rc::Rc<HashMap<R, Vec<C>>>,
    /// KM_RSUCC: per role `S = R⁻`, the reach concepts of `R` — for the QOGF path
    /// where only the forward inverse edge `S(p,h)` exists (the `R(h,p)` back-edge
    /// is unmaterialised). `p --S--> h` ⟺ `h --R--> p`, so flag filler `h`.
    reach_via_inv: std::rc::Rc<HashMap<R, Vec<C>>>,
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
    /// KM_HT_QO_SHIQ (P2.1, the sound SHIQ completion): build NON-SHARED
    /// successors (each ∃ makes a fresh node owned by its creating source) with
    /// ancestor subset blocking for termination — Konclude's mechanism
    /// (`createSuccessorIndividual` + `applyALLRule` forward over genuine edges +
    /// optimized subset blocking). Eliminates the shared-filler ∀ pollution
    /// (`qo_insufficient` critical-ALL) at the source: a `∀R.C` write now lands on
    /// the source's OWN successor, never a node another source also reaches.
    shiq: bool,
    /// KM_HT_QO_NOPOLLUTE (Konclude `isCriticalALLConceptDescriptorInsufficient`):
    /// when a critical-ALL ∀-write lands on a shared filler, DEFER it (mark the
    /// target insufficient) instead of writing `lit` into the filler's label. Keeps
    /// shared fillers small (base + range-forced only) so the precompute converges.
    no_pollute: bool,
    /// KM_HT_QO_PSPLIT (Konclude copy-on-conflict for the NF4 forward-∀ path): when
    /// the forward broadcast `R(n,t) ⊓ lit(n) → e(t)` would impose a predecessor-
    /// specific operand `e` on a SHARED ∃-filler `t`, redirect `n`'s edge to a
    /// content-keyed successor (keyed by filler-concept + n's accumulated operand
    /// set) instead of polluting `t`. Reproduces Konclude's separate-successor-by-
    /// context (≈217k contexts on 14817) so the `∃R.X⊑Y` backward broadcast stays
    /// LOCAL and bounded — keeping the broadcasts (unlike NOPOLLUTE), hence complete.
    psplit: bool,
    /// KM_HT_QO_APPROX (Konclude CCalculationTableauApproximationSaturation): at a
    /// disjunction, PICK the first live disjunct (greedy, non-backtracking) and
    /// mark the concept insufficient, instead of parking. Produces an approximate
    /// model whose labels are the possible-subsumer candidates (the branch-resolved,
    /// role-mediated consequences) — the candidate source the forward-only pass
    /// lacks. Over-approximate: a calculated test confirms each candidate.
    approx: bool,
    /// KM_HT_QO_NODECERTAIN: map from a CONCEPT-LEVEL disjunction's clause id to
    /// the ⋂-closure `D` of its disjuncts (a concept in every disjunct's closure,
    /// hence true in every branch). When such a disjunction parks at a node, inject
    /// `D` AT THAT NODE and continue (don't park): `D` then fires the role rules
    /// (∃R.X⊑Y) forward, so role-mediated certain subsumers reach the predecessor —
    /// which the concept-lattice `certain_disjunction_consequences` cannot do.
    /// Sound (D holds in all branches); complete for subsumption.
    node_certain: Option<std::sync::Arc<HashMap<usize, Vec<C>>>>,
    /// per-saturation guard: an injected concept-level disjunction is not
    /// re-injected each time its clause re-fires at the same node.
    nc_resolved: HashSet<(Node, usize)>,
    /// P2.1 ancestor link (parallel to `label`): the predecessor node that created
    /// this successor, for the blocking ancestor walk. `None` for roots/self-nodes.
    qo_parent: Vec<Option<Node>>,
    /// KM_HT_QO_SPLIT (port #2, copy-on-conflict): the faithful Konclude middle
    /// ground between the over-sharing `sat_filler` (one node per `(fil,role)`,
    /// which forces a critical-ALL deferral the moment two predecessors impose
    /// incompatible `∀R` operands on it — the 7581/giant over-defer) and the
    /// non-shared `shiq` mode (one successor per source, ×concepts OOM). A
    /// forward `∀R.C` write whose operand is not already forced does NOT trip
    /// `qo_insufficient`; instead the source's `R`-edge is REDIRECTED off the
    /// shared base filler onto a node keyed by `(base-fil, R, source's accumulated
    /// ∀R-operand set)` (`copyDependingIndividualNode`). Base/shared fillers stay
    /// unpolluted (their label is sound for every sharing predecessor); the
    /// per-operand-set split nodes carry the operands. Nodes are bounded by the
    /// number of DISTINCT operand sets, not by predecessors, so two predecessors
    /// imposing the same operands still share — Konclude's content sharing.
    split_mode: bool,
    /// Base ∃-filler concept of each node (parallel to `label`): the `fil` of the
    /// `∃R.fil` that created it, used as the split key's base. `None` for
    /// roots/concept self-nodes that were never an ∃-filler.
    node_fil: Vec<Option<CLit>>,
    /// Accumulated forward `∀R`-operand set imposed by a source node on its
    /// `R`-successors (`split_mode`). Grows monotonically; the sorted form is the
    /// split key.
    src_forall: HashMap<(Node, R), HashSet<CLit>>,
    /// Content-keyed split fillers: `(base-fil, role, sorted-∀-operand-set) → node`.
    /// Sources imposing the same operand set on the same `(fil,role)` share one
    /// node (content sharing); a new operand set creates a fresh seeded node.
    split_filler: HashMap<(CLit, R, Vec<CLit>), Node>,
    /// KM_HT_QO_CARDMERGE (Konclude ≤-rule / `mergeIndividualNode`): PERFORM the
    /// forced successor merge a functional/at-most `Eq`-head demands, in the
    /// forward pass, instead of deferring (`card_defer`). Sound under separate
    /// fillers only (merge FILLER nodes, never concept self-nodes — that would
    /// conflate classification). The two merged successors are first PRIVATIZED to
    /// the constrained predecessor (copied off the shared filler), so the merge
    /// cannot pollute other predecessors that lack the `≤n` — the same per-source
    /// discipline port #2 uses for `∀`. The victim is then folded into the
    /// survivor (union labels — a clash ⇒ source unsat — and re-point edges) via
    /// the `merged_into` union-find.
    card_merge: bool,
    /// Union-find redirect (parallel to `label`): `Some(s)` ⇒ this node was merged
    /// INTO survivor `s` and is DEAD — evacuated (no label, no edges, absent from
    /// every index); only stale worklist entries may still name it, skipped via the
    /// dead check at each pop. `None` ⇒ live. (Kept inert by the content-shared
    /// merge, which redirects edges instead of evacuating nodes; the dead checks
    /// are then always false but stay as a safety net.)
    merged_into: Vec<Option<Node>>,
    /// Defining seed of each filler node (parallel to `label`): the sorted set of
    /// literals that IDENTIFY it — its base ∃-fil, plus (for a content-merged or
    /// split node) the fils/operands folded into it. Empty for self/root nodes.
    /// Two cardinality merges or splits producing the same seed share one node, so
    /// the node count is bounded by the distinct seed-sets, not by predecessors.
    node_seed: Vec<Vec<CLit>>,
    /// Content-keyed filler nodes: `(role, sorted seed-set) → node`. A
    /// cardinality merge (and, in the unified path, a `∀`-split) redirects the
    /// constrained predecessor's r-edge onto the node for the union seed-set,
    /// creating + seeding it on first use. The content-sharing that keeps the
    /// merge bounded on the high-cardinality giants.
    seed_node: HashMap<(R, Vec<CLit>), Node>,
    /// Node-count backstop for the content-shared merge: once the model exceeds
    /// this, stop creating merged nodes and fall back to `card_defer` (sound). Far
    /// above any healthy run; only a pathological fan-out trips it.
    merge_budget: usize,
    /// KM_HT_QO_EDGEFAST (elc clone-free edge port): reuse one scratch buffer for
    /// the `prop`/`fprop` element copies in the edge loop instead of allocating a
    /// fresh `Vec` per edge pop (800k+ edges on the throughput giants). `edge_buf`
    /// holds the NF4 backward/forward-link conclusions; `to_fire_buf` holds the
    /// guard-filtered role-clause ids. Capacity is retained across pops (elc's
    /// `nf4_buf` pattern), so the per-edge allocation churn collapses to one alloc.
    /// Result-identical — same elements, same firing order.
    edgefast: bool,
    /// Deduplicate ordinary NF4 propagation conclusions across one drain wave.
    prop_batch_on: bool,
    edge_buf: Vec<CLit>,
    to_fire_buf: Vec<usize>,
    /// KM_HT_QO_EDGEPROBE: gate for the QO work-volume counters (off ⇒ the hot-path
    /// increments are skipped, so production has no overhead). `edgeprobe_iv` is the
    /// QOEDGE print interval (in edge pops).
    edgeprobe: bool,
    edgeprobe_iv: u64,
    /// Wall-clock start of the current `saturate_global` pass — lets the QOSAT/
    /// QODRAIN/QOEDGE heartbeats print elapsed seconds, so a rate collapse is
    /// visible directly in wall time (the throughput-giant diagnosis). Set at the
    /// top of `saturate_global`; only read under `KM_HT_TRACE`.
    sat_t0: Option<Instant>,
    /// Last wall-clock heartbeat print (the TIME-driven probe). The QODRAIN/QOEDGE
    /// prints are pop-count-gated, so they go SILENT during a rate collapse (the
    /// exact symptom we want to see). `hb_check` prints at most every `hb_interval`
    /// seconds regardless of pop rate, so a stall shows up as a heartbeat with
    /// barely-moving counters. Gated on `edgeprobe`.
    last_hb: Option<Instant>,
    hb_interval: f64,
    /// KM_QO_EDGE_COMPOSE (default OFF): faithful port of Konclude's role-automaton
    /// edge composition.  For each detected chain `R1∘R2⊑R` (incl. transitive
    /// `R∘R⊑R`), a fresh `R1`-edge `(s,t)` joined with an existing `R2`-edge
    /// `(t,z)` creates a composed `R`-edge `(s,z)` — and dually for a fresh
    /// `R2`-edge.  This is the mechanism Konclude's precompute uses to derive
    /// `∃dev.0926` on a root that only has `∃part.(∃dev.0926)` via `part∘dev⊑dev`
    /// (ore_ont_14817's 71 missing subsumptions).  Bounded by ACTUAL edges (each
    /// unique `(s,role,t)` is added at most once), not the ∀-filler cross-product
    /// that cascaded under KM_QO_CHAIN_UNFOLD.  The two lookup maps key the
    /// O(degree) join on each fresh edge:
    ///   `chain_fwd[R1] = [(R2, R), ...]`  — fresh R1-edge (s,t): scan t's R2-outs
    ///   `chain_bwd[R2] = [(R1, R), ...]`  — fresh R2-edge (t,z): scan t's R1-ins
    chain_fwd: HashMap<R, Vec<(R, R)>>,
    chain_bwd: HashMap<R, Vec<(R, R)>>,
    /// KM_QO_EDGE_COMPOSE: set when the edge-composition cascade exceeded the
    /// per-concept edge budget (KM_QO_EC_BUDGET, default 200k).  The drain loop
    /// bails with `edge_bailed = true` instead of `unsupported = true` so the
    /// concept goes to residue (Ht edge-compose) rather than deferring the whole.
    /// Also set under KM_TRANS_CHAIN_COMPOSE when the __cmpp__ clause propagation
    /// cascades (the transitive marker spreading through high-fanout part-edges).
    edge_bailed: bool,
}

/// undoable mutation for the residue-test DFS.
enum QoUndo {
    Lit(Node, CLit),
    Edge(Node, R, Node),
    NodeNew,
    Unsat(Node),
    Pending(usize), // pending grew to this len
    ConceptNode(CLit),
    Prop(R, Node, usize),  // prop[(R,Node)] grew to this len
    Fprop(R, Node, usize), // fprop[(R,Node)] grew to this len
    Filler(CLit, u32),     // filler_node[(CLit, class)] was created
    SatFiller(CLit, R),    // sat_filler[(CLit, role)] was created
}

pub struct QoResult {
    pub unsupported: bool,
    pub clashed: bool,
    pub sufficient: bool,
    pub root_label: HashSet<C>,
    /// KM_QO_EDGE_COMPOSE: the edge-composition cascade exceeded the per-concept
    /// edge budget.  The forward label is INCOMPLETE (chain-derived subsumers may
    /// be missing) but not unsound.  Treat as insufficient → residue (the Ht
    /// complete-tableau with edge-compose derives the missing chain subsumers).
    pub edge_bailed: bool,
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
        let fastimpl = std::env::var_os("KM_HT_QO_FASTIMPL").is_some();
        let mut simple_impl: HashMap<CLit, Vec<CLit>> = HashMap::new();
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
        // r-Succ (KM_RSUCC): transitive-reachability propagation clauses of the
        // shape `C(y) ∧ R(x,y) → C(x)` (same concept C on the role SOURCE in the
        // head and on the role TARGET in the body — the `__trans__`/`__chain__`
        // transitivity encoding).  In the shared forward model the head `C(x)` on
        // a filler `x` reached across an inverse back-edge is suppressed (a filler
        // label is not read as a subsumer), so the per-predecessor reconstruction
        // never fires — the transitive+inverse unsat is missed.  `reach_by_role[R]`
        // lets `kp_finalize` mark such a filler insufficient (→ residue → complete
        // tableau, which decides it correctly).
        let mut reach_by_role: HashMap<R, Vec<C>> = HashMap::new();
        for rec in clauses.iter() {
            let body = &rec.1;
            let head = &rec.0.head;
            if head.len() != 1 {
                continue;
            }
            let (hc, hxv) = match head[0] {
                Atom::Concept { lit, t } if !lit.neg => (lit.c, t),
                _ => continue,
            };
            let mut role: Option<(R, Var, Var)> = None;
            let mut bconc: Option<(C, Var)> = None;
            let mut ok = true;
            for a in body {
                match a {
                    Atom::Role { r, s, t } if role.is_none() => role = Some((*r, *s, *t)),
                    Atom::Concept { lit, t } if !lit.neg && bconc.is_none() => {
                        bconc = Some((lit.c, *t))
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
            if let (Some((r, sv, tv)), Some((bc, bcv))) = (role, bconc) {
                // head concept on the role source, body concept (same C) on the target.
                if hc == bc && hxv == sv && bcv == tv {
                    reach_by_role.entry(r).or_default().push(hc);
                }
            }
        }
        // Inverse-role map from bridging clauses `R(x,y) → S(y,x)` (S = R⁻), used by
        // the QOGF global-shared path: there the per-predecessor back-edge `R(h,p)`
        // is never materialised, but the FORWARD inverse edge `S(p,h)` (= R⁻) IS in
        // `out_edges[p]`. So `reach_via_inv[S]` lets the reach post-pass flag the
        // filler `h` from `p --S--> h` when `p` carries the reach concept `C`.
        let mut inv_map: HashMap<R, R> = HashMap::new();
        for rec in clauses.iter() {
            let body = &rec.1;
            let head = &rec.0.head;
            if body.len() != 1 || head.len() != 1 {
                continue;
            }
            if let (
                Atom::Role {
                    r: br,
                    s: bs,
                    t: bt,
                },
                Atom::Role {
                    r: hr,
                    s: hs,
                    t: ht,
                },
            ) = (&body[0], &head[0])
            {
                // R(x,y) → S(y,x): head source = body target, head dest = body source.
                if *hs == *bt && *ht == *bs && *br != *hr {
                    inv_map.insert(*br, *hr);
                }
            }
        }
        let mut reach_via_inv: HashMap<R, Vec<C>> = HashMap::new();
        for (&r, cs) in reach_by_role.iter() {
            if let Some(&rinv) = inv_map.get(&r) {
                reach_via_inv
                    .entry(rinv)
                    .or_default()
                    .extend(cs.iter().copied());
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
                Atom::Role {
                    r: hr,
                    s: hs,
                    t: ht,
                } if hs == sv && ht == tv => {
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
            // KM_KEEP_CHAIN_AXIOMS: the raw `R1∘R2⊑R` (and `R∘R⊑R` transitive)
            // role axioms are 2-role-body / 1-role-head clauses kept in the
            // stream ONLY for chain/transitivity detection (the fprop chain-
            // unfolding + the Uni self-propagation).  They must NOT enter the
            // QoSat role-clause indexes: a 2-role-body clause hits the slow
            // `role_noguard` path (fires on every edge of each of its roles),
            // which blows up the saturation (14817 kc.tin: 60s timeout vs 13.5s
            // baseline).  The chain semantics is handled by the fprop unfolding,
            // not by matching the raw axiom.  Skip them here.
            if has_role
                && std::env::var_os("KM_KEEP_CHAIN_AXIOMS").is_some()
                && body.len() == 2
                && body.iter().all(|a| matches!(a, Atom::Role { .. }))
                && head.len() == 1
                && matches!(head[0], Atom::Role { .. })
            {
                continue;
            }
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
                // elc NF1 fast path: `C(x) → D(x)` (single concept body on X, single
                // concept head on X). Index as C → D and skip concept_trig.
                let simple = fastimpl
                    && body.len() == 1
                    && head.len() == 1
                    && matches!(body[0], Atom::Concept { t, .. } if t == X)
                    && matches!(head[0], Atom::Concept { t, .. } if t == X);
                if simple {
                    if let (Atom::Concept { lit: bl, .. }, Atom::Concept { lit: hl, .. }) =
                        (&body[0], &head[0])
                    {
                        simple_impl.entry(*bl).or_default().push(*hl);
                    }
                } else {
                    for a in body {
                        if let Atom::Concept { lit, .. } = a {
                            concept_trig.entry(*lit).or_default().push(cid);
                        }
                    }
                }
            }
        }
        // ---- QoSat chain-unfolding of ∀R.C (Konclude generateRoleChain-
        // AutomatConcept, the begin --R1--> mid --R2--> end unfolding) ----
        // SUPERSeded by the Ht path (Ht::new chain-unfolding clauses, gated
        // KM_KEEP_CHAIN_AXIOMS) for the complete-tableau decision.  Kept behind
        // KM_QO_CHAIN_UNFOLD (default OFF) because it cascades on high-fanout
        // creation roles (14817 dev: 9-14M edge pops).  Useful for low-fanout
        // ontologies where the QoSat fast path can soundly compose the chain ∀.
        // Sound (R1∘R2⊑R ⟹ ∀R.C ⊑ ∀R1.∀R2.C).  Fresh marker concepts allocated
        // past the max concept id.
        if fprop_on && std::env::var_os("KM_QO_CHAIN_UNFOLD").is_some() {
            // detect chains R1∘R2⊑R (2-role-body, 1-role-head, not all-equal)
            let mut chains: Vec<(R, R, R)> = Vec::new();
            for rec in clauses.iter() {
                let body = &rec.1;
                let head = &rec.0.head;
                let rb: Vec<&Atom> = body
                    .iter()
                    .filter(|a| matches!(a, Atom::Role { .. }))
                    .collect();
                if body.len() == 2
                    && head.len() == 1
                    && matches!(body[0], Atom::Role { .. })
                    && matches!(body[1], Atom::Role { .. })
                    && matches!(head[0], Atom::Role { .. })
                {
                    if let (
                        Atom::Role {
                            r: r1,
                            s: r1s,
                            t: r1t,
                        },
                        Atom::Role {
                            r: r2,
                            s: r2s,
                            t: r2t,
                        },
                        Atom::Role {
                            r: hr,
                            s: hs,
                            t: ht_,
                        },
                    ) = (rb[0], rb[1], &head[0])
                    {
                        let (fr, sr, mid_ok) = if r1t == r2s {
                            (*r1, *r2, true)
                        } else if r2t == r1s {
                            (*r2, *r1, true)
                        } else {
                            (0, 0, false)
                        };
                        if mid_ok
                            && *hs == *r1s
                            && *ht_ == *r2t
                            && *r1s != *r2t
                            && !(fr == sr && sr == *hr)
                        {
                            chains.push((fr, sr, *hr));
                        }
                    }
                }
            }
            // detect transitive roles (R∘R⊑R) for self-propagation
            let mut transitive: HashSet<R> = HashSet::new();
            for rec in clauses.iter() {
                let body = &rec.1;
                let head = &rec.0.head;
                let rb: Vec<&Atom> = body
                    .iter()
                    .filter(|a| matches!(a, Atom::Role { .. }))
                    .collect();
                if body.len() == 2
                    && head.len() == 1
                    && matches!(body[0], Atom::Role { .. })
                    && matches!(body[1], Atom::Role { .. })
                    && matches!(head[0], Atom::Role { .. })
                {
                    if let (
                        Atom::Role {
                            r: r1,
                            s: r1s,
                            t: r1t,
                        },
                        Atom::Role {
                            r: r2,
                            s: r2s,
                            t: r2t,
                        },
                        Atom::Role {
                            r: hr,
                            s: hs,
                            t: ht_,
                        },
                    ) = (rb[0], rb[1], &head[0])
                    {
                        if r1 == r2
                            && r2 == hr
                            && r1t == r2s
                            && *hs == *r1s
                            && *ht_ == *r2t
                            && *r1s != *r2t
                        {
                            transitive.insert(*hr);
                        }
                    }
                }
            }
            // Faithful port of CExtractPropagationIntoCreationDirectionPreProcess:
            // collect CREATION ROLES — roles R for which some ∃R.D exists in the
            // clauses (an Exists head atom), plus their super-roles (Konclude's
            // getIndirectSuperRoleList).  Only ∀R.C whose R is a creation role
            // needs propagation into a created successor (the bound that prevents
            // the ∀-cascade on every edge).  This is the gating Konclude uses to
            // keep the saturation bounded.
            let mut creation_roles: HashSet<R> = HashSet::new();
            for rec in clauses.iter() {
                for a in &rec.0.head {
                    if let Atom::Exists { r, .. } = a {
                        creation_roles.insert(*r);
                    }
                }
            }
            // close over super-roles
            let creation_closure: HashSet<R> = {
                let mut out = HashSet::new();
                for &r in &creation_roles {
                    let mut st = vec![r];
                    while let Some(u) = st.pop() {
                        if out.insert(u) {
                            for &v in superrole.get(&u).map(|x| x.as_slice()).unwrap_or(&[]) {
                                st.push(v);
                            }
                        }
                    }
                }
                out
            };
            if !chains.is_empty() {
                // super-role closure (reflexive-transitive) for chain targeting
                let super_close = |r: R| -> HashSet<R> {
                    let mut out = HashSet::new();
                    out.insert(r);
                    let mut st = vec![r];
                    while let Some(u) = st.pop() {
                        for &v in superrole.get(&u).map(|x| x.as_slice()).unwrap_or(&[]) {
                            if out.insert(v) {
                                st.push(v);
                            }
                        }
                    }
                    out
                };
                // max concept id (allocate fresh markers past it)
                let mut maxc: C = 0;
                for rec in clauses.iter() {
                    for a in rec.1.iter().chain(rec.0.head.iter()) {
                        match a {
                            Atom::Concept { lit, .. } => maxc = maxc.max(lit.c + 1),
                            Atom::Exists { fil, .. } => maxc = maxc.max(fil.c + 1),
                            _ => {}
                        }
                    }
                }
                let mut next_marker: C = maxc;
                // snapshot the fprop_rule (guard -> [(R, E)]) to iterate while mutating
                let snap: Vec<(CLit, Vec<(R, CLit)>)> =
                    fprop_rule.iter().map(|(k, v)| (*k, v.clone())).collect();
                // M2 marker for (R2, parent_guard, E): carries ∀R2.E
                let mut chain_markers: HashMap<(R, CLit, CLit), CLit> = HashMap::new();
                for (guard, rules) in &snap {
                    for &(r, e) in rules {
                        // Konclude propagation-into-creation-direction gate: only
                        // unfold ∀R.C whose R is a creation role.  Non-creation ∀s
                        // never need to reach a created successor, so propagating
                        // them is wasted work (the cascade source).
                        if !creation_closure.contains(&r) {
                            continue;
                        }
                        // for each chain R1∘R2⊑U with U ⊑* r (r is U or a sub-role of U)
                        for &(r1, r2, u) in chains.iter() {
                            if !super_close(u).contains(&r) {
                                continue;
                            }
                            // M2 = marker for ∀R2.E
                            let m2 = *chain_markers.entry((r2, *guard, e)).or_insert_with(|| {
                                let id = CLit {
                                    neg: false,
                                    c: next_marker,
                                };
                                next_marker += 1;
                                // M2's own fprop_rule: ∀R2.E fires E on R2-successors
                                fprop_rule.entry(id).or_default().push((r2, e));
                                // NOTE: the transitive self-loop on R2 (∀R2.C
                                // re-fires on R2-successors) is NOT added here.
                                // On the shared-filler model the self-prop
                                // `(r2, id)` cascades (every R2-edge re-fires id
                                // onto a shared filler → non-convergent).  The
                                // transitive ∀R2.C chase is handled by the
                                // existing __trans__ marker-propagation +
                                // reach_by_role/kp_finalize post-pass + residue
                                // complete tableau (sound).  Adding the self-loop
                                // here is faithful to Konclude's automaton but
                                // requires copy-on-conflict (copyDependingIndividual
                                // Node) to bound — the deep architectural piece.
                                id
                            });
                            // carry M2 across the R1-edge: guard D on source ∧ R1-edge → M2 on successor
                            let entry = fprop_rule.entry(*guard).or_default();
                            if !entry.contains(&(r1, m2)) {
                                entry.push((r1, m2));
                            }
                        }
                        // The parent ∀R.C transitive self-propagation (fprop_rule[D]
                        // += (r, D)) is intentionally NOT added: on the shared-filler
                        // model it cascades (every R-edge re-fires D onto a shared
                        // filler).  The transitive ∀R.C chase is handled by the
                        // existing __trans__ + reach_by_role + residue path (sound).
                        // The chain-unfolding above (M2 across R1) is the novel
                        // composition; the self-loop needs copy-on-conflict to bound.
                    }
                }
            }
        }
        // KM_QO_EDGE_COMPOSE: chain edge-composition indexes are populated by
        // `install_edge_compose` (called from the Ht classify path with the
        // side-data chains from `set_chains`).  The raw chain axioms are filtered
        // from the clause stream by the frontend, so detection from `clauses`
        // here would find nothing — the chain info MUST come through the side
        // channel.  See `install_edge_compose`.
        let mut chain_fwd: HashMap<R, Vec<(R, R)>> = HashMap::new();
        let mut chain_bwd: HashMap<R, Vec<(R, R)>> = HashMap::new();
        QoSat {
            clauses,
            label: Vec::new(),
            out_edges: Vec::new(),
            in_edges: Vec::new(),
            edge_seen: HashSet::new(),
            edge_seen_on: std::env::var_os("KM_HT_QO_EDGESET").is_some(),
            concept_node: HashMap::new(),
            pending: Vec::new(),
            pending_by_node: Vec::new(),
            node_unsat: HashSet::new(),
            lit_work: Vec::new(),
            edge_work: Vec::new(),
            edge_budget: u64::MAX,
            node_work: Vec::new(),
            guard_refire: Vec::new(),
            concept_trig,
            simple_impl,
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
            kpwrite: std::env::var_os("KM_HT_QO_KPWRITE").is_some(),
            inv_edges: HashSet::new(),
            inv_bridge_cid,
            kp_insufficient: false,
            kp_miss: 0,
            kp_check1: HashSet::new(),
            kp_checkn: Vec::new(),
            kp_insuff_nodes: HashSet::new(),
            kp_guard: std::rc::Rc::new(kp_guard_set),
            kp_guard_only: std::env::var_os("KM_HT_QO_KPGUARD").is_some(),
            rsucc: std::env::var_os("KM_RSUCC").is_some(),
            reach_by_role: std::rc::Rc::new(reach_by_role),
            reach_via_inv: std::rc::Rc::new(reach_via_inv),
            // KPWRITE's soundness needs separate filler nodes so `on_self`
            // distinguishes a real predecessor (sound write) from a shared filler
            // (must stay a check); enabling it implies `sat_mode`.
            sat_mode: std::env::var_os("KM_HT_QO_SAT").is_some()
                || std::env::var_os("KM_HT_QO_KPWRITE").is_some(),
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
            shiq: std::env::var_os("KM_HT_QO_SHIQ").is_some(),
            // KM_HT_QO_NOPOLLUTE (Konclude `isCriticalALLConceptDescriptorInsufficient`):
            // a critical-ALL ∀-write onto a shared filler is DEFERRED, not written.
            // The shared filler keeps only its base + range-forced (clean) label, so
            // it never accumulates the union of all predecessors' ∀-consequences and
            // the precompute converges (Konclude ~20 concepts/node vs KM's ~850). The
            // affected seeds are flagged insufficient and re-verified in the residue.
            no_pollute: std::env::var_os("KM_HT_QO_NOPOLLUTE").is_some(),
            psplit: std::env::var_os("KM_HT_QO_PSPLIT").is_some(),
            approx: std::env::var_os("KM_HT_QO_APPROX").is_some(),
            node_certain: None,
            nc_resolved: HashSet::new(),
            qo_parent: Vec::new(),
            split_mode: std::env::var_os("KM_HT_QO_SPLIT").is_some(),
            node_fil: Vec::new(),
            src_forall: HashMap::new(),
            split_filler: HashMap::new(),
            card_merge: std::env::var_os("KM_HT_QO_CARDMERGE").is_some(),
            merged_into: Vec::new(),
            node_seed: Vec::new(),
            seed_node: HashMap::new(),
            merge_budget: std::env::var("KM_HT_QO_MERGE_BUDGET")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(3_000_000usize),
            edgefast: std::env::var_os("KM_HT_QO_EDGEFAST").is_some(),
            prop_batch_on: std::env::var_os("KM_HT_QO_PROP_BATCH").is_some(),
            edge_buf: Vec::new(),
            to_fire_buf: Vec::new(),
            edgeprobe: std::env::var_os("KM_HT_QO_EDGEPROBE").is_some(),
            edgeprobe_iv: std::env::var("KM_HT_QO_EDGEPROBE")
                .ok()
                .and_then(|s| s.parse().ok())
                .filter(|&n| n > 0)
                .unwrap_or(2_000),
            sat_t0: None,
            last_hb: None,
            hb_interval: std::env::var("KM_HT_QO_HB")
                .ok()
                .and_then(|s| s.parse().ok())
                .filter(|&n: &f64| n > 0.0)
                .unwrap_or(2.0),
            chain_fwd,
            chain_bwd,
            edge_bailed: false,
        }
    }

    /// Seconds elapsed in the current `saturate_global` pass (0.0 before it starts).
    /// Only called from the `KM_HT_TRACE` heartbeats.
    fn sat_elapsed(&self) -> f64 {
        self.sat_t0
            .map(|t| t.elapsed().as_secs_f64())
            .unwrap_or(0.0)
    }

    /// KM_QO_EDGE_COMPOSE: install the role-chain edge-composition indexes from
    /// the side-data chains `R1∘R2⊑R` (incl. transitive `R∘R⊑R`) received via
    /// `Ht::set_chains`.  Faithful port of Konclude's role-automaton edge
    /// composition: a fresh `R1`-edge `(s,t)` joined with an `R2`-edge `(t,z)`
    /// creates a composed `R`-edge `(s,z)` (and dually for a fresh `R2`-edge).
    /// Bounded by actual edges (each unique edge added at most once), NOT the
    /// ∀-filler cross-product that cascaded under KM_QO_CHAIN_UNFOLD.  Gated by
    /// `KM_QO_EDGE_COMPOSE` (default OFF until corpus-validated).
    fn install_edge_compose(&mut self, chains: &[(R, R, R)]) {
        if !std::env::var_os("KM_QO_EDGE_COMPOSE").is_some() {
            return;
        }
        for &(r1, r2, hr) in chains {
            self.chain_fwd.entry(r1).or_default().push((r2, hr));
            self.chain_bwd.entry(r2).or_default().push((r1, hr));
        }
    }

    /// TIME-driven heartbeat (debug): print at most every `hb_interval` seconds,
    /// regardless of how fast pops advance — so a throughput collapse is visible
    /// (the pop-count-gated QODRAIN/QOEDGE lines go silent when the rate drops).
    /// `tag` names the active loop. No-op unless `edgeprobe` + `KM_HT_TRACE`.
    fn hb_check(&mut self, tag: &str) {
        if !self.edgeprobe {
            return;
        }
        let now = Instant::now();
        let due = match self.last_hb {
            Some(last) => now.duration_since(last).as_secs_f64() >= self.hb_interval,
            None => true,
        };
        if due {
            self.last_hb = Some(now);
            if std::env::var_os("KM_HT_TRACE").is_some() {
                eprintln!(
                    "QOHB {} el={:.1}s nodes={} lit_work={} edge_work={} node_work={} pending={} | apply={} kpw={} addlit={} frc={} match={} fprope={}",
                    tag, self.sat_elapsed(), self.label.len(), self.lit_work.len(),
                    self.edge_work.len(), self.node_work.len(), self.pending.len(),
                    DBG_APPLY.load(Ordering::Relaxed), DBG_KPW.load(Ordering::Relaxed),
                    DBG_ADDLIT.load(Ordering::Relaxed), DBG_FRC.load(Ordering::Relaxed),
                    DBG_MATCH.load(Ordering::Relaxed), DBG_FPROPE.load(Ordering::Relaxed),
                );
            }
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
        self.pending_by_node.clear();
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
        self.node_fil.clear();
        self.src_forall.clear();
        self.split_filler.clear();
        self.merged_into.clear();
        self.node_seed.clear();
        self.seed_node.clear();
        self.trail.clear();
        self.unsupported = false;
        self.open_disj = 0;
        self.nc_resolved.clear();
        self.edge_bailed = false;
    }

    fn new_node(&mut self) -> Node {
        let id = self.label.len();
        self.label.push(HashSet::new());
        self.out_edges.push(Vec::new());
        self.in_edges.push(Vec::new());
        self.node_range.push(0);
        self.is_filler.push(false);
        self.qo_parent.push(None);
        self.node_fil.push(None);
        self.merged_into.push(None);
        self.node_seed.push(Vec::new());
        self.pending_by_node.push(Vec::new());
        self.node_work.push(id);
        if self.tracing {
            self.trail.push(QoUndo::NodeNew);
        }
        id
    }

    /// Remove `pending[i]` while keeping the `pending_by_node` index consistent
    /// (P0). swap_remove moves the last entry into slot `i`; both the removed
    /// entry's node-list and (if a different entry moved) the moved entry's
    /// node-list are fixed up. Does NOT touch `open_disj` (the caller owns that,
    /// matching the prior inline `swap_remove` + decrement). Non-tracing only —
    /// the tracing residue DFS never builds `pending_by_node`.
    fn pending_remove(&mut self, i: usize) {
        let last = self.pending.len() - 1;
        let (n, _) = self.pending[i];
        if let Some(pos) = self.pending_by_node[n].iter().position(|&x| x == i) {
            self.pending_by_node[n].swap_remove(pos);
        }
        self.pending.swap_remove(i);
        if i != last {
            // the entry that was at `last` now sits at `i`: retarget its index.
            let (nm, _) = self.pending[i];
            if let Some(p) = self.pending_by_node[nm].iter().position(|&x| x == last) {
                self.pending_by_node[nm][p] = i;
            }
        }
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
        if self.edgeprobe {
            DBG_ADDLIT.fetch_add(1, Ordering::Relaxed);
        }
        if self.node_unsat.contains(&n) {
            return false;
        }
        // a merged-away (dead) node is inert: writes resolve to its survivor via
        // the caller's `find`, never to the evacuated node itself.
        if self.merged_into[n].is_some() {
            return false;
        }
        let comp = CLit {
            neg: !lit.neg,
            c: lit.c,
        };
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
            // KM_HT_QO_CARDMERGE: a FILLER node dying (e.g. a forced cardinality
            // merge produced an inconsistent successor — a clash that the merge's
            // union only triggers later, via a disjointness clause, not at union
            // time) means the ∃-sources relying on it cannot satisfy their
            // existential in the shared model. The shared pass has no unsat
            // back-propagation, so DEFER those sources: seed the node insufficient
            // and let the gate's reverse-reach mark every concept reaching it.
            // Sound (never reports the source unsat from the shared model) and
            // scoped to the new flag, so other paths are unchanged.
            if self.card_merge && self.is_filler[n] {
                self.kp_insuff_nodes.insert(n);
                self.qo_insufficient = true;
                self.kp_insufficient = true;
            }
            if self.tracing {
                self.trail.push(QoUndo::Unsat(n));
                return;
            }
            // P0: remove `n`'s parked disjunctions via the per-node index — O(deg(n))
            // instead of the O(|pending|) full scan (763k on 14817). The probe now
            // measures the actual per-node work removed.
            if self.edgeprobe {
                let pl = self.pending_by_node[n].len() as u64;
                DBG_KILLSCAN.fetch_add(pl, Ordering::Relaxed);
                DBG_KILLS.fetch_add(1, Ordering::Relaxed);
            }
            while let Some(&idx) = self.pending_by_node[n].last() {
                self.pending_remove(idx);
                self.open_disj = self.open_disj.saturating_sub(1);
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
            if self.tracing {
                self.trail.push(QoUndo::SatFiller(fil, r));
            }
            if self.split_mode {
                self.node_fil[n] = Some(fil);
            }
            if self.card_merge {
                self.node_seed[n] = vec![fil]; // base seed for content-merge keying
            }
            self.add_lit(n, fil);
            return n;
        }
        let cls = self.range_class.get(&r).copied().unwrap_or(0);
        if cls == 0 {
            let n = self.concept_node_of(fil);
            // The concept self-node doubles as the shared `∃r.fil` filler. Record
            // `fil` as its base so `split_mode` can redirect a `∀r` writer off it,
            // keeping the self-node (read for classification, G1) unpolluted.
            if self.split_mode && self.node_fil[n].is_none() {
                self.node_fil[n] = Some(fil);
            }
            return n;
        }
        if let Some(&n) = self.filler_node.get(&(fil, cls)) {
            return n;
        }
        let n = self.new_node();
        self.node_range[n] = cls;
        self.filler_node.insert((fil, cls), n);
        if self.split_mode {
            self.node_fil[n] = Some(fil);
        }
        if self.tracing {
            self.trail.push(QoUndo::Filler(fil, cls));
        }
        self.add_lit(n, fil);
        n
    }

    fn add_edge(&mut self, s: Node, r: R, t: Node) {
        if self.merged_into[s].is_some() || self.merged_into[t].is_some() {
            return; // never wire an edge to/from a dead (merged) node
        }
        if self.edge_seen_on {
            if !self.edge_seen.insert((s, r, t)) {
                return;
            }
        } else if self.out_edges[s]
            .iter()
            .any(|(rr, tt)| *rr == r && *tt == t)
        {
            return;
        }
        self.out_edges[s].push((r, t));
        self.in_edges[t].push((r, s));
        self.edge_work.push((s, r, t));
        if self.tracing {
            self.trail.push(QoUndo::Edge(s, r, t));
        }
    }

    /// Drop the edge `(s, r, t)` from both adjacency indexes (`split_mode`
    /// copy-on-conflict redirect only). The shared-node saturation is otherwise
    /// monotone (edges only grow); this is the single non-monotone operation, and
    /// it is sound because the redirect always re-adds `(s, r, m)` to a node `m`
    /// whose label is a superset of the relevant content of `t` (the base/shared
    /// filler that `t` was). No undo is recorded: `split_mode` runs only in the
    /// non-tracing global pass (the residue DFS keeps the old defer behaviour).
    fn remove_edge(&mut self, s: Node, r: R, t: Node) {
        if self.edge_seen_on {
            self.edge_seen.remove(&(s, r, t));
        }
        self.out_edges[s].retain(|&(rr, tt)| !(rr == r && tt == t));
        self.in_edges[t].retain(|&(rr, ss)| !(rr == r && ss == s));
    }

    /// Port #2 copy-on-conflict (`split_mode`). A forward `∀r.lit` write from
    /// source `anchor` over the edge `(anchor, r, n)` whose operand `lit` is not
    /// already forced on the shared filler `n`. Instead of polluting `n` (unsound
    /// across predecessors) or deferring (`qo_insufficient`, the over-defer),
    /// REDIRECT `anchor`'s `r`-edge onto a node keyed by `(base-fil, r, anchor's
    /// accumulated ∀r-operand set)`: Konclude's `copyDependingIndividualNode`. The
    /// keyed node carries `fil` + the operands, so the operand fires downstream
    /// (complete) without conflating predecessors (sound). Returns true iff the
    /// redirect was applied (the head is then discharged); false ⇒ caller keeps
    /// the old defer behaviour (the write was not a plain forward `∀r` from `X`).
    fn try_split_redirect(
        &mut self,
        cid: usize,
        anchor: Node,
        n: Node,
        head_t: Var,
        lit: CLit,
    ) -> bool {
        // The base ∃-filler concept that keys `n`; without it `n` is not a
        // shared filler we know how to split (e.g. a root/self seed) ⇒ defer.
        let fil = match self.node_fil[n] {
            Some(f) => f,
            None => return false,
        };
        // Recover the edge role: a body role atom `r(X, head_t)` whose target is
        // the head var and whose source is the clause anchor `X`, witnessed by a
        // real edge `(anchor, r, n)`. Only this plain forward shape is redirected;
        // backward (inverse) `∀` writes (head var = role SOURCE) fall through.
        let body = &self.clauses[cid].1;
        let mut role: Option<R> = None;
        for a in body.iter() {
            if let Atom::Role { r, s, t } = *a {
                if s == X
                    && t == head_t
                    && self.out_edges[anchor]
                        .iter()
                        .any(|&(rr, tt)| rr == r && tt == n)
                {
                    role = Some(r);
                    break;
                }
            }
        }
        let r = match role {
            Some(r) => r,
            None => return false,
        };
        // Accumulate `lit` into the source's ∀r-operand set; the sorted set is the
        // content key. A growing set re-keys to a fresh (larger) node, leaving the
        // smaller node for predecessors that imposed only the smaller set.
        let ops = self.src_forall.entry((anchor, r)).or_default();
        ops.insert(lit);
        let mut key_ops: Vec<CLit> = ops.iter().copied().collect();
        key_ops.sort();
        let m = match self.split_filler.get(&(fil, r, key_ops.clone())) {
            Some(&m) => m,
            None => {
                let m = self.new_node();
                self.is_filler[m] = true;
                self.node_fil[m] = Some(fil);
                self.add_lit(m, fil);
                for &op in &key_ops {
                    self.add_lit(m, op);
                }
                self.split_filler.insert((fil, r, key_ops), m);
                m
            }
        };
        if m == n {
            return false; // degenerate (would re-add the same edge); defer.
        }
        self.remove_edge(anchor, r, n);
        self.add_edge(anchor, r, m);
        DBG_SPLIT.fetch_add(1, Ordering::Relaxed);
        true
    }

    /// KM_HT_QO_PSPLIT copy-on-conflict for the NF4 forward broadcast. `src` is
    /// about to impose operand `e` on its shared r-successor `t` (via
    /// `R(src,t) ⊓ lit(src) → e(t)`). Instead of writing `e` into the shared `t`
    /// (conflation), redirect `src`'s r-edge to a content-keyed successor `m` keyed
    /// by `(filler-concept, r, src's accumulated operand set)` — the same key as
    /// `try_split_redirect`, so the apply_head and fprop paths share split nodes.
    /// `e` lands on `m` (seeded with the operand set). Returns true if redirected.
    fn fprop_split_redirect(&mut self, src: Node, r: R, t: Node, e: CLit) -> bool {
        let fil = match self.node_fil[t] {
            Some(f) => f,
            None => return false,
        };
        // src must actually have the shared r-edge to `t` to redirect it.
        if !self.out_edges[src]
            .iter()
            .any(|&(rr, tt)| rr == r && tt == t)
        {
            return false;
        }
        let ops = self.src_forall.entry((src, r)).or_default();
        ops.insert(e);
        let mut key_ops: Vec<CLit> = ops.iter().copied().collect();
        key_ops.sort();
        let m = match self.split_filler.get(&(fil, r, key_ops.clone())) {
            Some(&m) => m,
            None => {
                let m = self.new_node();
                self.is_filler[m] = true;
                self.node_fil[m] = Some(fil);
                self.add_lit(m, fil);
                for &op in &key_ops {
                    self.add_lit(m, op);
                }
                self.split_filler.insert((fil, r, key_ops), m);
                m
            }
        };
        if m == t {
            return false;
        }
        self.remove_edge(src, r, t);
        self.add_edge(src, r, m);
        DBG_SPLIT.fetch_add(1, Ordering::Relaxed);
        true
    }

    /// Content-keyed merged/split filler (KM_HT_QO_CARDMERGE): the node for
    /// `(role, sorted seed-set)`, created + seeded on first use. A cardinality
    /// merge redirects the constrained predecessor's r-edges onto it; predecessors
    /// forcing the same seed-set share ONE node (the content sharing that bounds
    /// the node count). Seeding a contradictory set (e.g. `C` and `¬C`) lets the
    /// node clash through the normal disjointness machinery (then `kill_node`'s
    /// filler-death hook defers its ∃-sources).
    fn seed_filler(&mut self, r: R, seed: &[CLit]) -> Node {
        let key = (r, seed.to_vec());
        if let Some(&n) = self.seed_node.get(&key) {
            return n;
        }
        let n = self.new_node();
        self.is_filler[n] = true;
        self.node_seed[n] = seed.to_vec();
        if let Some(&f) = seed.first() {
            self.node_fil[n] = Some(f);
        }
        for &l in seed {
            self.add_lit(n, l);
        }
        self.seed_node.insert(key, n);
        n
    }

    /// The cardinality role of a forced `Eq(sv, tv)` head: a body role atom
    /// `r(X, sv)` and `r(X, tv)` for the SAME `r`. `None` (defer) if the head is
    /// not this plain functional/at-most shape.
    fn eq_merge_role(&self, cid: usize, sv: Var, tv: Var) -> Option<R> {
        let body = &self.clauses[cid].1;
        let mut rs: Option<R> = None;
        let mut rt: Option<R> = None;
        for a in body {
            if let Atom::Role { r, s, t } = *a {
                if s == X && t == sv {
                    rs = Some(r);
                }
                if s == X && t == tv {
                    rt = Some(r);
                }
            }
        }
        match (rs, rt) {
            (Some(a), Some(b)) if a == b => Some(a),
            _ => None,
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
                if self.lit_work.is_empty()
                    && self.node_work.is_empty()
                    && self.edge_work.is_empty()
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

    /// P2.1b optimized subset blocking (Konclude `isLabelConceptOptimizedBlocking`).
    /// `n` (a non-shared successor) is BLOCKED if some proper ancestor `a` along the
    /// `qo_parent` chain has `label[n] ⊆ label[a]` (B1). A blocked node's
    /// existentials are not expanded — the ancestor already witnesses the same (or a
    /// larger) successor pattern, so a fresh subtree is redundant. This bounds the
    /// per-source expansion that otherwise blows up (27 GB on 7914 without it).
    /// (B2 — the parent must carry the blocker's `∀r`-operands — is required for
    /// completeness under inverse roles and is added in the next increment; with
    /// `KM_HT_QO_INVCOMPOSE` the inverse is composed to forward writes, which limits
    /// the B1-only exposure.)
    fn qo_blocked(&self, n: Node) -> bool {
        let ln = &self.label[n];
        let mut a = self.qo_parent[n];
        while let Some(p) = a {
            if ln.len() <= self.label[p].len() && ln.is_subset(&self.label[p]) {
                return true;
            }
            a = self.qo_parent[p];
        }
        false
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
        let cap = named_concepts
            .len()
            .saturating_add(500_000)
            .max(QO_NODE_CAP);
        let trace = std::env::var_os("KM_HT_TRACE").is_some();
        self.sat_t0 = Some(Instant::now());
        self.last_hb = None;
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
                    "QOSAT el={:.1}s guard={} nodes={} lit_work={} edge_work={} node_work={} pending={} open_disj={}",
                    self.sat_elapsed(), guard, self.label.len(), self.lit_work.len(),
                    self.edge_work.len(), self.node_work.len(), self.pending.len(), self.open_disj
                );
            }
            if guard > 50_000_000 || self.label.len() > cap {
                if trace {
                    // Konclude-comparable precompute outcome. Konclude's non-branching
                    // precompute records cardinality bounds and converges (e.g. 14817:
                    // "Finished precomputing in 3296 ms"); KM's shared-model precompute
                    // diverges here when the frontend's `⊤→Q∨NQ` cardinality-recognition
                    // excluded-middle parks on every node (pending) and the edge closure
                    // cascades (edge_work). Report the blocker, not just "unsupported".
                    eprintln!(
                        "QO PRECOMPUTE DID-NOT-CONVERGE el={:.0}ms nodes={} pending={} edge_work={} stored_edges~{} (cardinality-recognition / disjunction parking)",
                        self.sat_elapsed() * 1000.0, self.label.len(), self.pending.len(),
                        self.edge_work.len(),
                        (0..self.label.len()).map(|i| self.out_edges[i].len()).sum::<usize>(),
                    );
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
                if self.lit_work.is_empty()
                    && self.node_work.is_empty()
                    && self.edge_work.is_empty()
                {
                    break;
                }
            }
        }
        // NB: r-Succ deliberately does NOT trigger kp_finalize here. In the global
        // shared model the reach post-pass flags every filler whose predecessor
        // carries a `__trans`/`__chain` concept across a part_of/has_part edge — a
        // pattern so pervasive in UBERON-style ontologies (7914: 213880 fillers,
        // residue 327→7090) that the residue-complete verify explodes to a timeout.
        // The sound per-predecessor reconstruction the giant path needs is the
        // non-shared-filler (copy-on-conflict) infrastructure, not a flag-to-residue
        // pass. r-Succ stays on the per-concept QOPC path (`qo_classify_perconcept`),
        // where the model is small and the flag is precise.
        // Konclude-comparable precompute outcome: the worklists drained and every
        // parked disjunction was harvested/resolved — the analogue of Konclude's
        // "Finished precomputing in N ms". A converging precompute here is the
        // precondition for the cheap per-concept satisfiable-test classification
        // that follows (Konclude does ~one satisfiable test per concept, 0
        // calculated subsumption tests, on a converged precompute).
        if trace {
            eprintln!(
                "QO PRECOMPUTE converged el={:.0}ms nodes={} stored_edges~{} pending={}",
                self.sat_elapsed() * 1000.0,
                self.label.len(),
                (0..self.label.len())
                    .map(|i| self.out_edges[i].len())
                    .sum::<usize>(),
                self.pending.len(),
            );
        }
        if self.kpset || self.fcheck {
            self.kp_finalize();
        }
        self.finish_global()
    }

    /// Drain all worklists once: literal-triggered clauses, new-node globals,
    /// edge-triggered role clauses, and harvest obligations.
    fn drain_work(&mut self) {
        // KM_HT_QO_PROP_BATCH: collect ordinary NF4 backward-link conclusions by
        // target node for this drain wave.  Large role hierarchies can present the
        // same `(node, literal)` through thousands of edges; calling `add_lit` for
        // every presentation dominates the precompute even though all but the
        // first are no-ops.  Delaying these monotone writes until the end of the
        // wave and applying their union once preserves the fixpoint.  It is enabled
        // only with complete role re-firing, which guarantees clauses whose guard
        // arrives after an edge are re-anchored on that edge.
        let prop_batch_on = self.complete_roles && self.prop_batch_on && !self.tracing;
        let mut prop_batch: HashMap<Node, HashSet<CLit>> = HashMap::new();
        while let Some((n, lit)) = self.lit_work.pop() {
            let d = QO_DRAIN.fetch_add(1, Ordering::Relaxed);
            if self.edgeprobe && d % 5_000 == 0 {
                self.hb_check("lit");
            }
            if d > 0 && d % 2_000_000 == 0 && std::env::var_os("KM_HT_TRACE").is_some() {
                eprintln!(
                    "QODRAIN el={:.1}s steps={} nodes={} lit_work={} edge_work={} node_work={} pending={} | harvest_disj={} noop={}",
                    self.sat_elapsed(), d, self.label.len(), self.lit_work.len(), self.edge_work.len(),
                    self.node_work.len(), self.pending.len(),
                    DBG_HARVEST_DISJ.load(Ordering::Relaxed),
                    DBG_HARVEST_NOOP.load(Ordering::Relaxed)
                );
                // KM_HT_QO_EDGESTATS: edge-concentration probe. Total stored edges,
                // distinct filler targets, and the max in-degree — to confirm whether
                // the edge_work growth is per-node materialization into a few shared
                // fillers (ELK backward-links would collapse it) vs a genuinely wide
                // edge set.
                if std::env::var_os("KM_HT_QO_EDGESTATS").is_some() {
                    let nn = self.label.len();
                    let total: usize = (0..nn).map(|i| self.out_edges[i].len()).sum();
                    let nfill = (0..nn).filter(|&i| self.is_filler[i]).count();
                    let mut maxin = 0usize;
                    let mut fill_in: usize = 0;
                    for i in 0..nn {
                        let ind = self.in_edges[i].len();
                        if ind > maxin {
                            maxin = ind;
                        }
                        if self.is_filler[i] {
                            fill_in += ind;
                        }
                    }
                    eprintln!(
                        "QOEDGESTATS stored_edges={} fillers={} max_in_degree={} edges_into_fillers={}",
                        total, nfill, maxin, fill_in
                    );
                }
            }
            if self.node_unsat.contains(&n) || self.merged_into[n].is_some() {
                continue;
            }
            // Fire the concept clauses triggered by `lit`. The trigger lists are
            // immutable after `new()`, but a per-pop `.clone()` of a hot lit's
            // list (some concepts trigger tens of thousands of clauses) was a
            // multi-GB allocation churn at the 2M-pop scale. Take the list out of
            // the map (O(1) move, no element copy), iterate, then restore it —
            // `fire_concept_clause` never touches `concept_trig`, so this is safe.
            // elc NF1 fast path (KM_HT_QO_FASTIMPL): `C(x)→D(x)` clauses indexed as
            // C→[D…] apply directly with add_lit (apply_head of a single concept head
            // IS add_lit), skipping the substitution alloc + apply_head machinery.
            if !self.simple_impl.is_empty() {
                if let Some(heads) = self.simple_impl.remove(&lit) {
                    for &e in &heads {
                        self.add_lit(n, e);
                        if self.node_unsat.contains(&n) {
                            break;
                        }
                    }
                    self.simple_impl.insert(lit, heads);
                }
            }
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
            // KM_HT_QO_NOPOLLUTE: a shared ∃-filler conflates every predecessor's
            // successor. Broadcasting its NF4 backward link `R(x,n) ⊓ lit(n) → e(x)`
            // to all (here 60897) R-predecessors is the cascade driver (and, on a
            // shared filler, the over-derivation Konclude defers): one predecessor's
            // ∀-forced `lit` would otherwise impose `e` on ALL predecessors. Skip the
            // broadcast and flag the filler insufficient ⇒ the residue re-verifies the
            // affected seeds on the complete tableau. Keeps the precompute bounded.
            let filler_defer = self.no_pollute && self.sat_mode && self.is_filler[n];
            if filler_defer && self.prop_rule.contains_key(&lit) {
                self.kp_insuff_nodes.insert(n);
                self.qo_insufficient = true;
            }
            if let Some(rules) = (!filler_defer)
                .then(|| ())
                .and_then(|_| self.prop_rule.remove(&lit))
            {
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
                        if prop_batch_on && !via_inv {
                            if !self.label[x].contains(&e) {
                                prop_batch.entry(x).or_default().insert(e);
                            }
                        } else {
                            self.kp_write(x, e, via_inv);
                        }
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
            if self.fprop_on && !filler_defer {
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
                            // KM_HT_QO_PSPLIT: if `e` would pollute a shared filler,
                            // redirect `n`'s edge to a content-keyed successor (the
                            // operand lands there). Konclude copy-on-conflict.
                            if self.psplit
                                && self.sat_mode
                                && self.is_filler[t]
                                && self.node_fil[t].is_some()
                                && !self.label[t].contains(&e)
                                && self.fprop_split_redirect(n, r, t, e)
                            {
                                continue;
                            }
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
            if self.edgeprobe && e % 2_000 == 0 {
                self.hb_check("node");
            }
            if e > 0 && e % 200_000 == 0 && std::env::var_os("KM_HT_TRACE").is_some() {
                eprintln!(
                    "QONODE el={:.1}s pops={} global_per_node={} edge_work={} node_work={}",
                    self.sat_elapsed(),
                    e,
                    self.global.len(),
                    self.edge_work.len(),
                    self.node_work.len()
                );
            }
            if self.node_unsat.contains(&n) || self.merged_into[n].is_some() {
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
            // Edge-pop budget: a per-concept model whose ∀-pollution cascade explodes
            // bails here (node_cap cannot catch it — nodes stay fixed while edges blow
            // up). u64::MAX for the unbounded global/complete passes.
            if self.edge_budget != u64::MAX {
                if self.edge_budget == 0 {
                    // A per-concept edge budget was set (KM_QO_EC_BUDGET under
                    // KM_QO_EDGE_COMPOSE, or KM_TRANS_CHAIN_COMPOSE).  Bail to
                    // residue (insufficient) instead of deferring the whole
                    // classification (unsupported) — the Ht complete-tableau
                    // (with blocking) derives the missing subsumers there.
                    self.edge_bailed = true;
                    self.qo_insufficient = true;
                    return;
                }
                self.edge_budget -= 1;
            }
            if self.edgeprobe && e % 2_000 == 0 {
                self.hb_check("edge");
            }
            if self.edgeprobe {
                if e > 0 && e % self.edgeprobe_iv == 0 && std::env::var_os("KM_HT_TRACE").is_some()
                {
                    eprintln!(
                        "QOEDGE el={:.1}s pops={} edge_work={} lit_work={} nodes={} | frc={} match={} apply={} fprope={} kpw={} addlit={} trigscan={} maxlabel={}",
                        self.sat_elapsed(), e, self.edge_work.len(), self.lit_work.len(), self.label.len(),
                        DBG_FRC.load(Ordering::Relaxed), DBG_MATCH.load(Ordering::Relaxed),
                        DBG_APPLY.load(Ordering::Relaxed), DBG_FPROPE.load(Ordering::Relaxed),
                        DBG_KPW.load(Ordering::Relaxed), DBG_ADDLIT.load(Ordering::Relaxed),
                        DBG_TRIGSCAN.load(Ordering::Relaxed), DBG_MAXLABEL.load(Ordering::Relaxed),
                    );
                }
            } else if e > 0 && e % 200_000 == 0 && std::env::var_os("KM_HT_TRACE").is_some() {
                eprintln!(
                    "QOEDGE pops={} edge_work={} lit_work={} node_work={} nodes={}",
                    e,
                    self.edge_work.len(),
                    self.lit_work.len(),
                    self.node_work.len(),
                    self.label.len()
                );
            }
            // a merge evacuated one endpoint: this is a stale edge, its work was
            // migrated onto the survivor's fresh edges.
            if self.merged_into[s].is_some() || self.merged_into[t].is_some() {
                continue;
            }
            // Slow-pop probe: capture this edge pop's start time + the prop/fprop
            // set sizes it is about to iterate, so a single pathological pop (a
            // giant prop set / a heavy fire_role_clause fan-out) is pinpointed.
            // A big prop set is announced BEFORE the loop (so it shows even if that
            // loop is the one that hangs); the end-of-pop timer reports the rest.
            let dbg_pop_t0 = if self.edgeprobe {
                Some(Instant::now())
            } else {
                None
            };
            let dbg_propn = if self.edgeprobe {
                self.prop.get(&(r, t)).map(|v| v.len()).unwrap_or(0)
            } else {
                0
            };
            let dbg_fpropn = if self.edgeprobe && self.fprop_on {
                self.fprop.get(&(r, s)).map(|v| v.len()).unwrap_or(0)
            } else {
                0
            };
            if self.edgeprobe
                && (dbg_propn > 50_000 || dbg_fpropn > 50_000)
                && std::env::var_os("KM_HT_TRACE").is_some()
            {
                eprintln!(
                    "QOSLOW el={:.1}s BIG set at pop: s={} r={} t={} propset={} fpropset={} label[s]={} label[t]={}",
                    self.sat_elapsed(), s, r, t, dbg_propn, dbg_fpropn,
                    self.label[s].len(), self.label[t].len()
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
            if self.edgefast {
                // elc clone-free port: copy the conclusions into the reusable
                // `edge_buf` (capacity retained across pops) instead of a fresh
                // per-edge `Vec`. Identical elements, identical order.
                let via_inv = self.kpset && self.inv_edges.contains(&(s, r, t));
                let mut buf = std::mem::take(&mut self.edge_buf);
                buf.clear();
                if let Some(es) = self.prop.get(&(r, t)) {
                    buf.extend_from_slice(es);
                }
                if prop_batch_on && !via_inv {
                    let target = prop_batch.entry(s).or_default();
                    for &lit in &buf {
                        if !self.label[s].contains(&lit) {
                            target.insert(lit);
                        }
                    }
                } else {
                    for &e in &buf {
                        self.kp_write(s, e, via_inv);
                        if self.unsupported {
                            self.edge_buf = buf;
                            return;
                        }
                    }
                }
                self.edge_buf = buf;
            } else if let Some(es) = self.prop.get(&(r, t)) {
                let es: Vec<CLit> = es.clone();
                // KPSet: if this fresh edge is an inverse back-edge, the inherited
                // backward links are containment checks at `s`, never writes.
                let via_inv = self.kpset && self.inv_edges.contains(&(s, r, t));
                if prop_batch_on && !via_inv {
                    let target = prop_batch.entry(s).or_default();
                    for lit in es {
                        if !self.label[s].contains(&lit) {
                            target.insert(lit);
                        }
                    }
                } else {
                    for e in es {
                        self.kp_write(s, e, via_inv);
                        if self.unsupported {
                            return;
                        }
                    }
                }
            }
            // Forward mirror: the fresh `r`-edge `(s,t)` inherits everything `s`'s
            // label has already broadcast forward for role `r` — the head-on-target
            // NF4 consequences land on the new successor `t`. O(consequences), no
            // clause matching. (The guard-arrives-after-edge direction is the
            // `fprop_rule` push in the lit loop.)
            if self.fprop_on {
                if self.edgefast {
                    let mut buf = std::mem::take(&mut self.edge_buf);
                    buf.clear();
                    if let Some(es) = self.fprop.get(&(r, s)) {
                        buf.extend_from_slice(es);
                    }
                    for &e in &buf {
                        self.fprop_emit(t, e);
                        if self.unsupported {
                            self.edge_buf = buf;
                            return;
                        }
                    }
                    self.edge_buf = buf;
                } else if let Some(es) = self.fprop.get(&(r, s)) {
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
            // elc clone-free port: reuse `to_fire_buf` across edge pops instead of
            // a fresh `Vec` per edge. Identical contents, identical order.
            let mut to_fire: Vec<usize> = if self.edgefast {
                std::mem::take(&mut self.to_fire_buf)
            } else {
                Vec::new()
            };
            to_fire.clear();
            if let Some(cids) = self.role_noguard.get(&r) {
                to_fire.extend_from_slice(cids);
            }
            if !self.role_src_trig.is_empty() {
                if self.edgeprobe {
                    let ls = self.label[s].len() as u64;
                    DBG_TRIGSCAN.fetch_add(ls, Ordering::Relaxed);
                    DBG_MAXLABEL.fetch_max(ls, Ordering::Relaxed);
                }
                for &lit in &self.label[s] {
                    if let Some(cids) = self.role_src_trig.get(&(r, lit)) {
                        to_fire.extend_from_slice(cids);
                    }
                }
            }
            if !self.role_tgt_trig.is_empty() {
                if self.edgeprobe {
                    let lt = self.label[t].len() as u64;
                    DBG_TRIGSCAN.fetch_add(lt, Ordering::Relaxed);
                    DBG_MAXLABEL.fetch_max(lt, Ordering::Relaxed);
                }
                for &lit in &self.label[t] {
                    if let Some(cids) = self.role_tgt_trig.get(&(r, lit)) {
                        to_fire.extend_from_slice(cids);
                    }
                }
            }
            let dbg_tofire = to_fire.len();
            for &cid in &to_fire {
                self.fire_role_clause(cid, s, r, t);
                if self.unsupported {
                    if self.edgefast {
                        self.to_fire_buf = to_fire;
                    }
                    return;
                }
            }
            if self.edgefast {
                self.to_fire_buf = to_fire;
            }
            // KM_QO_EDGE_COMPOSE: role-automaton edge composition (Konclude's
            // applyAutomatTransactions).  A fresh R-edge `(s,t)` triggers, for
            // each chain R1∘R2⊑R whose FIRST role R1==r, a join with every
            // existing R2-edge `(t,z)` → composed R-edge `(s,z)`; and dually,
            // for each chain whose SECOND role R2==r, a join with every
            // existing R1-edge `(x,s)` (i.e. `s`'s R1-predecessors) → composed
            // R-edge `(x,t)`.  `add_edge` dedups + pushes fresh edges onto
            // `edge_work`, so the composition is monotone, bounded by actual
            // reachable edges (not the ∀-filler cross-product).  Gather first
            // (immutable borrows of `out_edges`/`in_edges` + the index), then
            // `add_edge` (mutable).
            if !self.chain_fwd.is_empty() {
                let mut new_edges: Vec<(Node, R, Node)> = Vec::new();
                // forward: fresh R1-edge (s,t), chain R1∘R2⊑R ⇒ R2-edge (t,z) → R-edge (s,z)
                if let Some(chains) = self.chain_fwd.get(&r) {
                    for &(r2, hr) in chains {
                        for &(rr, z) in &self.out_edges[t] {
                            if rr == r2 && z != t {
                                new_edges.push((s, hr, z));
                            }
                        }
                    }
                }
                // backward: fresh R2-edge (s,t), chain R1∘R2⊑R ⇒ R1-edge (x,s) → R-edge (x,t)
                if let Some(chains) = self.chain_bwd.get(&r) {
                    for &(r1, hr) in chains {
                        for &(rr, x) in &self.in_edges[s] {
                            if rr == r1 && x != s {
                                new_edges.push((x, hr, t));
                            }
                        }
                    }
                }
                for (ss, rr, tt) in new_edges {
                    if self.unsupported {
                        break;
                    }
                    self.add_edge(ss, rr, tt);
                }
            }
            // End-of-pop slow timer: a single edge pop should be sub-microsecond; if
            // it took a meaningful slice of wall time, report the breakdown so the
            // throughput sink is attributed to prop-inheritance vs role-clause fan-out.
            if let Some(t0) = dbg_pop_t0 {
                let el = t0.elapsed().as_secs_f64();
                if el > 0.25 && std::env::var_os("KM_HT_TRACE").is_some() {
                    eprintln!(
                        "QOSLOW el={:.1}s edge pop took {:.2}s: s={} r={} t={} | propset={} fpropset={} to_fire={} label[s]={} label[t]={}",
                        self.sat_elapsed(), el, s, r, t, dbg_propn, dbg_fpropn,
                        dbg_tofire, self.label[s].len(), self.label[t].len()
                    );
                }
            }
        }
        if prop_batch_on && !prop_batch.is_empty() {
            // Stable node/literal order keeps diagnostic runs reproducible even
            // though the union itself is hash-based.
            let mut nodes: Vec<(Node, HashSet<CLit>)> = prop_batch.into_iter().collect();
            nodes.sort_unstable_by_key(|(n, _)| *n);
            for (n, lits) in nodes {
                let mut lits: Vec<CLit> = lits.into_iter().collect();
                lits.sort_unstable_by_key(|l| (l.c, l.neg));
                for lit in lits {
                    self.add_lit(n, lit);
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
            if self.edgeprobe {
                let g = DBG_GRFIRE.fetch_add(1, Ordering::Relaxed);
                if g % 5_000 == 0 {
                    self.hb_check("grfire");
                }
                if g > 0 && g % 200_000 == 0 && std::env::var_os("KM_HT_TRACE").is_some() {
                    eprintln!(
                        "QOGRFIRE el={:.1}s pops={} guard_refire={} lit_work={} edge_work={} | frc={} match={} apply={} fprope={} kpw={} addlit={}",
                        self.sat_elapsed(), g, self.guard_refire.len(), self.lit_work.len(), self.edge_work.len(),
                        DBG_FRC.load(Ordering::Relaxed), DBG_MATCH.load(Ordering::Relaxed),
                        DBG_APPLY.load(Ordering::Relaxed), DBG_FPROPE.load(Ordering::Relaxed),
                        DBG_KPW.load(Ordering::Relaxed), DBG_ADDLIT.load(Ordering::Relaxed),
                    );
                }
            }
            if self.node_unsat.contains(&n) || self.merged_into[n].is_some() {
                continue;
            }
            // Re-read the edge-list length each iteration: a cardinality merge /
            // ∀-split fired here can `remove_edge` an incident edge of `n`, shrinking
            // the list, so a cached length would index out of bounds. Reading
            // `out_edges[n][i]` each step fires only CURRENT edges (never a redirected
            // -away stale edge); any not-yet-fired edge is still covered by `edge_work`.
            let mut i = 0;
            while i < self.out_edges[n].len() {
                let (r, t) = self.out_edges[n][i];
                self.fire_role_clause(cid, n, r, t);
                if self.unsupported {
                    return;
                }
                i += 1;
            }
            let mut j = 0;
            while j < self.in_edges[n].len() {
                let (r, s) = self.in_edges[n][j];
                self.fire_role_clause(cid, s, r, n);
                if self.unsupported {
                    return;
                }
                j += 1;
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
        if self.edgeprobe && std::env::var_os("KM_HT_TRACE").is_some() {
            eprintln!(
                "QOPHASE harvest_all START el={:.1}s over {} parked disjunctions",
                self.sat_elapsed(),
                parked.len()
            );
        }
        for (i, (n, cid)) in parked.iter().enumerate() {
            if self.edgeprobe && i % 50_000 == 0 {
                self.hb_check("harvest");
            }
            if self.node_unsat.contains(n) {
                continue;
            }
            self.harvest_disj(*n, *cid);
            if self.unsupported {
                return;
            }
        }
        if self.edgeprobe && std::env::var_os("KM_HT_TRACE").is_some() {
            eprintln!(
                "QOPHASE harvest_all DONE el={:.1}s harvest_disj={} noop={}",
                self.sat_elapsed(),
                DBG_HARVEST_DISJ.load(Ordering::Relaxed),
                DBG_HARVEST_NOOP.load(Ordering::Relaxed)
            );
        }
    }

    /// For parked disjunction `cid` at `n`: intersect the positive labels of
    /// the dedicated nodes of all live disjuncts and add the intersection to
    /// `n`. The negative labels are intersected too (common negated
    /// consequences). Sound because the disjunction is still parked: whatever
    /// disjunct is eventually chosen, all of them carry the common label.
    fn harvest_disj(&mut self, n: Node, cid: usize) {
        DBG_HARVEST_DISJ.fetch_add(1, Ordering::Relaxed);
        let before = self.label[n].len();
        self.harvest_disj_inner(n, cid);
        if self.label[n].len() == before {
            DBG_HARVEST_NOOP.fetch_add(1, Ordering::Relaxed);
        }
    }

    fn harvest_disj_inner(&mut self, n: Node, cid: usize) {
        let head = &self.clauses[cid].0.head;
        // collect live disjuncts (Concept only; Exists/Role park at apply_head
        // is satisfied-by-routing, so a parked disj is all Concept).
        let mut disj_nodes: Vec<(Node, CLit)> = Vec::new();
        for h in head {
            if let Atom::Concept { lit, t: _ } = h {
                if self.label[n].contains(lit) {
                    return; // satisfied — no longer parked
                }
                let comp = CLit {
                    neg: !lit.neg,
                    c: lit.c,
                };
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
                && !self.label[n].contains(&CLit {
                    neg: !lit.neg,
                    c: lit.c,
                })
            {
                self.add_lit(n, lit);
            }
        }
    }

    /// Re-evaluate ALL parked disjunctions (global pass at fixpoint).
    fn eval_all_parked(&mut self) {
        let pend = self.pending.clone();
        if self.edgeprobe && std::env::var_os("KM_HT_TRACE").is_some() {
            eprintln!(
                "QOPHASE eval_all_parked START el={:.1}s over {} parked",
                self.sat_elapsed(),
                pend.len()
            );
        }
        for (i, (n, _cid)) in pend.iter().enumerate() {
            if self.edgeprobe && i % 50_000 == 0 {
                self.hb_check("eval_parked");
            }
            self.eval_parked_at(*n);
        }
        if self.edgeprobe && std::env::var_os("KM_HT_TRACE").is_some() {
            eprintln!("QOPHASE eval_all_parked DONE el={:.1}s", self.sat_elapsed());
        }
    }

    /// Konclude pseudo-model build (CSatisfiableTaskClassificationMessageAnalyser
    /// .cpp:1832): a bounded (depth ≤ MAX_PM_DEPTH, ≤ MAX_PM_NODES) tree of model
    /// nodes from THIS concept's forward saturation (call after `saturate`). The
    /// forward labels are deterministic; the parked-disjunction heads are the
    /// non-deterministic possible labels. Each role records its successor count
    /// (`upperAtLeast`/`lowerAtMost`) and links the first successor's child node.
    /// Over-bound successors mark `valid_roles=false` (skipped by the prune).
    fn build_pmodel(&self) -> PModel {
        let mut pm = PModel {
            nodes: vec![PmNode::default()],
        };
        let mut map: HashMap<Node, usize> = HashMap::new();
        map.insert(0, 0);
        let mut queue: Vec<(Node, u32)> = vec![(0, 0)];
        let mut head = 0usize;
        while head < queue.len() {
            let (n, depth) = queue[head];
            head += 1;
            let pid = map[&n];
            for lit in self.label[n].iter() {
                if !lit.neg {
                    pm.nodes[pid].concepts.insert(lit.c, true); // deterministic
                }
            }
            // non-deterministic possible labels: parked-disjunction heads at `n`.
            for &(anchor, cid) in self.pending.iter() {
                if anchor == n {
                    for atom in self.clauses[cid].0.head.iter() {
                        if let Atom::Concept { lit, .. } = atom {
                            if !lit.neg {
                                pm.nodes[pid].concepts.entry(lit.c).or_insert(false);
                            }
                        }
                    }
                }
            }
            if depth >= MAX_PM_DEPTH {
                if !self.out_edges[n].is_empty() {
                    pm.nodes[pid].valid_roles = false; // successors not modelled
                }
                continue;
            }
            let mut by_role: std::collections::BTreeMap<R, Vec<Node>> =
                std::collections::BTreeMap::new();
            for &(r, t) in self.out_edges[n].iter() {
                by_role.entry(r).or_default().push(t);
            }
            for (r, succs) in by_role {
                let child = succs[0];
                let cidx = if let Some(&id) = map.get(&child) {
                    id
                } else if pm.nodes.len() < MAX_PM_NODES {
                    let id = pm.nodes.len();
                    pm.nodes.push(PmNode::default());
                    map.insert(child, id);
                    queue.push((child, depth + 1));
                    id
                } else {
                    pm.nodes[pid].valid_roles = false; // over node bound
                    continue;
                };
                pm.nodes[pid].roles.insert(
                    r,
                    PmRole {
                        det: true,
                        lower_at_least: 0,
                        upper_at_least: succs.len() as i64,
                        upper_at_most: i64::MAX,
                        lower_at_most: succs.len() as i64,
                        succ_model: cidx as i64,
                    },
                );
            }
        }
        pm
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
            edge_bailed: self.edge_bailed,
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
                    if self.edge_seen_on {
                        self.edge_seen.remove(&(s, r, t));
                    }
                    if let Some(out) = self.out_edges.get_mut(s) {
                        out.retain(|(rr, tt)| !(*rr == r && *tt == t));
                    }
                    if let Some(inc) = self.in_edges.get_mut(t) {
                        inc.retain(|(rr, ss)| !(*rr == r && *ss == s));
                    }
                }
                QoUndo::NodeNew => {
                    // Must pop EVERY parallel array `new_node` pushes, or the node
                    // arrays desync after a branch rollback (a later `new_node`
                    // reuses an id whose `merged_into`/`node_fil`/… slot is stale).
                    self.label.pop();
                    self.out_edges.pop();
                    self.in_edges.pop();
                    self.node_range.pop();
                    self.qo_parent.pop();
                    self.is_filler.pop();
                    self.node_fil.pop();
                    self.merged_into.pop();
                    self.node_seed.pop();
                    self.pending_by_node.pop();
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
                QoUndo::SatFiller(fil, r) => {
                    self.sat_filler.remove(&(fil, r));
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
                    let comp = CLit {
                        neg: !lit.neg,
                        c: lit.c,
                    };
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
                    let comp = CLit {
                        neg: !lit.neg,
                        c: lit.c,
                    };
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
                    let comp = CLit {
                        neg: !lit.neg,
                        c: lit.c,
                    };
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
            eprintln!(
                "KM_HT [qo-residue] anchor={} extra={:?} -> r={} unsup={} tainted={} {}ms",
                anchor, extra, r, unsup, tainted, dur
            );
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
            eprintln!(
                "QORES phase2: tests={} verified residue_subs={}",
                tested,
                subs.len()
            );
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
        if self.edgeprobe {
            DBG_FRC.fetch_add(1, Ordering::Relaxed);
        }
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
                // A self-loop body atom `r(x,x)` (s == t, same var) is only witnessed
                // by a SELF edge `r(es,es)`; anchoring it on a non-self edge with
                // es != et would bind the single var to `et` and silently drop the
                // es==et constraint (UNSOUND — same bug as fire_anchor_edge; this is
                // the QoSat saturation path `km classify` uses for 10908's
                // ObjectHasSelf + inverse, forcing the located-in occupant spatial).
                if *s == *t && es != et {
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
        if self.edgeprobe {
            let m = DBG_MATCH.fetch_add(1, Ordering::Relaxed);
            // A single `match_body` that recurses millions of times is a chain-clause
            // binding explosion over a high-degree node — the suspected single-pop
            // sink. Print periodically (wall time + depth) so it is visible even while
            // the enclosing edge pop never returns.
            if m % 5_000_000 == 0 && std::env::var_os("KM_HT_TRACE").is_some() {
                eprintln!(
                    "QOMATCH el={:.1}s match_body_calls={} apply={} addlit={}",
                    self.sat_elapsed(),
                    m,
                    DBG_APPLY.load(Ordering::Relaxed),
                    DBG_ADDLIT.load(Ordering::Relaxed)
                );
            }
        }
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
                    if self.out_edges[sn]
                        .iter()
                        .any(|(rr, tt)| *rr == *r && *tt == tn)
                    {
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
        if self.edgeprobe {
            DBG_APPLY.fetch_add(1, Ordering::Relaxed);
        }
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
                        // SPLIT (port #2): the operand is already present on the
                        // target (e.g. the re-fire onto the just-created split node,
                        // which was seeded with it) ⇒ discharged, NOT a critical-ALL
                        // insufficiency. Guarded by `split_mode` so non-split
                        // semantics (where this falls through to the write below) are
                        // byte-identical.
                        if self.split_mode && self.label[n].contains(&lit) {
                            satisfied = true;
                            break;
                        }
                        let cls = self.node_range[n] as usize;
                        // P2.1: under `shiq` the successor `n` is the source's OWN
                        // non-shared node, so this ∀-write is sound exactly as in
                        // Konclude's `applyALLRule` (forward over a genuine edge into
                        // an independent successor). No critical-ALL insufficiency.
                        let clean = self.shiq || (cls != 0 && self.class_set[cls].contains(&lit));
                        // KM_HT_QO_SPLIT (port #2 copy-on-conflict): a single-operand
                        // forward `∀r.lit` whose operand is not already forced ⇒
                        // redirect the source's r-edge onto a content-keyed split
                        // filler instead of polluting the shared filler / deferring
                        // (`qo_insufficient`). Restricted to the pure single-concept
                        // head shape so a `⊔` under `∀` still parks normally.
                        if self.split_mode
                            && !clean
                            && head.len() == 1
                            && !self.node_unsat.contains(&n)
                            && !self.label[n].contains(&lit)
                        {
                            let anchor = sigma[X as usize].expect("X bound");
                            if self.try_split_redirect(cid, anchor, n, t, lit) {
                                satisfied = true;
                                break;
                            }
                        }
                        if !clean {
                            DBG_FORALL_INSUFF.fetch_add(1, Ordering::Relaxed);
                            self.qo_insufficient = true;
                            // KM_HT_QO_CARD per-node split: the write into successor
                            // `n` is model-specific (critical-ALL). Record `n` as
                            // insufficient so the affected-set reverse-reachability
                            // marks every concept whose model reaches `n`; CLEAN
                            // concepts (not reaching `n`) keep a sound label.
                            if self.card_defer {
                                self.kp_insuff_nodes.insert(n);
                            }
                            // KM_HT_QO_NOPOLLUTE (Konclude
                            // `isCriticalALLConceptDescriptorInsufficient`): on a shared
                            // filler, DEFER this critical-ALL write — do NOT add `lit`.
                            // Writing it would accumulate the union of every
                            // predecessor's ∀-consequences onto the one shared filler
                            // (KM ~850 concepts/node) and re-trigger ∃ → the
                            // non-converging cascade. Discharging the obligation here
                            // (the seed is already flagged insufficient ⇒ residue
                            // re-verifies) keeps the filler small and the precompute
                            // bounded (Konclude ~20/node, converges in ~4.5 s).
                            if self.no_pollute && self.sat_mode && self.is_filler[n] {
                                self.kp_insuff_nodes.insert(n);
                                satisfied = true;
                                break;
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
                    let comp = CLit {
                        neg: !lit.neg,
                        c: lit.c,
                    };
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
                    if self.shiq {
                        // P2.1 (Konclude `createSuccessorIndividual`): a NON-SHARED
                        // successor owned by `n`. `∀R.C` from `n` lands here and can
                        // never pollute another source's filler. Reuse `n`'s own
                        // existing r-successor carrying `fil` (idempotent per source);
                        // otherwise create a fresh node with parent link `n` (for the
                        // ancestor blocking walk).
                        // P2.1b ANCESTOR SUBSET BLOCKING (Konclude
                        // `detectIndividualNodeBlockedStatus` / optimized subset): if
                        // `n` is blocked by an ancestor whose label is a superset, do
                        // NOT expand `n`'s existentials — the ancestor already
                        // witnesses an identical (or larger) successor pattern, so a
                        // fresh subtree is redundant. This is what bounds the
                        // otherwise-unbounded per-source expansion (27 GB on 7914).
                        if self.qo_blocked(n) {
                            satisfied = true;
                            break;
                        }
                        let existing = self.out_edges[n]
                            .iter()
                            .find(|(rr, tt)| *rr == r && self.label[*tt as usize].contains(&fil))
                            .map(|&(_, tt)| tt);
                        let f = match existing {
                            Some(f) => f,
                            None => {
                                let f = self.new_node();
                                self.qo_parent[f] = Some(n);
                                self.is_filler[f] = true;
                                self.add_lit(f, fil);
                                f
                            }
                        };
                        if !self.out_edges[n]
                            .iter()
                            .any(|(rr, tt)| *rr == r && *tt == f)
                        {
                            self.add_edge(n, r, f);
                        }
                        satisfied = true;
                        break;
                    }
                    let f = self.ensure_filler(r, fil);
                    if !self.out_edges[n]
                        .iter()
                        .any(|(rr, tt)| *rr == r && *tt == f)
                    {
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
                Atom::Eq { s, t } => {
                    // SOUND self-equality short-circuit: in the shared-node model an
                    // at-most body usually binds both `R`-successors to the SAME
                    // shared filler node (one node per `(fil,role)`), so the forced
                    // equality is `node == node` — trivially satisfied, NO merge, NO
                    // insufficiency. Marking it insufficient (as the blanket defer
                    // did) is a spurious over-deferral: on 9724 it is the bulk of the
                    // 98M card-insuff firings (only 674 distinct Eq-heads). Only a
                    // merge of two DISTINCT successor nodes is a real cardinality
                    // obligation the shared pass cannot represent.
                    let sn = sigma[s as usize].expect("Eq s bound");
                    let tn = sigma[t as usize].expect("Eq t bound");
                    if sn == tn {
                        satisfied = true;
                        break;
                    }
                    // KM_HT_QO_CARDMERGE (Konclude ≤-rule, CONTENT-SHARED form): the
                    // forced merge of two DISTINCT filler successors is realised by
                    // redirecting the constrained predecessor's r-edges onto ONE
                    // node keyed by the UNION of the two successors' defining seeds
                    // — exactly port #2's content keying, but over fil-sets. No
                    // per-predecessor copy (the earlier privatize+union-find blew the
                    // node count up on the high-cardinality giants); predecessors
                    // forcing the same fil-set merge share one merged node. Sound:
                    // every such predecessor genuinely has an r-successor that is
                    // each of those fils; the merged node carries them and re-derives
                    // its own closure. A resulting clash is caught when the merged
                    // node's label trips a disjointness clause → kill_node defers its
                    // ∃-sources (the filler-death hook). Only filler nodes merge,
                    // never concept self-nodes. Node-budget backstop: past the budget,
                    // fall through to the (sound) card_defer rather than grow further.
                    if self.card_merge
                        && self.is_filler[sn]
                        && self.is_filler[tn]
                        && !self.node_seed[sn].is_empty()
                        && !self.node_seed[tn].is_empty()
                        && !self.node_unsat.contains(&sn)
                        && !self.node_unsat.contains(&tn)
                        && self.label.len() < self.merge_budget
                    {
                        if let Some(r) = self.eq_merge_role(cid, s, t) {
                            let anchor = sigma[X as usize].expect("X bound");
                            let mut set: std::collections::BTreeSet<CLit> =
                                std::collections::BTreeSet::new();
                            set.extend(self.node_seed[sn].iter().copied());
                            set.extend(self.node_seed[tn].iter().copied());
                            let seed: Vec<CLit> = set.into_iter().collect();
                            let m = self.seed_filler(r, &seed);
                            if m != sn {
                                self.remove_edge(anchor, r, sn);
                            }
                            if m != tn {
                                self.remove_edge(anchor, r, tn);
                            }
                            self.add_edge(anchor, r, m);
                            DBG_CARDMERGE.fetch_add(1, Ordering::Relaxed);
                            satisfied = true;
                            break;
                        }
                    }
                    // at-most / functional cardinality forces a successor merge the
                    // shared-node saturation cannot represent soundly. KM_HT_QO_CARD:
                    // mark the anchor node INSUFFICIENT (Konclude's deferral) and
                    // treat the head as satisfied (no write), so the pass completes
                    // for every other concept; the per-node split routes only the
                    // cardinality-affected concepts to the complete verify. Default
                    // (flag off): bail the whole pass `unsupported` (legacy — no
                    // regression on the non-SHIF onts).
                    if self.card_defer {
                        DBG_CARD_INSUFF.fetch_add(1, Ordering::Relaxed);
                        if self.card_merge {
                            if !self.is_filler[sn] || !self.is_filler[tn] {
                                DBG_EQ_NONFILLER.fetch_add(1, Ordering::Relaxed);
                            } else if self.eq_merge_role(cid, s, t).is_none() {
                                DBG_EQ_NOROLE.fetch_add(1, Ordering::Relaxed);
                            } else if self.node_unsat.contains(&sn) || self.node_unsat.contains(&tn)
                            {
                                DBG_EQ_UNSAT.fetch_add(1, Ordering::Relaxed);
                            } else {
                                DBG_EQ_OTHER.fetch_add(1, Ordering::Relaxed);
                            }
                        }
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
        // ≥2 live. KM_HT_QO_APPROX (Konclude approximate saturation): instead of
        // parking, pick the first live disjunct and continue (non-backtracking),
        // marking the concept insufficient. The picked branch's forward closure
        // becomes the possible-subsumer candidate set; a calculated test confirms.
        if self.approx {
            self.qo_insufficient = true;
            self.pending.push((anchor, cid)); // still recorded as a parked disjunction
            self.open_disj += 1;
            self.add_lit(live[0].0, live[0].1);
            return;
        }
        // KM_HT_QO_NODECERTAIN: a concept-level disjunction parked at `anchor`
        // entails (in every branch) the ⋂-closure `D` of its disjuncts. Inject `D`
        // at `anchor` and continue WITHOUT parking: re-saturation fires the role
        // rules on `D`, so role-mediated certain subsumers reach the predecessor.
        // The disjunct-specific (non-certain) part is correctly dropped — it is not
        // a subsumer. Guarded per (node,cid) against re-injection.
        if let Some(nc) = self.node_certain.clone() {
            if let Some(d) = nc.get(&cid) {
                if self.nc_resolved.insert((anchor, cid)) {
                    for &c in d.iter() {
                        self.add_lit(anchor, CLit::pos(c));
                    }
                }
                return; // resolved to the certain part; not parked
            }
        }
        // Otherwise park. Record and count as open.
        if self.tracing {
            self.trail.push(QoUndo::Pending(self.pending.len()));
        } else {
            // P0: index the parked entry by its anchor node (non-tracing only).
            self.pending_by_node[anchor].push(self.pending.len());
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
        // KPCLASH precision: an inverse-anchored head is a genuine under-detected
        // inconsistency only when it is FULLY REFUTED at fixpoint — every concept
        // disjunct's complement present and none satisfied (an empty head is the
        // degenerate fully-refuted case). A head with an undetermined disjunct, or
        // a role/∃ disjunct we cannot cheaply refute, is dropped (no deferral, no
        // flag): the shared model need not represent that backward contribution.
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
                let (n, lit) = disj[0];
                // KM_HT_QO_KPWRITE: a UNIT inverse-anchored head (the sole absent
                // operand) on a real self/named node is a definite, sound backward
                // write (Konclude `applyALLRule`). Perform it; only a shared-filler
                // target stays a deferred check.
                let on_self = !(self.sat_mode && self.is_filler[n]);
                if self.kpwrite && on_self {
                    self.add_lit(n, lit);
                } else {
                    self.kp_check1.insert(disj[0]);
                }
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
        if self.edgeprobe {
            DBG_FPROPE.fetch_add(1, Ordering::Relaxed);
        }
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
                // KM_HT_QO_KPWRITE: a composed-clause head landing on a real
                // self/named node is the sound Konclude backward write ⇒ perform it.
                if self.kpwrite && on_self {
                    self.add_lit(t, e);
                    return;
                }
                let critical = on_self || !self.kp_guard_only || self.kp_guard.contains(&e.c);
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
        if self.edgeprobe {
            DBG_KPW.fetch_add(1, Ordering::Relaxed);
        }
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
                // KM_HT_QO_KPWRITE (Konclude `applyALLRule` backward write): the
                // operand lands on a real self/named predecessor ⇒ it is a sound
                // named-subsumer contribution (every R-predecessor of the shared
                // filler genuinely entails it). WRITE+propagate it instead of
                // deferring a check, so pervasive inverse propagation certifies in
                // the single pass. A shared-filler target stays a check.
                if self.kpwrite && on_self {
                    return self.add_lit(n, lit);
                }
                let critical = on_self || !self.kp_guard_only || self.kp_guard.contains(&lit.c);
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
        // r-Succ reconstruction post-pass (KM_RSUCC): in the shared forward model
        // the head `C(x)` of a transitive-reach clause `C(y) ∧ R(x,y) → C(x)`,
        // fired with `x` a shared filler and `y` its predecessor across an inverse
        // back-edge, is suppressed (a filler label is not read as a subsumer), so
        // the per-predecessor reconstruction never propagates `C` to the filler.
        // Detect it structurally: a filler `s` with an `R`-edge to a `t` that
        // carries a reach concept `C` (for `(R, C)` a reach clause) while `s`
        // lacks `C`. Such a filler is NOT soundly decided by the shared model ⇒
        // mark it insufficient so the reverse-reach pulls every concept whose
        // model reaches it into the residue-complete tableau (which decides it).
        if self.rsucc && (!self.reach_by_role.is_empty() || !self.reach_via_inv.is_empty()) {
            let direct = self.reach_by_role.clone();
            let viainv = self.reach_via_inv.clone();
            let nn = self.out_edges.len();
            let mut _flagged = 0u64;
            let (mut _de, mut _ie, mut _dpred, mut _ipred) = (0u64, 0u64, 0u64, 0u64);
            // ONE edge scan over `out_edges`, each edge `src --r--> dst`:
            //  - direct `r ∈ reach_by_role`: `r` is the reach role, so `src` is the
            //    filler and `dst` its predecessor (the materialised back-edge case).
            //  - inverse `r ∈ reach_via_inv`: `r = R⁻`, so `src` is the predecessor
            //    and `dst` the filler (the QOGF case: only the forward inverse edge
            //    exists). `src --R⁻--> dst` ⟺ `dst --R--> src`.
            // Either way: flag the FILLER when the PREDECESSOR carries reach `C` and
            // the filler does not — the per-predecessor reconstruction the shared
            // model could not perform. Sound (only marks insufficient → residue).
            for src in 0..nn {
                let ne = self.out_edges[src].len();
                for k in 0..ne {
                    let (r, dst) = self.out_edges[src][k];
                    if let Some(cs) = direct.get(&r) {
                        _de += 1;
                        if self.is_filler[src] && !self.node_unsat.contains(&src) {
                            for &c in cs {
                                let lit = CLit { neg: false, c };
                                if !self.node_unsat.contains(&dst) && self.label[dst].contains(&lit)
                                {
                                    _dpred += 1;
                                    if !self.label[src].contains(&lit) {
                                        self.kp_insufficient = true;
                                        self.kp_miss += 1;
                                        self.kp_insuff_nodes.insert(src);
                                        _flagged += 1;
                                    }
                                }
                            }
                        }
                    }
                    if let Some(cs) = viainv.get(&r) {
                        _ie += 1;
                        if self.is_filler[dst] && !self.node_unsat.contains(&dst) {
                            for &c in cs {
                                let lit = CLit { neg: false, c };
                                if !self.node_unsat.contains(&src) && self.label[src].contains(&lit)
                                {
                                    _ipred += 1;
                                    if !self.label[dst].contains(&lit) {
                                        self.kp_insufficient = true;
                                        self.kp_miss += 1;
                                        self.kp_insuff_nodes.insert(dst);
                                        _flagged += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            if _flagged > 0 && std::env::var_os("KM_HT_TRACE").is_some() {
                eprintln!(
                    "RSUCC post-pass: direct_roles={} inv_roles={} nodes={} flagged={} (direct_edges={} inv_edges={})",
                    direct.len(), viainv.len(), nn, _flagged, _de, _ie
                );
            }
        }
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
        // P0 fast path (non-tracing): visit only `n`'s parked disjunctions via the
        // per-node index — O(deg(n)) instead of the O(|pending|) full scan that was
        // quadratic when `pending` reaches 763k (14817). The tracing residue DFS
        // does not maintain `pending_by_node`, so it keeps the linear scan.
        if !self.tracing {
            if self.edgeprobe {
                let pl = self.pending_by_node[n].len() as u64;
                DBG_EVALSCAN.fetch_add(pl, Ordering::Relaxed);
                DBG_MAXLABEL.fetch_max(self.pending.len() as u64, Ordering::Relaxed);
            }
            let mut k = 0;
            while k < self.pending_by_node[n].len() {
                if self.node_unsat.contains(&n) {
                    return;
                }
                let idx = self.pending_by_node[n][k];
                let cid = self.pending[idx].1;
                let (satisfied, live) = self.eval_disj_state(n, cid);
                if satisfied {
                    self.pending_remove(idx);
                    self.open_disj = self.open_disj.saturating_sub(1);
                    continue; // pending_by_node[n][k] now holds a different entry
                }
                if live.is_empty() {
                    self.kill_node(n);
                    return;
                }
                if live.len() == 1 {
                    self.pending_remove(idx);
                    self.open_disj = self.open_disj.saturating_sub(1);
                    self.add_lit(n, live[0]);
                    continue;
                }
                k += 1;
            }
            return;
        }
        let mut i = 0;
        while i < self.pending.len() {
            if self.pending[i].0 != n || self.node_unsat.contains(&n) {
                i += 1;
                continue;
            }
            let cid = self.pending[i].1;
            let (satisfied, live) = self.eval_disj_state(n, cid);
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

    /// Shared disjunction-state classifier for `eval_parked_at`: at node `n`, is
    /// the parked disjunction `cid` already satisfied, and what are its still-live
    /// (neither asserted nor refuted) Concept disjuncts? Identical logic to the
    /// prior inline scan, factored so both the indexed and linear paths share it.
    fn eval_disj_state(&self, n: Node, cid: usize) -> (bool, Vec<CLit>) {
        let head = &self.clauses[cid].0.head;
        let mut live: Vec<CLit> = Vec::new();
        for h in head {
            if let Atom::Concept { lit, t: _ } = h {
                if self.label[n].contains(lit) {
                    return (true, Vec::new());
                }
                let comp = CLit {
                    neg: !lit.neg,
                    c: lit.c,
                };
                if self.label[n].contains(&comp) {
                    continue;
                }
                live.push(*lit);
            }
        }
        (false, live)
    }
}

impl Ht {
    fn lean_wire_lit(lit: CLit) -> LeanHtLit {
        LeanHtLit {
            concept: lit.c as usize,
            neg: lit.neg,
        }
    }

    fn lean_wire_atom(atom: &Atom) -> LeanHtAtom {
        match *atom {
            Atom::Concept { lit, t } => LeanHtAtom::Concept {
                literal: Self::lean_wire_lit(lit),
                node: t as usize,
            },
            Atom::Role { r, s, t } => LeanHtAtom::Role {
                role: r as usize,
                source: s as usize,
                target: t as usize,
            },
            Atom::Exists { r, fil, t } => LeanHtAtom::Exists_ {
                role: r as usize,
                filler: Self::lean_wire_lit(fil),
                node: t as usize,
            },
            Atom::Eq { s, t } => LeanHtAtom::Eq {
                left: s as usize,
                right: t as usize,
            },
        }
    }

    fn lean_refutation_assignments(
        variable_count: usize,
        active_nodes: usize,
    ) -> Option<Vec<Vec<Node>>> {
        let assignment_count = (0..variable_count)
            .try_fold(1usize, |count, _| count.checked_mul(active_nodes))?;
        if assignment_count > 1_000_000 {
            return None;
        }
        let mut assignments = vec![Vec::with_capacity(variable_count)];
        for _ in 0..variable_count {
            let mut next = Vec::with_capacity(assignments.len().saturating_mul(active_nodes));
            for assignment in assignments {
                for node in 0..active_nodes {
                    let mut extended = assignment.clone();
                    extended.push(node);
                    next.push(extended);
                }
            }
            assignments = next;
        }
        Some(assignments)
    }

    fn lean_refutation(
        &self,
        state: &mut LeanHtRefutationState,
        variable_count: usize,
        node_budget: usize,
    ) -> Option<(LeanHtRefutationTree, usize)> {
        if state.clashes() {
            return Some((LeanHtRefutationTree::Clash, state.active_nodes));
        }

        let assignments =
            Self::lean_refutation_assignments(variable_count, state.active_nodes)?;
        for (clause_id, record) in self.clauses.iter().enumerate() {
            let clause = &record.0;
            for assignment in &assignments {
                let body_holds = clause
                    .body
                    .iter()
                    .all(|atom| state.holds(atom, assignment));
                if !body_holds {
                    continue;
                }
                let head_holds = clause
                    .head
                    .iter()
                    .any(|atom| state.holds(atom, assignment));
                if head_holds {
                    continue;
                }

                let mut children = Vec::with_capacity(clause.head.len());
                let mut max_used = state.active_nodes;
                for atom in &clause.head {
                    if matches!(atom, Atom::Eq { .. }) {
                        return None;
                    }
                    let inserted = state.insert(atom, assignment);
                    debug_assert!(inserted, "an unsatisfied branch head must be absent");
                    let result = self.lean_refutation(state, variable_count, node_budget);
                    state.remove(atom, assignment);
                    let Some((child, child_used)) = result else {
                        return None;
                    };
                    max_used = max_used.max(child_used);
                    children.push(child);
                }
                return Some((
                    LeanHtRefutationTree::Branch {
                        clause: clause_id,
                        assignment: assignment.clone(),
                        children,
                    },
                    max_used,
                ));
            }
        }

        let obligation = state
            .obligations
            .iter()
            .copied()
            .filter(|&(role, filler, source)| !state.witness_for(role, filler, source))
            .min();
        if let Some((role, filler, source)) = obligation {
            if state.active_nodes >= node_budget {
                return None;
            }
            let target = state.active_nodes;
            state.active_nodes += 1;
            let inserted_edge = state.edges.insert((role, source, target));
            let inserted_label = state.labels.insert((target, filler));
            debug_assert!(inserted_edge && inserted_label, "the witness target is fresh");
            let result = self.lean_refutation(state, variable_count, node_budget);
            state.labels.remove(&(target, filler));
            state.edges.remove(&(role, source, target));
            state.active_nodes -= 1;
            let (child, max_used) = result?;
            return Some((
                LeanHtRefutationTree::Witness {
                    source,
                    target,
                    role: role as usize,
                    filler: Self::lean_wire_lit(filler),
                    child: Box::new(child),
                },
                max_used,
            ));
        }

        None
    }

    fn lean_eq_refutation(
        &self,
        state: &mut LeanHtRefutationState,
        variable_count: usize,
        node_budget: usize,
    ) -> Option<(LeanHtEqRefutationTree, usize)> {
        if state.clashes() {
            return Some((LeanHtEqRefutationTree::Clash, state.active_nodes));
        }

        let assignments =
            Self::lean_refutation_assignments(variable_count, state.active_nodes)?;
        for (clause_id, record) in self.clauses.iter().enumerate() {
            let clause = &record.0;
            for assignment in &assignments {
                if !clause.body.iter().all(|atom| state.holds(atom, assignment))
                    || clause.head.iter().any(|atom| state.holds(atom, assignment))
                {
                    continue;
                }
                let mut children = Vec::with_capacity(clause.head.len());
                let mut max_used = state.active_nodes;
                for atom in &clause.head {
                    let inserted = state.insert(atom, assignment);
                    debug_assert!(inserted, "an unsatisfied equality-aware head must be absent");
                    let successor = state.equality_wire_state(node_budget);
                    let result = self.lean_eq_refutation(state, variable_count, node_budget);
                    state.remove(atom, assignment);
                    let (child, child_used) = result?;
                    max_used = max_used.max(child_used);
                    children.push((successor, child));
                }
                return Some((
                    LeanHtEqRefutationTree::Branch {
                        clause: clause_id,
                        assignment: assignment.clone(),
                        children,
                    },
                    max_used,
                ));
            }
        }

        let obligation = state
            .obligations
            .iter()
            .copied()
            .filter(|&(role, filler, source)| !state.witness_for(role, filler, source))
            .min();
        if let Some((role, filler, source)) = obligation {
            if state.active_nodes >= node_budget {
                return None;
            }
            let target = state.active_nodes;
            state.active_nodes += 1;
            let edge = (role, source, target);
            let label = (target, filler);
            let inserted_edge = state.edges.insert(edge);
            let inserted_label = state.labels.insert(label);
            debug_assert!(inserted_edge && inserted_label, "the witness target is fresh");
            state.edge_order.insert(0, edge);
            state.label_order.insert(0, label);
            let result = self.lean_eq_refutation(state, variable_count, node_budget);
            state.label_order.remove(0);
            state.edge_order.remove(0);
            state.labels.remove(&label);
            state.edges.remove(&edge);
            state.active_nodes -= 1;
            let (child, max_used) = result?;
            return Some((
                LeanHtEqRefutationTree::Witness {
                    source,
                    target,
                    role: role as usize,
                    filler: Self::lean_wire_lit(filler),
                    child: Box::new(child),
                },
                max_used,
            ));
        }
        None
    }

    fn lean_eq_refutation_certificate_json(
        &self,
        initial_labels: &[(Node, CLit)],
        evidence: impl FnOnce(LeanHtEqRefutationTree) -> LeanHtEqEvidence,
    ) -> Result<String, String> {
        let mut variable_count = 0usize;
        let mut concept_count = 0usize;
        let mut role_count = 0usize;
        for record in &self.clauses {
            for atom in record.0.body.iter().chain(record.0.head.iter()) {
                match atom {
                    Atom::Concept { lit, t } => {
                        variable_count = variable_count.max(*t as usize + 1);
                        concept_count = concept_count.max(lit.c as usize + 1);
                    }
                    Atom::Role { r, s, t } => {
                        variable_count = variable_count.max(*s as usize + 1);
                        variable_count = variable_count.max(*t as usize + 1);
                        role_count = role_count.max(*r as usize + 1);
                    }
                    Atom::Exists { r, fil, t } => {
                        variable_count = variable_count.max(*t as usize + 1);
                        concept_count = concept_count.max(fil.c as usize + 1);
                        role_count = role_count.max(*r as usize + 1);
                    }
                    Atom::Eq { s, t } => {
                        variable_count = variable_count.max(*s as usize + 1);
                        variable_count = variable_count.max(*t as usize + 1);
                    }
                }
            }
        }
        for &(node, literal) in initial_labels {
            if node != 0 {
                return Err("HT Lean equality query certificates require root node 0".to_string());
            }
            concept_count = concept_count.max(literal.c as usize + 1);
        }
        let ontology = self
            .clauses
            .iter()
            .map(|record| LeanHtClause {
                body: record.0.body.iter().map(Self::lean_wire_atom).collect(),
                head: record.0.head.iter().map(Self::lean_wire_atom).collect(),
            })
            .collect();
        let node_budget = std::env::var("KM_HT_LEAN_UNSAT_NODES")
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
            .filter(|&value| (1..=64).contains(&value))
            .unwrap_or(8);
        let mut state = LeanHtRefutationState::root(initial_labels);
        let (tree, _node_count) = self
            .lean_eq_refutation(&mut state, variable_count, node_budget)
            .ok_or_else(|| "ontology has an open or node-capped equality refutation branch".to_string())?;
        let root_state = state.equality_wire_state(node_budget);
        serde_json::to_string(&LeanHtEqCertificate {
            version: 2,
            node_count: node_budget,
            concept_count,
            role_count,
            variable_count,
            ontology,
            state: root_state,
            evidence: evidence(tree),
        })
        .map_err(|error| error.to_string())
    }

    /// Construct an exhaustive empty-root refutation for the exact normalized
    /// ontology. Concept, role, and existential heads are monotone finite facts.
    /// Unwitnessed existential obligations may allocate a fresh finite node; the
    /// node cap bounds search and an open or cap-exhausted branch declines.
    /// Equality heads are rejected because they require a separately certified
    /// merge. Publication still requires Lean checker acceptance.
    fn lean_refutation_certificate_json(
        &self,
        initial_labels: &[(Node, CLit)],
        evidence: impl FnOnce(LeanHtRefutationTree) -> LeanHtEvidence,
    ) -> Result<String, String> {
        if self
            .clauses
            .iter()
            .any(|record| record.0.head.iter().any(|atom| matches!(atom, Atom::Eq { .. })))
        {
            return Err(
                "HT Lean UNSAT certificate v1 does not support equality heads".to_string(),
            );
        }

        let mut variable_count = 0usize;
        let mut concept_count = 0usize;
        let mut role_count = 0usize;
        for record in &self.clauses {
            for atom in record.0.body.iter().chain(record.0.head.iter()) {
                match atom {
                    Atom::Concept { lit, t } => {
                        variable_count = variable_count.max(*t as usize + 1);
                        concept_count = concept_count.max(lit.c as usize + 1);
                    }
                    Atom::Role { r, s, t } => {
                        variable_count = variable_count.max(*s as usize + 1);
                        variable_count = variable_count.max(*t as usize + 1);
                        role_count = role_count.max(*r as usize + 1);
                    }
                    Atom::Exists { r, fil, t } => {
                        variable_count = variable_count.max(*t as usize + 1);
                        concept_count = concept_count.max(fil.c as usize + 1);
                        role_count = role_count.max(*r as usize + 1);
                    }
                    Atom::Eq { s, t } => {
                        variable_count = variable_count.max(*s as usize + 1);
                        variable_count = variable_count.max(*t as usize + 1);
                    }
                }
            }
        }
        for &(node, literal) in initial_labels {
            if node != 0 {
                return Err("HT Lean query certificates require root node 0".to_string());
            }
            concept_count = concept_count.max(literal.c as usize + 1);
        }
        let ontology = self
            .clauses
            .iter()
            .map(|record| LeanHtClause {
                body: record.0.body.iter().map(Self::lean_wire_atom).collect(),
                head: record.0.head.iter().map(Self::lean_wire_atom).collect(),
            })
            .collect();
        let node_budget = std::env::var("KM_HT_LEAN_UNSAT_NODES")
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
            .filter(|&value| (1..=64).contains(&value))
            .unwrap_or(8);
        let (tree, node_count) = self
            .lean_refutation(
                &mut LeanHtRefutationState::root(initial_labels),
                variable_count,
                node_budget,
            )
            .ok_or_else(|| "ontology has an open or node-capped refutation branch".to_string())?;

        serde_json::to_string(&LeanHtCertificate {
            version: 1,
            node_count,
            concept_count,
            role_count,
            variable_count,
            ontology,
            labels: initial_labels
                .iter()
                .map(|&(node, literal)| LeanHtLabel {
                    node,
                    literal: Self::lean_wire_lit(literal),
                })
                .collect(),
            edges: Vec::new(),
            obligations: Vec::new(),
            evidence: evidence(tree),
        })
        .map_err(|error| error.to_string())
    }

    pub fn lean_unsat_certificate_json(&self) -> Result<String, String> {
        if self
            .clauses
            .iter()
            .any(|record| record.0.head.iter().any(|atom| matches!(atom, Atom::Eq { .. })))
        {
            return self.lean_eq_refutation_certificate_json(&[], |tree| {
                LeanHtEqEvidence::Unsat { tree }
            });
        }
        self.lean_refutation_certificate_json(&[], |tree| LeanHtEvidence::Unsat { tree })
    }

    /// Certify `sub ⊑ sup` by refuting the exact root labels `sub` and `¬sup`.
    pub fn lean_subsumption_certificate_json(&self, sub: C, sup: C) -> Result<String, String> {
        let labels = [
            (0, CLit { c: sub, neg: false }),
            (0, CLit { c: sup, neg: true }),
        ];
        if self
            .clauses
            .iter()
            .any(|record| record.0.head.iter().any(|atom| matches!(atom, Atom::Eq { .. })))
        {
            return self.lean_eq_refutation_certificate_json(&labels, |tree| {
                LeanHtEqEvidence::Subsumption {
                    root: 0,
                    sub: sub as usize,
                    sup: sup as usize,
                    tree,
                }
            });
        }
        self.lean_refutation_certificate_json(&labels, |tree| LeanHtEvidence::Subsumption {
            root: 0,
            sub: sub as usize,
            sup: sup as usize,
            tree,
        })
    }

    /// Certify that `concept` is unsatisfiable by refuting its exact root label.
    pub fn lean_unsatisfiable_concept_certificate_json(
        &self,
        concept: C,
    ) -> Result<String, String> {
        let labels = [(0, CLit { c: concept, neg: false })];
        if self
            .clauses
            .iter()
            .any(|record| record.0.head.iter().any(|atom| matches!(atom, Atom::Eq { .. })))
        {
            return self.lean_eq_refutation_certificate_json(&labels, |tree| {
                LeanHtEqEvidence::UnsatisfiableConcept {
                    root: 0,
                    concept: concept as usize,
                    tree,
                }
            });
        }
        self.lean_refutation_certificate_json(&labels, |tree| {
            LeanHtEvidence::UnsatisfiableConcept {
                root: 0,
                concept: concept as usize,
                tree,
            }
        })
    }

    /// Serialize the exact terminal completion graph and normalized HT clauses.
    /// Equality-free evidence uses wire version 1. Equality-aware SAT and
    /// query-countermodel evidence uses version 2 with the complete merge
    /// forest and quotient witnesses.
    fn lean_sat_certificate_json_with_evidence(
        &self,
        evidence: LeanHtEvidence,
    ) -> Result<String, String> {
        if self.ext.clash.is_some() {
            return Err("cannot certify a clashing hypertableau state".to_string());
        }
        if self.ext.unsupported {
            return Err("cannot certify an unsupported hypertableau state".to_string());
        }
        if !self.anywhere || self.block_mode != 1 {
            return Err(
                "HT Lean SAT certificate v1 supports default anywhere-subset blocking only"
                    .to_string(),
            );
        }
        let has_equality = self.clauses.iter().any(|record| {
            record
                .0
                .body
                .iter()
                .chain(record.0.head.iter())
                .any(|atom| matches!(atom, Atom::Eq { .. }))
        });
        let mut variable_count = 0usize;
        let mut concept_count = 0usize;
        let mut role_count = 0usize;
        let mut note_atom = |atom: &Atom| match *atom {
            Atom::Concept { lit, t } => {
                variable_count = variable_count.max(t as usize + 1);
                concept_count = concept_count.max(lit.c as usize + 1);
            }
            Atom::Role { r, s, t } => {
                variable_count = variable_count.max(s as usize + 1).max(t as usize + 1);
                role_count = role_count.max(r as usize + 1);
            }
            Atom::Exists { r, fil, t } => {
                variable_count = variable_count.max(t as usize + 1);
                concept_count = concept_count.max(fil.c as usize + 1);
                role_count = role_count.max(r as usize + 1);
            }
            Atom::Eq { s, t } => {
                variable_count = variable_count.max(s as usize + 1).max(t as usize + 1);
            }
        };
        for record in &self.clauses {
            for atom in record.0.body.iter().chain(record.0.head.iter()) {
                note_atom(atom);
            }
        }
        drop(note_atom);

        let ontology = self
            .clauses
            .iter()
            .map(|record| LeanHtClause {
                body: record.0.body.iter().map(Self::lean_wire_atom).collect(),
                head: record.0.head.iter().map(Self::lean_wire_atom).collect(),
            })
            .collect();
        let mut labels = Vec::new();
        for (node, label) in self.ext.concepts.iter().enumerate() {
            for &literal in label.keys() {
                concept_count = concept_count.max(literal.c as usize + 1);
                labels.push(LeanHtLabel {
                    node,
                    literal: Self::lean_wire_lit(literal),
                });
            }
        }
        labels.sort_unstable_by_key(|label| {
            (label.node, label.literal.concept, label.literal.neg)
        });
        let mut edges = Vec::new();
        for (source, outgoing) in self.ext.out_edges.iter().enumerate() {
            for &(role, target, _) in outgoing {
                role_count = role_count.max(role as usize + 1);
                edges.push(LeanHtEdge {
                    role: role as usize,
                    source,
                    target,
                });
            }
        }
        // A blocked node represents an unraveling position whose continuation
        // is the earlier unblocked superset-label node. Materialize that fold as
        // ordinary candidate edges. Lean does not trust this blocker relation:
        // it exhaustively checks the resulting finite graph against every
        // ontology grounding, so a wrong fold is rejected rather than assumed.
        let mut blocked_by = vec![None; self.ext.num_nodes()];
        let mut unblocked: Vec<Node> = Vec::new();
        for node in 0..self.ext.num_nodes() {
            let label = &self.ext.concepts[node];
            if self.ext.blockable[node] && !label.is_empty() {
                blocked_by[node] = unblocked.iter().copied().find(|&candidate| {
                    let candidate_label = &self.ext.concepts[candidate];
                    candidate_label.len() >= label.len()
                        && label
                            .keys()
                            .all(|literal| candidate_label.contains_key(literal))
                });
            }
            if blocked_by[node].is_none() {
                unblocked.push(node);
            }
        }
        for (node, blocker) in blocked_by.into_iter().enumerate() {
            let Some(blocker) = blocker else { continue };
            for &(role, target, _) in &self.ext.out_edges[blocker] {
                role_count = role_count.max(role as usize + 1);
                edges.push(LeanHtEdge {
                    role: role as usize,
                    source: node,
                    target,
                });
            }
        }
        edges.sort_unstable_by_key(|edge| (edge.role, edge.source, edge.target));
        edges.dedup_by_key(|edge| (edge.role, edge.source, edge.target));
        let mut obligations = self
            .ext
            .obligations
            .iter()
            .map(|obligation| {
                concept_count = concept_count.max(obligation.fil.c as usize + 1);
                role_count = role_count.max(obligation.r as usize + 1);
                LeanHtObligation {
                    role: obligation.r as usize,
                    filler: Self::lean_wire_lit(obligation.fil),
                    node: obligation.n,
                }
            })
            .collect::<Vec<_>>();
        obligations.sort_unstable_by_key(|obligation| {
            (
                obligation.role,
                obligation.node,
                obligation.filler.concept,
                obligation.filler.neg,
            )
        });

        if has_equality {
            let equality_evidence = match evidence {
                LeanHtEvidence::Sat => LeanHtEqEvidence::Sat,
                LeanHtEvidence::NonSubsumption { root, sub, sup } => {
                    LeanHtEqEvidence::NonSubsumption { root, sub, sup }
                }
                LeanHtEvidence::SatisfiableConcept { root, concept } => {
                    LeanHtEqEvidence::SatisfiableConcept { root, concept }
                }
                _ => {
                    return Err(
                        "HT Lean equality SAT certificates cannot encode refutation evidence"
                            .to_string(),
                    );
                }
            };
            let node_count = self.ext.num_nodes();
            let mut equalities = Vec::new();
            let mut representative_paths = Vec::with_capacity(node_count);
            for node in 0..node_count {
                let mut path = Vec::new();
                let mut current = node;
                while let Some(parent) = self.ext.merged[current] {
                    equalities.push(LeanHtEquality {
                        left: current,
                        right: parent,
                    });
                    path.push(parent);
                    current = parent;
                }
                representative_paths.push(path);
            }
            equalities.sort_unstable_by_key(|equality| (equality.left, equality.right));
            equalities.dedup_by_key(|equality| (equality.left, equality.right));
            let representatives = (0..node_count)
                .map(|node| self.ext.resolve(node))
                .collect();
            return serde_json::to_string(&LeanHtEqCertificate {
                version: 2,
                node_count,
                concept_count,
                role_count,
                variable_count,
                ontology,
                state: LeanHtEqState {
                    labels,
                    edges,
                    obligations,
                    equalities,
                    representatives,
                    representative_paths,
                },
                evidence: equality_evidence,
            })
            .map_err(|error| error.to_string());
        }

        serde_json::to_string(&LeanHtCertificate {
            version: 1,
            node_count: self.ext.num_nodes(),
            concept_count,
            role_count,
            variable_count,
            ontology,
            labels,
            edges,
            obligations,
            evidence,
        })
        .map_err(|error| error.to_string())
    }

    pub fn lean_sat_certificate_json(&self) -> Result<String, String> {
        self.lean_sat_certificate_json_with_evidence(LeanHtEvidence::Sat)
    }

    /// Serialize a checked countermodel for `sub ⋢ sup` from the terminal
    /// graph of a successful `{sub, ¬sup}` consistency probe.
    pub fn lean_non_subsumption_certificate_json(
        &self,
        sub: C,
        sup: C,
    ) -> Result<String, String> {
        let root = self
            .ext
            .concepts
            .first()
            .ok_or_else(|| "HT Lean countermodel has no query root".to_string())?;
        if !root.contains_key(&CLit { c: sub, neg: false })
            || !root.contains_key(&CLit { c: sup, neg: true })
        {
            return Err("HT Lean countermodel does not contain the declared query".to_string());
        }
        self.lean_sat_certificate_json_with_evidence(LeanHtEvidence::NonSubsumption {
            root: 0,
            sub: sub as usize,
            sup: sup as usize,
        })
    }

    /// Serialize a checked model of `concept` from the terminal graph of a
    /// successful `{concept}` consistency probe.
    pub fn lean_satisfiable_concept_certificate_json(
        &self,
        concept: C,
    ) -> Result<String, String> {
        let root = self
            .ext
            .concepts
            .first()
            .ok_or_else(|| "HT Lean concept model has no query root".to_string())?;
        if !root.contains_key(&CLit {
            c: concept,
            neg: false,
        }) {
            return Err("HT Lean concept model does not contain the declared concept".to_string());
        }
        self.lean_sat_certificate_json_with_evidence(LeanHtEvidence::SatisfiableConcept {
            root: 0,
            concept: concept as usize,
        })
    }

    /// Produce a complete checker-ready named taxonomy. Every concept and every
    /// ordered pair receives either a bounded refutation or a checked finite
    /// countermodel. Failure of any cell rejects the entire matrix.
    pub fn lean_taxonomy_certificate_json(&mut self, named: &[C]) -> Result<String, String> {
        if named.is_empty() {
            return Err("HT Lean taxonomy certificate requires named concepts".to_string());
        }
        let mut unique = HashSet::with_capacity(named.len());
        if !named.iter().all(|concept| unique.insert(*concept)) {
            return Err("HT Lean taxonomy certificate requires unique named concepts".to_string());
        }

        let payload = |document: String| -> Result<
            (
                serde_json::Value,
                Option<serde_json::Value>,
                serde_json::Value,
                bool,
            ),
            String,
        > {
            let value: serde_json::Value =
                serde_json::from_str(&document).map_err(|error| error.to_string())?;
            let object = value
                .as_object()
                .ok_or_else(|| "HT Lean query certificate is not an object".to_string())?;
            let version = object
                .get("version")
                .and_then(serde_json::Value::as_u64)
                .ok_or_else(|| "HT Lean query certificate has no numeric version".to_string())?;
            match version {
                1 => {
                    let query = serde_json::json!({
                        "node_count": object.get("node_count").cloned().ok_or("missing node_count")?,
                        "labels": object.get("labels").cloned().ok_or("missing labels")?,
                        "edges": object.get("edges").cloned().ok_or("missing edges")?,
                        "obligations": object.get("obligations").cloned().ok_or("missing obligations")?,
                        "evidence": object.get("evidence").cloned().ok_or("missing evidence")?,
                    });
                    let mixed = serde_json::json!({ "plain": { "payload": query.clone() } });
                    Ok((value, Some(query), mixed, false))
                }
                2 => {
                    let mixed = serde_json::json!({
                        "equality": {
                            "node_count": object.get("node_count").cloned().ok_or("missing node_count")?,
                            "state": object.get("state").cloned().ok_or("missing equality state")?,
                            "evidence": object.get("evidence").cloned().ok_or("missing evidence")?,
                        }
                    });
                    Ok((value, None, mixed, true))
                }
                other => Err(format!("unsupported HT query certificate version {other}")),
            }
        };

        let mut legacy_concepts = Vec::with_capacity(named.len());
        let mut mixed_concepts = Vec::with_capacity(named.len());
        let mut legacy_subsumptions = Vec::with_capacity(named.len());
        let mut mixed_subsumptions = Vec::with_capacity(named.len());
        let mut base: Option<serde_json::Value> = None;
        let mut concept_count = 0u64;
        let mut has_equality = false;

        let mut note_document = |document: String| -> Result<
            (Option<serde_json::Value>, serde_json::Value),
            String,
        > {
                let (full, legacy, mixed, equality) = payload(document)?;
                has_equality |= equality;
                concept_count = concept_count.max(
                    full["concept_count"]
                        .as_u64()
                        .ok_or_else(|| "invalid concept_count".to_string())?,
                );
                if let Some(previous) = &base {
                    for field in ["role_count", "variable_count", "ontology"] {
                        if previous[field] != full[field] {
                            return Err(format!(
                                "HT Lean taxonomy query changed shared {field}"
                            ));
                        }
                    }
                } else {
                    base = Some(full);
                }
                Ok((legacy, mixed))
            };

        for &concept in named {
            let satisfiable = self
                .consistent(&[CLit::pos(concept)])
                .ok_or_else(|| "HT concept probe left the certified fragment".to_string())?;
            let document = if satisfiable {
                self.lean_satisfiable_concept_certificate_json(concept)?
            } else {
                self.lean_unsatisfiable_concept_certificate_json(concept)?
            };
            let (legacy, mixed) = note_document(document)?;
            legacy_concepts.push(legacy);
            mixed_concepts.push(mixed);
        }

        for &sub in named {
            let mut legacy_row = Vec::with_capacity(named.len());
            let mut mixed_row = Vec::with_capacity(named.len());
            for &sup in named {
                let satisfiable = self
                    .consistent(&[CLit::pos(sub), CLit { c: sup, neg: true }])
                    .ok_or_else(|| "HT subsumption probe left the certified fragment".to_string())?;
                let document = if satisfiable {
                    self.lean_non_subsumption_certificate_json(sub, sup)?
                } else {
                    self.lean_subsumption_certificate_json(sub, sup)?
                };
                let (legacy, mixed) = note_document(document)?;
                legacy_row.push(legacy);
                mixed_row.push(mixed);
            }
            legacy_subsumptions.push(legacy_row);
            mixed_subsumptions.push(mixed_row);
        }

        let base = base.ok_or_else(|| "HT Lean taxonomy has no evidence".to_string())?;
        concept_count = concept_count.max(
            named
                .iter()
                .map(|&concept| concept as u64 + 1)
                .max()
                .unwrap_or(0),
        );
        let (version, concepts, subsumptions) = if has_equality {
            (2, mixed_concepts, mixed_subsumptions)
        } else {
            let concepts = legacy_concepts
                .into_iter()
                .map(|payload| payload.ok_or_else(|| "missing version-1 concept payload".to_string()))
                .collect::<Result<Vec<_>, _>>()?;
            let subsumptions = legacy_subsumptions
                .into_iter()
                .map(|row| {
                    row.into_iter()
                        .map(|payload| payload.ok_or_else(|| "missing version-1 subsumption payload".to_string()))
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?;
            (1, concepts, subsumptions)
        };
        serde_json::to_string(&serde_json::json!({
            "version": version,
            "concept_count": concept_count,
            "role_count": base["role_count"],
            "variable_count": base["variable_count"],
            "ontology": base["ontology"],
            "named": named.iter().map(|&concept| concept as usize).collect::<Vec<_>>(),
            "concepts": concepts,
            "subsumptions": subsumptions,
        }))
        .map_err(|error| error.to_string())
    }

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
                let nhc = rec
                    .0
                    .head
                    .iter()
                    .filter(|a| matches!(a, Atom::Concept { .. }))
                    .count();
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
        for clause in &mut clauses {
            eliminate_body_equalities(clause);
        }
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
        // KM_KEEP_CHAIN_AXIOMS chain-unfolding is applied via `set_chains` (after
        // construction, when the TInput side data is available).  See `set_chains`.

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
                let nhc = rec
                    .0
                    .head
                    .iter()
                    .filter(|a| matches!(a, Atom::Concept { .. }))
                    .count();
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
        let forall_idx = index_forall(&clauses);
        let cert_number_roles: HashSet<R> = clauses
            .iter()
            .filter(|clause| clause.head.iter().any(|atom| matches!(atom, Atom::Eq { .. })))
            .flat_map(|clause| {
                clause.body.iter().filter_map(|atom| match atom {
                    Atom::Role { r, .. } => Some(*r),
                    _ => None,
                })
            })
            .collect();
        let ht = Ht {
            clauses: recs,
            forall_idx,
            card_defs: HashMap::new(),
            card: std::env::var_os("KM_NO_HT_CARD").is_none(),
            card_recog: std::env::var_os("KM_NO_HT_CARD_RECOG").is_none(),
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
            // KM_HT_AUTOBLOCK (port of Konclude's default `mConfOptimizedSubSetBlocking
            // = true`): when the clause set has inverse roles (bridging clauses) and
            // the mode is not explicitly pinned, select the SOUND-under-inverse
            // optimized blocking (mode 5) instead of the subset default (mode 1, which
            // is unsound under inverse). An explicit KM_HT_BLOCK / KM_HT_SUBSET_BLOCK
            // always wins. Gated (default off) so the validated default path is
            // unchanged until the routing is ORE-validated.
            block_mode: if std::env::var_os("KM_HT_SUBSET_BLOCK").is_some() {
                1
            } else if std::env::var_os("KM_HT_BLOCK").is_some() {
                env_u8("KM_HT_BLOCK", 1)
            } else if std::env::var_os("KM_HT_AUTOBLOCK").is_some() && has_inverse_bridge(&clauses)
            {
                5
            } else {
                1
            },
            cache: HashMap::new(),
            steps: 0,
            backtracks: 0,
            backjumps: 0,
            negfired: 0,
            branch_pushes: 0,
            disjunct_tries: 0,
            block_us: 0,
            cert_no_blocking: std::env::var_os("KM_HT_CERT_NO_BLOCKING").is_some(),
            cert_number_roles,
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
            hb: std::env::var("KM_HT_HB")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(200_000),
            tick: 0,
            cur_depth: 0,
            activity: HashMap::new(),
            ord_mode: env_u8("KM_HT_ORD", 0),
            pick_mode: env_u8("KM_HT_PICK", 0),
            do_restart: std::env::var_os("KM_HT_RESTART").is_some(),
            rbase: std::env::var("KM_HT_RBASE")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(200),
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
            satcache3: std::env::var_os("KM_HT_SATCACHE3").is_some(),
            sat_sigs3: HashSet::new(),
            sc3_pooled: 0,
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
            force_qmerge: false,
            force_number: false,
            sat_labels: Vec::new(),
            satfold_watch: HashMap::new(),
            satfold_hits: 0,
            nom_set: Vec::new(),
            native_abox: NativeAboxState::default(),
            qo_edge_chains: Vec::new(),
            ht_chain_fwd: HashMap::new(),
            ht_chain_bwd: HashMap::new(),
            ht_tcc_clauses: Vec::new(),
        };
        if ht.trace {
            let (mut hrole, mut heq, mut hexists, mut hdisj, mut hdisj_ex) = (0, 0, 0, 0, 0);
            for (c, _, _) in &ht.clauses {
                let nrole = c
                    .head
                    .iter()
                    .filter(|a| matches!(a, Atom::Role { .. }))
                    .count();
                let neq = c
                    .head
                    .iter()
                    .filter(|a| matches!(a, Atom::Eq { .. }))
                    .count();
                let nex = c
                    .head
                    .iter()
                    .filter(|a| matches!(a, Atom::Exists { .. }))
                    .count();
                if nrole > 0 {
                    hrole += 1;
                }
                if neq > 0 {
                    heq += 1;
                }
                if nex > 0 {
                    hexists += 1;
                }
                if c.head.len() >= 2 {
                    hdisj += 1;
                }
                if c.head.len() >= 2 && nex > 0 {
                    hdisj_ex += 1;
                }
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

    /// KM_QO_EDGE_COMPOSE: install the chain edge-composition indexes directly
    /// (for fresh Ht workers, e.g. the residue-complete tableau, that don't run
    /// `set_chains`).  Copies the forward/backward chain indexes built by the
    /// parent Ht's `set_chains`.
    pub fn set_edge_compose(&mut self, fwd: HashMap<R, Vec<(R, R)>>, bwd: HashMap<R, Vec<(R, R)>>) {
        if !fwd.is_empty() {
            self.ht_chain_fwd = fwd;
            self.ht_chain_bwd = bwd;
        }
    }

    /// Ht-only TCC: extend the clause template with the `__cmpp__` clauses (stored
    /// separately so QoSat never sees them).  Called by the residue workers + the
    /// TESTONE path so the Ht complete-tableau (with blocking) propagates the
    /// transitive markers through cross-role chains, deriving the chain subsumers
    /// the shared-filler QoSat misses.
    pub fn set_tcc_clauses(&mut self, tcc: Vec<Clause>) {
        if !tcc.is_empty() {
            self.ht_tcc_clauses = tcc;
        }
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

    /// Force the n≥2 qualified ≤n merge branch on, independent of KM_HT_QMERGE.
    pub fn set_qmerge(&mut self) {
        self.force_qmerge = true;
    }

    /// Enable qualified-cardinality handling (≤n / ≥n recognition / functional)
    /// when the input KB is a number KB, independent of the KM_HT_NUMBER /
    /// KM_HT_QMERGE env flags. The ≥n / ≤n recognition heads need the merge branch,
    /// so this also forces qmerge on. Inert when `on` is false.
    pub fn set_number(&mut self, on: bool) {
        if on {
            self.force_number = true;
            self.force_qmerge = true;
        }
    }

    /// KM_HT_CARD: install the first-class number restrictions (marker concept →
    /// `CardDef`) and enable the Konclude number rules. Called by cb_to_ht (and by
    /// the unit tests) to feed `≥n`/`≤n` as first-class concepts rather than the
    /// clausified `⋁ Eq` pigeonhole.
    pub fn set_card_defs(&mut self, defs: HashMap<C, CardDef>) {
        self.cert_number_roles
            .extend(defs.values().map(|definition| definition.role));
        self.card_defs = defs;
        self.card = true;
    }

    /// KM_KEEP_CHAIN_AXIOMS: install the detected role chains `(R1,R2,R)` and
    /// transitive roles, and emit the chain-unfolding clauses (faithful port of
    /// Konclude's generateRoleChainAutomatConcept).  For each ∀R.C clause
    /// `D(x) ∧ R(x,y) → C(y)` and chain R1∘R2⊑R, emit:
    ///   `D(x) ∧ R1(x,y) → M2(y)` + `M2(x) ∧ R2(x,y) → C(y)`
    /// so ∀R.C ≡ ∀R1.∀R2.C propagates through generated successors (the Ht
    /// creates per-edge successors, no shared-filler pollution).  Sound
    /// (R1∘R2⊑R ⟹ ∀R.C ⊑ ∀R1.∀R2.C).  Rebuilds the trigger indexes after
    /// appending the clauses.
    pub fn set_chains(&mut self, chains: Vec<(R, R, R)>, transitive: Vec<R>) {
        // Store the CROSS-ROLE chains for QoSat edge-composition (KM_QO_EDGE_COMPOSE).
        // Transitive self-chains R∘R⊑R are EXCLUDED: they create the full transitive
        // edge closure, which cascades on shared-filler QoSat (no blocking) — the
        // ∀-propagation of transitive roles is already handled by
        // `transitivity_clauses`.  The 71 missing subsumptions on 14817 need only
        // the cross-role chain `part∘dev⊑dev` (anonymous-successor composition),
        // not the transitive self-composition.
        let edge_chains: Vec<(R, R, R)> = chains
            .iter()
            .filter(|(r1, r2, _)| !(r1 == r2 && transitive.contains(r1)))
            .copied()
            .collect();
        if !edge_chains.is_empty() {
            self.qo_edge_chains = edge_chains;
        }
        // Ht path (complete tableau, bounded by blocking): use ALL chains incl.
        // transitive self-chains R∘R⊑R.  The Ht's subset-blocking bounds the
        // model, so the composition fixpoint converges (unlike shared-filler QoSat).
        if std::env::var_os("KM_HT_EDGE_COMPOSE").is_some() {
            let mut all_chains = chains.clone();
            for &r in &transitive {
                all_chains.push((r, r, r));
            }
            for (r1, r2, hr) in &all_chains {
                self.ht_chain_fwd.entry(*r1).or_default().push((*r2, *hr));
                self.ht_chain_bwd.entry(*r2).or_default().push((*r1, *hr));
            }
        }
        if chains.is_empty() && transitive.is_empty() {
            return;
        }
        let clauses: Vec<Clause> = self.clauses.iter().map(|(c, _, _)| c.clone()).collect();
        // Ht-only transitive-chain compose (__cmpp__ clauses): propagate the
        // transitive markers through cross-role chains.  Stored separately
        // (ht_tcc_clauses) so QoSat never sees them (cascade); the Ht residue
        // workers extend their template with these.
        let tcc = ht_transitive_chain_compose(&clauses, &chains, &transitive);
        // The ∀-unfolding clauses (ht_chain_unfolding_clauses) are ALSO Ht-only:
        // they cascade on the shared-filler QoSat (the ∀R1.∀R2.C propagation
        // through high-fanout creation roles).  Store them alongside the TCC
        // clauses so ONLY the Ht residue workers (with blocking) see them.
        let unfold = if chains.is_empty() {
            Vec::new()
        } else {
            ht_chain_unfolding_clauses(&clauses, &chains, &transitive)
        };
        let mut ht_only: Vec<Clause> = tcc;
        ht_only.extend(unfold);
        if !ht_only.is_empty() {
            if std::env::var_os("KM_HT_STATS").is_some() {
                eprintln!("KM_HT_STATS ht-only (tcc+unfold) clauses={}", ht_only.len());
            }
            self.ht_tcc_clauses = ht_only;
        }
    }

    /// KM_HT_CARD: install number restrictions from the cb_to_ht TInput, whose
    /// `card_defs` carry plain ids (the `CardDef`/`CardKind` types are private).
    /// Each tuple is `(marker, is_min, n, role, filler)`; fillers are positive
    /// (the frontend reifies `≥n role.C` with a positive marker `C`).
    pub fn set_card_defs_raw(&mut self, defs: &[(C, bool, u32, R, C)]) {
        let mut map: HashMap<C, CardDef> = HashMap::new();
        for &(marker, is_min, n, role, filler) in defs {
            map.insert(
                marker,
                CardDef {
                    kind: if is_min { CardKind::Min } else { CardKind::Max },
                    n,
                    role,
                    filler: CLit {
                        neg: false,
                        c: filler,
                    },
                },
            );
        }
        self.set_card_defs(map);
    }

    /// Provide the nominal concept ids (the o-rule singletons `{o}`). Re-applied to
    /// the per-query `Ext` in `consistent`; empty ⇒ inert.
    pub fn set_nominals(&mut self, noms: Vec<C>) {
        self.nom_set = noms;
    }

    /// Install a complete, already-id-validated named-individual ABox.  This is
    /// inert when all vectors are empty.  The caller must withhold this setter
    /// for a partial payload; the route gate enforces that contract.
    pub fn set_native_abox(
        &mut self,
        individuals: Vec<(Vec<C>, Vec<C>)>,
        different: Vec<(usize, usize)>,
        role_assertions: Vec<(R, usize, usize)>,
    ) {
        self.native_abox = NativeAboxState {
            individuals,
            different,
            role_assertions,
        };
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
                eprintln!(
                    "KM_HT [satfold] labels={} hits={}",
                    self.sat_labels.len(),
                    self.satfold_hits
                );
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
    /// B2a of Konclude optimized blocking (KM_HT_BLOCK=5): for every role `r` on an
    /// edge from `w` back to its predecessor `v` (the inverse/own-role direction —
    /// present only when inverse materialises a w→v edge), and every ∀r.D the
    /// candidate blocker `wp` carries (some `C0 ∈ L(wp)` with a `(C0,r)→D` clause in
    /// `forall_idx`), `v` must already carry `D`. Vacuously true when `w` has no edge
    /// back to `v` (no inverse) ⇒ B1 subset alone suffices. See
    /// docs/KONCLUDE-BLOCKING-SPEC.md.
    fn b2a_holds(&self, w: Node, wp: Node, v: Node) -> bool {
        for (r, t, _) in &self.ext.out_edges[w] {
            if *t != v {
                continue;
            }
            for c0 in self.ext.concepts[wp].keys() {
                if let Some(heads) = self.forall_idx.get(&(*c0, *r)) {
                    for d in heads {
                        if !self.ext.concepts[v].contains_key(d) {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }

    /// Conservative detector for the missing SHOIQ nominal-introduction rule.
    ///
    /// An NI premise can arise when an at-most restriction on a root individual
    /// produces an annotated equality involving a blockable role neighbour that
    /// is *not* a direct successor of that root. Direct successors are explicitly
    /// excluded by the NI rule and are handled by ordinary equality merging.
    ///
    /// We do not retain equality annotations, so this deliberately
    /// over-approximates: any live non-successor blockable neighbour along a role
    /// that occurs in an equality-head clause makes the worker defer.
    fn nominal_number_non_successor(&self) -> bool {
        if self.cert_number_roles.is_empty() {
            return false;
        }
        for raw_source in 0..self.ext.num_nodes() {
            let source = self.ext.resolve(raw_source);
            if source != raw_source
                || self.ext.blockable[source]
                || self.ext.merged[source].is_some()
            {
                continue;
            }
            for &(role, raw_target, _) in &self.ext.out_edges[source] {
                if !self.cert_number_roles.contains(&role) {
                    continue;
                }
                let target = self.ext.resolve(raw_target);
                if target == source
                    || !self.ext.blockable[target]
                    || self.ext.merged[target].is_some()
                {
                    continue;
                }
                let direct_successor = self.ext.pred[target]
                    .map(|parent| self.ext.resolve(parent) == source)
                    .unwrap_or(false);
                if !direct_successor {
                    if self.trace {
                        eprintln!(
                            "TR cert-ni-risk non-successor source={} role={} target={} pred={:?}",
                            source, role, target, self.ext.pred[target]
                        );
                    }
                    return true;
                }
            }
        }
        false
    }

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
            let mut seen: HashSet<Vec<u64>> = HashSet::with_capacity(nn);
            for n in 0..nn {
                if !self.ext.blockable[n] {
                    continue;
                }
                let p = match self.ext.pred[n] {
                    Some(p) => p,
                    None => continue, // root has no parent edge; never blocked
                };
                // KM_HT_SATCACHE3: a full-label pairwise signature witnessed
                // consistent (unblocked, clash-free) in a prior completed model
                // blocks this node — cross-query saturation reuse for the sound
                // mode-3 route. Checked before the within-model dedup so reuse fires
                // even for the first node carrying the signature in this build.
                if self.satcache3 && self.sat_sigs3.contains(&self.ext.i3_signature_full(n, p)) {
                    blocked[n] = true;
                    continue;
                }
                // shared with the incremental i3_recompute, so the two are identical.
                let sig = self.ext.i3_signature(n, p);
                if !seen.insert(sig) {
                    blocked[n] = true;
                }
            }
        } else if mode == 4 {
            // DOUBLE BLOCKING (mode 4): the SOUND SHIQ pairwise condition for
            // ontologies WITH inverse roles (Horrocks/Sattler/Tobies). Block n by
            // the first earlier unblocked node with an identical FULL-label
            // bidirectional signature: full label(n) = label(m), full label(pred n)
            // = label(pred m), and the pred↔node edge roles match in BOTH directions
            // (`i3_signature_full`). Unlike mode 3 (positive core, sound only without
            // inverse) this matches negatives and the inverse edge, so unraveling the
            // blocker into n's position respects every constraint n carries — sound
            // under inverse + number. Folds less than mode 3 (so larger models), but
            // it is the correct blocking for the inverse-bound family. Hashed O(n).
            let mut seen: HashSet<Vec<u64>> = HashSet::with_capacity(nn);
            for n in 0..nn {
                if !self.ext.blockable[n] {
                    continue;
                }
                let p = match self.ext.pred[n] {
                    Some(p) => p,
                    None => continue,
                };
                let sig = self.ext.i3_signature_full(n, p);
                if self.satcache3 && self.sat_sigs3.contains(&sig) {
                    blocked[n] = true;
                    continue;
                }
                if !seen.insert(sig) {
                    blocked[n] = true;
                }
            }
            // INDIRECT blocking (Horrocks/Sattler/Tobies): a node with a (directly
            // or indirectly) blocked predecessor is itself blocked and must not be
            // expanded — its blocker's unraveling already covers it. This is what
            // makes double blocking TERMINATE under ∀-over-inverse: a backward ∀
            // (∀r⁻.C) completes a node's label only after its successor exists, so
            // the frontier node never *directly* matches an earlier complete node.
            // But once its predecessor directly blocks, the frontier is indirectly
            // blocked and the chain stops. `pred[n] < n` (parent precedes child) so
            // one ascending pass propagates transitively (blocked[pred] is final
            // when we reach n). Clash detection is unaffected — blocking only gates
            // ∃-expansion, never `add_concept`'s clash raise.
            for n in 0..nn {
                if blocked[n] || !self.ext.blockable[n] {
                    continue;
                }
                if let Some(p) = self.ext.pred[n] {
                    if blocked[p] {
                        blocked[n] = true;
                    }
                }
            }
        } else if mode == 5 {
            // KONCLUDE OPTIMIZED BLOCKING port (isLabelConceptOptimizedBlocking):
            // B1 = L(w) ⊆ L(w') (SUBSET, not equality); B2a = for every role r on a
            // w→v edge (v = pred(w), the inverse/own-role direction) and every ∀r.D
            // the blocker w' carries (some C0 ∈ L(w') with a (C0,r)→D clause), the
            // predecessor v already carries D. Subset B1 folds the ∀-over-inverse
            // frontier-lag directly — an incomplete frontier node {B} ⊆ a complete
            // blocker {B,CC} blocks immediately — and B2a keeps subset blocking SOUND
            // under inverse (plain subset is unsound there). Then the indirect pass
            // (Konclude PRFINDIRECTBLOCKED). O(n²·|label|): correctness-first port;
            // Konclude caches via signatures. See docs/KONCLUDE-BLOCKING-SPEC.md.
            // ANYWHERE CANDIDATE-HASH search (Konclude
            // mConfAnywhereBlockingCandidateHashSearch): a blocker w' must satisfy
            // B1 = L(w) ⊆ L(w'), so w' appears in the posting list of EVERY concept
            // of w, hence in the list of w's RAREST concept. Scanning only that list
            // (earlier UNBLOCKED nodes, id order) replaces the O(n²) pairwise scan
            // with O(n · rarest-posting-len) — the same inverted index mode 1 uses —
            // and is RESULT-IDENTICAL: every B1 superset candidate is in the rarest
            // list, scanned in id order, first b2a-passing match wins (= the 0..w
            // first match). The B2a ∀-operand check (inverse soundness) is applied
            // per candidate exactly as before.
            let enc = |k: &CLit| -> usize { ((k.c as usize) << 1) | (k.neg as usize) };
            let mut bb = self.block_buf.borrow_mut();
            let BlockBuf { lists, touched } = &mut *bb;
            for &t in touched.iter() {
                lists[t].clear();
            }
            touched.clear();
            for w in 0..nn {
                let lw = &self.ext.concepts[w];
                if self.ext.blockable[w] && !lw.is_empty() {
                    if let Some(v) = self.ext.pred[w] {
                        let lwlen = lw.len();
                        // rarest concept of w ⇒ shortest candidate posting list.
                        let mut best: usize = usize::MAX;
                        let mut best_len = usize::MAX;
                        for k in lw.keys() {
                            let e = enc(k);
                            let l = lists.get(e).map_or(0, |v| v.len());
                            if l < best_len {
                                best_len = l;
                                best = e;
                            }
                        }
                        if let Some(cands) = lists.get(best) {
                            for &wp in cands {
                                let lwp = &self.ext.concepts[wp];
                                if lwp.len() >= lwlen
                                    && lw.keys().all(|k| lwp.contains_key(k))
                                    && self.b2a_holds(w, wp, v)
                                {
                                    blocked[w] = true;
                                    break;
                                }
                            }
                        }
                    }
                }
                // only earlier UNBLOCKED nodes are candidate blockers.
                if !blocked[w] {
                    for k in self.ext.concepts[w].keys() {
                        let e = enc(k);
                        if e >= lists.len() {
                            lists.resize_with(e + 1, Vec::new);
                        }
                        if lists[e].is_empty() {
                            touched.push(e);
                        }
                        lists[e].push(w);
                    }
                }
            }
            drop(bb);
            for n in 0..nn {
                if blocked[n] || !self.ext.blockable[n] {
                    continue;
                }
                if let Some(p) = self.ext.pred[n] {
                    if blocked[p] {
                        blocked[n] = true;
                    }
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
            eprintln!(
                "KM_HT [blocking] mode={} nodes={} blockable={} blocked={} ({}%)",
                mode,
                nn,
                blk,
                nb,
                if nn > 0 { nb * 100 / nn } else { 0 }
            );
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
                    // KM_HT_CARD: a positive marker concept installs its number
                    // restriction (Konclude's `≥n`/`≤n` concept on the node). ≥n is
                    // a deferred obligation (created on unblocked nodes in
                    // `process_obligations`); ≤n is handled when its role-successors
                    // are counted (`process_card_max`).
                    if self.card && !lit.neg {
                        if let Some(&def) = self.card_defs.get(&lit.c) {
                            let node = self.ext.resolve(n);
                            let dep = self
                                .ext
                                .dep_of(node, lit)
                                .cloned()
                                .unwrap_or_else(dep_empty);
                            let at = self.ext.trail.len();
                            let req = CardReq {
                                n: node,
                                role: def.role,
                                filler: def.filler,
                                bound: def.n,
                                dep,
                                at,
                            };
                            match def.kind {
                                CardKind::Min => self.ext.card_min.push(req),
                                CardKind::Max => self.ext.card_max.push(req),
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
                    // KM_QO_EDGE_COMPOSE: role-automaton edge composition on the
                    // complete-tableau path (bounded by Ht blocking).  A fresh
                    // R-edge (s,t) triggers, for each chain R1∘R2⊑R with R1==r, a
                    // join with every existing R2-edge (t,z) → R-edge (s,z); and
                    // dually for R2==r, a join with every R1-edge (x,s) → R-edge
                    // (x,t).  add_edge dedups + re-queues, so the composition is
                    // monotone and converges (the model is finite under blocking).
                    if !self.ht_chain_fwd.is_empty() {
                        let mut new_edges: Vec<(R, Node, Node)> = Vec::new();
                        if let Some(chains) = self.ht_chain_fwd.get(&r) {
                            for &(r2, hr) in chains {
                                for &(rr, z, _) in &self.ext.out_edges[t] {
                                    if rr == r2 && z != t {
                                        new_edges.push((hr, s, z));
                                    }
                                }
                            }
                        }
                        if let Some(chains) = self.ht_chain_bwd.get(&r) {
                            for &(r1, hr) in chains {
                                for &(rr, x, _) in &self.ext.in_edges[s] {
                                    if rr == r1 && x != s {
                                        new_edges.push((hr, x, t));
                                    }
                                }
                            }
                        }
                        let dep = self
                            .ext
                            .dep_of(s, CLit::pos(0))
                            .cloned()
                            .unwrap_or_else(dep_empty);
                        for (rr, ss, tt) in new_edges {
                            if self.ext.has_clash() {
                                return;
                            }
                            self.ext.add_edge(rr, ss, tt, &dep);
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
                let comp = CLit {
                    neg: !lit.neg,
                    c: lit.c,
                };
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
                    branch = Some(GD {
                        disjuncts: live,
                        dep: dep_union(&bdep, &dead_dep),
                    });
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
                DEval::Branch(live, dep) => {
                    return Scan::Branch(GD {
                        disjuncts: live,
                        dep,
                    })
                }
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
            // KM_HT_SATCACHE3 consults the cross-query pool only in the full
            // `compute_blocked` (it owns `self.sat_sigs3`); fall off the incremental
            // mode-3 path when the cache is live so pooled blocks fire.
            Some(
                if self.ext.incr2
                    && (self.block_mode == 1 || (self.block_mode == 3 && !self.satcache3))
                {
                    // mode 1 = subset (i2_*), mode 3 = pairwise (i3_*); both re-evaluate
                    // only the changed suffix, identical to the full scan.
                    let b = if self.block_mode == 3 {
                        self.ext.i3_recompute()
                    } else {
                        self.ext.i2_recompute()
                    };
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
                            "i{} blocking mismatch: nn={} full_blk={} inc_blk={} first_diff={:?}",
                            self.block_mode,
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
                },
            )
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
        // KM_HT_CARD: ≥n successor creation (Konclude `applyATLEASTRule`), blocked-
        // gated exactly like the ∃ obligations above so a blocked node never spawns
        // cardinality successors (the model-folding the legacy Eq-merge lost).
        if self.card && !self.ext.card_min.is_empty() {
            made |= self.process_card_min(&blocked);
        }
        made
    }

    /// Greedy maximal set of `node`'s `role`-successors that carry `filler` and
    /// are pairwise DISTINCT. A lower bound on the true distinct count (greedy ≤
    /// max-clique), so `len() >= bound` SOUNDLY witnesses that `≥bound role.filler`
    /// already holds — the `applyATLEASTRule` refire guard
    /// (`hasDistinctRoleSuccessorConcepts`). Successors are resolved through merges.
    fn distinct_filler_succ(&self, node: Node, role: R, filler: CLit) -> Vec<Node> {
        let mut succ: Vec<Node> = self.ext.out_edges[node]
            .iter()
            .filter(|&&(r, _, _)| r == role)
            .map(|&(_, t, _)| self.ext.resolve(t))
            .filter(|&t| self.ext.has_concept(t, filler))
            .collect();
        succ.sort_unstable();
        succ.dedup();
        let mut chosen: Vec<Node> = Vec::new();
        for s in succ {
            if chosen
                .iter()
                .all(|&c| self.ext.are_distinct(c, s).is_some())
            {
                chosen.push(s);
            }
        }
        chosen
    }

    /// KM_HT_CARD ≥n rule (Konclude `applyATLEASTRule` + `createDistinctSuccessor`
    /// `Individuals`): for each `≥bound role.filler` obligation on an UNBLOCKED node
    /// that lacks `bound` pairwise-distinct `filler`-successors, create the missing
    /// successors (each `filler`-labelled) and assert the whole set pairwise
    /// distinct. Idempotent: once `bound` distinct successors exist the guard skips.
    fn process_card_min(&mut self, blocked: &Option<Vec<bool>>) -> bool {
        let mut made = false;
        for idx in 0..self.ext.card_min.len() {
            let (n0, role, filler, bound, dep) = {
                let cm = &self.ext.card_min[idx];
                (cm.n, cm.role, cm.filler, cm.bound, cm.dep.clone())
            };
            if bound == 0 {
                continue;
            }
            let node = self.ext.resolve(n0);
            if self.ext.merged[n0].is_some() && self.ext.resolve(n0) != n0 {
                // victim folded into a survivor: the survivor carries the marker
                // and its own card_min entry, so skip this stale one.
                continue;
            }
            let is_blk = match blocked {
                Some(b) => b[node],
                None => ancestor_blocked(&self.ext, node),
            };
            if is_blk {
                continue;
            }
            let mut all = self.distinct_filler_succ(node, role, filler);
            if all.len() as u32 >= bound {
                continue;
            }
            self.heartbeat("card-min");
            while (all.len() as u32) < bound {
                let t = self.ext.new_node(Some(node));
                self.ext.add_edge(role, node, t, &dep);
                self.ext.add_concept(t, filler, &dep);
                if self.ext.has_clash() {
                    return true;
                }
                all.push(t);
            }
            for i in 0..all.len() {
                for j in (i + 1)..all.len() {
                    self.ext.add_distinct(all[i], all[j], &dep);
                    if self.ext.has_clash() {
                        return true;
                    }
                }
            }
            made = true;
        }
        made
    }

    /// KM_HT_CARD ≤n step (Konclude `applyATMOSTRule` + `qualifyMergingIndividual`
    /// `Nodes`/choose), run at `Scan::Sat` where the model is saturated and no
    /// disjunction is pending — so branching one choice here never accumulates a
    /// duplicate. Finds the first still-violated `≤bound role.filler` and branches
    /// ONE step:
    ///   - an UNQUALIFIED `role`-successor (neither `filler` nor `¬filler`) ⇒
    ///     branch it `filler` vs `¬filler` (the choose rule, exact counting);
    ///   - `> bound` qualified successors that are all pairwise DISTINCT ⇒ CLASH
    ///     (the `≤n` cannot be met, no merge is possible);
    ///   - `> bound` qualified successors with a mergeable (non-distinct) pair ⇒
    ///     branch the merge over the candidate pairs (`branch_merge`).
    /// Returns `Some(out)` when it branched or clashed, `None` when every `≤n`
    /// holds (the model is genuinely complete).
    fn card_max_step(&mut self, depth: Level) -> Option<Out> {
        let nreq = self.ext.card_max.len();
        for idx in 0..nreq {
            let (n0, role, filler, bound, mdep) = {
                let cm = &self.ext.card_max[idx];
                (cm.n, cm.role, cm.filler, cm.bound, cm.dep.clone())
            };
            let node = self.ext.resolve(n0);
            let comp = CLit {
                neg: !filler.neg,
                c: filler.c,
            };
            let mut succ: Vec<Node> = self.ext.out_edges[node]
                .iter()
                .filter(|&&(r, _, _)| r == role)
                .map(|&(_, t, _)| self.ext.resolve(t))
                .collect();
            succ.sort_unstable();
            succ.dedup();
            // choose: first successor not yet committed to filler / ¬filler.
            let unqual = succ
                .iter()
                .copied()
                .find(|&s| !self.ext.has_concept(s, filler) && !self.ext.has_concept(s, comp));
            if let Some(s) = unqual {
                let edep = edge_dep(&self.ext, role, node, s).unwrap_or_else(dep_empty);
                let base = dep_union(&mdep, &edep);
                return Some(self.branch_choose(s, filler, &base, depth));
            }
            // all qualified: the filler-carrying successors are the counted ones.
            let cs: Vec<Node> = succ
                .into_iter()
                .filter(|&s| self.ext.has_concept(s, filler))
                .collect();
            if cs.len() as u32 <= bound {
                continue; // this ≤n already holds
            }
            // > bound qualified successors. Collect mergeable (non-distinct) pairs;
            // a missing pair means two are provably distinct (contributes to the
            // clash reason if NO pair is mergeable).
            let mut pairs: Vec<(Node, Node)> = Vec::new();
            let mut distinct_dep = dep_empty();
            for i in 0..cs.len() {
                for j in (i + 1)..cs.len() {
                    match self.ext.are_distinct(cs[i], cs[j]) {
                        Some(dd) => distinct_dep = dep_union(&distinct_dep, &dd),
                        None => {
                            let (a, b) = if cs[i] <= cs[j] {
                                (cs[i], cs[j])
                            } else {
                                (cs[j], cs[i])
                            };
                            pairs.push((a, b));
                        }
                    }
                }
            }
            if pairs.is_empty() {
                // every counted successor is pairwise distinct ⇒ ≤n is unsatisfiable.
                // The clash reason is the ≤n marker + each successor's edge and
                // filler membership + the inequality witnesses (conservative, so a
                // backjump never skips a contributing decision).
                let mut dep = dep_union(&mdep, &distinct_dep);
                for &s in &cs {
                    if let Some(d) = edge_dep(&self.ext, role, node, s) {
                        dep = dep_union(&dep, &d);
                    }
                    if let Some(d) = self.ext.dep_of(s, filler) {
                        dep = dep_union(&dep, d);
                    }
                }
                return Some(self.conflict_out(dep));
            }
            // a merge is possible: branch over which mergeable pair to identify.
            // The base dep carries the ≤n marker plus each counted successor's edge
            // and filler reason, so a merge-induced clash backjumps correctly.
            let mut bdep = mdep.clone();
            for &s in &cs {
                if let Some(d) = edge_dep(&self.ext, role, node, s) {
                    bdep = dep_union(&bdep, &d);
                }
                if let Some(d) = self.ext.dep_of(s, filler) {
                    bdep = dep_union(&bdep, d);
                }
            }
            self.ext.push_card(Vec::new(), pairs, bdep);
            let mid = self.ext.pending_merge.len() - 1;
            return Some(self.branch_merge(mid, depth));
        }
        None
    }

    /// Is `filler` IMPOSSIBLE at node `s` — would asserting it clash given the
    /// current (saturated) model? Used by `card_recog_step` to qualify an otherwise
    /// unqualified `≤n` successor as `¬filler` (so it does not count toward the
    /// bound). Tentatively adds `filler`, propagates the consequences, reads the
    /// clash, then backtracks to leave the model exactly as it was. Returns the
    /// clash dependency when impossible (a sound justification for `¬filler` at
    /// `s`), else `None`. Sound: a purely hypothetical probe with no lasting effect.
    fn filler_impossible(&mut self, s: Node, filler: CLit) -> Option<DepSet> {
        let comp = CLit {
            neg: !filler.neg,
            c: filler.c,
        };
        if self.ext.has_concept(s, comp) {
            return Some(self.ext.dep_of(s, comp).cloned().unwrap_or_else(dep_empty));
        }
        if self.ext.has_concept(s, filler) {
            return None;
        }
        let mark = self.ext.trail.len();
        let saved_clash = self.ext.clash.take(); // None at Scan::Sat
        self.ext.add_concept(s, filler, &dep_empty());
        self.propagate();
        let result = self.ext.clash.take();
        self.ext.queue.clear();
        self.ext.backtrack_to(mark);
        self.ext.clash = saved_clash;
        result
    }

    /// KM_HT_CARD_RECOG: propagation-based `≤n` RECOGNITION. Run only at a saturated
    /// model (`Scan::Sat`), where every node's `r.F`-successor count is FINAL. For
    /// each `≤n role.filler` marker `Q` (a `Max` `card_def`) and each canonical node
    /// `v` not already carrying `Q`, count `v`'s distinct `role`-successors: those
    /// provably carrying `filler` (definite), those carrying `¬filler` (excluded),
    /// and the still-unqualified rest. If `definite + unqualified ≤ n`, then AT MOST
    /// `n` of them can be the filler in any extension, so `≤n role.filler` holds and
    /// we DERIVE `Q` deterministically (no branch). This replaces the frontend's
    /// `⊤→Q∨NQ` excluded middle (dropped by cb_to_ht under the same flag), which
    /// branched on every node. Sound: deriving `Q` only enables the first-class `≤n`
    /// enforcement (`card_max`) + the recognition chains, both of which already hold
    /// for a node that satisfies `≤n`; any later branch that pushes the count over
    /// `n` clashes against that enforcement with `Q`'s conservative dep, so
    /// backjumping stays correct. Monotone (markers are only ever added), so it
    /// reaches a fixpoint. Returns true iff it derived a new marker.
    fn card_recog_step(&mut self) -> bool {
        if self.card_defs.is_empty() {
            return false;
        }
        let maxdefs: Vec<(C, CardDef)> = self
            .card_defs
            .iter()
            .filter(|(_, d)| d.kind == CardKind::Max)
            .map(|(&c, &d)| (c, d))
            .collect();
        if maxdefs.is_empty() {
            return false;
        }
        let nn = self.ext.num_nodes();
        if std::env::var_os("KM_HT_RECOG_DBG").is_some() {
            eprintln!(
                "RECOG_STEP card_defs={} maxdefs={} nn={}",
                self.card_defs.len(),
                maxdefs.len(),
                nn
            );
        }
        let mut made = false;
        for raw in 0..nn {
            let v = self.ext.resolve(raw);
            // canonical nodes only (a merged victim is dead; its survivor is visited).
            if v != raw || self.ext.merged[v].is_some() {
                continue;
            }
            for &(marker, def) in &maxdefs {
                let qlit = CLit {
                    neg: false,
                    c: marker,
                };
                if self.ext.has_concept(v, qlit) {
                    continue;
                }
                let comp = CLit {
                    neg: !def.filler.neg,
                    c: def.filler.c,
                };
                let mut succ: Vec<Node> = self.ext.out_edges[v]
                    .iter()
                    .filter(|&&(r, _, _)| r == def.role)
                    .map(|&(_, t, _)| self.ext.resolve(t))
                    .collect();
                succ.sort_unstable();
                succ.dedup();
                // Classify successors first (owned `succ`, cloned deps) so no `ext`
                // borrow is held across the mutating `filler_impossible` probe.
                let mut definite: u32 = 0;
                let mut dep = dep_empty();
                let mut unqual: Vec<Node> = Vec::new();
                for &s in &succ {
                    let edep = edge_dep(&self.ext, def.role, v, s);
                    if self.ext.has_concept(s, def.filler) {
                        definite += 1;
                        if let Some(d) = edep {
                            dep = dep_union(&dep, &d);
                        }
                        if let Some(d) = self.ext.dep_of(s, def.filler) {
                            dep = dep_union(&dep, d);
                        }
                    } else if self.ext.has_concept(s, comp) {
                        if let Some(d) = edep {
                            dep = dep_union(&dep, &d);
                        }
                        if let Some(d) = self.ext.dep_of(s, comp) {
                            dep = dep_union(&dep, d);
                        }
                    } else {
                        if let Some(d) = edep {
                            dep = dep_union(&dep, &d);
                        }
                        unqual.push(s);
                    }
                }
                if definite > def.n {
                    continue; // already over the bound — `v` does not satisfy `≤n`.
                }
                // An unqualified successor that CANNOT carry the filler (asserting it
                // clashes, e.g. a disjoint-class successor) is provably `¬filler` and
                // does not count; one that could be the filler does.
                let mut could = definite;
                for &s in &unqual {
                    match self.filler_impossible(s, def.filler) {
                        Some(cdep) => dep = dep_union(&dep, &cdep),
                        None => could += 1,
                    }
                    if could > def.n {
                        break;
                    }
                }
                if std::env::var_os("KM_HT_RECOG_DBG").is_some() && !succ.is_empty() {
                    eprintln!(
                        "RECOG node={} marker={} role={} filler={} n={} succ={} could={} -> {}",
                        v,
                        marker,
                        def.role,
                        def.filler.c,
                        def.n,
                        succ.len(),
                        could,
                        if could <= def.n { "DERIVE" } else { "skip" }
                    );
                }
                if could <= def.n && self.ext.add_concept(v, qlit, &dep) {
                    made = true;
                }
            }
        }
        made
    }

    /// KM_HT_CARD choose branch (Konclude `applyAutomatChooseRule`): a `≤n`-counted
    /// successor `s` must commit to `filler` or `¬filler` for exact counting. Try
    /// `filler` first, then `¬filler`; standard dependency-directed backjump (mirror
    /// of `branch_merge`'s two-option loop).
    fn branch_choose(&mut self, s: Node, filler: CLit, base: &DepSet, depth: Level) -> Out {
        let level = depth + 1;
        let comp = CLit {
            neg: !filler.neg,
            c: filler.c,
        };
        self.branch_pushes += 1;
        let mut fail = dep_empty();
        for &lit in &[filler, comp] {
            self.disjunct_tries += 1;
            let mark = self.ext.mark();
            let dep = dep_add(base, level);
            self.ext.add_concept(s, lit, &dep);
            let sub = self.dfs(level);
            match sub {
                Out::Sat => return Out::Sat,
                Out::Restart => {
                    self.ext.backtrack_to(mark);
                    return Out::Restart;
                }
                Out::Conflict(cd) => {
                    self.backtracks += 1;
                    self.ext.backtrack_to(mark);
                    if !dep_contains(&cd, level) {
                        self.backjumps += 1;
                        return Out::Conflict(cd);
                    }
                    fail = dep_union(&fail, &cd);
                }
            }
        }
        Out::Conflict(dep_remove(&fail, level))
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
        if self.stats && std::env::var_os("KM_HT_DEPSTATS").is_some() && self.conflicts % 2000 == 0
        {
            // dump the conflict's decision levels + their nodes: are the ~6 culprit
            // decisions at low/stable nodes (node-keyed learning suffices once
            // staleness is fixed) or scattered across recreated deep nodes
            // (label-keyed learning required)? Also the level spread vs depth.
            let mut lv: Vec<(Level, Node)> = Vec::new();
            let mut cur = &cd;
            while let Some(n) = cur {
                let l = n.level as usize;
                let nd = if l < self.decisions.len() {
                    self.decisions[l].0
                } else {
                    usize::MAX
                };
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
            self.decisions
                .resize(l + 1, (0, 0, CLit { neg: false, c: 0 }));
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
            let comp = CLit {
                neg: !other.2.neg,
                c: other.2.c,
            };
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

    /// Scan pending ≤n merge choices for one not yet satisfied (no candidate pair
    /// already identified). Returns its index, or None if all are satisfied. A
    /// satisfied entry needs no branch: identifying any one of its n+1 successors
    /// leaves n distinct, so the AtMost holds.
    fn next_merge(&self) -> Option<usize> {
        for (id, md) in self.ext.pending_merge.iter().enumerate() {
            // satisfied if some candidate pair is already identified, OR (for a ≥n
            // recognition) the recognized concept is already present.
            let pair_sat = md
                .pairs
                .iter()
                .any(|&(a, b)| self.ext.resolve(a) == self.ext.resolve(b));
            let con_sat = md
                .concepts
                .iter()
                .any(|&(n, lit)| self.ext.has_concept(self.ext.resolve(n), lit));
            if !pair_sat && !con_sat {
                return Some(id);
            }
        }
        None
    }

    /// Branch a deferred qualified-cardinality choice: try each live option in
    /// turn. For a ≤n AtMost the options are the candidate successor pairs (the
    /// AtMost rule's non-deterministic merge); for a ≥n recognition (`≥n r.F ⊑ Q`)
    /// they additionally include asserting the recognized concept `Q`. A forbidden
    /// identification clashes via the ≥m distinctness clauses (`⊥ ⟵ Eq(yi,yj)`),
    /// forcing the next option; if every option clashes the choice is unsatisfiable
    /// here. Mirrors the concept-disjunction branch: mark / apply / recurse,
    /// backjump when the conflict is independent of this level, else accumulate.
    fn branch_merge(&mut self, mid: usize, depth: Level) -> Out {
        let level = depth + 1;
        let pairs = self.ext.pending_merge[mid].pairs.clone();
        let concepts = self.ext.pending_merge[mid].concepts.clone();
        let bdep = self.ext.pending_merge[mid].bdep.clone();
        // Recompute liveness (the model changed since the push). A satisfied option
        // — the recognized concept already present, or a pair already identified —
        // discharges the choice with no new decision. A dead recognized concept
        // (its complement present) folds its reason into the branch dep.
        let mut dead = dep_empty();
        let mut options: Vec<MergeChoice> = Vec::new();
        for &(n, lit) in &concepts {
            let rn = self.ext.resolve(n);
            if self.ext.has_concept(rn, lit) {
                return self.dfs(depth);
            }
            let comp = CLit {
                neg: !lit.neg,
                c: lit.c,
            };
            if let Some(d) = self.ext.dep_of(rn, comp) {
                dead = dep_union(&dead, d);
            } else {
                options.push(MergeChoice::Concept(rn, lit));
            }
        }
        for &(a, b) in &pairs {
            let ra = self.ext.resolve(a);
            let rb = self.ext.resolve(b);
            if ra == rb {
                return self.dfs(depth);
            }
            options.push(MergeChoice::Merge(ra, rb));
        }
        let gddep = dep_union(&bdep, &dead);
        if options.is_empty() {
            // no live option (all recognized concepts dead, no candidate pair):
            // the disjunction is empty ⇒ clash on the folded reason.
            return self.conflict_out(gddep);
        }
        self.branch_pushes += 1;
        let mut fail = dep_empty();
        for opt in &options {
            self.disjunct_tries += 1;
            let mark = self.ext.mark();
            let dep = dep_add(&gddep, level);
            match *opt {
                MergeChoice::Concept(n, lit) => {
                    self.ext.add_concept(n, lit, &dep);
                }
                MergeChoice::Merge(a, b) => self.ext.merge_into(a, b, &dep),
            }
            // dfs's head re-propagates and detects any merge-/assertion-induced clash.
            let sub = self.dfs(level);
            match sub {
                Out::Sat => return Out::Sat,
                Out::Restart => {
                    self.ext.backtrack_to(mark);
                    return Out::Restart;
                }
                Out::Conflict(cd) => {
                    self.backtracks += 1;
                    self.ext.backtrack_to(mark);
                    if !dep_contains(&cd, level) {
                        self.backjumps += 1;
                        return Out::Conflict(cd);
                    }
                    fail = dep_union(&fail, &cd);
                }
            }
        }
        Out::Conflict(dep_remove(&fail, level))
    }

    fn dfs(&mut self, depth: Level) -> Out {
        loop {
            self.steps += 1;
            self.cur_depth = depth;
            self.heartbeat("dfs");
            if self.trace {
                eprintln!(
                    "TR dfs depth={} step={} pending={}",
                    depth,
                    self.steps,
                    self.ext.pending.len()
                );
            }
            let _pt0 = Instant::now();
            self.propagate();
            self.prop_us += _pt0.elapsed().as_micros();
            if self.ext.has_clash() {
                if self.trace {
                    eprintln!("TR prop-clash depth={}", depth);
                }
                return self.conflict_out(self.ext.clash_dep());
            }
            // Nominals (o-rule): deterministically merge nominal carriers before
            // expanding obligations / branching, so a singleton's identity is fixed
            // (and a resulting clash found early). Re-propagate after any merge.
            if !self.ext.nominals.is_empty() {
                let merged = self.ext.process_nominals();
                if self.ext.has_clash() {
                    if self.trace {
                        eprintln!("TR nominal-clash depth={}", depth);
                    }
                    return self.conflict_out(self.ext.clash_dep());
                }
                if merged {
                    continue;
                }
            }
            let _ot0 = Instant::now();
            let _made = self.process_obligations();
            self.oblig_us += _ot0.elapsed().as_micros();
            if _made {
                if self.trace {
                    eprintln!("TR oblig-made depth={}", depth);
                }
                continue;
            }
            let action = if self.watch {
                self.next_action_incremental()
            } else {
                self.next_action_from_pending()
            };
            match action {
                Scan::Clash => {
                    if self.trace {
                        eprintln!("TR scan-clash depth={}", depth);
                    }
                    return self.conflict_out(self.ext.clash_dep());
                }
                Scan::Unit => {
                    if self.trace {
                        eprintln!("TR scan-unit depth={}", depth);
                    }
                    continue;
                }
                Scan::Sat => {
                    if self.trace {
                        eprintln!("TR scan-sat depth={}", depth);
                    }
                    // KM_HT_CARD: discharge a still-violated first-class ≤n
                    // restriction (Konclude `applyATMOSTRule`: choose then merge)
                    // before declaring the model complete.
                    if self.card && !self.ext.card_max.is_empty() {
                        if let Some(out) = self.card_max_step(depth) {
                            return out;
                        }
                    }
                    // Before declaring the model complete, discharge any pending ≤n
                    // qualified-cardinality merge (KM_HT_QMERGE): a still-violated
                    // AtMost is a non-deterministic choice of which pair to identify.
                    if self.ext.qmerge {
                        if let Some(mid) = self.next_merge() {
                            return self.branch_merge(mid, depth);
                        }
                    }
                    // KM_HT_CARD_RECOG: derive any ≤n recognition marker that now
                    // provably holds at this saturated model (deterministic, no
                    // branch). A newly derived marker fires recognition chains and
                    // ≤n enforcement, so re-propagate and re-scan before declaring
                    // the model complete.
                    if self.card_recog && self.card_recog_step() {
                        continue;
                    }
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
                        eprintln!(
                            "TR branch depth={} level={} ndisj={}",
                            depth,
                            level,
                            gd.disjuncts.len()
                        );
                    }
                    self.order_disjuncts(&mut gd.disjuncts);
                    self.branch_pushes += 1;
                    let mut fail = dep_empty();
                    for (di, d) in gd.disjuncts.iter().enumerate() {
                        self.disjunct_tries += 1;
                        let mark = self.ext.mark();
                        let dep = dep_add(&gd.dep, level);
                        if self.trace {
                            eprintln!(
                                "TR try di={} node={} c={} neg={} mark={}",
                                di, d.node, d.lit.c, d.lit.neg, mark
                            );
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
                                if self.lblng {
                                    self.unrecord_choice(level);
                                }
                                return Out::Restart;
                            }
                            Out::Conflict(cd) => {
                                self.backtracks += 1;
                                // VSIDS-style: blame the disjunct we just tried.
                                if self.ord_mode != 0 || self.pick_mode == 2 {
                                    *self.activity.entry(d.lit.c).or_insert(0) += 1;
                                }
                                if self.trace {
                                    eprintln!(
                                        "TR conflict di={} depth={} cd_max={} contains_level={}",
                                        di,
                                        depth,
                                        dep_max(&cd),
                                        dep_contains(&cd, level)
                                    );
                                }
                                self.ext.backtrack_to(mark);
                                if !dep_contains(&cd, level) {
                                    self.backjumps += 1;
                                    if self.lblng {
                                        self.unrecord_choice(level);
                                    }
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
                                    let comp = CLit {
                                        neg: !d.lit.neg,
                                        c: d.lit.c,
                                    };
                                    self.negfired += 1;
                                    self.ext.add_concept(d.node, comp, &ndep);
                                    if self.ext.has_clash() {
                                        // ¬D_di immediately clashes ⇒ the disjunction is
                                        // unsat under the current outer choices.
                                        let cd2 = self.ext.clash_dep();
                                        self.ext.backtrack_to(mark);
                                        if self.lblng {
                                            self.unrecord_choice(level);
                                        }
                                        if !dep_contains(&cd2, level) {
                                            return Out::Conflict(cd2);
                                        }
                                        return Out::Conflict(dep_remove(
                                            &dep_union(&fail, &cd2),
                                            level,
                                        ));
                                    }
                                }
                            }
                        }
                    }
                    if self.trace {
                        eprintln!("TR branch-exhausted depth={}", depth);
                    }
                    if self.lblng {
                        self.unrecord_choice(level);
                    }
                    return Out::Conflict(dep_remove(&fail, level));
                }
            }
        }
    }

    /// Run one ordinary consistency probe and retain its completed model when it
    /// is satisfiable.  UNSAT probes deliberately have no model snapshot.
    pub fn consistent_with_snapshot(
        &mut self,
        seed: &[CLit],
    ) -> Option<(bool, Option<HtModelSnapshot>)> {
        let satisfiable = self.consistent(seed)?;
        let snapshot = satisfiable.then(|| HtModelSnapshot {
            ext: self.ext.clone(),
        });
        Some((satisfiable, snapshot))
    }

    /// Check whether a previously completed model can be extended after
    /// monotone clause addition.
    ///
    /// `Some(snapshot)` is a new complete clash-free model and therefore a valid
    /// SAT witness. `None` means only that this particular old branch could not be
    /// extended (or the replay reached an unsupported/restart boundary); callers
    /// must perform a fresh exhaustive probe. In particular, `None` is never an
    /// UNSAT answer.
    pub fn resume_satisfiable_model(
        &mut self,
        snapshot: &HtModelSnapshot,
    ) -> Option<HtModelSnapshot> {
        self.ext = snapshot.ext.clone();
        self.ext.prepare_addition_replay();
        self.ext.watch = self.watch;
        if self.force_fast {
            self.ext.incr2 = true;
            self.ext.incroblig = true;
        }
        if self.force_qmerge {
            self.ext.qmerge = true;
        }
        if self.force_number {
            self.ext.number = true;
        }
        self.ext.block3 = self.block_mode == 3;
        if !self.nom_set.is_empty() {
            self.ext.nominals = self.nom_set.iter().copied().collect();
        }

        self.cache.clear();
        self.decisions.clear();
        self.learned.clear();
        self.lwatch.clear();
        self.cur_choices.clear();
        self.dec_sig.clear();
        self.dec_choice.clear();
        self.lng.clear();
        self.lng_watch.clear();
        self.lng_fires = 0;
        self.luby_idx = 1;
        // A replay is a witness-validation fast path. If search requests a
        // restart, fall back to the ordinary fresh probe rather than rebuilding
        // this fixed witness with different historical branch assumptions.
        self.restart_limit = u64::MAX;

        match self.dfs(0) {
            Out::Sat if !self.ext.unsupported => Some(HtModelSnapshot {
                ext: self.ext.clone(),
            }),
            Out::Conflict(_) | Out::Restart | Out::Sat => None,
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
            if self.block_mode == 1 && self.ext.incr2 {
                self.ext.enable_block_bits();
            }
            if self.force_qmerge {
                self.ext.qmerge = true;
            }
            if self.force_number {
                self.ext.number = true;
            }
            // tell Ext whether mode-3 (pairwise) blocking is live, so add_edge
            // widens the incremental suffix on edge changes (the signature uses
            // the parent edge). Subset blocking (mode 1) is label-only.
            self.ext.block3 = self.block_mode == 3;
            // Nominals (o-rule): Ext::new resets the set, so re-apply each rebuild.
            if !self.nom_set.is_empty() {
                self.ext.nominals = self.nom_set.iter().copied().collect();
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
            // Keep the taxonomy/query root at node 0: model-label extraction and
            // candidate generation are intentionally keyed to that node.  Named
            // individuals are separate non-blockable roots in the same global
            // completion graph, exactly as in an ABox model.
            let root = self.ext.new_root();
            for &lit in seed {
                self.ext.add_concept(root, lit, &dep_empty());
            }
            let mut named_roots = Vec::with_capacity(self.native_abox.individuals.len());
            for (proxies, assertions) in &self.native_abox.individuals {
                let node = self.ext.new_root();
                named_roots.push(node);
                for &concept in proxies.iter().chain(assertions.iter()) {
                    self.ext.add_concept(node, CLit::pos(concept), &dep_empty());
                }
            }
            for &(left, right) in &self.native_abox.different {
                let (Some(&left), Some(&right)) = (named_roots.get(left), named_roots.get(right))
                else {
                    self.ext.unsupported = true;
                    continue;
                };
                self.ext.add_distinct(left, right, &dep_empty());
            }
            for &(role, source, target) in &self.native_abox.role_assertions {
                let (Some(&source), Some(&target)) =
                    (named_roots.get(source), named_roots.get(target))
                else {
                    self.ext.unsupported = true;
                    continue;
                };
                self.ext.add_edge(role, source, target, &dep_empty());
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
                    if self.cert_no_blocking {
                        let ni_risk = self.nominal_number_non_successor();
                        if ni_risk && std::env::var_os("KM_HT_TRACE").is_some() {
                            eprintln!(
                                "TR cert-defer ni-risk={}",
                                ni_risk
                            );
                        }
                        if ni_risk {
                            return None;
                        }
                    }
                    let sat = matches!(other, Out::Sat);
                    // KM_HT_SATCACHE3: pool the FULL-label pairwise signatures of
                    // this completed clash-free model's UNBLOCKED blockable nodes —
                    // genuine witnesses whose subtree was fully expanded. A pooled
                    // signature blocks any later mode-3 node with the same (label,
                    // parent, edge) context, sharing the saturation across queries.
                    // Restricted to unblocked nodes so the witness is real (a blocked
                    // node's subtree was never expanded). Sound for the SHIQ mode-3
                    // fragment (the full label carries this query's negatives, so the
                    // witness respects every forbidden concept of the blocked node).
                    if sat && self.satcache3 && self.block_mode == 3 {
                        let nn = self.ext.num_nodes();
                        let blk = self.compute_blocked();
                        for n in 0..nn {
                            if !self.ext.blockable[n] || blk[n] {
                                continue;
                            }
                            if let Some(p) = self.ext.pred[n] {
                                let sig = self.ext.i3_signature_full(n, p);
                                if self.sat_sigs3.insert(sig) {
                                    self.sc3_pooled += 1;
                                }
                            }
                        }
                    }
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
                        let blocked = if self.anywhere {
                            self.compute_blocked()
                        } else {
                            vec![false; nn]
                        };
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
            let mut s: Vec<C> = self.ext.concepts[n]
                .keys()
                .filter(|k| !k.neg)
                .map(|k| k.c)
                .collect();
            s.sort_unstable();
            sigs.push(s);
        }
        let mut sizes: Vec<usize> = sigs.iter().map(|s| s.len()).collect();
        sizes.sort_unstable();
        let distinct: HashSet<&Vec<C>> = sigs.iter().collect();
        let blocked = if self.anywhere {
            self.compute_blocked()
        } else {
            vec![false; nn]
        };
        let nblk = blocked.iter().filter(|b| **b).count();
        let med = if sizes.is_empty() {
            0
        } else {
            sizes[sizes.len() / 2]
        };
        eprintln!(
            "KM_HT [dumplabels] nodes={} distinct_pos_labels={} blocked={} label_size(min/med/max)={}/{}/{}",
            nn, distinct.len(), nblk,
            sizes.first().copied().unwrap_or(0), med, sizes.last().copied().unwrap_or(0)
        );
        // UNBLOCKED nodes drive branching: how many DISTINCT labels among them,
        // and are they pairwise-incomparable (no subset relation ⇒ subset blocking
        // cannot fold them; the diversity comes from exclusive-disjunct choices)?
        let mut ublabels: Vec<&Vec<C>> =
            (0..nn).filter(|&n| !blocked[n]).map(|n| &sigs[n]).collect();
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
                if sub_ab || sub_ba {
                    comp += 1;
                } else {
                    incomp += 1;
                }
            }
        }
        eprintln!(
            "KM_HT [dumplabels] unblocked_distinct={} pairs(comparable/incomparable)={}/{}",
            ub_distinct, comp, incomp
        );
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
                let comp = CLit {
                    neg: !lit.neg,
                    c: lit.c,
                };
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
                Some(
                    self.ext.concepts[0]
                        .keys()
                        .filter(|k| !k.neg)
                        .map(|k| k.c)
                        .collect(),
                )
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

    /// KM_HT_QO_RESIDUE_COMPLETE: complete the AFFECTED (residue) concepts of a
    /// card-split deferral with the full tableau, RESTRICTED to the residue. The
    /// clean bulk is already certified by the forward pass (sound + complete: a
    /// clean concept reaches no insufficient node), so only the few affected
    /// concepts need the complete decision procedure — not a fresh global
    /// classify of all 58k concepts (the explosion the gate exists to avoid).
    ///
    /// For each residue concept `a`: build one real model `M_a` (`consistent(a)`)
    /// and read its positive query concepts. That set is a SOUND + COMPLETE
    /// candidate superset of `a`'s subsumers — a true subsumer holds in EVERY
    /// model of `a`, so it is in `M_a`; a concept FALSE in `M_a` is a refutation
    /// (`a ⋢ b`). Confirm each candidate `b` with `consistent(a ⊓ ¬b)`. The gate's
    /// polluted forward label is never trusted; the answer is the complete
    /// tableau verdict for the residue. `None` if a model build goes
    /// out-of-fragment (sound: the caller defers to CB).
    ///
    /// Immutable `self`: each worker owns a cloned `Ht`, so this can run while the
    /// caller still holds the forward `QoSat` borrow of `self.clauses`.
    /// KM_HT_QO_CERTAIN — Konclude-style deterministic disjunction resolution.
    /// A parked concept-level disjunction `Q → h1 ⊔ … ⊔ hk` entails, in EVERY
    /// model, the intersection of the disjuncts' subsumer closures
    /// `D = ⋂ᵢ closure(hᵢ)` (a concept in all branches is certain). For every
    /// concept `A` that carries the body (`Q ∈ closure(A)`), add `D` to `A`'s
    /// subsumers — deterministically, no branch, no model build. This is the
    /// certain part Konclude derives in saturation; it (a) recovers the genuine
    /// disjunction-mediated subsumers and (b) makes the false-residue concepts
    /// cheap (their `D` is already present ⇒ nothing added). Sound: every emitted
    /// pair holds in all models. Iterated to a fixpoint (an added subsumer may be
    /// the body of another disjunction). Returns the new (a, b) pairs.
    /// Clause ids of CONCEPT-LEVEL disjunctions: head ≥2 and every head/body atom
    /// is a positive Concept on the central variable X. These are the disjunctions
    /// whose certain consequence is the concept ⋂-closure (no edge spanned), so a
    /// residue concept parked ONLY on these is fully explained by the forward pass
    /// + `certain_disjunction_consequences` and needs no model build.
    fn concept_level_disjunction_cids(&self) -> HashSet<usize> {
        let mut out = HashSet::new();
        for (cid, (cl, _, _)) in self.clauses.iter().enumerate() {
            if cl.head.len() < 2 {
                continue;
            }
            let ok = cl
                .head
                .iter()
                .chain(cl.body.iter())
                .all(|a| matches!(a, Atom::Concept { lit, t } if !lit.neg && *t == X))
                && !cl.body.is_empty();
            if ok {
                out.insert(cid);
            }
        }
        out
    }

    fn certain_disjunction_consequences(&self, subs: &[(C, C)], qset: &HashSet<C>) -> Vec<(C, C)> {
        // closure maps: fwd[a] = subsumers of a; inv[b] = concepts subsumed by b.
        let mut fwd: HashMap<C, HashSet<C>> = HashMap::new();
        let mut inv: HashMap<C, HashSet<C>> = HashMap::new();
        for &(a, b) in subs {
            fwd.entry(a).or_default().insert(b);
            inv.entry(b).or_default().insert(a);
        }
        // Concept-level disjunctions: head ≥2, all positive Concept atoms at the
        // same (single) variable, body all positive Concept atoms. (∃/role/Eq
        // heads or multi-var disjunctions are not concept-level certain rules.)
        let mut disj: Vec<(Vec<C>, Vec<C>)> = Vec::new();
        for (cl, _, _) in &self.clauses {
            if cl.head.len() < 2 {
                continue;
            }
            // Concept-level ⟺ EVERY head and body atom is a positive Concept on the
            // CENTRAL variable X. A head atom on another variable (e.g. a role
            // successor `e(y)`) means the disjunction spans an edge and its ⋂-closure
            // is NOT a sound certain consequence at X — reject the whole clause.
            let mut ok = true;
            let mut heads: Vec<C> = Vec::new();
            for a in &cl.head {
                match a {
                    Atom::Concept { lit, t } if !lit.neg && *t == X => heads.push(lit.c),
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                continue;
            }
            let mut body: Vec<C> = Vec::new();
            for a in &cl.body {
                match a {
                    Atom::Concept { lit, t } if !lit.neg && *t == X => body.push(lit.c),
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok || body.is_empty() {
                continue;
            }
            disj.push((body, heads));
        }
        let contains = |fwd: &HashMap<C, HashSet<C>>, a: C, x: C| -> bool {
            a == x || fwd.get(&a).map_or(false, |s| s.contains(&x))
        };
        let mut new_subs: Vec<(C, C)> = Vec::new();
        loop {
            let mut round: Vec<(C, C)> = Vec::new();
            for (body, heads) in &disj {
                // D = ⋂ closure(hᵢ) ∩ qset, closure(h) = fwd[h] ∪ {h}.
                let mut it = heads.iter();
                let h0 = *it.next().unwrap();
                let mut d: HashSet<C> = fwd.get(&h0).cloned().unwrap_or_default();
                d.insert(h0);
                for &h in it {
                    let ch = fwd.get(&h);
                    d.retain(|x| *x == h || ch.map_or(false, |s| s.contains(x)));
                    if d.is_empty() {
                        break;
                    }
                }
                d.retain(|x| qset.contains(x));
                if d.is_empty() {
                    continue;
                }
                // triggers = concepts carrying every body concept in their closure.
                let mut triggers: HashSet<C> = inv.get(&body[0]).cloned().unwrap_or_default();
                triggers.insert(body[0]);
                for &qb in &body[1..] {
                    let t2 = inv.get(&qb);
                    triggers.retain(|a| *a == qb || t2.map_or(false, |s| s.contains(a)));
                }
                for &a in &triggers {
                    // Only emit subsumptions whose SUBCLASS is a real query concept
                    // (the body trigger may itself be a synthetic Q-marker, which is
                    // not a classified class — Konclude never reports marker subs).
                    if !qset.contains(&a) {
                        continue;
                    }
                    for &x in &d {
                        if x != a && !contains(&fwd, a, x) {
                            round.push((a, x));
                        }
                    }
                }
            }
            let mut changed = false;
            for (a, x) in round {
                if fwd.entry(a).or_default().insert(x) {
                    inv.entry(x).or_default().insert(a);
                    new_subs.push((a, x));
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        new_subs
    }

    fn qo_residue_complete(
        &self,
        residue: &[C],
        qset: &HashSet<C>,
        known: &HashMap<C, HashSet<C>>,
    ) -> Option<(Vec<C>, Vec<(C, C)>)> {
        let trace = std::env::var_os("KM_HT_TRACE").is_some();
        let t0 = std::time::Instant::now();
        let par = std::env::var("KM_HT_PAR")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(1)
            .max(1);
        let nthreads = par.min(residue.len().max(1)).max(1);
        let template: Vec<Clause> = self.clauses.iter().map(|(c, _, _)| c.clone()).collect();
        let anywhere = self.anywhere;
        let next = std::sync::atomic::AtomicUsize::new(0);
        const RWORKER_STACK: usize = 512 * 1024 * 1024;
        let residue_ref = residue;
        let qset_ref = qset;
        let known_ref = known;
        // KM_QO_EDGE_COMPOSE: copy the chain-composition indexes (built by the
        // parent's set_chains) into each residue worker so the complete tableau
        // composes role-chain edges (bounded by Ht blocking).
        let ec_fwd = self.ht_chain_fwd.clone();
        let ec_bwd = self.ht_chain_bwd.clone();
        // per worker: Some((unsat, subs)) or None ⇒ out-of-fragment, defer whole.
        let parts: Vec<Option<(Vec<C>, Vec<(C, C)>, u64, f64, f64)>> = std::thread::scope(|s| {
            let next = &next;
            let handles: Vec<_> = (0..nthreads)
                .map(|_| {
                    let tmpl = template.clone();
                    let ec_fwd = ec_fwd.clone();
                    let ec_bwd = ec_bwd.clone();
                    std::thread::Builder::new()
                        .stack_size(RWORKER_STACK)
                        .spawn_scoped(
                            s,
                            move || -> Option<(Vec<C>, Vec<(C, C)>, u64, f64, f64)> {
                                let mut w = Ht::new(tmpl);
                                w.set_anywhere(anywhere);
                                w.set_fast_tableau(); // result-identical speedups
                                w.set_edge_compose(ec_fwd, ec_bwd);
                                // The residue concept's complete tableau may meet an
                                // equality-head clause (`≤n` / functional, the `⋁ Eq`
                                // disjunctive head). Without `number` the apply_head Eq
                                // arm bails `unsupported` ⇒ the whole residue-complete
                                // defers to CB (ore_ont_7499: a single ≤n concept forces
                                // the defer). Enable the number+qmerge cardinality merge
                                // (the same sound rule the card route uses): Eq-heads now
                                // route to `push_card`/`branch_merge`. Result-identical on
                                // a pure-disjunction residue (no Eq head ⇒ number inert).
                                w.force_number = true;
                                w.force_qmerge = true;
                                let mut subs: Vec<(C, C)> = Vec::new();
                                let mut unsat: Vec<C> = Vec::new();
                                let mut nconf: u64 = 0;
                                // KM_HT_QO_RESIDUE_SAMPLE=N: process only the first N residue
                                // concepts (diagnostic: measure per-concept model-build vs
                                // candidate-test cost without waiting for all 9755).
                                let sample = std::env::var("KM_HT_QO_RESIDUE_SAMPLE")
                                    .ok()
                                    .and_then(|s| s.parse::<usize>().ok())
                                    .unwrap_or(0);
                                let mut t_model = std::time::Duration::ZERO;
                                let mut t_cand = std::time::Duration::ZERO;
                                loop {
                                    let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                                    if i >= residue_ref.len() || (sample > 0 && i >= sample) {
                                        break;
                                    }
                                    let a = residue_ref[i];
                                    // one real model of `a`.
                                    let tm = std::time::Instant::now();
                                    let cons_a = w.consistent(&[CLit::pos(a)]);
                                    t_model += tm.elapsed();
                                    match cons_a {
                                        Some(false) => {
                                            unsat.push(a); // a ⊑ ⊥ ⇒ unsatisfiable
                                            continue;
                                        }
                                        None => return None, // out-of-fragment ⇒ defer
                                        Some(true) => {}
                                    }
                                    // candidate superset = positive query concepts at root,
                                    // MINUS the already-confirmed sound subsumers (`known[a]`,
                                    // the residue concept's monotone forward-only label — the
                                    // caller already emitted those). Only the uncertain ones
                                    // (added by resolving the parked disjunction) pay the
                                    // expensive `A ⊓ ¬B` unsat proof. This is the lever that
                                    // cuts the per-concept candidate count from "all subsumers"
                                    // to "the few the disjunction could change".
                                    let ka = known_ref.get(&a);
                                    let cand: Vec<C> = w.ext.concepts[0]
                                        .keys()
                                        .filter(|k| !k.neg)
                                        .map(|k| k.c)
                                        .filter(|b| *b != a && qset_ref.contains(b))
                                        .filter(|b| ka.map_or(true, |s| !s.contains(b)))
                                        .collect();
                                    let tc = std::time::Instant::now();
                                    for b in cand {
                                        nconf += 1;
                                        match w.consistent(&[CLit::pos(a), CLit::neg(b)]) {
                                            Some(false) => subs.push((a, b)), // a ⊓ ¬b unsat ⇒ a ⊑ b
                                            Some(true) => {}                  // satisfiable ⇒ a ⋢ b
                                            None => return None,              // defer
                                        }
                                    }
                                    t_cand += tc.elapsed();
                                }
                                Some((
                                    unsat,
                                    subs,
                                    nconf,
                                    t_model.as_secs_f64(),
                                    t_cand.as_secs_f64(),
                                ))
                            },
                        )
                        .expect("spawn residue-complete worker")
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let mut unsat: Vec<C> = Vec::new();
        let mut subs: Vec<(C, C)> = Vec::new();
        let mut nconf: u64 = 0;
        let (mut tmod, mut tcnd) = (0f64, 0f64);
        for part in parts {
            match part {
                Some((u, s, k, tm, tc)) => {
                    unsat.extend(u);
                    subs.extend(s);
                    nconf += k;
                    tmod += tm;
                    tcnd += tc;
                }
                None => return None, // a worker hit out-of-fragment ⇒ defer whole
            }
        }
        if trace {
            eprintln!(
                "QOGF residue-complete: {} concepts, {} confirms, subs={} unsat={} [{:.2}s wall, model-build={:.1}s cand-test={:.1}s (thread-summed), {} threads]",
                residue.len(),
                nconf,
                subs.len(),
                unsat.len(),
                t0.elapsed().as_secs_f64(),
                tmod, tcnd,
                nthreads
            );
        }
        Some((unsat, subs))
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
                let mut v: Vec<C> = self.ext.concepts[n]
                    .keys()
                    .filter(|k| !k.neg)
                    .map(|k| k.c)
                    .collect();
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
            if self.trace {
                eprintln!("TR classify-return (global, consistent)");
            }
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
        let par = std::env::var("KM_HT_PAR")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(1);
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
        // only the number of Phase-1 sat-tests changes. The orchestrator enables
        // it for production workers; direct worker users can still select it with
        // the environment flag.
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
                        let mut v: Vec<C> = self.ext.concepts[n]
                            .keys()
                            .filter(|k| !k.neg)
                            .map(|k| k.c)
                            .collect();
                        v.sort_unstable();
                        if core.contains(&v) {
                            shared += 1;
                        }
                    }
                    eprintln!(
                        "KM_HT [coreprobe] concept={} nodes={} shared_with_core={} ({}%)",
                        a,
                        nn,
                        shared,
                        if nn > 0 { 100 * shared / nn } else { 0 }
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
            if (qi == 0 || self.backtracks - bt0 > 5000)
                && std::env::var_os("KM_HT_DUMPLABELS").is_some()
            {
                eprintln!(
                    "KM_HT [dumplabels] FOR concept={} qi={} backtracks_here={}",
                    a,
                    qi,
                    self.backtracks - bt0
                );
                self.dump_labels();
            }
        }
        if self.stats && witreuse {
            eprintln!(
                "KM_HT [witreuse] queries={} reused={} built={}",
                queries.len(),
                wit_hits,
                queries.len() as u64 - wit_hits
            );
        }
        if self.stats && self.satcache3 {
            eprintln!(
                "KM_HT [satcache3] pooled_full_sigs={} distinct={}",
                self.sc3_pooled,
                self.sat_sigs3.len()
            );
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
            // metric: O(classes), not O(classes^2)). The orchestrator enables it
            // for production workers; direct worker users can still select it
            // with the environment flag.
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
                let mut possible: HashSet<C> = if modelprune {
                    cand.iter().copied().collect()
                } else {
                    HashSet::new()
                };
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
                eprintln!(
                    "KM_HT [classify-p2] modelprune={} sat_q={} phase2_tests={}",
                    modelprune,
                    sat_q.len(),
                    tests
                );
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
                if self.i2_calls > 0 {
                    self.i2_suf_sum / self.i2_calls as u128
                } else {
                    0
                },
            );
        }
        if self.trace {
            eprintln!(
                "TR classify-return (full) sat={} unsat={} subs={}",
                sat_q.len(),
                unsat.len(),
                subs.len()
            );
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
    /// the sequential modelprune/witreuse/etc. paths are not mirrored because
    /// they are either inert or order-dependent under parallelism.
    fn classify_parallel(&self, queries: &[C], par: usize) -> Option<(bool, Vec<C>, Vec<(C, C)>)> {
        use std::sync::atomic::{AtomicUsize, Ordering};
        let qset: HashSet<C> = queries.iter().copied().collect();
        let template: Vec<Clause> = self.clauses.iter().map(|(c, _, _)| c.clone()).collect();
        let anywhere = self.anywhere;
        let stats = self.stats;
        // Per-worker config that the fresh `Ht::new(template)` does NOT inherit from
        // the clause set: the first-class number rules (`card_defs`) and the SHOQ
        // o-rule (`nom_set`) live in struct fields, not the clauses (the clausal
        // pigeonhole was dropped for the card route). Without re-installing these,
        // a parallel worker classifies WITHOUT cardinality / nominals -> wrong
        // subsumers (the documented "10908 collapses to 86/6001 at PAR=8" was this:
        // workers missing the o-rule, not a race). Each worker owns its `Ht`, so the
        // re-installed state is per-thread -> sound. Re-applied below in both phases.
        let p_card_defs = self.card_defs.clone();
        let p_nom_set = self.nom_set.clone();
        let p_native_abox = self.native_abox.clone();
        let p_force_number = self.force_number;
        let p_force_qmerge = self.force_qmerge;
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
                    let card_defs = p_card_defs.clone();
                    let nom_set = p_nom_set.clone();
                    let native_abox = p_native_abox.clone();
                    std::thread::Builder::new()
                        .stack_size(HT_WORKER_STACK)
                        .spawn_scoped(s, move || -> Option<Vec<(C, bool, Vec<C>)>> {
                            let mut w = Ht::new(tmpl);
                            w.set_anywhere(anywhere);
                            w.force_number = p_force_number;
                            w.force_qmerge = p_force_qmerge;
                            if !card_defs.is_empty() {
                                w.set_card_defs(card_defs);
                            }
                            if !nom_set.is_empty() {
                                w.set_nominals(nom_set);
                            }
                            w.native_abox = native_abox;
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
            let (told, qset, satset, labels, next2) = (&told, &qset, &satset, &labels, &next2);
            let handles: Vec<_> = (0..nthreads.min(nl.max(1)))
                .map(|_| {
                    let tmpl = template.clone();
                    let card_defs = p_card_defs.clone();
                    let nom_set = p_nom_set.clone();
                    let native_abox = p_native_abox.clone();
                    std::thread::Builder::new()
                        .stack_size(HT_WORKER_STACK)
                        .spawn_scoped(s, move || -> Option<Vec<(C, C)>> {
                            let mut w = Ht::new(tmpl);
                            w.set_anywhere(anywhere);
                            w.force_number = p_force_number;
                            w.force_qmerge = p_force_qmerge;
                            if !card_defs.is_empty() {
                                w.set_card_defs(card_defs);
                            }
                            if !nom_set.is_empty() {
                                w.set_nominals(nom_set);
                            }
                            w.native_abox = native_abox;
                            let mut subs = Vec::new();
                            loop {
                                let li = next2.fetch_add(1, Ordering::Relaxed);
                                if li >= nl {
                                    break;
                                }
                                let (a, lab) = &labels[li];
                                let a = *a;
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
                nthreads,
                nq,
                sat_q.len(),
                subs.len()
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
        qf.install_edge_compose(&self.qo_edge_chains);
        qf.complete_roles = true;
        let t_pre = Instant::now();
        let g = qf.saturate_global(queries);
        if trace {
            eprintln!(
                "QOPHASE precompute DONE in {:.1}s: nodes={} pending={} insuff_nodes={} qo_insuff={} kp_insuff={} unsupported={}",
                t_pre.elapsed().as_secs_f64(), qf.label.len(), qf.pending.len(),
                qf.kp_insuff_nodes.len(), qf.qo_insufficient, qf.kp_insufficient, g.unsupported
            );
        }
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
                eprintln!(
                    "QOGF split-diag: redirects={} forall_insuff={} card_insuff={} cardmerges={}",
                    DBG_SPLIT.load(Ordering::Relaxed),
                    DBG_FORALL_INSUFF.load(Ordering::Relaxed),
                    DBG_CARD_INSUFF.load(Ordering::Relaxed),
                    DBG_CARDMERGE.load(Ordering::Relaxed)
                );
                eprintln!(
                    "QOGF eq-defer-why: nonfiller={} norole={} unsat={} other={}",
                    DBG_EQ_NONFILLER.load(Ordering::Relaxed),
                    DBG_EQ_NOROLE.load(Ordering::Relaxed),
                    DBG_EQ_UNSAT.load(Ordering::Relaxed),
                    DBG_EQ_OTHER.load(Ordering::Relaxed)
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
            // The pending-disjunction seeding, in_edges-only closure, and the
            // residue-complete verify are ALL confined to KM_HT_QO_RESIDUE_COMPLETE
            // so the default KM_HT_QO_CARD card-split path stays byte-identical
            // (pending-empty guard + bidirectional closure) until corpus-validated.
            let residue_complete = std::env::var_os("KM_HT_QO_RESIDUE_COMPLETE").is_some();
            // Engage the global-forward classification when a cardinality was
            // deferred (default path: card_defer + pending-empty), OR — under
            // residue-complete only — when there are PARKED DISJUNCTIONS but no
            // cardinality. A pure-∀+⊔ ontology (ore_ont_3215: 18323 disjunctions,
            // head_eq=0) otherwise falls to per-concept classify_parallel, which
            // branches every disjunction per query (timeout). The forward pass
            // parks the disjunctions into qf.pending; seeding them as affected lets
            // the clean bulk emit and the disjunction core go to the O(n) per-concept
            // residue-complete verify. Confined to the opt-in residue-complete path.
            let engage = (qf.card_defer && (residue_complete || qf.pending.is_empty()))
                || (residue_complete && !qf.pending.is_empty());
            if engage && !g.unsupported {
                let nn = qf.label.len();
                let mut affected = vec![false; nn];
                let mut stack: Vec<Node> = Vec::new();
                // Affected seeds = every node carrying a deferred obligation:
                //  - cardinality Eq-head / critical-∀ writes (kp_insuff_nodes), and
                //  - PARKED DISJUNCTION anchors (residue-complete only): a node with
                //    an unresolved ⊔ has an incomplete forward label, so any concept
                //    whose model reaches it is affected. Seeding them lets the clean
                //    bulk emit even while a disjunction/cardinality core remains.
                for &n in &qf.kp_insuff_nodes {
                    if n < nn && !affected[n] {
                        affected[n] = true;
                        stack.push(n);
                    }
                }
                if residue_complete {
                    for &(anchor, _cid) in &qf.pending {
                        if anchor < nn && !affected[anchor] {
                            affected[anchor] = true;
                            stack.push(anchor);
                        }
                    }
                }
                // REVERSE reach only (in_edges) under residue-complete: a named query
                // concept's root label is read at its root node, and an insufficiency
                // / parked disjunction at node `s` can only pollute that root if `s`
                // lies in the root's forward model — i.e. the root is an ANCESTOR of
                // `s`. Walking predecessors (in_edges) from each seed marks exactly
                // those ancestors. Down-pollution (out_edges) only reaches anonymous
                // successor labels, never a query root (roots 0..|queries| are never
                // fillers), so it cannot change a query concept's subsumers. This
                // matches the corpus-validated QOKP closure and shrinks the residue
                // from the bidirectional over-approximation. The default path keeps
                // the conservative both-directions closure; KM_HT_QO_BIDIR forces it.
                let bidir = !residue_complete || std::env::var_os("KM_HT_QO_BIDIR").is_some();
                while let Some(n) = stack.pop() {
                    for &(_, p) in &qf.in_edges[n] {
                        if !affected[p] {
                            affected[p] = true;
                            stack.push(p);
                        }
                    }
                    if bidir {
                        for &(_, t) in &qf.out_edges[n] {
                            if !affected[t] {
                                affected[t] = true;
                                stack.push(t);
                            }
                        }
                    }
                }
                let mut cs: Vec<(C, C)> = Vec::new();
                let mut cu: Vec<C> = Vec::new();
                let mut residue: Vec<C> = Vec::new();
                for (i, &a) in queries.iter().enumerate() {
                    if i >= nn || affected[i] {
                        residue.push(a);
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
                let res = residue.len();
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
                // KM_HT_QO_RESIDUE_COMPLETE: finish the affected concepts with the
                // complete tableau, restricted to the residue (the clean bulk above
                // is already sound + complete). Bounded by KM_HT_QO_RESIDUE_CAP
                // (default 5000) so a deferral with a still-large affected set falls
                // through to CB rather than spawning a runaway verify.
                if residue_complete {
                    let rcap: usize = std::env::var("KM_HT_QO_RESIDUE_CAP")
                        .ok()
                        .and_then(|v| v.parse().ok())
                        .unwrap_or(5000);
                    if res <= rcap {
                        let t_res = Instant::now();
                        let rc = self.qo_residue_complete(&residue, &qset, &HashMap::new());
                        if trace {
                            eprintln!(
                                "QOPHASE residue-complete ({} concepts) returned {} in {:.1}s",
                                res,
                                if rc.is_some() { "certified" } else { "defer" },
                                t_res.elapsed().as_secs_f64()
                            );
                        }
                        if let Some((ru, rsv)) = rc {
                            cu.extend(ru);
                            cs.extend(rsv);
                            let consistent = !(!queries.is_empty() && cu.len() == queries.len());
                            if trace {
                                eprintln!(
                                    "QOGF residue-complete certified: total_subs={} total_unsat={}",
                                    cs.len(),
                                    cu.len()
                                );
                            }
                            return Some((consistent, cu, cs));
                        }
                        if trace {
                            eprintln!("QOGF residue-complete could not certify ⇒ defer");
                        }
                    } else if trace {
                        eprintln!(
                            "QOGF residue-complete: residue {} > cap {} ⇒ defer",
                            res, rcap
                        );
                    }
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
        let node_of: HashMap<C, Node> = queries
            .iter()
            .enumerate()
            .map(|(i, &c)| (c, i as Node))
            .collect();
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
                            || gg.label_pos[n]
                                .iter()
                                .any(|b| *b != *a && qset.contains(b) && !fwd.contains(b))
                    })
                    .collect()
            } else {
                // inverse-having roles: any role in an inverse-bridge clause (a single
                // role head whose args are swapped versus a body role atom).
                let mut inv_roles: HashSet<R> = HashSet::new();
                for rec in self.clauses.iter() {
                    let head = &rec.0.head;
                    if head.len() == 1 {
                        if let Atom::Role {
                            r: hr,
                            s: hs,
                            t: ht,
                        } = &head[0]
                        {
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
            eprintln!(
                "QOPC entry queries={} clauses={}",
                queries.len(),
                self.clauses.len()
            );
        }
        // KM_HT_QO_TESTONE=A,B : adjudicate one pair A⊑B with the COMPLETE Ht
        // tableau (a different engine than QoSat) — does consistent(A ⊓ ¬B) say
        // unsat (A⊑B certain) or sat (not a subsumer)? Decides whether a QoSat-side
        // incompleteness or a contested gold explains a missing pair.
        if let Ok(v) = std::env::var("KM_HT_QO_TESTONE") {
            let parts: Vec<C> = v.split(',').filter_map(|s| s.parse().ok()).collect();
            if parts.len() == 2 {
                let (a, b) = (parts[0], parts[1]);
                let template: Vec<Clause> =
                    self.clauses.iter().map(|(c, _, _)| c.clone()).collect();
                let mut w = Ht::new(template);
                w.set_fast_tableau();
                w.set_edge_compose(self.ht_chain_fwd.clone(), self.ht_chain_bwd.clone());
                let sat_a = w.consistent(&[CLit::pos(a)]);
                let mut w2 = Ht::new(self.clauses.iter().map(|(c, _, _)| c.clone()).collect());
                w2.set_fast_tableau();
                w2.set_edge_compose(self.ht_chain_fwd.clone(), self.ht_chain_bwd.clone());
                let sat_anb = w2.consistent(&[CLit::pos(a), CLit::neg(b)]);
                eprintln!(
                    "QOTESTONE a={} b={}: consistent(a)={:?} consistent(a⊓¬b)={:?}  ⇒ {}",
                    a,
                    b,
                    sat_a,
                    sat_anb,
                    match sat_anb {
                        Some(false) => "a⊑b CERTAIN (QoSat gap)",
                        Some(true) => "a⋢b (gold contested)",
                        None => "unsupported/defer",
                    }
                );
                if std::env::var_os("KM_HT_TESTONE_TRACE").is_some() {
                    let e = &w2.ext;
                    let nn = e.num_nodes();
                    let mut ebyrole: std::collections::HashMap<R, u64> =
                        std::collections::HashMap::new();
                    let mut tot_e = 0u64;
                    for s in 0..nn {
                        for (r, _t, _d) in &e.out_edges[s] {
                            *ebyrole.entry(*r).or_default() += 1;
                            tot_e += 1;
                        }
                    }
                    // does any node carry B (b) positively? (root deriving B would clash with ¬B)
                    let mut nodes_with_b: Vec<Node> = Vec::new();
                    for n in 0..nn {
                        if e.concepts[n].contains_key(&CLit::pos(b)) {
                            nodes_with_b.push(n);
                        }
                    }
                    // root (node 0) positive label
                    let mut root_pos: Vec<C> = e.concepts[0]
                        .keys()
                        .filter(|k| !k.neg)
                        .map(|k| k.c)
                        .collect();
                    root_pos.sort_unstable();
                    let mut root_neg: Vec<C> = e.concepts[0]
                        .keys()
                        .filter(|k| k.neg)
                        .map(|k| k.c)
                        .collect();
                    root_neg.sort_unstable();
                    // max BFS depth from root over any role
                    let mut dist = vec![u32::MAX; nn];
                    if nn > 0 {
                        dist[0] = 0;
                    }
                    let mut qdep = std::collections::VecDeque::new();
                    qdep.push_back(0u32);
                    let mut maxd = 0u32;
                    while let Some(u) = qdep.pop_front() {
                        for (_r, t, _d) in &e.out_edges[u as usize] {
                            if dist[*t] == u32::MAX {
                                dist[*t] = dist[u as usize] + 1;
                                maxd = maxd.max(dist[*t]);
                                qdep.push_back(*t as u32);
                            }
                        }
                    }
                    let mut ebyrole_v: Vec<(R, u64)> = ebyrole.into_iter().collect();
                    ebyrole_v.sort_unstable_by_key(|x| x.1);
                    eprintln!(
                        "TESTONE_TRACE: unsupported={} nodes={} edges_total={} max_depth={} branch_pushes={} backtracks={} steps={} | nodes_with_B({})={} | roles(by cnt): {:?}",
                        e.unsupported, nn, tot_e, maxd, w2.branch_pushes, w2.backtracks, w2.steps,
                        b, nodes_with_b.len(), ebyrole_v
                    );
                    eprintln!(
                        "TESTONE_TRACE: root_pos_count={} root_pos(first40)={:?}",
                        root_pos.len(),
                        &root_pos[..root_pos.len().min(40)]
                    );
                    eprintln!(
                        "TESTONE_TRACE: root_neg_count={} root_neg={:?}",
                        root_neg.len(),
                        &root_neg
                    );
                }
            }
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
        // KM_HT_QO_PC_TALLY: feasibility diagnostic — process ALL query concepts,
        // counting sufficient / insufficient / unsupported / clashed instead of
        // deferring the whole classification on the first insufficient concept.
        // Confirms whether per-concept forward saturation is uniformly tractable on
        // a giant (no shared-filler explosion at any single root) and measures the
        // residue (insufficient) size that a per-concept residue verify would face.
        let pc_tally = std::env::var_os("KM_HT_QO_PC_TALLY").is_some();
        // Under the census, cap each per-concept saturation small so a concept whose
        // forward closure explodes (a general/near-⊤ concept) bails fast as `unsup`
        // instead of stalling the whole census — separating the tractable per-concept
        // models (suff/insuff) from the explosive residue (unsup) that needs the
        // blocking tableau. Override with KM_HT_QO_PC_CAP.
        let pc_cap: usize = std::env::var("KM_HT_QO_PC_CAP")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(30_000);
        // Edge-pop budget per concept (bounds the ∀-pollution cascade that node_cap
        // cannot). A tractable per-concept model drains in thousands of pops; an
        // exploding one bails as `unsup`. Override with KM_HT_QO_PC_EBUDGET.
        let pc_ebudget: u64 = std::env::var("KM_HT_QO_PC_EBUDGET")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(1_000_000);
        let mut tally = (0u64, 0u64, 0u64, 0u64); // (suff, insuff, unsup, clash)
        let mut qf = QoSat::new_opts(
            &self.clauses,
            true,
            std::env::var_os("KM_HT_QO_FPROP").is_some(),
        );
        qf.install_edge_compose(&self.qo_edge_chains);
        qf.complete_roles = true;
        qf.node_cap = cap;
        if pc_tally {
            qf.node_cap = pc_cap;
        }
        let mut qu = QoSat::new_opts(
            &self.clauses,
            false,
            std::env::var_os("KM_HT_QO_FPROP").is_some(),
        );
        qu.install_edge_compose(&self.qo_edge_chains);
        qu.complete_roles = true;
        qu.node_cap = cap;
        let mut unsat: Vec<C> = Vec::new();
        let mut subs: Vec<(C, C)> = Vec::new();
        let mut cands: Vec<(C, C)> = Vec::new();
        let mut unsat_cands: Vec<C> = Vec::new();
        // KM_HT_QO_PC_RESIDUE (Konclude classify phase): instead of DEFERRING the
        // whole classification on the first concept whose forward saturation parks a
        // disjunction (`!sufficient`), COLLECT those concepts into a residue and
        // finish them with the per-concept complete tableau (`qo_residue_complete`).
        // The sufficient bulk (48609/58364 on ore_ont_14817 with CARD_RECOG) is read
        // directly off its forward closure; only the small insufficient residue
        // (9755) pays a complete test — exactly Konclude's precompute + per-concept
        // SAT split, now that NOPOLLUTE makes the forward pass converge and CARD_RECOG
        // collapses the cardinality-recognition disjunctions.
        let pc_residue = std::env::var_os("KM_HT_QO_PC_RESIDUE").is_some();
        let mut residue: Vec<C> = Vec::new();
        let t_pc = Instant::now();
        // KM_HT_QO_PC_RESIDUE parallel bulk: the sufficient-bulk forward saturation
        // is independent per concept, so fan it out over KM_HT_PAR threads (each its
        // own QoSat over a cloned clause template). A thread returns None if any
        // concept is out-of-fragment ⇒ defer the whole. Only the simple forward path
        // (no KM_HT_QO_VERIFY inverse-candidate pass, no census) is parallelised here.
        if pc_residue && !want_cands && !pc_tally {
            let par = std::env::var("KM_HT_PAR")
                .ok()
                .and_then(|s| s.parse::<usize>().ok())
                .unwrap_or(1)
                .max(1);
            let nthreads = par.min(queries.len().max(1)).max(1);
            let fprop = std::env::var_os("KM_HT_QO_FPROP").is_some();
            let next = std::sync::atomic::AtomicUsize::new(0);
            let clauses_ref: &[ClauseRec] = &self.clauses;
            let queries_ref = queries;
            let qset_ref = &qset;
            // KM_HT_QO_RESIDUE_HIST: per-clause histogram of which parked
            // disjunctions make a concept residue. hist[cid] = #residue concepts
            // that parked clause `cid`. Diagnostic for the 9755-vs-Konclude-675 gap.
            let res_hist: Option<Vec<std::sync::atomic::AtomicUsize>> =
                if std::env::var_os("KM_HT_QO_RESIDUE_HIST").is_some() {
                    Some(
                        (0..clauses_ref.len())
                            .map(|_| std::sync::atomic::AtomicUsize::new(0))
                            .collect(),
                    )
                } else {
                    None
                };
            let res_hist_ref = res_hist.as_ref();
            // KM_HT_QO_DISCHARGE: a residue concept whose parked disjunctions are
            // ALL concept-level (⋂-closure already in its forward label) is false
            // residue — skip its model build. Konclude resolves these without a
            // calculated test.
            let discharge = std::env::var_os("KM_HT_QO_DISCHARGE").is_some();
            // KM_HT_QO_INPLACE: complete each insufficient concept on the qf that
            // ALREADY saturated it (a converging ~100-node per-concept model),
            // reusing qo_residue_classify (Phase 1 one completion → candidates,
            // Phase 2 verify via in-place subtree branching). No fresh consistent()
            // rebuild. False residue has no candidate ⇒ no test (cheap); only the
            // genuinely role-mediated concepts run calculated tests. None ⇒ defer
            // that concept to the fresh-build residue (sound).
            let inplace = std::env::var_os("KM_HT_QO_INPLACE").is_some();
            let pmbuild = std::env::var_os("KM_HT_QO_PMBUILD").is_some();
            let probe: Option<C> = std::env::var("KM_HT_QO_PROBE")
                .ok()
                .and_then(|s| s.parse().ok());
            let probe_sup: Option<C> = std::env::var("KM_HT_QO_PROBE_SUP")
                .ok()
                .and_then(|s| s.parse().ok());
            let nodecertain = std::env::var_os("KM_HT_QO_NODECERTAIN").is_some();
            let concept_level: HashSet<usize> = if discharge || nodecertain {
                self.concept_level_disjunction_cids()
            } else {
                HashSet::new()
            };
            let concept_level_ref = &concept_level;
            // KM_HT_QO_NODECERTAIN: precompute cid → ⋂-closure D of its disjuncts
            // (concept-level disjunctions only). Injected at parked nodes so the
            // role rules fire forward — recovers role-mediated certain subsumers.
            let nc_map: Option<std::sync::Arc<HashMap<usize, Vec<C>>>> = if nodecertain {
                let m = build_nodecertain_map(clauses_ref, concept_level_ref, fprop, cap);
                if std::env::var_os("KM_HT_TRACE").is_some() {
                    eprintln!(
                        "QONODECERTAIN map: {} concept-level disjunctions enriched",
                        m.len()
                    );
                    if let Ok(p) = std::env::var("KM_HT_QO_PROBE_CID") {
                        if let Ok(pc) = p.parse::<usize>() {
                            eprintln!(
                                "QONODECERTAIN cid={} in_map={} D_len={:?}",
                                pc,
                                m.contains_key(&pc),
                                m.get(&pc).map(|d| d.len())
                            );
                        }
                    }
                    // how many concept-level cids had a NON-empty intersection
                    eprintln!(
                        "QONODECERTAIN concept_level_total={}",
                        concept_level_ref.len()
                    );
                }
                Some(std::sync::Arc::new(m))
            } else {
                None
            };
            let nc_map_ref = &nc_map;
            let chains_ref = &self.qo_edge_chains;
            // (unsat, subs, residue, residue_sound[concept→sound subsumers])
            type PcPart = (Vec<C>, Vec<(C, C)>, Vec<C>, Vec<(C, Vec<C>)>);
            let parts: Vec<Option<PcPart>> = std::thread::scope(|s| {
                let next = &next;
                let handles: Vec<_> = (0..nthreads)
                    .map(|_| {
                        let tmpl: Vec<ClauseRec> = clauses_ref.to_vec();
                        std::thread::Builder::new()
                            .stack_size(64 * 1024 * 1024)
                            .spawn_scoped(s, move || -> Option<PcPart> {
                                let mut qf = QoSat::new_opts(&tmpl, true, fprop);
                                qf.install_edge_compose(chains_ref);
                                qf.complete_roles = true;
                                qf.node_cap = cap;
                                // KM_QO_EDGE_COMPOSE: bound the edge-composition
                                // cascade per concept.  Small models (the 9 true
                                // chain-derived) derive 4120 well under this; general
                                // concepts (large ∃-closures) bail to residue (Ht).
                                if !chains_ref.is_empty() {
                                    qf.edge_budget = std::env::var("KM_QO_EC_BUDGET")
                                        .ok().and_then(|s| s.parse().ok()).unwrap_or(200_000);
                                }
                                // KM_TRANS_CHAIN_COMPOSE: the __cmpp__ clauses can
                                // cascade the transitive marker through high-fanout
                                // part-edges on the shared-filler model.  Bound it so
                                // cascading concepts bail to residue (Ht, with
                                // blocking) instead of stalling.
                                if std::env::var_os("KM_TRANS_CHAIN_COMPOSE").is_some() {
                                    qf.edge_budget = qf.edge_budget.min(
                                        std::env::var("KM_QO_EC_BUDGET")
                                            .ok().and_then(|s| s.parse().ok()).unwrap_or(200_000));
                                }
                                qf.node_certain = nc_map_ref.clone();
                                let mut lsub: Vec<(C, C)> = Vec::new();
                                let mut luns: Vec<C> = Vec::new();
                                let mut lres: Vec<C> = Vec::new();
                                let mut lknown: Vec<(C, Vec<C>)> = Vec::new();
                                loop {
                                    let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                                    if i >= queries_ref.len() {
                                        break;
                                    }
                                    let a = queries_ref[i];
                                    qf.reset();
                                    let rf = qf.saturate(&[CLit::pos(a)]);
                                    if probe == Some(a) {
                                        // model-structure dump: node/edge counts, and where
                                        // key concepts land (P=__trans, the chain target, the
                                        // super). Reveals if the part_of chain expands + P fires.
                                        let nnodes = qf.label.len();
                                        let nedges: usize = qf.out_edges.iter().map(|e| e.len()).sum();
                                        let has = |cid: C| qf.label.iter().any(|l| l.contains(&CLit::pos(cid)));
                                        let root_has = |cid: C| qf.label.get(0).map(|l| l.contains(&CLit::pos(cid))).unwrap_or(false);
                                        let dbg: Vec<C> = std::env::var("KM_HT_QO_PROBE_IDS")
                                            .ok().map(|s| s.split(',').filter_map(|x| x.parse().ok()).collect())
                                            .unwrap_or_default();
                                        eprintln!("QOPROBE2 a={} nodes={} edges={} | for each id (root_has, any_has):", a, nnodes, nedges);
                                        for &cid in &dbg {
                                            eprintln!("QOPROBE2   c{} root={} any={}", cid, root_has(cid), has(cid));
                                        }
                                        let sup_in = probe_sup.map(|y| rf.root_label.contains(&y));
                                        let cl_park = qf.pending.iter().filter(|(_, c)| concept_level_ref.contains(c)).count();
                                        let cids: Vec<usize> = {
                                            let mut s: Vec<usize> = qf.pending.iter().map(|(_, c)| *c).collect();
                                            s.sort_unstable(); s.dedup(); s
                                        };
                                        eprintln!(
                                            "QOPROBE a={} suff={} clashed={} pending={} (concept_level={}) distinct_cids={} sup{:?}_in_label={:?} rootlen={}",
                                            a, rf.sufficient, rf.clashed, qf.pending.len(), cl_park,
                                            cids.len(), probe_sup, sup_in, rf.root_label.len()
                                        );
                                        eprintln!("QOPROBE   parked cids={:?}", &cids[..cids.len().min(40)]);
                                    }
                                    if rf.unsupported {
                                        return None; // out-of-fragment ⇒ defer whole
                                    }
                                    if rf.clashed {
                                        luns.push(a); // sound forward-only unsat
                                        continue;
                                    }
                                    // A forward-only label is SOUND (monotone, no branch)
                                    // whether or not the pass is sufficient: emit its
                                    // query subsumers directly. For an INSUFFICIENT concept
                                    // these are the confirmed-known subsumers the complete
                                    // residue test then skips (testing only the uncertain
                                    // delta the parked disjunction could add).
                                    let mut sound: Vec<C> = Vec::new();
                                    for &b in &rf.root_label {
                                        if b != a && qset_ref.contains(&b) {
                                            lsub.push((a, b)); // sound
                                            sound.push(b);
                                        }
                                    }
                                    if rf.edge_bailed {
                                        // edge-composition cascade exceeded budget:
                                        // the forward label is sound but may miss
                                        // chain subsumers → residue (Ht edge-compose).
                                        lres.push(a);
                                        lknown.push((a, sound));
                                        continue;
                                    }
                                    // KM_HT_TCC_CLAUSES (Ht-only __cmpp__): the forward
                                    // QoSat (without the __cmpp__ clauses, which cascade
                                    // on shared-fillers) misses chain-derived subsumers.
                                    // If the concept's model has a chain-opportunity (an
                                    // R1-edge to a node with an R2-edge, for some chain
                                    // R1∘R2⊑R), send it to residue where the Ht (WITH the
                                    // __cmpp__ clauses + blocking) derives them.
                                    if rf.sufficient && !chains_ref.is_empty() {
                                        let mut chain_opp = false;
                                        'outer: for &(_, r2, _hr) in chains_ref.iter() {
                                            for n in 0..qf.out_edges.len() {
                                                for &(_, y) in &qf.out_edges[n] {
                                                    if y < qf.out_edges.len()
                                                        && qf.out_edges[y].iter().any(|(rr, _)| *rr == r2)
                                                    {
                                                        chain_opp = true;
                                                        break 'outer;
                                                    }
                                                }
                                            }
                                        }
                                        if chain_opp {
                                            lres.push(a);
                                            lknown.push((a, sound));
                                            continue;
                                        }
                                    }
                                    // Milestone 1 validation: build the pseudo-model and
                                    // accumulate size stats to compare with Konclude.
                                    if pmbuild {
                                        let pm = qf.build_pmodel();
                                        let nn = pm.nodes.len() as u64;
                                        let nc: u64 = pm.nodes.iter().map(|x| x.concepts.len() as u64).sum();
                                        let mc = pm.nodes.iter().map(|x| x.concepts.len()).max().unwrap_or(0) as u64;
                                        DBG_PM_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                                        DBG_PM_TOTNODES.fetch_add(nn, std::sync::atomic::Ordering::Relaxed);
                                        DBG_PM_TOTCONC.fetch_add(nc, std::sync::atomic::Ordering::Relaxed);
                                        DBG_PM_MAXNODES.fetch_max(nn, std::sync::atomic::Ordering::Relaxed);
                                        DBG_PM_MAXCONC.fetch_max(mc, std::sync::atomic::Ordering::Relaxed);
                                    }
                                    if !rf.sufficient {
                                        // KM_HT_QO_INPLACE: complete on the already-built
                                        // per-concept model (no fresh consistent() rebuild).
                                        if inplace {
                                            let clean_set: HashSet<C> =
                                                rf.root_label.iter().copied().collect();
                                            match qf.qo_residue_classify(
                                                &[(a, 0)],
                                                std::slice::from_ref(&clean_set),
                                                qset_ref,
                                            ) {
                                                Some((luns2, lsub2)) => {
                                                    luns.extend(luns2);
                                                    lsub.extend(lsub2);
                                                    continue;
                                                }
                                                None => {} // defer to fresh build below
                                            }
                                        }
                                        // KM_HT_QO_DISCHARGE: a concept-level disjunction is
                                        // safe to discharge (its ⋂-closure is already in the
                                        // forward label) ONLY when it parks at the ROOT node.
                                        // At a FILLER node the same disjunction carries
                                        // role-mediated certain consequences (∃R.disjunct⊑Y
                                        // with Y common to all disjuncts) that the concept
                                        // ⋂-closure cannot reach — those concepts need the
                                        // real model build. Discharge iff every parked
                                        // disjunction is concept-level AND root-anchored.
                                        if discharge
                                            && qf.pending.iter().all(|(n, cid)| {
                                                *n == 0 && concept_level_ref.contains(cid)
                                            })
                                        {
                                            continue;
                                        }
                                        lres.push(a); // parked disjunction ⇒ complete-test
                                        lknown.push((a, sound));
                                        // Tag this residue concept by the DISTINCT clauses
                                        // whose parked disjunctions left it insufficient.
                                        if let Some(h) = res_hist_ref {
                                            let mut seen: HashSet<usize> = HashSet::new();
                                            for &(_n, cid) in qf.pending.iter() {
                                                if seen.insert(cid) {
                                                    h[cid].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                                                }
                                            }
                                        }
                                    }
                                }
                                Some((luns, lsub, lres, lknown))
                            })
                            .expect("spawn pc bulk worker")
                    })
                    .collect();
                handles.into_iter().map(|h| h.join().unwrap()).collect()
            });
            let mut known: HashMap<C, HashSet<C>> = HashMap::new();
            for part in parts {
                match part {
                    Some((u, sb, r, kn)) => {
                        unsat.extend(u);
                        subs.extend(sb);
                        residue.extend(r);
                        for (a, s) in kn {
                            known.insert(a, s.into_iter().collect());
                        }
                    }
                    None => {
                        if trace {
                            eprintln!("QOPC bulk: a concept is out-of-fragment ⇒ defer to CB");
                        }
                        return None;
                    }
                }
            }
            if trace {
                eprintln!(
                    "QOPC bulk done el={:.1}s: suff_subs={} unsat={} residue={} ({} threads)",
                    t_pc.elapsed().as_secs_f64(),
                    subs.len(),
                    unsat.len(),
                    residue.len(),
                    nthreads
                );
                if pmbuild {
                    let cnt = DBG_PM_COUNT.load(Ordering::Relaxed).max(1);
                    eprintln!(
                        "QOPMBUILD: {} pseudo-models | nodes max={} avg={:.1} | concepts/model max={} avg={:.1}",
                        DBG_PM_COUNT.load(Ordering::Relaxed),
                        DBG_PM_MAXNODES.load(Ordering::Relaxed),
                        DBG_PM_TOTNODES.load(Ordering::Relaxed) as f64 / cnt as f64,
                        DBG_PM_MAXCONC.load(Ordering::Relaxed),
                        DBG_PM_TOTCONC.load(Ordering::Relaxed) as f64 / cnt as f64,
                    );
                }
            }
            if let Some(h) = res_hist_ref {
                let mut rows: Vec<(usize, usize)> = h
                    .iter()
                    .enumerate()
                    .map(|(cid, c)| (cid, c.load(std::sync::atomic::Ordering::Relaxed)))
                    .filter(|&(_, c)| c > 0)
                    .collect();
                rows.sort_by(|a, b| b.1.cmp(&a.1));
                let total: usize = rows.iter().map(|&(_, c)| c).sum();
                eprintln!(
                    "QORESHIST residue={} distinct_clauses={} total_parkings={}",
                    residue.len(),
                    rows.len(),
                    total
                );
                for (cid, c) in rows.iter().take(40) {
                    let cl = &self.clauses[*cid].0;
                    let hstr: Vec<String> = cl.head.iter().map(fmt_atom_dbg).collect();
                    let bstr: Vec<String> = cl.body.iter().map(fmt_atom_dbg).collect();
                    eprintln!(
                        "QORESHIST cid={} n={} head=[{}] body=[{}]",
                        cid,
                        c,
                        hstr.join(" ; "),
                        bstr.join(" , ")
                    );
                }
            }
            // KM_HT_QO_CERTAIN: deterministic disjunction resolution (the certain
            // ⋂-closure consequence). Adds the disjunction-mediated subsumers
            // without any model build; the false-residue concepts gain nothing.
            if std::env::var_os("KM_HT_QO_CERTAIN").is_some() {
                let t_c = std::time::Instant::now();
                let new_subs = self.certain_disjunction_consequences(&subs, &qset);
                if trace {
                    eprintln!(
                        "QOCERTAIN: +{} certain disjunction subs el={:.2}s",
                        new_subs.len(),
                        t_c.elapsed().as_secs_f64()
                    );
                }
                subs.extend(new_subs);
                // KM_HT_QO_CERTAIN_ONLY: emit bulk ∪ certain, skip the residue
                // complete test (measure the certain-derivation's coverage vs gold).
                if std::env::var_os("KM_HT_QO_CERTAIN_ONLY").is_some() {
                    let consistent = !(!queries.is_empty() && unsat.len() == queries.len());
                    self.pc_candidates = Vec::new();
                    self.pc_unsat_candidates = Vec::new();
                    self.pc_tainted = Vec::new();
                    return Some((consistent, unsat, subs));
                }
            }
            // fall through to the shared residue-complete block below.
            if pc_residue && !residue.is_empty() {
                if trace {
                    eprintln!(
                        "QOPC residue-complete: {} insufficient of {} (suff bulk {} subs) el={:.1}s",
                        residue.len(), queries.len(), subs.len(), t_pc.elapsed().as_secs_f64()
                    );
                }
                match self.qo_residue_complete(&residue, &qset, &known) {
                    Some((ru, rs)) => {
                        unsat.extend(ru);
                        subs.extend(rs);
                    }
                    None => {
                        if trace {
                            eprintln!("QOPC residue-complete could not certify ⇒ defer to CB");
                        }
                        return None;
                    }
                }
            }
            let consistent = !(!queries.is_empty() && unsat.len() == queries.len());
            if trace {
                eprintln!(
                    "QOPC done (parallel) subs={} unsat={} consistent={} el={:.1}s",
                    subs.len(),
                    unsat.len(),
                    consistent,
                    t_pc.elapsed().as_secs_f64()
                );
            }
            self.pc_candidates = Vec::new();
            self.pc_unsat_candidates = Vec::new();
            self.pc_tainted = Vec::new();
            return Some((consistent, unsat, subs));
        }
        for (i, &a) in queries.iter().enumerate() {
            qf.reset();
            if pc_tally {
                qf.edge_budget = pc_ebudget;
            }
            let rf = qf.saturate(&[CLit::pos(a)]);
            if pc_tally {
                // Count + continue (no defer): the feasibility/residue census.
                if rf.unsupported {
                    tally.2 += 1;
                } else if rf.clashed {
                    tally.3 += 1;
                } else if !rf.sufficient {
                    tally.1 += 1;
                } else {
                    tally.0 += 1;
                }
                if trace && i > 0 && i % 5000 == 0 {
                    eprintln!(
                        "QOPC_TALLY {}/{} el={:.1}s suff={} insuff={} unsup={} clash={}",
                        i,
                        queries.len(),
                        t_pc.elapsed().as_secs_f64(),
                        tally.0,
                        tally.1,
                        tally.2,
                        tally.3
                    );
                }
                continue;
            }
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
                if pc_residue {
                    residue.push(a); // finish with the complete tableau after the bulk
                    continue;
                }
                if trace {
                    eprintln!(
                        "QOPC bail (insufficient) at {}/{} concept {}",
                        i,
                        queries.len(),
                        a
                    );
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
                    // r-Succ (KM_RSUCC): the inverse-augmented forward pass reports
                    // `sufficient`, but a transitive-reachability head `C(x)` on a
                    // shared filler reached across an inverse back-edge was suppressed
                    // (never written, never finalized in the per-concept QOPC path),
                    // so the transitive+inverse reconstruction unsat can be MISSED.
                    // `kp_finalize` runs the reach post-pass (and drains the deferred
                    // inverse-edge checks); if it flags an insufficiency, the forward
                    // model is not trustworthy for `a` ⇒ let the complete tableau
                    // decide it (verify drops it if `a` is really satisfiable). Sound.
                    if qu.rsucc {
                        qu.kp_finalize();
                        if qu.kp_insufficient {
                            unsat_cands.push(a);
                        }
                    }
                }
            }
            if trace && i > 0 && i % 5000 == 0 {
                eprintln!(
                    "QOPC {}/{} subs={} cands={} unsat={} ucands={}",
                    i,
                    queries.len(),
                    subs.len(),
                    cands.len(),
                    unsat.len(),
                    unsat_cands.len()
                );
            }
        }
        if pc_tally {
            eprintln!(
                "QOPC_TALLY DONE concepts={} el={:.1}s suff={} insuff={} unsup={} clash={} (per-concept feasibility: residue = insuff+unsup)",
                queries.len(), t_pc.elapsed().as_secs_f64(),
                tally.0, tally.1, tally.2, tally.3
            );
            // Return a benign answer so the caller does not fall through to the
            // monolithic classify (this is a diagnostic, not a real classification).
            return Some((true, Vec::new(), Vec::new()));
        }
        // Finish the insufficient residue with the per-concept complete tableau.
        // `qo_residue_complete` runs one real model per concept (depth 0 once
        // CARD_RECOG handles cardinality deterministically) + a told-subsumer-keyed
        // per-candidate refutation, parallel over KM_HT_PAR. A `None` means a residue
        // concept is out-of-fragment for the tableau too ⇒ defer the whole (sound).
        if pc_residue && !residue.is_empty() {
            if trace {
                eprintln!(
                    "QOPC residue-complete: {} insufficient of {} (suff bulk {} subs so far) el={:.1}s",
                    residue.len(), queries.len(), subs.len(), t_pc.elapsed().as_secs_f64()
                );
            }
            match self.qo_residue_complete(&residue, &qset, &HashMap::new()) {
                Some((ru, rs)) => {
                    unsat.extend(ru);
                    subs.extend(rs);
                }
                None => {
                    if trace {
                        eprintln!("QOPC residue-complete could not certify ⇒ defer to CB");
                    }
                    return None;
                }
            }
        }
        let consistent = !(!queries.is_empty() && unsat.len() == queries.len());
        if trace {
            eprintln!(
                "QOPC done subs={} cands={} unsat={} ucands={} consistent={}",
                subs.len(),
                cands.len(),
                unsat.len(),
                unsat_cands.len(),
                consistent
            );
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
        let _sg_t0 = std::time::Instant::now();
        let g = qk.saturate_global(queries);
        if trace || std::env::var_os("KM_HT_QO_PMTIME").is_some() {
            eprintln!(
                "KPSET saturate_global: {:.2}s nodes={} unsupported={} kp_insuff={} qo_insuff={} pending={}",
                _sg_t0.elapsed().as_secs_f64(),
                qk.label.len(),
                g.unsupported,
                qk.kp_insufficient,
                qk.qo_insufficient,
                qk.pending.len()
            );
        }
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
                // KM_HT_QO_DUMP_AFFECTED=<path>: write the affected (residue) query
                // concept IDs (one per line), to feed a complete-SAT pass restricted
                // to the residue — the lazy-clean-bulk + complete-residue hybrid.
                if let Some(p) = std::env::var_os("KM_HT_QO_DUMP_AFFECTED") {
                    use std::io::Write as _;
                    if let Ok(mut f) = std::fs::File::create(&p) {
                        for &(a, _) in &residue_nodes {
                            let _ = writeln!(f, "{}", a);
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
                    eprintln!(
                        "QOKP insuff-source: forall(∀)={} card(≤n)={} cardmerge_done={} | eq_defer[nonfiller={} norole={} unsat={} other={}]",
                        DBG_FORALL_INSUFF.load(Ordering::Relaxed),
                        DBG_CARD_INSUFF.load(Ordering::Relaxed),
                        DBG_CARDMERGE.load(Ordering::Relaxed),
                        DBG_EQ_NONFILLER.load(Ordering::Relaxed),
                        DBG_EQ_NOROLE.load(Ordering::Relaxed),
                        DBG_EQ_UNSAT.load(Ordering::Relaxed),
                        DBG_EQ_OTHER.load(Ordering::Relaxed),
                    );
                }
                if residue.is_empty() {
                    // every query concept CLEAN ⇒ sound+complete from the single pass.
                    let consistent = !(!queries.is_empty() && clean_unsat.len() == queries.len());
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
                    && (qk.residue_unsafe || (qk.kp_insuff_nodes.is_empty() && !qk.qo_insufficient))
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
        let node_of: HashMap<C, Node> = queries
            .iter()
            .enumerate()
            .map(|(i, &c)| (c, i as Node))
            .collect();
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
        // The hybrid pays off when there is an inverse contribution to compose, so a
        // non-inverse ont normally defers here (it would only pay INVCOMPOSE/sat_mode
        // overhead). EXCEPTION: under residue-complete, the global-forward path is
        // also the lazy-saturation classifier for PURE-DISJUNCTION onts (ore_ont_3215:
        // SHI, 18323 disjunctions, no inverse bridge) — the same structure Konclude
        // uses (non-branching precompute + residue SAT tests). Those have no inverse
        // bridge but DO have parked disjunctions the residue-complete verify decides,
        // so do not defer them here; let the forward pass + residue-complete run.
        let residue_complete_disj = std::env::var_os("KM_HT_QO_RESIDUE_COMPLETE").is_some();
        if certify_only && count_inverse_bridges(&self.clauses) == 0 && !residue_complete_disj {
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
        // KM_NO_INVCOMPOSE off-switch: INVCOMPOSE turns compact inverse propagation
        // into a LARGER forward saturation (9724: 125519 -> 139934 clauses) that
        // overruns the node cap (`unsupported`). Konclude does the opposite — it
        // keeps the inverse and writes backward (`applyALLRule` = KM_HT_QO_KPWRITE),
        // creating NO new nodes. This switch lets the kpwrite path keep the bridges.
        if std::env::var_os("KM_HT_QO_INVCOMPOSE").is_some()
            && std::env::var_os("KM_NO_INVCOMPOSE").is_none()
        {
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
            // KM_HT_QO_GFCERT (2026-06-26): before deferring, try the CLEAN
            // global-forward certify. `qo_classify_global_fwd` returns `Some` ONLY
            // when the single forward pass is fully clean AND complete — either the
            // card-split affected-set is empty (`res == 0`) or, in INVCOMPOSE
            // write-mode, there are ZERO residual inverse bridges (composition
            // total, so the forward closure already includes every inverse
            // contribution). Both are sound (forward-only never over-derives) and
            // complete by their guards; every incomplete/insufficient/parked case
            // returns `None` ⇒ we still defer to CB. This recovers onts whose few
            // inverse bridges compose totally (7581: 4 bridges → 0 residual via
            // INVCHAIN, certifies in ~18s) WITHOUT running the verify funnel that
            // blows up on the hard giants. Opt-in until corpus-validated.
            if std::env::var_os("KM_HT_QO_GFCERT").is_some() {
                if let Some(r) = self.qo_classify_global_fwd(queries) {
                    if std::env::var_os("KM_HT_TRACE").is_some() {
                        eprintln!(
                            "QO router: global-forward CLEAN certify (sound+complete) ⇒ answer"
                        );
                    }
                    return Some(r);
                }
            }
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
                    let template: Vec<Clause> =
                        self.clauses.iter().map(|(c, _, _)| c.clone()).collect();
                    // Ht-only TCC: extend the residue template with the __cmpp__ clauses so
                    // the complete tableau (with blocking) propagates transitive markers
                    // through cross-role chains.  The QoSat (reads &self.clauses) never sees
                    // them — no cascade.  The Ht's blocking bounds the propagation.
                    let template: Vec<Clause> = if !self.ht_tcc_clauses.is_empty() {
                        let mut t = template;
                        t.extend(self.ht_tcc_clauses.iter().cloned());
                        t
                    } else {
                        template
                    };
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
                                            let i = next
                                                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
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
            eprintln!(
                "QOC entry queries={} clauses={}",
                queries.len(),
                self.clauses.len()
            );
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
            && queries
                .iter()
                .all(|&a| qs.node_unsat.contains(&node_of[&a]));
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
                eprintln!(
                    "KM_HT [qo-p1] qi={}/{} a={} node={} dead={} suff={} open={} lab_sz={}",
                    qi,
                    queries.len(),
                    a,
                    n,
                    dead,
                    suff,
                    open,
                    lab.len()
                );
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
            for b in known
                .iter()
                .copied()
                .filter(|b| *b != a && qset.contains(b) && satset.contains(b))
            {
                subs.push((a, b));
            }
            // candidates = possible(a) minus known, restricted to query concepts.
            let mut cand: Vec<C> = possible
                .get(&a)
                .map(|s| {
                    s.iter()
                        .copied()
                        .filter(|b| {
                            *b != a && qset.contains(b) && satset.contains(b) && !known.contains(b)
                        })
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
                    let comp = CLit {
                        neg: !lit.neg,
                        c: lit.c,
                    };
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

// ===================== Konclude pseudo-model subsumer prune ====================
//
// Faithful port of Konclude's fast pseudo-model subsumption precheck
// (CClassificationClassPseudoModel{Data,RoleData} + isPseudoModelSubsumerPossible,
// COptimizedKPSetClassSubsumptionClassifierThread.cpp:1626). Each concept gets a
// bounded (depth ≤ MAX_PM_DEPTH, ≤ MAX_PM_NODES) labelled tree of model nodes; the
// prune answers "can subsumer B still subsume subsumed A?" purely from the two
// pseudo-models, returning false ⇒ definitely-not-subsumed (no tableau test). It
// can only ELIMINATE a candidate, never confirm a subsumption.

const MAX_PM_DEPTH: u32 = 3;
const MAX_PM_NODES: usize = 30;

/// Per-role cardinality record (CClassificationClassPseudoModelRoleData).
#[derive(Clone, Debug, Default)]
struct PmRole {
    /// mDeterministicFlag: this role has a deterministic successor.
    det: bool,
    lower_at_least: i64, // max deterministic ≥n parameter on this role
    upper_at_least: i64, // number of successor nodes actually present
    upper_at_most: i64,  // min deterministic ≤n parameter
    lower_at_most: i64,  // number of successor nodes (lower bound)
    succ_model: i64,     // child model-node id, or -1
}

impl PmRole {
    /// CClassificationClassPseudoModelRoleData::isPossibleSubsumerOf
    /// (`self` = subsumer B's role data, `subsumed` = A's).
    fn is_possible_subsumer_of(&self, subsumed: &PmRole) -> bool {
        if self.det {
            if self.lower_at_least > subsumed.upper_at_least {
                return false; // B needs more successors than A's model can have
            }
            if self.upper_at_most < subsumed.lower_at_most {
                return false; // B caps successors below A's forced minimum
            }
        }
        true
    }
}

/// One pseudo-model node (CClassificationClassPseudoModelData): concept→det-flag
/// and role→role-data maps, each with a validity flag (false when the originating
/// tableau node was blocked / cached / nominal / over-bound ⇒ skipped by the prune).
#[derive(Clone, Debug)]
struct PmNode {
    concepts: std::collections::BTreeMap<C, bool>, // concept → deterministic
    roles: std::collections::BTreeMap<R, PmRole>,
    valid_concepts: bool,
    valid_roles: bool,
}

impl Default for PmNode {
    fn default() -> Self {
        PmNode {
            concepts: std::collections::BTreeMap::new(),
            roles: std::collections::BTreeMap::new(),
            valid_concepts: true,
            valid_roles: true,
        }
    }
}

/// A concept's pseudo-model: a bounded tree of nodes; node 0 is the root.
#[derive(Clone, Debug, Default)]
struct PModel {
    nodes: Vec<PmNode>,
}

/// isPseudoModelSubsumerPossible (COptimizedKPSetClassSubsumptionClassifierThread
/// .cpp:1626). Can subsumer `b`@`bn` still subsume subsumed `a`@`an`? Returns
/// false ⇒ prune (definitely not subsumed). A deterministic feature B requires but
/// A lacks ⇒ impossible. Non-deterministic B-entries never prune. Recurses on
/// shared roles into the successor models (same A-subsumed / B-subsumer direction).
fn pm_subsumer_possible(a: &PModel, an: usize, b: &PModel, bn: usize) -> bool {
    let na = &a.nodes[an];
    let nb = &b.nodes[bn];
    // (a) concept check: a deterministic B-concept absent from A ⇒ prune.
    if na.valid_concepts && nb.valid_concepts {
        for (&cb, &det_b) in nb.concepts.iter() {
            if det_b && !na.concepts.contains_key(&cb) {
                return false;
            }
        }
    }
    // (b) role / cardinality check.
    if na.valid_roles && nb.valid_roles {
        for (&rb, rb_data) in nb.roles.iter() {
            match na.roles.get(&rb) {
                Some(ra_data) => {
                    if !rb_data.is_possible_subsumer_of(ra_data) {
                        return false;
                    }
                    if ra_data.succ_model >= 0 && rb_data.succ_model >= 0 {
                        if !pm_subsumer_possible(
                            a,
                            ra_data.succ_model as usize,
                            b,
                            rb_data.succ_model as usize,
                        ) {
                            return false;
                        }
                    }
                }
                None => {
                    // role present in B only: prune iff deterministic in B.
                    if rb_data.det {
                        return false;
                    }
                }
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    // Konclude pm_subsumer_possible: a deterministic subsumer-concept absent in the
    // subsumed prunes; non-deterministic does not; cardinality bounds prune.
    fn pm_one(concepts: &[(C, bool)], roles: &[(R, PmRole)]) -> PModel {
        let mut n = PmNode::default();
        for &(c, d) in concepts {
            n.concepts.insert(c, d);
        }
        for (r, rd) in roles {
            n.roles.insert(*r, rd.clone());
        }
        PModel { nodes: vec![n] }
    }

    #[test]
    fn pm_prune_concept_deterministic() {
        // A = {A det, S det}; subsumer S = {S det} ⇒ possible (S's det ⊆ A).
        let a = pm_one(&[(1, true), (2, true)], &[]);
        let s = pm_one(&[(2, true)], &[]);
        assert!(pm_subsumer_possible(&a, 0, &s, 0));
        // unrelated CC = {9 det}: 9 absent in A and deterministic ⇒ PRUNE.
        let cc = pm_one(&[(9, true)], &[]);
        assert!(!pm_subsumer_possible(&a, 0, &cc, 0));
        // CC' = {9 NONdet}: absent but non-deterministic ⇒ NOT pruned.
        let cc2 = pm_one(&[(9, false)], &[]);
        assert!(pm_subsumer_possible(&a, 0, &cc2, 0));
    }

    #[test]
    fn pm_prune_cardinality() {
        // B needs ≥3 on role r (det); A's model has only 1 successor ⇒ PRUNE.
        let a = pm_one(
            &[],
            &[(
                0,
                PmRole {
                    det: true,
                    upper_at_least: 1,
                    ..Default::default()
                },
            )],
        );
        let b = pm_one(
            &[],
            &[(
                0,
                PmRole {
                    det: true,
                    lower_at_least: 3,
                    ..Default::default()
                },
            )],
        );
        assert!(!pm_subsumer_possible(&a, 0, &b, 0));
        // role present only in B and deterministic ⇒ PRUNE.
        let a2 = pm_one(&[], &[]);
        assert!(!pm_subsumer_possible(&a2, 0, &b, 0));
    }

    fn lit(neg: bool, c: C) -> CLit {
        CLit { neg, c }
    }

    #[test]
    fn subset_blocking_bit_labels_track_add_and_backtrack() {
        let mut ext = Ext::new();
        ext.incr2 = true;
        ext.enable_block_bits();
        let root = ext.new_root();
        let child = ext.new_node(Some(root));
        for l in [lit(false, 1), lit(true, 70)] {
            ext.add_concept(root, l, &dep_empty());
            ext.add_concept(child, l, &dep_empty());
        }
        assert_eq!(ext.i2_recompute(), vec![false, true]);

        let mark = ext.mark();
        ext.add_concept(child, lit(false, 130), &dep_empty());
        assert_eq!(ext.i2_recompute(), vec![false, false]);
        ext.backtrack_to(mark);
        assert_eq!(ext.i2_recompute(), vec![false, true]);

        for n in 0..ext.num_nodes() {
            for c in 0..160 {
                for neg in [false, true] {
                    let l = lit(neg, c);
                    let e = Ext::enc_lit(l);
                    let bit = ext.block_bits.as_ref().unwrap()[n]
                        .get(e >> 6)
                        .is_some_and(|word| word & (1u64 << (e & 63)) != 0);
                    assert_eq!(bit, ext.concepts[n].contains_key(&l));
                }
            }
        }
    }
    fn con(neg: bool, c: C, t: Var) -> Atom {
        Atom::Concept {
            lit: CLit { neg, c },
            t,
        }
    }
    fn role(r: R, s: Var, t: Var) -> Atom {
        Atom::Role { r, s, t }
    }
    fn exists(r: R, neg: bool, c: C, t: Var) -> Atom {
        Atom::Exists {
            r,
            fil: CLit { neg, c },
            t,
        }
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
    fn ni_certificate_accepts_direct_number_role_successor() {
        let mut t = ht(Vec::new());
        t.cert_number_roles.insert(R0);
        let root = t.ext.new_root();
        let child = t.ext.new_node(Some(root));
        t.ext.add_edge(R0, root, child, &dep_empty());
        assert!(!t.nominal_number_non_successor());
    }

    #[test]
    fn ni_certificate_rejects_non_successor_number_role_neighbour() {
        let mut t = ht(Vec::new());
        t.cert_number_roles.insert(R0);
        let root = t.ext.new_root();
        let other_root = t.ext.new_root();
        let child = t.ext.new_node(Some(other_root));
        t.ext.add_edge(R0, root, child, &dep_empty());
        assert!(t.nominal_number_non_successor());
    }

    #[test]
    fn distinct_pair_merge_clashes() {
        // Konclude `isIndividualNodesMergeable`: merging an asserted-distinct pair
        // is a clash. The clash dep carries BOTH the merge cause and the
        // inequality witness, so it backjumps past whichever is shallower.
        let mut e = Ext::new();
        let a = e.new_root();
        let b = e.new_root();
        e.add_distinct(a, b, &dep_add(&dep_empty(), 3));
        assert!(e.are_distinct(a, b).is_some());
        e.merge_into(a, b, &dep_add(&dep_empty(), 7));
        assert!(e.has_clash());
        assert_eq!(dep_max(&e.clash_dep()), 7);
    }

    #[test]
    fn distinct_self_is_clash() {
        // a ≠ a is an immediate contradiction.
        let mut e = Ext::new();
        let a = e.new_root();
        e.add_distinct(a, a, &dep_add(&dep_empty(), 4));
        assert!(e.has_clash());
    }

    #[test]
    fn distinct_backtrack_undoes_then_mergeable() {
        // The inequality is trail-recorded: a backtrack past it makes the pair
        // mergeable again with no clash.
        let mut e = Ext::new();
        let a = e.new_root();
        let b = e.new_root();
        let m = e.mark();
        e.add_distinct(a, b, &dep_empty());
        assert!(e.are_distinct(a, b).is_some());
        e.backtrack_to(m);
        assert!(e.are_distinct(a, b).is_none());
        e.merge_into(a, b, &dep_empty());
        assert!(!e.has_clash());
    }

    #[test]
    fn card_atleast_sat_builds_successors() {
        // A ⊑ ≥2 R0.FC : satisfiable; builds two distinct FC-successors.
        const MK: C = 20;
        const FC: C = 21;
        let cls = vec![Clause::new(vec![con(false, A, X)], vec![con(false, MK, X)])];
        let mut t = ht(cls);
        let mut defs = HashMap::new();
        defs.insert(
            MK,
            CardDef {
                kind: CardKind::Min,
                n: 2,
                role: R0,
                filler: CLit::pos(FC),
            },
        );
        t.set_card_defs(defs);
        assert_eq!(t.consistent(&[CLit::pos(A)]), Some(true));
    }

    #[test]
    fn card_atleast_unsat_via_filler_clash() {
        // A ⊑ ≥1 R0.FC, FC ⊑ ⊥ ⇒ {A} unsat: the required successor carries FC,
        // which clashes (FC ⊑ G and FC ⊑ ¬G). Confirms the rule creates the
        // successor and propagates the filler.
        const MK: C = 20;
        const FC: C = 21;
        const G: C = 22;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![con(false, MK, X)]),
            Clause::new(vec![con(false, FC, X)], vec![con(false, G, X)]),
            Clause::new(vec![con(false, FC, X)], vec![con(true, G, X)]),
        ];
        let mut t = ht(cls);
        let mut defs = HashMap::new();
        defs.insert(
            MK,
            CardDef {
                kind: CardKind::Min,
                n: 1,
                role: R0,
                filler: CLit::pos(FC),
            },
        );
        t.set_card_defs(defs);
        assert_eq!(t.consistent(&[CLit::pos(A)]), Some(false));
    }

    #[test]
    fn card_atleast_recursive_terminates_via_blocking() {
        // A ⊑ ≥1 R0.A : an infinite R0-chain that MUST be folded by blocking. The
        // ≥n rule is gated by blocking exactly like ∃, so the successor (label
        // {A, marker}) is blocked by the root and spawns no further successors ⇒
        // consistent and terminating (the model-folding the legacy Eq-merge lost).
        const MK: C = 20;
        let cls = vec![Clause::new(vec![con(false, A, X)], vec![con(false, MK, X)])];
        let mut t = ht(cls);
        let mut defs = HashMap::new();
        defs.insert(
            MK,
            CardDef {
                kind: CardKind::Min,
                n: 1,
                role: R0,
                filler: CLit::pos(A),
            },
        );
        t.set_card_defs(defs);
        assert_eq!(t.consistent(&[CLit::pos(A)]), Some(true));
    }

    #[test]
    fn card_atmost_distinct_clash() {
        // A ⊑ ≥3 R0.FC ⊓ ≤2 R0.FC : three pairwise-distinct FC-successors cannot
        // fit into ≤2 (no mergeable pair) ⇒ {A} unsat. Exercises the ≤n
        // distinct-clash path against the ≥n distinct successors.
        const MN: C = 20;
        const MX: C = 21;
        const FC: C = 22;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![con(false, MN, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(false, MX, X)]),
        ];
        let mut t = ht(cls);
        let mut defs = HashMap::new();
        defs.insert(
            MN,
            CardDef {
                kind: CardKind::Min,
                n: 3,
                role: R0,
                filler: CLit::pos(FC),
            },
        );
        defs.insert(
            MX,
            CardDef {
                kind: CardKind::Max,
                n: 2,
                role: R0,
                filler: CLit::pos(FC),
            },
        );
        t.set_card_defs(defs);
        assert_eq!(t.consistent(&[CLit::pos(A)]), Some(false));
    }

    #[test]
    fn card_atmost_merge_sat() {
        // A ⊑ ∃R0.G0 ⊓ ∃R0.G1 ⊓ ≤1 R0.FC, G0⊑FC, G1⊑FC: two NON-distinct
        // FC-successors merge to satisfy ≤1 ⇒ SAT.
        const MX: C = 21;
        const FC: C = 22;
        const G0: C = 23;
        const G1: C = 24;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G0, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G1, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, FC, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(false, FC, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(false, MX, X)]),
        ];
        let mut t = ht(cls);
        let mut defs = HashMap::new();
        defs.insert(
            MX,
            CardDef {
                kind: CardKind::Max,
                n: 1,
                role: R0,
                filler: CLit::pos(FC),
            },
        );
        t.set_card_defs(defs);
        assert_eq!(t.consistent(&[CLit::pos(A)]), Some(true));
    }

    #[test]
    fn card_atmost_merge_clash() {
        // Same shape but G0⊑P, G1⊑¬P: the ≤1-forced merge of the two FC-successors
        // clashes (P ⊓ ¬P) and there is no other option ⇒ {A} unsat.
        const MX: C = 21;
        const FC: C = 22;
        const G0: C = 23;
        const G1: C = 24;
        const P: C = 25;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G0, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G1, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, FC, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(false, FC, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, P, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(true, P, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(false, MX, X)]),
        ];
        let mut t = ht(cls);
        let mut defs = HashMap::new();
        defs.insert(
            MX,
            CardDef {
                kind: CardKind::Max,
                n: 1,
                role: R0,
                filler: CLit::pos(FC),
            },
        );
        t.set_card_defs(defs);
        assert_eq!(t.consistent(&[CLit::pos(A)]), Some(false));
    }

    #[test]
    fn card_atmost_choose_picks_negative() {
        // A ⊑ ≤0 R0.FC ⊓ ∃R0.G1, G1 unrelated to FC: the unqualified successor must
        // be labelled ¬FC by the choose rule (≤0 forbids FC) ⇒ SAT. Exercises
        // `branch_choose` (the FC branch clashes, the ¬FC branch is the model).
        const MX: C = 21;
        const FC: C = 22;
        const G1: C = 24;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G1, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(false, MX, X)]),
        ];
        let mut t = ht(cls);
        let mut defs = HashMap::new();
        defs.insert(
            MX,
            CardDef {
                kind: CardKind::Max,
                n: 0,
                role: R0,
                filler: CLit::pos(FC),
            },
        );
        t.set_card_defs(defs);
        assert_eq!(t.consistent(&[CLit::pos(A)]), Some(true));
    }

    #[test]
    fn distinct_propagates_through_merge() {
        // a≠c, then merge b into a's survivor; if later we try to merge the
        // survivor with c it must clash (the inequality followed the merge).
        // Build: c≠a (distinct), merge a,b (ok, survivor=min). survivor still ≠ c.
        let mut e = Ext::new();
        let a = e.new_root();
        let b = e.new_root();
        let c = e.new_root();
        e.add_distinct(b, c, &dep_empty()); // b ≠ c
        e.merge_into(a, b, &dep_empty()); // b folds into a (survivor a)
        assert!(!e.has_clash());
        // a inherited b's inequality with c
        assert!(e.are_distinct(a, c).is_some());
        e.merge_into(a, c, &dep_empty());
        assert!(e.has_clash());
    }

    #[test]
    fn clash_a_and_not_a() {
        assert_eq!(
            ht(vec![]).consistent(&[CLit::pos(A), CLit::neg(A)]),
            Some(false)
        );
    }
    #[test]
    fn simple_sat() {
        assert_eq!(ht(vec![]).consistent(&[CLit::pos(A)]), Some(true));
    }
    #[test]
    fn existential_then_universal_clash() {
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(
                vec![con(false, A, X), role(R0, X, 1)],
                vec![con(true, B, 1)],
            ),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(false));
    }
    #[test]
    fn existential_universal_consistent() {
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(
                vec![con(false, A, X), role(R0, X, 1)],
                vec![con(false, D, 1)],
            ),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(true));
    }
    #[test]
    fn disjunction_unsat_both_branches_clash() {
        let cls = vec![
            Clause::new(
                vec![con(false, A, X)],
                vec![con(false, B, X), con(false, D, X)],
            ),
            Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(true, D, X)]),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(false));
    }
    #[test]
    fn disjunction_one_branch_open() {
        let cls = vec![
            Clause::new(
                vec![con(false, A, X)],
                vec![con(false, B, X), con(false, D, X)],
            ),
            Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(true));
    }
    #[test]
    fn unit_propagation_via_dead_disjunct() {
        // A ⊑ B ⊔ D, A ⊑ ¬B ⇒ D forced; {A,¬D} unsat. Exercises scan unit-prop.
        let cls = vec![
            Clause::new(
                vec![con(false, A, X)],
                vec![con(false, B, X), con(false, D, X)],
            ),
            Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
        ];
        assert_eq!(
            ht(cls).consistent(&[CLit::pos(A), CLit::neg(D)]),
            Some(false)
        );
    }
    #[test]
    fn horn_chain_delta() {
        // A→B, B→D ; {A,¬D} unsat — exercises delta trigger chaining.
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![con(false, B, X)]),
            Clause::new(vec![con(false, B, X)], vec![con(false, D, X)]),
        ];
        assert_eq!(
            ht(cls).consistent(&[CLit::pos(A), CLit::neg(D)]),
            Some(false)
        );
    }
    #[test]
    fn forall_propagation_delta_both_triggers() {
        // A ⊑ ∃r.B (succ gets B), B ⊑ C? no: A ⊑ ∀r.D and successor has B; check
        // ∀ fires whether the edge or the guard concept arrives first.
        // A→∃r.B ; A ∧ r(x,y) → D(y) ; D⊓B disjoint at y via D→¬B? use: A⊑∀r.¬B.
        const C2: C = 2;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(
                vec![con(false, A, X), role(R0, X, 1)],
                vec![con(false, C2, 1)],
            ),
            Clause::new(vec![con(false, C2, X)], vec![con(true, B, X)]),
        ];
        // successor is B (from ∃) and C2 (from ∀), C2→¬B clashes ⇒ A unsat.
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(false));
    }
    #[test]
    fn infinite_chain_blocks_and_terminates() {
        let cls = vec![Clause::new(
            vec![con(false, A, X)],
            vec![exists(R0, false, A, X)],
        )];
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
            Clause::new(
                vec![role(R0, X, 1), role(R0, X, 2)],
                vec![Atom::Eq { s: 1, t: 2 }],
            ),
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
            Clause::new(
                vec![role(R0, X, 1), role(R0, X, 2)],
                vec![Atom::Eq { s: 1, t: 2 }],
            ),
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
            Clause::new(
                vec![role(R0, X, 1), role(R0, X, 2)],
                vec![Atom::Eq { s: 1, t: 2 }],
            ),
        ];
        assert_eq!(ht(cls).consistent(&[CLit::pos(A)]), Some(true));
    }
    #[test]
    fn atmost2_qualified_merge_branch_sat() {
        // KM_HT_QMERGE: ≤2 r.F with three F-successors forces identifying one pair
        // (the AtMost rule's non-deterministic merge). y0:P, y1:Q, y2:P with
        // P⊓Q⊑⊥, so only merging the two P-successors avoids a clash — the search
        // must branch past the two clashing pairs ⇒ {A} SAT. Exercises the merge
        // branch + backtrack over a clashing choice (the n≥2 case at apply_head).
        std::env::set_var("KM_HT_NUMBER", "1");
        const F: C = 10;
        const P: C = 11;
        const Q: C = 12;
        const G0: C = 13;
        const G1: C = 14;
        const G2: C = 15;
        let atmost2 = Clause::new(
            vec![
                role(R0, X, 1),
                con(false, F, 1),
                role(R0, X, 2),
                con(false, F, 2),
                role(R0, X, 3),
                con(false, F, 3),
            ],
            vec![
                Atom::Eq { s: 1, t: 2 },
                Atom::Eq { s: 1, t: 3 },
                Atom::Eq { s: 2, t: 3 },
            ],
        );
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G0, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G1, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G2, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, F, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, P, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(false, F, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(false, Q, X)]),
            Clause::new(vec![con(false, G2, X)], vec![con(false, F, X)]),
            Clause::new(vec![con(false, G2, X)], vec![con(false, P, X)]),
            atmost2,
            Clause::new(vec![con(false, P, X), con(false, Q, X)], vec![]),
        ];
        let mut t = ht(cls);
        t.set_qmerge();
        assert_eq!(t.consistent(&[CLit::pos(A)]), Some(true));
    }
    #[test]
    fn atmost2_qualified_merge_branch_unsat() {
        // KM_HT_QMERGE: ≤2 r.F with three PAIRWISE-disjoint F-successors. Every
        // identification clashes, so the AtMost cannot be satisfied ⇒ {A} unsat.
        // Exercises the all-choices-fail conflict path of the merge branch.
        std::env::set_var("KM_HT_NUMBER", "1");
        const F: C = 10;
        const P: C = 11;
        const Q: C = 12;
        const S: C = 16;
        const G0: C = 13;
        const G1: C = 14;
        const G2: C = 15;
        let atmost2 = Clause::new(
            vec![
                role(R0, X, 1),
                con(false, F, 1),
                role(R0, X, 2),
                con(false, F, 2),
                role(R0, X, 3),
                con(false, F, 3),
            ],
            vec![
                Atom::Eq { s: 1, t: 2 },
                Atom::Eq { s: 1, t: 3 },
                Atom::Eq { s: 2, t: 3 },
            ],
        );
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G0, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G1, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G2, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, F, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, P, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(false, F, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(false, Q, X)]),
            Clause::new(vec![con(false, G2, X)], vec![con(false, F, X)]),
            Clause::new(vec![con(false, G2, X)], vec![con(false, S, X)]),
            atmost2,
            Clause::new(vec![con(false, P, X), con(false, Q, X)], vec![]),
            Clause::new(vec![con(false, P, X), con(false, S, X)], vec![]),
            Clause::new(vec![con(false, Q, X), con(false, S, X)], vec![]),
        ];
        let mut t = ht(cls);
        t.set_qmerge();
        assert_eq!(t.consistent(&[CLit::pos(A)]), Some(false));
    }
    #[test]
    fn atleast2_recognition_dead_merge_unsat() {
        // KM_HT_NUMBER: the ≥n recognition head `r(x,y0)∧F(y0)∧r(x,y1)∧F(y1) →
        // Q(x) ∨ y0≈y1` (the contrapositive of `≥2 r.F ⊑ Q`). A has two
        // r-successors in F that cannot merge (one carries P, the other ¬P), and
        // A ⊑ ¬Q. The Q disjunct is dead (¬Q present) and the only merge clashes
        // (P ⊓ ¬P) ⇒ {A} unsat (A ⊑ Q is forced). Exercises the mixed concept+Eq
        // head that previously bailed `unsupported`, via the dead-concept +
        // unit-merge path.
        std::env::set_var("KM_HT_NUMBER", "1");
        const F: C = 10;
        const P: C = 11;
        const Q: C = 12;
        const G0: C = 13;
        const G1: C = 14;
        let recog = Clause::new(
            vec![
                role(R0, X, 1),
                con(false, F, 1),
                role(R0, X, 2),
                con(false, F, 2),
            ],
            vec![con(false, Q, X), Atom::Eq { s: 1, t: 2 }],
        );
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G0, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G1, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, F, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, P, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(false, F, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(true, P, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(true, Q, X)]),
            recog,
        ];
        let mut t = ht(cls);
        t.set_number(true);
        assert_eq!(t.consistent(&[CLit::pos(A)]), Some(false));
    }
    #[test]
    fn atleast2_recognition_branch_asserts_concept_unsat() {
        // ≥2 recognition BRANCH: Q is live and the merge is dead (P / ¬P), so the
        // mixed head `Q ∨ y0≈y1` is a 2-option deferred branch. Q ⊑ Z conflicts
        // with A ⊑ ¬Z, and the merge clashes — both options fail ⇒ {A} unsat. This
        // can only be unsat if the recognition actually ASSERTS Q in its branch
        // (else the Q option is a spurious model). Exercises branch_merge over a
        // mixed concept+merge option set.
        std::env::set_var("KM_HT_NUMBER", "1");
        const F: C = 10;
        const P: C = 11;
        const Q: C = 12;
        const Z: C = 13;
        const G0: C = 14;
        const G1: C = 15;
        let recog = Clause::new(
            vec![
                role(R0, X, 1),
                con(false, F, 1),
                role(R0, X, 2),
                con(false, F, 2),
            ],
            vec![con(false, Q, X), Atom::Eq { s: 1, t: 2 }],
        );
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G0, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G1, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, F, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, P, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(false, F, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(true, P, X)]),
            Clause::new(vec![con(false, Q, X)], vec![con(false, Z, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(true, Z, X)]),
            recog,
        ];
        let mut t = ht(cls);
        t.set_number(true);
        assert_eq!(t.consistent(&[CLit::pos(A)]), Some(false));
    }
    #[test]
    fn atleast2_recognition_concept_branch_sat() {
        // Same shape, but the recognized Q is consistent (no ¬Z), so asserting Q
        // in the recognition branch yields a model ⇒ {A} sat. Guards against a
        // spurious recognition clash (the Q branch must be explored and succeed).
        std::env::set_var("KM_HT_NUMBER", "1");
        const F: C = 10;
        const P: C = 11;
        const Q: C = 12;
        const Z: C = 13;
        const G0: C = 14;
        const G1: C = 15;
        let recog = Clause::new(
            vec![
                role(R0, X, 1),
                con(false, F, 1),
                role(R0, X, 2),
                con(false, F, 2),
            ],
            vec![con(false, Q, X), Atom::Eq { s: 1, t: 2 }],
        );
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G0, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G1, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, F, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, P, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(false, F, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(true, P, X)]),
            Clause::new(vec![con(false, Q, X)], vec![con(false, Z, X)]),
            recog,
        ];
        let mut t = ht(cls);
        t.set_number(true);
        assert_eq!(t.consistent(&[CLit::pos(A)]), Some(true));
    }
    #[test]
    fn nominal_orule_merge_clash_unsat() {
        // Nominals: A has an r-successor in {o}⊓P and an s-successor in {o}⊓Q with
        // P⊓Q⊑⊥. The o-rule merges the two {o}-carriers (a singleton) into one
        // node, uniting P and Q ⇒ clash ⇒ {A} unsat. Exercises process_nominals
        // and the merge dep flowing into the clash.
        const N: C = 20;
        const P: C = 11;
        const Q: C = 12;
        const G0: C = 13;
        const G1: C = 14;
        const R1: R = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G0, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R1, false, G1, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, N, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, P, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(false, N, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(false, Q, X)]),
            Clause::new(vec![con(false, P, X), con(false, Q, X)], vec![]),
        ];
        let mut t = ht(cls);
        t.set_nominals(vec![N]);
        assert_eq!(t.consistent(&[CLit::pos(A)]), Some(false));
    }
    #[test]
    fn nominal_orule_merge_sat() {
        // Same shape, but both {o}-carriers carry the SAME concept P (no clash):
        // the o-rule merges them into one individual and the model is SAT.
        const N: C = 20;
        const P: C = 11;
        const G0: C = 13;
        const G1: C = 14;
        const R1: R = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, G0, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R1, false, G1, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, N, X)]),
            Clause::new(vec![con(false, G0, X)], vec![con(false, P, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(false, N, X)]),
            Clause::new(vec![con(false, G1, X)], vec![con(false, P, X)]),
        ];
        let mut t = ht(cls);
        t.set_nominals(vec![N]);
        assert_eq!(t.consistent(&[CLit::pos(A)]), Some(true));
    }
    #[test]
    fn anywhere_blocking_also_terminates() {
        let cls = vec![Clause::new(
            vec![con(false, A, X)],
            vec![exists(R0, false, A, X)],
        )];
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
            Clause::new(
                vec![con(false, P, X)],
                vec![con(false, Q, X), con(false, R_, X)],
            ),
            Clause::new(
                vec![con(false, A, X)],
                vec![con(false, B, X), con(false, D, X)],
            ),
            Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(true, D, X)]),
        ];
        assert_eq!(
            ht(cls).consistent(&[CLit::pos(P), CLit::pos(A)]),
            Some(false)
        );
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
                Clause::new(
                    vec![con(false, A, X)],
                    vec![con(false, B, X), con(false, D, X)],
                ),
                Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
                Clause::new(vec![con(false, A, X)], vec![con(true, D, X)]),
            ]
        };
        let open = || {
            vec![
                Clause::new(
                    vec![con(false, A, X)],
                    vec![con(false, B, X), con(false, D, X)],
                ),
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
            Clause::new(
                vec![con(false, A, X), role(S, X, 1)],
                vec![con(false, E, 1)],
            ),
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
                    Clause::new(
                        vec![con(false, A, X)],
                        vec![con(false, B, X), con(false, D, X)],
                    ),
                    Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
                    Clause::new(vec![con(false, A, X)], vec![con(true, D, X)]),
                ],
                vec![CLit::pos(A)],
                Some(false),
            ),
            (
                vec![
                    Clause::new(
                        vec![con(false, A, X)],
                        vec![con(false, B, X), con(false, D, X)],
                    ),
                    Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
                ],
                vec![CLit::pos(A), CLit::neg(D)],
                Some(false),
            ),
            (
                vec![
                    Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
                    Clause::new(
                        vec![con(false, A, X), role(R0, X, 1)],
                        vec![con(true, B, 1)],
                    ),
                ],
                vec![CLit::pos(A)],
                Some(false),
            ),
            (
                vec![Clause::new(
                    vec![con(false, A, X)],
                    vec![exists(R0, false, A, X)],
                )],
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
            Clause::new(
                vec![role(R0, X, z), con(false, G, z)],
                vec![con(false, H, X)],
            ),
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
            Clause::new(
                vec![con(false, D, y), role(R0, X, y)],
                vec![con(false, E, X)],
            ),
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
        assert!(
            !g.label_pos[nb].contains(&E),
            "E must not appear without an r-edge"
        );
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
            Clause::new(
                vec![con(false, D, y), role(R0, X, y)],
                vec![con(false, E, X)],
            ),
        ];
        let recs = mk_recs(&cls);
        let mut qs = QoSat::new(&recs);
        qs.complete_roles = true;
        let g = qs.saturate_global(&[A, A2, B, D, E]);
        assert!(!g.unsupported);
        let na = qs.concept_node[&CLit::pos(A)];
        let na2 = qs.concept_node[&CLit::pos(A2)];
        let nb = qs.concept_node[&CLit::pos(B)];
        assert!(
            g.label_pos[na].contains(&E),
            "A1 must get E via prop broadcast"
        );
        assert!(
            g.label_pos[na2].contains(&E),
            "A2 must get E via prop broadcast"
        );
        assert!(!g.label_pos[nb].contains(&E));
    }

    #[test]
    fn qosat_prop_batch_preserves_fixpoint() {
        // The same conclusion reaches A through two role/filler paths. The batch
        // path must union those presentations and still trigger the downstream
        // E -> F implication exactly as the eager schedule does.
        const R1: R = 1;
        const E: C = 7;
        const F: C = 8;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R1, false, D, X)]),
            Clause::new(
                vec![con(false, B, y), role(R0, X, y)],
                vec![con(false, E, X)],
            ),
            Clause::new(
                vec![con(false, D, y), role(R1, X, y)],
                vec![con(false, E, X)],
            ),
            Clause::new(vec![con(false, E, X)], vec![con(false, F, X)]),
        ];
        let recs = mk_recs(&cls);
        let queries = [A, B, D, E, F];

        let mut eager = QoSat::new(&recs);
        eager.complete_roles = true;
        let ge = eager.saturate_global(&queries);

        let mut batched = QoSat::new(&recs);
        batched.complete_roles = true;
        batched.prop_batch_on = true;
        batched.edge_seen_on = true;
        let gb = batched.saturate_global(&queries);

        assert_eq!(gb.unsupported, ge.unsupported);
        assert_eq!(gb.node_unsat, ge.node_unsat);
        assert_eq!(gb.sufficient, ge.sufficient);
        assert_eq!(gb.open_disj_per_node, ge.open_disj_per_node);
        assert_eq!(gb.label_pos, ge.label_pos);
        let na = batched.concept_node[&CLit::pos(A)];
        assert!(gb.label_pos[na].contains(&E));
        assert!(gb.label_pos[na].contains(&F));
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
            Clause::new(
                vec![con(false, D, X), role(R0, X, y)],
                vec![con(false, E, y)],
            ),
        ];
        let recs = mk_recs(&cls);
        let mut qs = QoSat::new_opts(&recs, false, true); // fprop_on = true
        qs.complete_roles = true;
        let g = qs.saturate_global(&[A, B, D, E]);
        assert!(!g.unsupported);
        assert!(
            !qs.qo_insufficient,
            "fprop capture must route the head-on-target clause away from apply_head"
        );
        let na = qs.concept_node[&CLit::pos(A)];
        let nb = qs.concept_node[&CLit::pos(B)];
        assert!(
            g.label_pos[nb].contains(&E),
            "B (A's r-successor) must get E via fprop forward broadcast"
        );
        assert!(
            !g.label_pos[na].contains(&E),
            "A (the source) must NOT get E"
        );
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
            Clause::new(
                vec![role(R0, X, y), con(false, CS, y)],
                vec![con(false, SPUR, X)],
            ),
            Clause::new(
                vec![role(R0, X, y), con(false, CR, y)],
                vec![con(false, GOOD, X)],
            ),
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
            Clause::new(
                vec![con(false, GUARD, X), role(R0, X, y)],
                vec![con(false, E, X)],
            ),
        ];
        let mut ht = ht(cls);
        let (_, _, subs) = ht.qo_classify_perconcept(&[A, B, GUARD, E]).unwrap();
        assert!(
            subs.contains(&(A, E)),
            "A ⊑ E must be derived (guard-after-edge)"
        );
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
            Clause::new(
                vec![role(R0, X, z), con(false, G, z)],
                vec![con(false, H, X)],
            ),
        ];
        let mut ht = ht(cls);
        let (_, _, subs) = ht.qo_classify_perconcept(&[A, H]).unwrap();
        assert!(
            subs.contains(&(A, H)),
            "A ⊑ H via transitive r-chain (per-concept)"
        );
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
            Clause::new(
                vec![role(R0, X, y), role(R0, X, z)],
                vec![Atom::Eq { s: y, t: z }],
            ),
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
            Clause::new(
                vec![role(R2, X, y), con(false, D, y)],
                vec![con(false, E, X)],
            ), // ∃r2.D ⊑ E
            Clause::new(vec![con(false, B, X)], vec![con(false, E, X)]), // B ⊑ E (forward)
        ];
        let mut ht = ht(cls);
        let (cons, _unsat, subs) = ht
            .qo_classify_kpset(&[A, B, D, E])
            .expect("inert inverse must certify (Some)");
        assert!(cons);
        assert!(
            subs.contains(&(B, E)),
            "B ⊑ E is real (forward) and must be kept"
        );
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
            Clause::new(
                vec![role(R2, X, y), con(false, D, y)],
                vec![con(false, E, X)],
            ), // ∃r2.D ⊑ E
        ];
        let mut ht = ht(cls);
        assert!(
            ht.qo_classify_kpset(&[A, B, D, E]).is_none(),
            "load-bearing/spurious inverse must defer (None), never over-derive B⊑E"
        );
    }

    #[test]
    fn kpwrite_backward_forall_certifies_self_node() {
        // Lever C (KM_HT_QO_KPWRITE): the sound backward-∀ write Konclude's
        // applyALLRule performs, which the pure-CHECK kpset over-defers.
        //   A ⊑ ∃R0.B,  R0(x,y) → R1(y,x)  (R1 = R0⁻; back-edge node(B)--R1-->node(A)),
        //   B ⊓ R1(x,y) ⊑ E (i.e. B ⊑ ∀R1.E = ∀R0⁻.E).
        // node(B) is the R0-filler of node(A); the bridge gives it an R1-edge back
        // to node(A); ∀R1.E then forces E onto node(A) (a real SELF node, a genuine
        // R0-predecessor of the B-filler). That is sound (A ⊑ ∃R0.B, B ⊑ ∀R0⁻.E ⟹
        // A ⊑ E). With KPWRITE the operand is WRITTEN to node(A) and the pass
        // certifies A ⊑ E with no miss; the pure check would defer (kp_insufficient).
        const R1: R = 1;
        const E: C = 7;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![role(R0, X, y)], vec![role(R1, y, X)]), // R1 = R0 inverse
            Clause::new(
                vec![con(false, B, X), role(R1, X, y)],
                vec![con(false, E, y)],
            ), // B ⊑ ∀R1.E
        ];
        let h = ht(cls);
        // CHECK-only (no kpwrite): the self-node write is deferred ⇒ insufficient.
        let mut chk = QoSat::new_opts(&h.clauses, false, false);
        chk.kpset = true;
        chk.complete_roles = true;
        chk.sat_mode = true;
        let _ = chk.saturate_global(&[A, B, E]);
        assert!(
            chk.kp_insufficient,
            "pure check must DEFER the backward self-node write (over-deferral baseline)"
        );
        // KPWRITE: the backward operand is written ⇒ A ⊑ E certified, no miss.
        let mut qk = QoSat::new_opts(&h.clauses, false, false);
        qk.kpset = true;
        qk.complete_roles = true;
        qk.sat_mode = true;
        qk.kpwrite = true;
        let g = qk.saturate_global(&[A, B, E]);
        assert!(
            !qk.kp_insufficient,
            "KPWRITE must NOT defer: the write is sound"
        );
        assert!(
            g.label_pos[0].contains(&E),
            "A ⊑ E must be derived by the sound backward write (node 0 = query A)"
        );
    }

    #[test]
    fn qo_shared_filler_conflict_ground_truth() {
        // Port #2 SOUNDNESS GUARD (copy-on-conflict). Two predecessors share the
        // (D,R0) filler in sat_mode, imposing CONTRADICTORY ∀R0 constraints on it:
        //   A ⊑ ∃R0.D ⊓ ∀R0.CC      (A's R0-successor must be CC)
        //   B ⊑ ∃R0.D ⊓ ∀R0.¬CC     (B's R0-successor must be ¬CC)
        // Each is individually SATISFIABLE (A's succ = D⊓CC; B's succ = D⊓¬CC). A
        // naive shared-filler write would union CC and ¬CC onto the one (D,R0) node
        // and clash BOTH ⇒ spurious A,B unsat (the 7581 pollution). The certify gate
        // must NEVER report A or B unsat: today it DEFERS (qo_insufficient on the
        // ∀-into-shared-filler); port #2 must certify with both consistent by copying
        // the filler. This test locks the SOUND ground truth (full tableau) so the
        // port cannot regress into the spurious double-clash.
        const CC: C = 4;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, D, X)]),
            Clause::new(
                vec![con(false, A, X), role(R0, X, 1)],
                vec![con(false, CC, 1)],
            ),
            Clause::new(vec![con(false, B, X)], vec![exists(R0, false, D, X)]),
            Clause::new(
                vec![con(false, B, X), role(R0, X, 1)],
                vec![con(true, CC, 1)],
            ),
        ];
        // Ground truth: each concept is consistent on its own (sound full tableau).
        assert_eq!(
            ht(cls.clone()).consistent(&[CLit::pos(A)]),
            Some(true),
            "A alone is SAT"
        );
        assert_eq!(
            ht(cls.clone()).consistent(&[CLit::pos(B)]),
            Some(true),
            "B alone is SAT"
        );
        // The certify gate must not claim either unsat: it either DEFERS (None today)
        // or, post port #2, certifies with neither A nor B in the unsat set.
        if let Some((_cons, unsat, _subs)) = ht(cls).qo_classify_kpset(&[A, B, D, CC]) {
            assert!(
                !unsat.contains(&A) && !unsat.contains(&B),
                "shared-filler ∀-conflict must NOT spuriously unsat A or B"
            );
        }
    }

    #[test]
    fn split_certifies_shared_filler_conflict() {
        // Port #2 (KM_HT_QO_SPLIT copy-on-conflict): the SAME KB as
        // qo_shared_filler_conflict_ground_truth, but with `split_mode` on the
        // forward pass must CERTIFY (no `qo_insufficient`, neither A nor B unsat)
        // by redirecting A's and B's R0-edges onto two distinct content-keyed
        // split fillers ({D,CC} and {D,¬CC}) — never polluting the shared D node.
        const CC: C = 4;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, D, X)]),
            Clause::new(
                vec![con(false, A, X), role(R0, X, 1)],
                vec![con(false, CC, 1)],
            ),
            Clause::new(vec![con(false, B, X)], vec![exists(R0, false, D, X)]),
            Clause::new(
                vec![con(false, B, X), role(R0, X, 1)],
                vec![con(true, CC, 1)],
            ),
        ];
        let h = ht(cls);
        let mut qs = QoSat::new_opts(&h.clauses, true, false); // forward-only (no inverse)
        qs.complete_roles = true;
        qs.split_mode = true;
        let g = qs.saturate_global(&[A, B, D, CC]);
        assert!(
            !qs.qo_insufficient,
            "split must NOT defer (copy-on-conflict avoids critical-ALL)"
        );
        assert!(!qs.unsupported, "split pass must complete");
        assert!(
            !g.node_unsat.contains(&0),
            "A (node 0) must not be spuriously unsat"
        );
        assert!(
            !g.node_unsat.contains(&1),
            "B (node 1) must not be spuriously unsat"
        );
    }

    #[test]
    fn split_forall_operand_still_propagates() {
        // Port #2 COMPLETENESS: the redirected ∀-operand must still fire downstream.
        //   A ⊑ ∃R0.D,  A ⊑ ∀R0.CC,  ∃R0.CC ⊑ F   (R0(x,y) ⊓ CC(y) → F(x)).
        // A's R0-successor carries CC (on the split filler {D,CC}), so the backward
        // NF4 fires F onto A: A ⊑ F. Splitting must not drop this contribution.
        const CC: C = 4;
        const F: C = 5;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, D, X)]),
            Clause::new(
                vec![con(false, A, X), role(R0, X, y)],
                vec![con(false, CC, y)],
            ),
            Clause::new(
                vec![role(R0, X, y), con(false, CC, y)],
                vec![con(false, F, X)],
            ),
        ];
        let h = ht(cls);
        let mut qs = QoSat::new_opts(&h.clauses, true, false);
        qs.complete_roles = true;
        qs.split_mode = true;
        let g = qs.saturate_global(&[A, D, CC, F]);
        assert!(!qs.qo_insufficient, "no critical-ALL deferral expected");
        // node 0 = A; the backward F(x) write lands on it.
        assert!(
            g.label_pos[0].contains(&F),
            "A ⊑ F must survive the split redirect"
        );
    }

    #[test]
    fn card_self_equality_not_insufficient() {
        // SOUND self-equality short-circuit (KM_HT_QO_CARD). A ⊑ ∃R0.D with a
        // functional R0 (R0(x,y1) ⊓ R0(x,y2) → y1=y2). In the shared-node model A's
        // single R0-successor is ONE node, so the at-most binds y1=y2=that node — a
        // self-equality, NOT a real merge. The forward pass must NOT mark A
        // insufficient (this is the spurious 98M-firing over-defer on 9724).
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, D, X)]),
            Clause::new(
                vec![role(R0, X, 1), role(R0, X, 2)],
                vec![Atom::Eq { s: 1, t: 2 }],
            ),
        ];
        let h = ht(cls);
        let mut qs = QoSat::new_opts(&h.clauses, true, false);
        qs.complete_roles = true;
        qs.card_defer = true;
        let _ = qs.saturate_global(&[A, D]);
        assert!(
            !qs.qo_insufficient,
            "self-equality merge must not mark insufficient"
        );
        assert!(
            !qs.kp_insufficient,
            "self-equality merge is not a real cardinality obligation"
        );
    }

    #[test]
    fn card_distinct_merge_still_defers() {
        // Complementary guard: two DISTINCT R0-successors (B and C2) forced equal IS
        // a real cardinality merge the shared pass cannot represent ⇒ it must still
        // defer (kp_insufficient), never be silently dropped by the short-circuit.
        const C2: C = 2;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, C2, X)]),
            Clause::new(
                vec![role(R0, X, 1), role(R0, X, 2)],
                vec![Atom::Eq { s: 1, t: 2 }],
            ),
        ];
        let h = ht(cls);
        let mut qs = QoSat::new_opts(&h.clauses, true, false);
        qs.complete_roles = true;
        qs.card_defer = true;
        let _ = qs.saturate_global(&[A, B, C2]);
        assert!(
            qs.kp_insufficient,
            "a distinct-successor merge must still defer"
        );
    }

    #[test]
    fn cardmerge_compatible_certifies() {
        // KM_HT_QO_CARDMERGE: A ⊑ ∃R0.B, A ⊑ ∃R0.D, R0 functional, B,D compatible.
        // The two distinct fillers merge into one {B,D} successor (no clash) ⇒ A is
        // CERTIFIED consistent, not deferred (the lever the blanket card_defer lacks).
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, D, X)]),
            Clause::new(
                vec![role(R0, X, 1), role(R0, X, 2)],
                vec![Atom::Eq { s: 1, t: 2 }],
            ),
        ];
        let h = ht(cls);
        let mut qs = QoSat::new_opts(&h.clauses, true, false);
        qs.complete_roles = true;
        qs.sat_mode = true;
        qs.card_merge = true;
        let g = qs.saturate_global(&[A, B, D]);
        assert!(
            !qs.qo_insufficient && !qs.kp_insufficient,
            "a consistent merge must certify, not defer"
        );
        assert!(!g.node_unsat.contains(&0), "A is consistent");
    }

    #[test]
    fn cardmerge_clash_defers() {
        // B ⊓ C2 ⊑ ⊥ makes the forced merge inconsistent ⇒ the anchor is DEFERRED
        // (kp_insufficient) to the complete verify, never silently certified.
        const C2: C = 2;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, C2, X)]),
            Clause::new(
                vec![role(R0, X, 1), role(R0, X, 2)],
                vec![Atom::Eq { s: 1, t: 2 }],
            ),
            Clause::new(vec![con(false, B, X), con(false, C2, X)], vec![]),
        ];
        let h = ht(cls);
        let mut qs = QoSat::new_opts(&h.clauses, true, false);
        qs.complete_roles = true;
        qs.sat_mode = true;
        qs.card_merge = true;
        let _ = qs.saturate_global(&[A, B, C2]);
        assert!(
            qs.kp_insufficient,
            "an inconsistent forced merge must defer the anchor"
        );
    }

    #[test]
    fn cardmerge_does_not_pollute_unconstrained_predecessor() {
        // SOUNDNESS (per-source privatize). P1=A ⊑ ∃R0.B ⊓ ∃R0.D with functional R0
        // (its two successors merge into {B,D}); P2 ⊑ ∃R0.B shares the (B,R0) filler
        // but has only ONE R0-successor (no merge). With ∃R0.D ⊑ G: A ⊑ G (its
        // merged successor has D) but P2 must NOT get G — privatize copies the
        // filler before merging, leaving P2's shared {B} successor untouched.
        const P2: C = 2;
        const G: C = 6;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, D, X)]),
            Clause::new(vec![con(false, P2, X)], vec![exists(R0, false, B, X)]),
            Clause::new(
                vec![role(R0, X, 1), role(R0, X, 2)],
                vec![Atom::Eq { s: 1, t: 2 }],
            ),
            Clause::new(
                vec![role(R0, X, 1), con(false, D, 1)],
                vec![con(false, G, X)],
            ),
        ];
        let h = ht(cls);
        let mut qs = QoSat::new_opts(&h.clauses, true, false);
        qs.complete_roles = true;
        qs.sat_mode = true;
        qs.card_merge = true;
        let g = qs.saturate_global(&[A, P2, B, D, G]);
        assert!(
            g.label_pos[0].contains(&G),
            "A ⊑ G (its merged successor carries D)"
        );
        assert!(
            !g.label_pos[1].contains(&G),
            "P2 must NOT get G — the merge must not pollute the shared filler"
        );
    }

    // ---- block_mode 4: sound SHIQ double-blocking + inverse propagation ----
    // (task #11 foundation; full-label bidirectional pairwise blocking)

    #[test]
    fn mode4_terminates_on_inverse_cycle() {
        // A ⊑ ∃R0.A is an infinite R0-chain; the inverse bridge R0(x,y)→R1(y,x)
        // makes every successor also an R1-predecessor. Double blocking must fold
        // the chain so consistent terminates with SAT (no infinite expansion/panic).
        const R1: R = 1;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, A, X)]),
            Clause::new(vec![role(R0, X, y)], vec![role(R1, y, X)]),
        ];
        let mut ht = ht(cls);
        ht.block_mode = 4;
        assert_eq!(ht.consistent(&[CLit::pos(A)]), Some(true));
    }

    #[test]
    fn mode4_backward_inverse_propagation_clash() {
        // A ⊑ ∃R0.B, B ⊑ ∃R0.B (infinite B-chain), inverse bridge R0(x,y)→R1(y,x),
        // B ⊑ ∀R1.CC (a B-node's R1-successor = its R0-PREDECESSOR gets CC), and
        // A ⊑ ¬CC. The successor n1:B has an R1-edge back to the root n0:A, so the
        // backward-∀ writes CC onto n0, clashing with A⊑¬CC ⇒ UNSAT. Exercises sound
        // inverse (backward) propagation under mode 4.
        const CC: C = 4;
        const R1: R = 1;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, B, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![role(R0, X, y)], vec![role(R1, y, X)]),
            Clause::new(
                vec![con(false, B, X), role(R1, X, y)],
                vec![con(false, CC, y)],
            ),
            Clause::new(vec![con(false, A, X)], vec![con(true, CC, X)]),
        ];
        let mut ht = ht(cls);
        ht.block_mode = 4;
        assert_eq!(ht.consistent(&[CLit::pos(A)]), Some(false));
    }

    #[test]
    fn mode4_inverse_model_is_satisfiable() {
        // Same backward-∀ shape but WITHOUT the A⊑¬CC clash: the model is satisfiable
        // and the infinite chain must be folded by double blocking. Guards against
        // OVER-blocking (spurious termination as UNSAT) and non-termination.
        const CC: C = 4;
        const R1: R = 1;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, B, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![role(R0, X, y)], vec![role(R1, y, X)]),
            Clause::new(
                vec![con(false, B, X), role(R1, X, y)],
                vec![con(false, CC, y)],
            ),
        ];
        let mut ht = ht(cls);
        ht.block_mode = 4;
        assert_eq!(ht.consistent(&[CLit::pos(A)]), Some(true));
    }

    #[test]
    fn mode4_agrees_with_default_on_noinverse_clash() {
        // Regression: mode 4 must give the same verdict as the default blocking on a
        // pure no-inverse case. A ⊑ ∃R0.B, A ⊓ R0 ⊑ ¬B (∀R0.¬B) ⇒ UNSAT.
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(
                vec![con(false, A, X), role(R0, X, 1)],
                vec![con(true, B, 1)],
            ),
        ];
        let mut ht = ht(cls);
        ht.block_mode = 4;
        assert_eq!(ht.consistent(&[CLit::pos(A)]), Some(false));
    }

    #[test]
    fn mode4_merge_cycle_inverse_terminates_sat() {
        // Cardinality merge × inverse × double blocking together. A ⊑ ∃R0.B,
        // A ⊑ ∃R0.D with R0 functional ⇒ the two R0-successors merge into one
        // {B,D} node. B ⊑ ∃R0.A makes the merged node spawn an A-successor, so the
        // model cycles {A}→{B,D}→{A}→… ; the inverse bridge R0(x,y)→R1(y,x) puts a
        // backward R1 edge on every node. B and D are NOT disjoint ⇒ SAT. Mode-4
        // must fold the cycle (a later {B,D}-node has the same full bidirectional
        // signature as the first) so consistent terminates instead of expanding
        // forever. Exercises merge-rewritten labels feeding the double-block key.
        std::env::set_var("KM_HT_NUMBER", "1");
        const R1: R = 1;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, D, X)]),
            // R0 functional: the two successors of A merge
            Clause::new(
                vec![role(R0, X, 1), role(R0, X, 2)],
                vec![Atom::Eq { s: 1, t: 2 }],
            ),
            // merged {B,D} node spawns an A-successor ⇒ infinite cycle
            Clause::new(vec![con(false, B, X)], vec![exists(R0, false, A, X)]),
            // inverse bridge
            Clause::new(vec![role(R0, X, y)], vec![role(R1, y, X)]),
        ];
        let mut ht = ht(cls);
        ht.block_mode = 4;
        assert_eq!(ht.consistent(&[CLit::pos(A)]), Some(true));
    }

    #[test]
    fn mode4_merge_clash_inverse_unsat() {
        // Same merge × inverse shape, but B ⊓ D ⊑ ⊥. The functional merge folds A's
        // two R0-successors into one node carrying both B and D, which clash ⇒ {A}
        // UNSAT. The clash is forced by the merge before any blocking can fold the
        // cycle, so mode-4 must still report UNSAT (guards against the double-block
        // key masking a merge-induced clash). Confident deterministic outcome.
        std::env::set_var("KM_HT_NUMBER", "1");
        const R1: R = 1;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, D, X)]),
            Clause::new(
                vec![role(R0, X, 1), role(R0, X, 2)],
                vec![Atom::Eq { s: 1, t: 2 }],
            ),
            Clause::new(vec![con(false, B, X)], vec![exists(R0, false, A, X)]),
            Clause::new(vec![role(R0, X, y)], vec![role(R1, y, X)]),
            // B ⊓ D ⊑ ⊥
            Clause::new(vec![con(false, B, X), con(false, D, X)], vec![]),
        ];
        let mut ht = ht(cls);
        ht.block_mode = 4;
        assert_eq!(ht.consistent(&[CLit::pos(A)]), Some(false));
    }

    // --- Konclude optimized blocking port (block_mode 5): B1 subset + B2a. The port
    // must reproduce the sound verdicts of the textbook double-blocking (mode 4). The
    // frontier-lag SAT case is the key one: subset B1 lets the incomplete frontier {B}
    // block against the complete {B,CC} blocker directly, so it terminates without
    // needing the indirect-blocking workaround mode 4 relies on. ---
    #[test]
    fn mode5_terminates_on_inverse_cycle() {
        const R1: R = 1;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, A, X)]),
            Clause::new(vec![role(R0, X, y)], vec![role(R1, y, X)]),
        ];
        let mut ht = ht(cls);
        ht.block_mode = 5;
        assert_eq!(ht.consistent(&[CLit::pos(A)]), Some(true));
    }

    #[test]
    fn mode5_inverse_model_is_satisfiable() {
        // The frontier-lag case (∀ over inverse). Konclude subset B1 ({B}⊆{B,CC}) +
        // B2a (CC at the predecessor, written by the backward ∀) blocks the frontier
        // node directly ⇒ terminates SAT without infinite expansion.
        const CC: C = 4;
        const R1: R = 1;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, B, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![role(R0, X, y)], vec![role(R1, y, X)]),
            Clause::new(
                vec![con(false, B, X), role(R1, X, y)],
                vec![con(false, CC, y)],
            ),
        ];
        let mut ht = ht(cls);
        ht.block_mode = 5;
        assert_eq!(ht.consistent(&[CLit::pos(A)]), Some(true));
    }

    #[test]
    fn mode5_backward_inverse_propagation_clash() {
        // Backward ∀ writes CC onto the root which is ¬CC ⇒ UNSAT. Blocking must not
        // mask the clash (it is raised before any block fires).
        const CC: C = 4;
        const R1: R = 1;
        let y: Var = 1;
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, B, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![role(R0, X, y)], vec![role(R1, y, X)]),
            Clause::new(
                vec![con(false, B, X), role(R1, X, y)],
                vec![con(false, CC, y)],
            ),
            Clause::new(vec![con(false, A, X)], vec![con(true, CC, X)]),
        ];
        let mut ht = ht(cls);
        ht.block_mode = 5;
        assert_eq!(ht.consistent(&[CLit::pos(A)]), Some(false));
    }

    #[test]
    fn mode5_agrees_with_default_on_noinverse_clash() {
        // No-inverse regression: A ⊑ ∃R0.B, A ⊓ R0 ⊑ ¬B ⇒ UNSAT (B1 subset alone,
        // B2a vacuous since no w→v edge).
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(
                vec![con(false, A, X), role(R0, X, 1)],
                vec![con(true, B, 1)],
            ),
        ];
        let mut ht = ht(cls);
        ht.block_mode = 5;
        assert_eq!(ht.consistent(&[CLit::pos(A)]), Some(false));
    }

    #[test]
    fn index_forall_picks_up_universal_clauses() {
        // The B2a index: `C0 ⊑ ∀r.D` clausified as C0(x) ∧ r(x,y) → D(y) is indexed
        // by (C0, r) → [D]; an ∃ head and a 2-role chain body are NOT indexed.
        const CC: C = 4;
        const R1: R = 1;
        let y: Var = 1;
        let cls = vec![
            // ∀: B ∧ R1(x,y) → CC(y)  ⇒ indexed (B,R1)->[CC]
            Clause::new(
                vec![con(false, B, X), role(R1, X, y)],
                vec![con(false, CC, y)],
            ),
            // ∃ head: not a universal
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            // plain bridge (role head): not a concept-universal
            Clause::new(vec![role(R0, X, y)], vec![role(R1, y, X)]),
        ];
        let idx = index_forall(&cls);
        assert_eq!(idx.get(&(CLit::pos(B), R1)), Some(&vec![CLit::pos(CC)]));
        assert_eq!(idx.get(&(CLit::pos(A), R0)), None);
        assert_eq!(idx.len(), 1);
    }

    #[test]
    fn has_inverse_bridge_detects_swapped_role_head() {
        const R1: R = 1;
        let y: Var = 1;
        // bridge R0(x,y) → R1(y,x): swapped vars, distinct roles ⇒ inverse present.
        let with_inv = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![role(R0, X, y)], vec![role(R1, y, X)]),
        ];
        assert!(has_inverse_bridge(&with_inv));
        // a plain role inclusion R0(x,y) → R1(x,y) (NON-swapped) is not inverse.
        let hierarchy = vec![Clause::new(vec![role(R0, X, y)], vec![role(R1, X, y)])];
        assert!(!has_inverse_bridge(&hierarchy));
        // no role-head clauses at all.
        let no_roles = vec![Clause::new(vec![con(false, A, X)], vec![con(false, B, X)])];
        assert!(!has_inverse_bridge(&no_roles));
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
        assert!(
            m.contains(&B),
            "B forced in A's model (A⊑B) ⇒ NOT refutable"
        );
        assert!(!m.contains(&CC), "CC absent in A's model ⇒ refutes A⊑CC");
    }

    #[test]
    fn native_abox_class_assertion_changes_global_consistency() {
        const NOM: C = 20;
        const ASSERTED: C = 21;
        let clauses = vec![Clause::new(vec![con(false, ASSERTED, X)], Vec::new())];

        let mut without = ht(clauses.clone());
        assert_eq!(without.consistent(&[]), Some(true));

        let mut with = ht(clauses);
        with.set_nominals(vec![NOM]);
        with.set_native_abox(vec![(vec![NOM], vec![ASSERTED])], Vec::new(), Vec::new());
        assert_eq!(with.consistent(&[]), Some(false));
    }

    #[test]
    fn native_abox_different_blocks_required_atmost_merge() {
        const SUBJECT: C = 20;
        const LEFT: C = 21;
        const RIGHT: C = 22;
        const MARKER: C = 23;
        const FILLER: C = 24;
        let seeds = vec![
            (vec![SUBJECT], vec![MARKER]),
            (vec![LEFT], vec![FILLER]),
            (vec![RIGHT], vec![FILLER]),
        ];
        let edges = vec![(R0, 0, 1), (R0, 0, 2)];

        let mut mergeable = ht(Vec::new());
        mergeable.set_nominals(vec![SUBJECT, LEFT, RIGHT]);
        mergeable.set_native_abox(seeds.clone(), Vec::new(), edges.clone());
        mergeable.set_card_defs_raw(&[(MARKER, false, 1, R0, FILLER)]);
        mergeable.set_number(true);
        assert_eq!(mergeable.consistent(&[]), Some(true));

        let mut distinct = ht(Vec::new());
        distinct.set_nominals(vec![SUBJECT, LEFT, RIGHT]);
        distinct.set_native_abox(seeds, vec![(1, 2)], edges);
        distinct.set_card_defs_raw(&[(MARKER, false, 1, R0, FILLER)]);
        distinct.set_number(true);
        assert_eq!(distinct.consistent(&[]), Some(false));
    }

    fn negative_edge_clash(role_id: R, source_nominal: C, target_nominal: C) -> Clause {
        Clause::new(
            vec![
                con(false, source_nominal, X),
                role(role_id, X, 1),
                con(false, target_nominal, 1),
            ],
            Vec::new(),
        )
    }

    #[test]
    fn native_abox_positive_and_negative_role_assertion_clash() {
        const NA: C = 20;
        const NB: C = 21;
        let mut t = ht(vec![negative_edge_clash(R0, NA, NB)]);
        t.set_nominals(vec![NA, NB]);
        t.set_native_abox(
            vec![(vec![NA], Vec::new()), (vec![NB], Vec::new())],
            Vec::new(),
            vec![(R0, 0, 1)],
        );
        assert_eq!(t.consistent(&[]), Some(false));
    }

    #[test]
    fn negative_role_assertion_sees_subrole_inverse_and_chain_edges() {
        const NA: C = 20;
        const NB: C = 21;
        const NC: C = 22;
        const SUB: R = 1;
        const TARGET: R = 2;
        const SECOND: R = 3;

        // SUB(a,b), SUB⊑TARGET, and ¬TARGET(a,b).
        let mut subrole = ht(vec![
            Clause::new(vec![role(SUB, X, 1)], vec![role(TARGET, X, 1)]),
            negative_edge_clash(TARGET, NA, NB),
        ]);
        subrole.set_nominals(vec![NA, NB]);
        subrole.set_native_abox(
            vec![(vec![NA], Vec::new()), (vec![NB], Vec::new())],
            Vec::new(),
            vec![(SUB, 0, 1)],
        );
        assert_eq!(subrole.consistent(&[]), Some(false));

        // SUB(a,b), inverse bridge SUB(x,y)->TARGET(y,x), and ¬TARGET(b,a).
        let mut inverse = ht(vec![
            Clause::new(vec![role(SUB, X, 1)], vec![role(TARGET, 1, X)]),
            negative_edge_clash(TARGET, NB, NA),
        ]);
        inverse.set_nominals(vec![NA, NB]);
        inverse.set_native_abox(
            vec![(vec![NA], Vec::new()), (vec![NB], Vec::new())],
            Vec::new(),
            vec![(SUB, 0, 1)],
        );
        assert_eq!(inverse.consistent(&[]), Some(false));

        // SUB(a,b), SECOND(b,c), SUB∘SECOND⊑TARGET, and ¬TARGET(a,c).
        let mut chain = ht(vec![
            Clause::new(
                vec![role(SUB, X, 1), role(SECOND, 1, 2)],
                vec![role(TARGET, X, 2)],
            ),
            negative_edge_clash(TARGET, NA, NC),
        ]);
        chain.set_nominals(vec![NA, NB, NC]);
        chain.set_native_abox(
            vec![
                (vec![NA], Vec::new()),
                (vec![NB], Vec::new()),
                (vec![NC], Vec::new()),
            ],
            Vec::new(),
            vec![(SUB, 0, 1), (SECOND, 1, 2)],
        );
        assert_eq!(chain.consistent(&[]), Some(false));
    }

    #[test]
    fn parallel_workers_retain_native_abox() {
        const NOM: C = 20;
        const ASSERTED: C = 21;
        let clauses = vec![Clause::new(vec![con(false, ASSERTED, X)], Vec::new())];
        let mut t = ht(clauses);
        t.set_nominals(vec![NOM]);
        t.set_native_abox(vec![(vec![NOM], vec![ASSERTED])], Vec::new(), Vec::new());
        let (_, unsat, _) = t
            .classify_parallel(&[A, B], 2)
            .expect("tiny native-ABox workers terminate");
        assert_eq!(
            unsat.len(),
            2,
            "both workers must see the global ABox clash"
        );
    }

    #[test]
    fn lean_sat_wire_serializes_the_exact_terminal_model() {
        let mut t = ht(vec![
            Clause::new(Vec::new(), vec![con(false, A, X)]),
            Clause::new(
                vec![con(false, A, X)],
                vec![exists(R0, false, B, X)],
            ),
        ]);
        assert_eq!(t.consistent(&[]), Some(true));
        let wire: serde_json::Value = serde_json::from_str(
            &t.lean_sat_certificate_json()
                .expect("clash-free equality-free state has a SAT certificate"),
        )
        .expect("certificate is JSON");
        assert_eq!(wire["version"], 1);
        assert_eq!(wire["evidence"], "sat");
        assert_eq!(wire["variable_count"], 1);
        assert_eq!(wire["ontology"].as_array().unwrap().len(), 2);
        assert!(wire["labels"].as_array().unwrap().len() >= 2);
        assert!(!wire["edges"].as_array().unwrap().is_empty());
        let terminal = wire["node_count"].as_u64().unwrap() - 1;
        assert!(wire["edges"].as_array().unwrap().iter().any(|edge| {
            edge["source"].as_u64() == Some(terminal)
        }), "the blocked terminal node receives its materialized continuation");
    }

    #[test]
    fn lean_sat_wire_serializes_the_exact_equality_quotient() {
        let mut t = ht(vec![Clause::new(
            Vec::new(),
            vec![Atom::Eq { s: X, t: 1 }],
        )]);
        let first = t.ext.new_root();
        let second = t.ext.new_node(Some(first));
        t.ext.merge_into(first, second, &dep_empty());
        let wire: serde_json::Value = serde_json::from_str(
            &t.lean_sat_certificate_json()
                .expect("the complete quotient has a SAT certificate"),
        )
        .expect("equality SAT certificate is JSON");
        assert_eq!(wire["version"], 2);
        assert_eq!(wire["evidence"], "sat");
        assert_eq!(wire["state"]["equalities"].as_array().unwrap().len(), 1);
        assert_eq!(wire["state"]["representatives"], serde_json::json!([0, 0]));
        assert_eq!(
            wire["state"]["representative_paths"],
            serde_json::json!([[], [0]])
        );
    }

    #[test]
    fn lean_equality_sat_wire_passes_native_checker_when_configured() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_CHECKER") else {
            return;
        };
        let mut t = ht(vec![Clause::new(
            Vec::new(),
            vec![Atom::Eq { s: X, t: 1 }],
        )]);
        let first = t.ext.new_root();
        let second = t.ext.new_node(Some(first));
        t.ext.merge_into(first, second, &dep_empty());
        let path = std::env::temp_dir().join(format!(
            "km-ht-eq-sat-cert-{}-{}.json",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        std::fs::write(&path, t.lean_sat_certificate_json().unwrap()).unwrap();
        let accepted = std::process::Command::new(&checker)
            .arg(&path)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .expect("run native Lean equality HT checker")
            .success();
        let _ = std::fs::remove_file(path);
        assert!(accepted, "Lean must accept the Rust equality SAT quotient");
    }

    fn equality_query_model() -> Ht {
        let mut t = ht(vec![Clause::new(
            Vec::new(),
            vec![Atom::Eq { s: X, t: 1 }],
        )]);
        let root = t.ext.new_root();
        t.ext.add_concept(root, CLit::pos(A), &dep_empty());
        t.ext
            .add_concept(root, CLit { c: B, neg: true }, &dep_empty());
        let second = t.ext.new_node(Some(root));
        t.ext.merge_into(root, second, &dep_empty());
        t
    }

    #[test]
    fn lean_equality_query_wires_serialize_quotient_countermodels() {
        let t = equality_query_model();
        let non_subsumption: serde_json::Value = serde_json::from_str(
            &t.lean_non_subsumption_certificate_json(A, B).unwrap(),
        )
        .unwrap();
        assert_eq!(non_subsumption["version"], 2);
        assert_eq!(
            non_subsumption["evidence"]["non_subsumption"],
            serde_json::json!({ "root": 0, "sub": A, "sup": B })
        );
        let satisfiable: serde_json::Value = serde_json::from_str(
            &t.lean_satisfiable_concept_certificate_json(A).unwrap(),
        )
        .unwrap();
        assert_eq!(satisfiable["version"], 2);
        assert_eq!(
            satisfiable["evidence"]["satisfiable_concept"],
            serde_json::json!({ "root": 0, "concept": A })
        );
    }

    #[test]
    fn lean_equality_query_wires_pass_native_checker_when_configured() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_CHECKER") else {
            return;
        };
        let t = equality_query_model();
        let documents = [
            t.lean_non_subsumption_certificate_json(A, B).unwrap(),
            t.lean_satisfiable_concept_certificate_json(A).unwrap(),
        ];
        for (index, document) in documents.iter().enumerate() {
            let path = std::env::temp_dir().join(format!(
                "km-ht-eq-query-cert-{}-{index}.json",
                std::process::id()
            ));
            std::fs::write(&path, document).unwrap();
            let accepted = std::process::Command::new(&checker)
                .arg(&path)
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .expect("run native Lean equality HT checker")
                .success();
            let _ = std::fs::remove_file(path);
            assert!(accepted, "Lean must accept Rust equality query evidence");
        }
    }

    #[test]
    fn lean_equality_refutation_query_wires_serialize() {
        let equality = Clause::new(Vec::new(), vec![Atom::Eq { s: X, t: 1 }]);
        let subsumption = ht(vec![
            equality.clone(),
            Clause::new(
                vec![con(false, A, X), con(true, B, X)],
                Vec::new(),
            ),
        ]);
        let subsumption_json = subsumption.lean_subsumption_certificate_json(A, B).unwrap();
        let document: serde_json::Value = serde_json::from_str(&subsumption_json).unwrap();
        assert_eq!(document["version"], 2);
        assert!(document["evidence"]["subsumption"].is_object());

        let unsatisfiable = ht(vec![
            equality,
            Clause::new(vec![con(false, A, X)], Vec::new()),
        ]);
        let unsatisfiable_json = unsatisfiable
            .lean_unsatisfiable_concept_certificate_json(A)
            .unwrap();
        let document: serde_json::Value = serde_json::from_str(&unsatisfiable_json).unwrap();
        assert_eq!(document["version"], 2);
        assert!(document["evidence"]["unsatisfiable_concept"].is_object());

        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_CHECKER") else {
            return;
        };
        for (index, document) in [subsumption_json, unsatisfiable_json]
            .iter()
            .enumerate()
        {
            let path = std::env::temp_dir().join(format!(
                "km-ht-eq-refutation-query-cert-{}-{index}.json",
                std::process::id()
            ));
            std::fs::write(&path, document).unwrap();
            let accepted = std::process::Command::new(&checker)
                .arg(&path)
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .expect("run native Lean equality HT checker")
                .success();
            let _ = std::fs::remove_file(path);
            assert!(
                accepted,
                "Lean must accept Rust equality refutation query evidence"
            );
        }
    }

    #[test]
    fn lean_concept_unsat_wire_exhausts_every_disjunct() {
        let t = ht(vec![
            Clause::new(Vec::new(), vec![con(false, A, X), con(false, B, X)]),
            Clause::new(vec![con(false, A, X)], Vec::new()),
            Clause::new(vec![con(false, B, X)], Vec::new()),
        ]);
        let wire: serde_json::Value = serde_json::from_str(
            &t.lean_unsat_certificate_json()
                .expect("both concept branches close"),
        )
        .expect("certificate is JSON");
        assert_eq!(wire["version"], 1);
        let root = &wire["evidence"]["unsat"]["tree"]["branch"];
        assert_eq!(root["clause"], 0);
        assert_eq!(root["assignment"], serde_json::json!([0]));
        assert_eq!(root["children"].as_array().unwrap().len(), 2);
        assert!(wire["labels"].as_array().unwrap().is_empty());
    }

    #[test]
    fn lean_concept_unsat_wire_refuses_an_open_branch() {
        let t = ht(vec![Clause::new(
            Vec::new(),
            vec![con(false, A, X), con(false, B, X)],
        )]);
        assert!(t.lean_unsat_certificate_json().is_err());
    }

    #[test]
    fn lean_subsumption_wire_refutes_the_exact_query_root() {
        let t = ht(vec![Clause::new(
            vec![con(false, A, X), con(true, B, X)],
            Vec::new(),
        )]);
        let wire: serde_json::Value = serde_json::from_str(
            &t.lean_subsumption_certificate_json(A, B)
                .expect("A and not-B close"),
        )
        .expect("subsumption certificate is JSON");
        let evidence = &wire["evidence"]["subsumption"];
        assert_eq!(evidence["root"], 0);
        assert_eq!(evidence["sub"], A);
        assert_eq!(evidence["sup"], B);
        assert_eq!(wire["labels"].as_array().unwrap().len(), 2);
        assert!(t.lean_subsumption_certificate_json(B, A).is_err());
    }

    #[test]
    fn lean_unsatisfiable_concept_wire_refutes_the_exact_query_root() {
        let t = ht(vec![Clause::new(vec![con(false, A, X)], Vec::new())]);
        let wire: serde_json::Value = serde_json::from_str(
            &t.lean_unsatisfiable_concept_certificate_json(A)
                .expect("A closes"),
        )
        .expect("unsatisfiable-concept certificate is JSON");
        let evidence = &wire["evidence"]["unsatisfiable_concept"];
        assert_eq!(evidence["root"], 0);
        assert_eq!(evidence["concept"], A);
        assert_eq!(wire["labels"].as_array().unwrap().len(), 1);
        assert!(t
            .lean_unsatisfiable_concept_certificate_json(B)
            .is_err());
    }

    #[test]
    fn lean_non_subsumption_wire_serializes_the_exact_countermodel_query() {
        let mut t = ht(Vec::new());
        assert_eq!(
            t.consistent(&[CLit::pos(A), CLit { c: B, neg: true }]),
            Some(true)
        );
        let wire: serde_json::Value = serde_json::from_str(
            &t.lean_non_subsumption_certificate_json(A, B)
                .expect("the retained model witnesses A and not-B"),
        )
        .expect("non-subsumption certificate is JSON");
        let evidence = &wire["evidence"]["non_subsumption"];
        assert_eq!(evidence["root"], 0);
        assert_eq!(evidence["sub"], A);
        assert_eq!(evidence["sup"], B);
        assert!(t.lean_non_subsumption_certificate_json(B, A).is_err());
    }

    #[test]
    fn lean_satisfiable_concept_wire_serializes_the_exact_model_query() {
        let mut t = ht(Vec::new());
        assert_eq!(t.consistent(&[CLit::pos(A)]), Some(true));
        let wire: serde_json::Value = serde_json::from_str(
            &t.lean_satisfiable_concept_certificate_json(A)
                .expect("the retained model witnesses A"),
        )
        .expect("satisfiable-concept certificate is JSON");
        let evidence = &wire["evidence"]["satisfiable_concept"];
        assert_eq!(evidence["root"], 0);
        assert_eq!(evidence["concept"], A);
        assert!(t.lean_satisfiable_concept_certificate_json(B).is_err());
    }

    #[test]
    fn lean_taxonomy_wire_covers_every_concept_and_ordered_pair() {
        let mut t = ht(Vec::new());
        let wire: serde_json::Value = serde_json::from_str(
            &t.lean_taxonomy_certificate_json(&[A, B])
                .expect("the empty ontology has finite evidence for every cell"),
        )
        .expect("taxonomy certificate is JSON");
        assert_eq!(wire["named"], serde_json::json!([A, B]));
        assert_eq!(wire["concepts"].as_array().unwrap().len(), 2);
        let rows = wire["subsumptions"].as_array().unwrap();
        assert_eq!(rows.len(), 2);
        assert!(rows.iter().all(|row| row.as_array().unwrap().len() == 2));
        assert!(wire["subsumptions"][0][0]["evidence"]["subsumption"].is_object());
        assert!(wire["subsumptions"][0][1]["evidence"]["non_subsumption"].is_object());
        assert!(t.lean_taxonomy_certificate_json(&[A, A]).is_err());
    }

    #[test]
    fn lean_taxonomy_wire_uses_equality_cells_for_a_genuine_equality_head() {
        let mut t = ht(vec![Clause::new(
            vec![con(false, D, X)],
            vec![con(false, A, X), Atom::Eq { s: X, t: X }],
        )]);
        let wire: serde_json::Value = serde_json::from_str(
            &t.lean_taxonomy_certificate_json(&[A, B])
                .expect("the equality-bearing ontology has evidence for every cell"),
        )
        .expect("mixed taxonomy certificate is JSON");
        assert_eq!(wire["version"], 2);
        assert!(wire["concepts"][0]["equality"].is_object());
        assert!(wire["subsumptions"][0][0]["equality"].is_object());
        assert!(wire["subsumptions"][0][1]["equality"].is_object());
    }

    #[test]
    fn lean_unsat_wire_closes_role_and_existential_branches() {
        let role_t = ht(vec![
            Clause::new(Vec::new(), vec![role(R0, X, X)]),
            Clause::new(vec![role(R0, X, X)], Vec::new()),
        ]);
        let role_wire: serde_json::Value = serde_json::from_str(
            &role_t
                .lean_unsat_certificate_json()
                .expect("the forced role loop closes"),
        )
        .expect("role certificate is JSON");
        assert_eq!(role_wire["role_count"], 1);
        assert_eq!(
            role_wire["evidence"]["unsat"]["tree"]["branch"]["children"]
                .as_array()
                .unwrap()
                .len(),
            1
        );

        let existential_t = ht(vec![
            Clause::new(Vec::new(), vec![exists(R0, false, A, X)]),
            Clause::new(vec![exists(R0, false, A, X)], Vec::new()),
        ]);
        assert!(existential_t.lean_unsat_certificate_json().is_ok());
    }

    #[test]
    fn lean_unsat_wire_serializes_equality_merges() {
        let t = ht(vec![
            Clause::new(Vec::new(), vec![exists(R0, false, A, X)]),
            Clause::new(
                vec![role(R0, X, 1)],
                vec![con(true, A, X)],
            ),
            Clause::new(
                vec![role(R0, X, 1)],
                vec![Atom::Eq { s: X, t: 1 }],
            ),
        ]);
        let wire: serde_json::Value = serde_json::from_str(
            &t.lean_unsat_certificate_json()
                .expect("the equality merge closes complementary labels"),
        )
        .expect("equality certificate is JSON");
        assert_eq!(wire["version"], 2);
        assert_eq!(wire["state"]["representatives"].as_array().unwrap().len(), 8);
        let encoded = serde_json::to_string(&wire).unwrap();
        assert!(encoded.contains("equalities"));
        assert!(encoded.contains("representative_paths"));
    }

    #[test]
    fn lean_equality_unsat_wire_passes_native_checker_when_configured() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_CHECKER") else {
            return;
        };
        let t = ht(vec![
            Clause::new(Vec::new(), vec![exists(R0, false, A, X)]),
            Clause::new(vec![role(R0, X, 1)], vec![con(true, A, X)]),
            Clause::new(vec![role(R0, X, 1)], vec![Atom::Eq { s: X, t: 1 }]),
        ]);
        let path = std::env::temp_dir().join(format!(
            "km-ht-eq-unsat-cert-{}-{}.json",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        std::fs::write(&path, t.lean_unsat_certificate_json().unwrap()).unwrap();
        let accepted = std::process::Command::new(&checker)
            .arg(&path)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .expect("run native Lean equality HT checker")
            .success();
        let _ = std::fs::remove_file(path);
        assert!(accepted, "Lean must accept the Rust equality UNSAT tree");
    }

    #[test]
    fn lean_unsat_wire_materializes_a_fresh_existential_witness() {
        let t = ht(vec![
            Clause::new(Vec::new(), vec![exists(R0, false, A, X)]),
            Clause::new(
                vec![role(R0, X, 1), con(false, A, 1)],
                Vec::new(),
            ),
        ]);
        let wire: serde_json::Value = serde_json::from_str(
            &t.lean_unsat_certificate_json()
                .expect("the existential witness reaches the guarded clash"),
        )
        .expect("witness certificate is JSON");
        assert_eq!(wire["node_count"], 2);
        let witness =
            &wire["evidence"]["unsat"]["tree"]["branch"]["children"][0]["witness"];
        assert_eq!(witness["source"], 0);
        assert_eq!(witness["target"], 1);
        assert_eq!(witness["role"], 0);
    }

    #[test]
    fn lean_unsat_assignment_enumeration_is_bounded() {
        assert_eq!(Ht::lean_refutation_assignments(2, 2).unwrap().len(), 4);
        assert!(Ht::lean_refutation_assignments(10, 10).is_none());
    }

    #[test]
    fn lean_unsat_wire_passes_native_checker_when_configured() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_CHECKER") else {
            return;
        };
        let t = ht(vec![
            Clause::new(Vec::new(), vec![exists(R0, false, A, X)]),
            Clause::new(
                vec![role(R0, X, 1), con(false, A, 1)],
                Vec::new(),
            ),
        ]);
        let path = std::env::temp_dir().join(format!(
            "km-ht-unsat-cert-{}-{}.json",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        std::fs::write(
            &path,
            t.lean_unsat_certificate_json()
                .expect("the fresh existential witness closes"),
        )
        .expect("write temporary HT certificate");
        let accepted = std::process::Command::new(&checker)
            .arg(&path)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .expect("run native Lean HT checker")
            .success();
        let _ = std::fs::remove_file(path);
        assert!(accepted, "Lean must accept the exact Rust UNSAT tree");
    }

    #[test]
    fn lean_query_wires_pass_native_checker_when_configured() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_CHECKER") else {
            return;
        };
        let mut countermodel = ht(Vec::new());
        assert_eq!(
            countermodel.consistent(&[CLit::pos(A), CLit { c: B, neg: true }]),
            Some(true)
        );
        let non_subsumption = countermodel
            .lean_non_subsumption_certificate_json(A, B)
            .expect("A and not-B have a finite countermodel");
        let mut concept_model = ht(Vec::new());
        assert_eq!(concept_model.consistent(&[CLit::pos(A)]), Some(true));
        let satisfiable_concept = concept_model
            .lean_satisfiable_concept_certificate_json(A)
            .expect("A has a finite model");
        let queries = [
            ht(vec![Clause::new(
                vec![con(false, A, X), con(true, B, X)],
                Vec::new(),
            )])
            .lean_subsumption_certificate_json(A, B)
            .expect("A and not-B close"),
            ht(vec![Clause::new(vec![con(false, A, X)], Vec::new())])
                .lean_unsatisfiable_concept_certificate_json(A)
                .expect("A closes"),
            non_subsumption,
            satisfiable_concept,
        ];
        for (index, document) in queries.iter().enumerate() {
            let path = std::env::temp_dir().join(format!(
                "km-ht-query-cert-{}-{index}.json",
                std::process::id()
            ));
            std::fs::write(&path, document).expect("write temporary HT query certificate");
            let accepted = std::process::Command::new(&checker)
                .arg(&path)
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .expect("run native Lean HT checker")
                .success();
            let _ = std::fs::remove_file(path);
            assert!(accepted, "Lean must accept Rust query certificate {index}");
        }
    }

    #[test]
    fn lean_taxonomy_wire_passes_native_checker_when_configured() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_TAXONOMY_CHECKER") else {
            return;
        };
        let path = std::env::temp_dir().join(format!(
            "km-ht-taxonomy-cert-{}.json",
            std::process::id()
        ));
        let mut plain = ht(Vec::new());
        let mut mixed = ht(vec![Clause::new(
            vec![con(false, D, X), Atom::Eq { s: X, t: X }],
            vec![con(false, A, X)],
        )]);
        let documents = [
            plain
                .lean_taxonomy_certificate_json(&[A, B])
                .expect("produce complete equality-free taxonomy"),
            mixed
                .lean_taxonomy_certificate_json(&[A, B])
                .expect("produce complete mixed equality taxonomy"),
        ];
        for document in &documents {
            std::fs::write(&path, document).expect("write temporary HT taxonomy certificate");
            let accepted = std::process::Command::new(&checker)
                .arg(&path)
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .expect("run native Lean HT taxonomy checker")
                .success();
            assert!(accepted, "Lean must accept the complete Rust taxonomy matrix");
        }
        let document = &documents[1];
        let mut tampered: serde_json::Value =
            serde_json::from_str(document).expect("taxonomy document is JSON");
        tampered["subsumptions"][0]
            .as_array_mut()
            .expect("first taxonomy row")
            .pop();
        std::fs::write(&path, serde_json::to_vec(&tampered).unwrap())
            .expect("write tampered HT taxonomy certificate");
        let rejected = !std::process::Command::new(&checker)
            .arg(&path)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .expect("run native Lean HT taxonomy checker on tampered matrix")
            .success();
        let _ = std::fs::remove_file(path);
        assert!(rejected, "Lean must reject a taxonomy with one missing cell");
    }

    #[test]
    fn lean_taxonomy_checker_accepts_a_materialized_equality_body() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_TAXONOMY_CHECKER") else {
            return;
        };
        let mut t = ht(vec![Clause::new(
            vec![Atom::Eq { s: X, t: X }],
            vec![con(false, A, X)],
        )]);
        assert_eq!(t.consistent(&[]), Some(true));
        let document = t
            .lean_taxonomy_certificate_json(&[A, B])
            .expect("produce a complete equality-body taxonomy");
        let path = std::env::temp_dir().join(format!(
            "km-ht-taxonomy-equality-body-gap-{}.json",
            std::process::id()
        ));
        std::fs::write(&path, document).unwrap();
        let accepted = std::process::Command::new(&checker)
            .arg(&path)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .expect("run native Lean checker on normalized equality-body model")
            .success();
        let _ = std::fs::remove_file(path);
        assert!(accepted, "the checker must accept the materialized equality body");
    }

    #[test]
    fn body_equality_substitutes_every_occurrence_before_saturation() {
        let y = 1;
        let mut t = ht(vec![Clause::new(
            vec![Atom::Eq { s: X, t: y }, con(false, D, y)],
            vec![con(false, A, X)],
        )]);
        assert_eq!(
            t.consistent(&[CLit::pos(D), CLit { c: A, neg: true }]),
            Some(false),
            "x=y and D(y) must force A(x) after equality elimination"
        );
    }

    #[test]
    fn transitive_body_equalities_share_one_representative() {
        let y = 1;
        let z = 2;
        let t = ht(vec![Clause::new(
            vec![
                Atom::Eq { s: y, t: z },
                Atom::Eq { s: X, t: y },
                con(false, D, z),
            ],
            vec![con(false, A, y)],
        )]);
        let clause = &t.clauses[0].0;
        assert!(matches!(clause.body.as_slice(),
            [Atom::Concept { lit, t }] if *lit == CLit::pos(D) && *t == X));
        assert!(matches!(clause.head.as_slice(),
            [Atom::Concept { lit, t }] if *lit == CLit::pos(A) && *t == X));
    }

    #[test]
    fn equality_premise_contradiction_becomes_a_global_clash() {
        let y = 1;
        let mut t = ht(vec![Clause::new(
            vec![Atom::Eq { s: X, t: y }],
            Vec::new(),
        )]);
        assert_eq!(t.consistent(&[]), Some(false));
    }
}
