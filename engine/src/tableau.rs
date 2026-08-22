//! Hypertableau consistency checker (Motik–Shearer–Horrocks, JAIR 2009),
//! milestone M1: the `ALC` fragment (concept names, ¬, ⊓, ⊔, ∀, ∃) plus role
//! hierarchy. No number restrictions (>1) and no nominals yet, so there is no
//! ≤-rule and no NI-rule, and ancestor *subset* blocking suffices for
//! termination (sound for `ALC` without inverse roles).
//!
//! This is the model-construction half of the planned CB+tableau hybrid
//! (`docs/HYBRID-TABLEAU.md`): it decides consistency of a set of HT-clauses by
//! building ONE completion graph with OR-branching + backtracking, instead of
//! saturating every consequence the way the CB engine does. On the
//! live-disjunction ontologies where the CB engine blows up, the tableau builds
//! a small blocked model and terminates.
//!
//! Correctness obligations it must satisfy (msh09): Lemma 5 (every branch clashes
//! ⇒ unsat), Lemma 6 (a clash-free complete leaf ⇒ sat, via unraveling),
//! Lemma 7 (termination via blocking). Validated against the HermiT oracle.
//
// Work in progress (M1): the public API is exercised by the unit tests and will
// be wired to a CLI/normaliser driver next, so allow dead code meanwhile.
#![allow(dead_code)]

use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use std::collections::{HashMap, HashSet, VecDeque};

thread_local! {
    /// Search statistics, only printed when `KM_TAB_STATS` is set. (expand calls,
    /// branch alternatives tried, branch alternatives that backtracked). Used to
    /// decide whether dependency-directed backjumping is worth building.
    static STATS: std::cell::Cell<(u64, u64, u64)> = const { std::cell::Cell::new((0, 0, 0)) };
}
#[inline]
fn stat_expand() {
    STATS.with(|s| {
        let (e, t, b) = s.get();
        s.set((e + 1, t, b));
        if (e + 1) % 200_000 == 0 && std::env::var_os("KM_TAB_STATS").is_some() {
            eprintln!(
                "KM_TAB_STATS progress expands={} branch_tries={} backtracks={}",
                e + 1,
                t,
                b
            );
        }
    });
}
#[inline]
fn stat_try() {
    STATS.with(|s| {
        let (e, t, b) = s.get();
        s.set((e, t + 1, b));
    });
}
#[inline]
fn stat_backtrack() {
    STATS.with(|s| {
        let (e, t, b) = s.get();
        s.set((e, t, b + 1));
    });
}
thread_local! {
    /// (decision-on-demand unit survivors asserted, DOD clashes). Only printed
    /// under KM_TAB_STATS; lets us confirm unit propagation actually fires.
    static UNITS: std::cell::Cell<(u64, u64)> = const { std::cell::Cell::new((0, 0)) };
}
#[inline]
fn stat_unit(applied: u64, clashed: bool) {
    UNITS.with(|s| {
        let (a, c) = s.get();
        s.set((a + applied, c + clashed as u64));
    });
}

/// Atomic concept id, atomic role id, clause variable, completion-graph node.
pub type C = u32;
pub type R = u32;
pub type Var = u32;
pub type Node = usize;

/// The center variable `x` of every HT-clause.
pub const X: Var = 0;

/// HermiT-style hypertableau (dependency-directed backjumping + disjunction
/// learning + anywhere blocking), built bottom-up alongside the legacy paths.
/// See the module header for the increment plan. Gated into `run_json` by
/// `KM_HT=1` once the main loop lands (INCR 4).
#[path = "hypertableau.rs"]
pub mod hypertableau;

/// A concept literal `A` or `¬A` (post-NNF, so concepts are atomic).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct CLit {
    pub neg: bool,
    pub c: C,
}
impl CLit {
    pub fn pos(c: C) -> CLit {
        CLit { neg: false, c }
    }
    pub fn neg(c: C) -> CLit {
        CLit { neg: true, c }
    }
    fn complement(&self) -> CLit {
        CLit {
            neg: !self.neg,
            c: self.c,
        }
    }
}

/// An HT-clause atom. `Exists` appears only in heads (`≥1 R.B`); `Eq` appears in
/// heads (`≤n R.C`, functional roles) and is discharged by *merging* the two
/// nodes; `Concept`/`Role` appear in bodies and heads.
#[derive(Clone, Debug)]
pub enum Atom {
    Concept { lit: CLit, t: Var },
    Role { r: R, s: Var, t: Var },
    Exists { r: R, fil: CLit, t: Var },
    Eq { s: Var, t: Var },
}

/// `body (conjunction) → head (disjunction)`. Empty head = `⊥` (clause forces a
/// clash when its body matches).
#[derive(Clone, Debug)]
pub struct Clause {
    pub body: Vec<Atom>,
    pub head: Vec<Atom>,
}

impl Clause {
    pub fn new(body: Vec<Atom>, head: Vec<Atom>) -> Clause {
        Clause { body, head }
    }
}

/// The completion graph: a labelled forest of individuals.
/// One reversible mutation recorded on the graph's `trail`. Replaying these in
/// reverse (`rollback_to`) restores the graph to an earlier checkpoint, so the
/// DFS in `expand` backtracks by undoing edits instead of cloning the whole
/// graph at every branch point. `present_lits` / `present_roles` are *not*
/// rolled back: they are a monotone over-approximation used only as a cheap
/// "can this clause match" pre-filter, so a stale-positive entry costs an extra
/// (failing) match attempt, never an unsound result.
#[derive(Clone)]
enum Undo {
    /// `add_concept(node, lit)` added `lit` freshly — remove it.
    Concept(Node, CLit),
    /// `add_edge(r, s, t)` added the edge freshly — remove it.
    Edge(R, Node, Node),
    /// `add_exobl(node, r, fil)` added the obligation freshly — remove it.
    Exobl(Node, R, CLit),
    /// `new_node` appended the last node slot — pop it.
    NewNode,
    /// `merge` collapsed `gone` into `keep` — invert it. Boxed so the common
    /// (small) trail records do not pay for this variant's four vectors.
    Merge(Box<MergeUndo>),
}

/// Everything needed to invert one `merge(keep ⟸ gone)`. The `bool` on each
/// moved concept / exobl / edge records whether that insertion was *fresh* on
/// the survivor (so undo removes exactly the entries the merge created, leaving
/// any that coincided with pre-existing ones intact).
#[derive(Clone)]
struct MergeUndo {
    keep: Node,
    gone: Node,
    moved_concepts: Vec<(CLit, bool)>,
    moved_exobl: Vec<((R, CLit), bool)>,
    moved_edges: Vec<((R, Node, Node), bool)>,
    moved_pred: Vec<Node>,
}

#[derive(Clone)]
struct Graph {
    /// concept label of each node
    concepts: Vec<HashSet<CLit>>,
    /// `≥1 R.B` obligations of each node (the ∃-rule discharges these)
    exobl: Vec<HashSet<(R, CLit)>>,
    /// role edges `R(from,to)` (atomic roles only). Kept for O(1) membership.
    edges: HashSet<(R, Node, Node)>,
    /// adjacency index mirroring `edges`: `out_edges[s]` holds `(r, t)` for every
    /// edge `(r, s, t)`. Lets the matcher and the ∃-rules iterate a node's actual
    /// successors instead of scanning all edges / all nodes. Maintained in lock
    /// step with `edges` through `raw_edge_insert` / `raw_edge_remove`.
    out_edges: Vec<Vec<(R, Node)>>,
    /// tree predecessor of each node (None for root individuals)
    pred: Vec<Option<Node>>,
    /// whether each node is blockable (a generated tree node) vs a root
    blockable: Vec<bool>,
    /// concept literals present on *some* node, and roles on *some* edge —
    /// indexes for cheap clause pruning (a clause whose body needs an absent
    /// predicate can never match, so it is never even attempted).
    present_lits: HashSet<CLit>,
    present_roles: HashSet<R>,
    /// union-find representative of each node. A node `n` is *alive* iff
    /// `repr[n] == n`; merging (the ≤-rule / functional-role Eq atom) points the
    /// merged-away node at its survivor. All stored edges/pred are kept pointing
    /// at survivors (rewritten on merge), so reads need `find` only defensively.
    repr: Vec<Node>,
    /// Undo log for backtracking: every mutator appends a record, `checkpoint`
    /// reads the length, and `rollback_to` replays records in reverse.
    trail: Vec<Undo>,
    /// Backjumping dependency sets (populated only on the incremental
    /// non-careful path; empty otherwise). Per-node concept deps, global edge
    /// deps, per-node ∃-obligation deps — each rolled back with its fact.
    cdep: Vec<HashMap<CLit, DepSet>>,
    edep: HashMap<(R, Node, Node), DepSet>,
    xdep: Vec<HashMap<(R, CLit), DepSet>>,
}

impl Graph {
    fn new() -> Graph {
        Graph {
            concepts: Vec::new(),
            exobl: Vec::new(),
            edges: HashSet::new(),
            out_edges: Vec::new(),
            pred: Vec::new(),
            blockable: Vec::new(),
            present_lits: HashSet::new(),
            present_roles: HashSet::new(),
            repr: Vec::new(),
            trail: Vec::new(),
            cdep: Vec::new(),
            edep: HashMap::new(),
            xdep: Vec::new(),
        }
    }

    fn new_node(&mut self, pred: Option<Node>, blockable: bool) -> Node {
        let id = self.concepts.len();
        self.concepts.push(HashSet::new());
        self.exobl.push(HashSet::new());
        self.out_edges.push(Vec::new());
        self.cdep.push(HashMap::new());
        self.xdep.push(HashMap::new());
        self.pred.push(pred);
        self.blockable.push(blockable);
        self.repr.push(id);
        self.trail.push(Undo::NewNode);
        id
    }

    /// Insert `(r, s, t)` into both `edges` and the `out_edges` mirror, keeping
    /// `present_roles` (a monotone index, never rolled back). Returns `true` iff
    /// the edge was new. Every edge insertion goes through here so the two stay
    /// consistent.
    fn raw_edge_insert(&mut self, r: R, s: Node, t: Node) -> bool {
        let fresh = self.edges.insert((r, s, t));
        if fresh {
            self.out_edges[s].push((r, t));
            self.present_roles.insert(r);
        }
        fresh
    }

    /// Remove `(r, s, t)` from both `edges` and the `out_edges` mirror. Returns
    /// `true` iff it was present.
    fn raw_edge_remove(&mut self, r: R, s: Node, t: Node) -> bool {
        let existed = self.edges.remove(&(r, s, t));
        if existed {
            if let Some(i) = self.out_edges[s]
                .iter()
                .position(|&(rr, tt)| rr == r && tt == t)
            {
                self.out_edges[s].swap_remove(i);
            }
        }
        existed
    }

    /// Current trail position; pass to `rollback_to` to undo everything since.
    fn checkpoint(&self) -> usize {
        self.trail.len()
    }

    /// Undo every mutation recorded since `cp`, restoring the graph to the state
    /// it had at that checkpoint (except the monotone `present_*` indexes).
    fn rollback_to(&mut self, cp: usize) {
        while self.trail.len() > cp {
            match self.trail.pop().unwrap() {
                Undo::Concept(node, lit) => {
                    self.concepts[node].remove(&lit);
                    self.cdep[node].remove(&lit);
                }
                Undo::Edge(r, s, t) => {
                    self.raw_edge_remove(r, s, t);
                    self.edep.remove(&(r, s, t));
                }
                Undo::Exobl(node, r, fil) => {
                    self.exobl[node].remove(&(r, fil));
                    self.xdep[node].remove(&(r, fil));
                }
                Undo::NewNode => {
                    // The appended node is always the last slot (later-created
                    // nodes have later trail records, already undone).
                    self.concepts.pop();
                    self.exobl.pop();
                    self.out_edges.pop();
                    self.cdep.pop();
                    self.xdep.pop();
                    self.pred.pop();
                    self.blockable.pop();
                    self.repr.pop();
                }
                Undo::Merge(m) => self.undo_merge(*m),
            }
        }
    }

    /// Invert one `merge` (see `MergeUndo`). Restores `gone` as its own
    /// representative, moves its concepts / obligations / edges / children back,
    /// and removes only the entries the merge freshly created on the survivor.
    fn undo_merge(&mut self, m: MergeUndo) {
        let MergeUndo {
            keep,
            gone,
            moved_concepts,
            moved_exobl,
            moved_edges,
            moved_pred,
        } = m;
        self.repr[gone] = gone;
        for n in moved_pred {
            self.pred[n] = Some(gone);
        }
        // Remove the rewrites that were newly inserted, then re-add the originals.
        for &((r, s, t), fresh) in &moved_edges {
            if fresh {
                let s2 = if s == gone { keep } else { s };
                let t2 = if t == gone { keep } else { t };
                self.raw_edge_remove(r, s2, t2);
            }
        }
        for &((r, s, t), _) in &moved_edges {
            self.raw_edge_insert(r, s, t);
        }
        for &(o, fresh) in &moved_exobl {
            if fresh {
                self.exobl[keep].remove(&o);
            }
            self.exobl[gone].insert(o);
        }
        for &(l, fresh) in &moved_concepts {
            if fresh {
                self.concepts[keep].remove(&l);
            }
            self.concepts[gone].insert(l);
        }
    }

    /// Union-find survivor of `x` (follows the merge chain; no path compression
    /// so it stays `&self`).
    fn find(&self, mut x: Node) -> Node {
        while self.repr[x] != x {
            x = self.repr[x];
        }
        x
    }

    /// A node is alive iff it is its own representative (not merged away).
    fn alive(&self, x: Node) -> bool {
        self.repr[x] == x
    }

    /// Merge node `y` into node `x` (the ≤-rule / functional Eq atom). The
    /// survivor is the lower id (created earlier — closer to the root, and for
    /// the merged-siblings case both share a parent so the tree shape is kept).
    /// Concept labels and ∃-obligations are unioned onto the survivor and every
    /// edge / tree-predecessor pointing at the merged node is rewritten, so the
    /// graph never again references the dead node.
    fn merge(&mut self, x: Node, y: Node) {
        let a = self.find(x);
        let b = self.find(y);
        if a == b {
            return;
        }
        let (keep, gone) = if a < b { (a, b) } else { (b, a) };
        // move concept labels (drain first to release the borrow), recording
        // which were fresh on the survivor so the merge can be inverted.
        let labs: Vec<CLit> = self.concepts[gone].drain().collect();
        let mut moved_concepts = Vec::with_capacity(labs.len());
        for l in labs {
            let fresh = self.concepts[keep].insert(l);
            if fresh {
                self.present_lits.insert(l);
            }
            moved_concepts.push((l, fresh));
        }
        // move ∃-obligations
        let obls: Vec<(R, CLit)> = self.exobl[gone].drain().collect();
        let mut moved_exobl = Vec::with_capacity(obls.len());
        for o in obls {
            let fresh = self.exobl[keep].insert(o);
            moved_exobl.push((o, fresh));
        }
        // rewrite every edge that touches `gone` (leave the rest untouched).
        let touching: Vec<(R, Node, Node)> = self
            .edges
            .iter()
            .copied()
            .filter(|&(_, s, t)| s == gone || t == gone)
            .collect();
        let mut moved_edges = Vec::with_capacity(touching.len());
        for (r, s, t) in touching {
            self.raw_edge_remove(r, s, t);
            let s2 = if s == gone { keep } else { s };
            let t2 = if t == gone { keep } else { t };
            let fresh = self.raw_edge_insert(r, s2, t2);
            moved_edges.push(((r, s, t), fresh));
        }
        // children of `gone` become children of `keep`
        let mut moved_pred = Vec::new();
        for (n, p) in self.pred.iter_mut().enumerate() {
            if *p == Some(gone) {
                *p = Some(keep);
                moved_pred.push(n);
            }
        }
        self.repr[gone] = keep;
        self.trail.push(Undo::Merge(Box::new(MergeUndo {
            keep,
            gone,
            moved_concepts,
            moved_exobl,
            moved_edges,
            moved_pred,
        })));
    }

    /// Insert a concept literal on a node, maintaining `present_lits`. Returns
    /// `true` iff it was newly added.
    fn add_concept(&mut self, node: Node, lit: CLit) -> bool {
        let fresh = self.concepts[node].insert(lit);
        if fresh {
            self.present_lits.insert(lit);
            self.trail.push(Undo::Concept(node, lit));
        }
        fresh
    }

    /// Insert a role edge (trailed), maintaining the `out_edges` mirror and
    /// `present_roles`. Returns `true` iff new.
    fn add_edge(&mut self, r: R, s: Node, t: Node) -> bool {
        let fresh = self.raw_edge_insert(r, s, t);
        if fresh {
            self.trail.push(Undo::Edge(r, s, t));
        }
        fresh
    }

    /// Record a `≥1 R.B` obligation on a node. Returns `true` iff new.
    fn add_exobl(&mut self, node: Node, r: R, fil: CLit) -> bool {
        let fresh = self.exobl[node].insert((r, fil));
        if fresh {
            self.trail.push(Undo::Exobl(node, r, fil));
        }
        fresh
    }

    fn n(&self) -> usize {
        self.concepts.len()
    }

    /// Ancestors of `s` along the tree-predecessor chain.
    fn ancestors(&self, mut s: Node) -> Vec<Node> {
        let mut out = Vec::new();
        while let Some(p) = self.pred[s] {
            out.push(p);
            s = p;
        }
        out
    }

    /// The set of roles on the directed edge `a → b` (scans only `a`'s successors).
    fn edge_label(&self, a: Node, b: Node) -> HashSet<R> {
        self.out_edges[a]
            .iter()
            .filter(|(_, t)| *t == b)
            .map(|(r, _)| *r)
            .collect()
    }

    /// Does node `s` carry a clash (`A` and `¬A`)?
    fn node_clash(&self, s: Node) -> bool {
        self.concepts[s]
            .iter()
            .any(|l| !l.neg && self.concepts[s].contains(&l.complement()))
    }
    fn clash(&self) -> bool {
        (0..self.n()).any(|s| self.node_clash(s))
    }
}

/// A substitution from clause variables to graph nodes. Clauses have only a
/// handful of variables (the centre `x` plus a few successors), so an inline
/// association vector is both faster and — crucially — allocation-free to clone
/// for the common small case, where `HashMap` allocated a fresh table per
/// solution (the dominant allocation churn in the matcher). Spills to the heap
/// only past four entries (e.g. large number restrictions).
#[derive(Clone, Default)]
struct Subst {
    v: SmallVec<[(Var, Node); 4]>,
}

impl Subst {
    fn new() -> Self {
        Subst { v: SmallVec::new() }
    }
    fn get(&self, k: Var) -> Option<Node> {
        self.v.iter().find(|(kk, _)| *kk == k).map(|(_, n)| *n)
    }
    fn contains(&self, k: Var) -> bool {
        self.v.iter().any(|(kk, _)| *kk == k)
    }
    /// Binding of `k`; panics if unbound (mirrors `HashMap`'s `Index`).
    fn lookup(&self, k: Var) -> Node {
        self.get(k)
            .expect("unbound clause variable in substitution")
    }
    fn insert(&mut self, k: Var, n: Node) {
        for e in self.v.iter_mut() {
            if e.0 == k {
                e.1 = n;
                return;
            }
        }
        self.v.push((k, n));
    }
    fn remove(&mut self, k: Var) {
        if let Some(i) = self.v.iter().position(|(kk, _)| *kk == k) {
            // order-independent (this is a map), so swap-remove is fine.
            self.v.swap_remove(i);
        }
    }
}

/// All variables occurring in a clause.
fn clause_vars(cl: &Clause) -> Vec<Var> {
    let mut vs = Vec::new();
    let push = |v: Var, vs: &mut Vec<Var>| {
        if !vs.contains(&v) {
            vs.push(v);
        }
    };
    for a in cl.body.iter().chain(cl.head.iter()) {
        match a {
            Atom::Concept { t, .. } => push(*t, &mut vs),
            Atom::Role { s, t, .. } => {
                push(*s, &mut vs);
                push(*t, &mut vs);
            }
            Atom::Exists { t, .. } => push(*t, &mut vs),
            Atom::Eq { s, t } => {
                push(*s, &mut vs);
                push(*t, &mut vs);
            }
        }
    }
    vs
}

/// The set of disjunction decision *levels* a derived fact depends on, used for
/// dependency-directed backjumping. A fact's dependency set is the union of the
/// dependency sets of the facts that derived it; a disjunct chosen at level `L`
/// additionally depends on `{L}`. When a clash's combined dependency set does not
/// contain the current decision level, that decision is irrelevant to the clash,
/// so the search backjumps past it (and its untried siblings) instead of
/// exploring them. Kept sorted and duplicate-free; usually tiny (most facts
/// depend on a single choice), so an inline 4-element vector avoids allocation.
#[derive(Clone, Default, PartialEq)]
struct DepSet {
    v: SmallVec<[u32; 4]>,
}

impl DepSet {
    fn new() -> Self {
        DepSet { v: SmallVec::new() }
    }
    fn singleton(l: u32) -> Self {
        let mut v = SmallVec::new();
        v.push(l);
        DepSet { v }
    }
    fn contains(&self, l: u32) -> bool {
        self.v.binary_search(&l).is_ok()
    }
    fn insert(&mut self, l: u32) {
        if let Err(i) = self.v.binary_search(&l) {
            self.v.insert(i, l);
        }
    }
    /// Merge `other` into `self` (sorted-union).
    fn union_with(&mut self, other: &DepSet) {
        for &l in &other.v {
            self.insert(l);
        }
    }
    /// Remove a level (used when a decision level is exhausted: its own number is
    /// dropped before propagating the residual dependencies to the parent).
    fn remove(&mut self, l: u32) {
        if let Ok(i) = self.v.binary_search(&l) {
            self.v.remove(i);
        }
    }
}

/// Result of a backjumping expansion: either a clash-free model was reached, or
/// the subtree clashed and `DepSet` records which decision levels the clash
/// depends on (so the caller can backjump).
enum Outcome {
    Sat,
    Conflict(DepSet),
}

/// A clause plus precomputed metadata for pruning: the concept literals and
/// roles its body requires, and whether it is disjunctive (≥2 head atoms).
struct ClauseInfo {
    cl: Clause,
    body_lits: Vec<CLit>,
    body_roles: Vec<R>,
    disjunctive: bool,
}

pub struct Tableau {
    clauses: Vec<ClauseInfo>,
    /// Semi-naive saturation index (non-disjunctive clauses only). Maps a body
    /// concept literal to the `(clause, body-variable)` pairs it can seed: when a
    /// fact `lit@node` is newly derived, only these clauses can fire a new
    /// consequence, and binding the variable to `node` avoids re-scanning all
    /// nodes for the centre. Built once in `new`.
    lit_index: HashMap<CLit, Vec<(usize, Var)>>,
    /// Likewise for role body atoms: role → `(clause, source-var, target-var)`.
    role_index: HashMap<R, Vec<(usize, Var, Var)>>,
    /// Non-disjunctive clauses with a head variable not bound by the body (e.g.
    /// `⊤ ⊑ C`): they must fire afresh on every new node. `(clause, the unbound
    /// head variable to bind to the node)`.
    node_triggered: Vec<(usize, Var)>,
    /// Use pairwise (double) blocking instead of subset blocking. Required for
    /// soundness when inverse roles are present (subset blocking lets a blocked
    /// node's label flow back up the tree via the inverse edge); harmless but
    /// slower otherwise, so it is enabled only when the KB declares inverses.
    pairwise: bool,
    /// KB has number restrictions (≤n / functional). Switches on the
    /// merge-capable expansion path and equality (rather than subset) blocking,
    /// which is sound for SHQ. Subset blocking is unsound with number
    /// restrictions; equality blocking keeps the cardinalities consistent under
    /// unravelling.
    number: bool,
    /// Nominal concepts `{a}` (one concept id per named individual proxy
    /// `__nom__a`). Each is a *singleton*: at most one element. The o-rule
    /// (`apply_nominal_merges`) enforces it by merging any two nodes that carry
    /// the same nominal literal, and `find_model` seeds one non-blockable root
    /// per nominal so the named individuals exist in every model (an ABox-level
    /// inconsistency is then caught by the consistency check). SHOQ (nominals +
    /// number, no inverse) is sound this way; SHOI/SHOIQ (nominals + inverse)
    /// is fenced by the converter because the NI-rule for root chains is not
    /// built.
    nominals: Vec<C>,
    /// KM_HT_BLOCKSKIP — do not branch a disjunction on a *blocked* node (its
    /// blocker carries a superset label and resolves it; the unravelling copies
    /// that resolution). Sound only on the inverse-free subset-blocking path; the
    /// direct realisation of "kill the per-node branching" (folds the model the
    /// way HermiT folds 197 nodes to ~3). Read once at construction.
    blockskip: bool,
    /// KM_HT_UNSATCACHE — within-search cache of node concept-labels proven
    /// intrinsically unsatisfiable (a disjunction on the node failed independent
    /// of every other decision). Inverse-free ⇒ a node's label determines its
    /// satisfiability, so any later node whose label is a superset clashes at
    /// once. The "within-search" ~1000x lever; sound on the non-careful path.
    unsatcache: bool,
    /// KM_HT_EQBLOCK — use *equality* blocking (L(s)=L(t)) instead of *subset*
    /// blocking on the inverse-free path. Subset blocking can declare a node
    /// satisfiable that an equal-label expansion would refute, so it is
    /// *incomplete* for ALC(H)+⊔ classification (it misses subsumptions). Equality
    /// blocking is complete and still terminates (finitely many distinct labels
    /// over a fixed signature). The completeness fix for the live-disjunction
    /// family (it recovers e.g. 5303's CHSubstructure⊑Hydrocarbon).
    eqblock: bool,
    /// KM_HT_LAZY — lazy unfolding: branch guarded disjunctions (non-empty body)
    /// before unguarded ⊤-level ones, deferring the excluded-middle / covering
    /// tautologies until nothing guarded is pending. Sound selection-order change.
    lazy: bool,
    /// KM_HT_DOD — decision-on-demand (DPLL-style unit propagation). A disjunction
    /// is never *branched* while it is still determined: inside the saturation
    /// fixpoint, every fired disjunction whose head disjuncts are all refuted but
    /// one has that one survivor asserted *deterministically* (with the refuting
    /// literals' deps folded in — sound resolution), and one whose disjuncts are
    /// *all* refuted clashes at once. Only genuinely open (≥2 unassigned disjuncts)
    /// disjunctions reach the branch point in `expand_inc`. This is the true lazy
    /// unfolding at the rule level — it collapses the per-node branching factor on
    /// the live ∀+⊔ family (every excluded-middle choice forced by the deterministic
    /// structure is propagated, not split). Non-careful path only. Changes what the
    /// search derives ⇒ Lean re-cert before any default-on.
    dod: bool,
}

/// Contrapositive Horn clauses for clash clauses (KM_HT_CONTRA). A clash clause
/// `A1 ⊓ … ⊓ An ⊑ ⊥` (empty head, all-Concept body on one variable) is logically
/// equivalent to its n contrapositives `⋀_{j≠i} Aj → ¬Ai`. The base hypertableau
/// only detects the clash once *every* Ai is present; the contrapositives let it
/// *derive* `¬Ai` as soon as the other n−1 hold, so negative literals propagate
/// through Horn closure. Two things hinge on that: decision-on-demand unit
/// propagation can fire on complementary disjunctions (no `¬Ai` is asserted
/// otherwise, so DOD is inert), and the negative branch's own consequences
/// (`¬A ⊑ ∃r.B`) get explored — the completeness gap that EMELIM silently drops.
/// Each added clause is entailed by the original, so the addition is sound.
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
                // A clash gated by a role/eq atom is not a pure single-node
                // concept clash — skip (its contrapositive is not a Horn unit).
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
            let head = vec![Atom::Concept {
                lit: lits[i].complement(),
                t: v,
            }];
            extra.push(Clause::new(body, head));
        }
    }
    extra
}

impl Tableau {
    pub fn new(clauses: Vec<Clause>) -> Tableau {
        let mut clauses = clauses;
        // KM_HT_CONTRA: enrich clash clauses with their contrapositives so negative
        // literals propagate (prerequisite for decision-on-demand to do anything).
        if std::env::var_os("KM_HT_CONTRA").is_some() {
            let extra = contrapositives(&clauses);
            if std::env::var_os("KM_TAB_STATS").is_some() {
                eprintln!("KM_TAB_STATS contrapositives added={}", extra.len());
            }
            clauses.extend(extra);
        }
        let infos = clauses
            .into_iter()
            .map(|cl| {
                let mut body_lits = Vec::new();
                let mut body_roles = Vec::new();
                for a in &cl.body {
                    match a {
                        Atom::Concept { lit, .. } => body_lits.push(*lit),
                        Atom::Role { r, .. } => body_roles.push(*r),
                        Atom::Exists { .. } => {} // ∃ never appears in a body
                        Atom::Eq { .. } => {}     // eq is a head-only construct here
                    }
                }
                let disjunctive = cl.head.len() >= 2;
                ClauseInfo {
                    cl,
                    body_lits,
                    body_roles,
                    disjunctive,
                }
            })
            .collect::<Vec<_>>();
        // Build the semi-naive index over non-disjunctive clauses.
        let mut lit_index: HashMap<CLit, Vec<(usize, Var)>> = HashMap::new();
        let mut role_index: HashMap<R, Vec<(usize, Var, Var)>> = HashMap::new();
        let mut node_triggered: Vec<(usize, Var)> = Vec::new();
        for (ci, info) in infos.iter().enumerate() {
            if info.disjunctive {
                continue;
            }
            let mut body_vars: Vec<Var> = Vec::new();
            for a in &info.cl.body {
                match a {
                    Atom::Concept { lit, t } => {
                        lit_index.entry(*lit).or_default().push((ci, *t));
                        body_vars.push(*t);
                    }
                    Atom::Role { r, s, t } => {
                        role_index.entry(*r).or_default().push((ci, *s, *t));
                        body_vars.push(*s);
                        body_vars.push(*t);
                    }
                    _ => {}
                }
            }
            // A head variable not bound by the body makes the clause fire on every
            // node (the centre ranges over all individuals).
            for v in clause_vars(&info.cl) {
                if !body_vars.contains(&v) {
                    node_triggered.push((ci, v));
                    break;
                }
            }
        }
        Tableau {
            clauses: infos,
            lit_index,
            role_index,
            node_triggered,
            pairwise: false,
            number: false,
            nominals: Vec::new(),
            blockskip: std::env::var_os("KM_HT_BLOCKSKIP").is_some(),
            unsatcache: std::env::var_os("KM_HT_UNSATCACHE").is_some(),
            eqblock: std::env::var_os("KM_HT_EQBLOCK").is_some(),
            lazy: std::env::var_os("KM_HT_LAZY").is_some(),
            dod: std::env::var_os("KM_HT_DOD").is_some(),
        }
    }

    /// Enable pairwise blocking (for KBs with inverse roles).
    pub fn set_pairwise(&mut self, on: bool) {
        self.pairwise = on;
    }

    /// Enable the merge-capable path + equality blocking (for KBs with number
    /// restrictions / functional roles).
    pub fn set_number(&mut self, on: bool) {
        self.number = on;
    }

    /// Declare the nominal concepts (singleton `{a}` proxies). Switches on the
    /// merge-capable path, root seeding, equality blocking, and the o-rule.
    pub fn set_nominals(&mut self, noms: Vec<C>) {
        self.nominals = noms;
    }

    /// Does this KB need the careful (merge-capable) expansion path? True when
    /// number restrictions, inverse roles, or nominals are present — each needs
    /// `horn_saturate` (deterministic merges) rather than the fast batched
    /// `saturate`.
    fn careful(&self) -> bool {
        self.number || self.pairwise || !self.nominals.is_empty()
    }

    /// Is node `s` blocked? Subset (ancestor) blocking for the inverse-free case;
    /// pairwise (double) blocking when inverse roles are present.
    ///
    /// Subset: a blockable `s` is blocked iff some blockable ancestor `t` has
    /// `L(s) ⊆ L(t)` (sound for ALCH and SH).
    ///
    /// Pairwise: a blockable `s` with parent `p` is blocked iff some blockable
    /// strict ancestor `s2` with parent `p2` has `L(s)=L(s2)`, `L(p)=L(p2)`, and
    /// equal edge labels in both directions `p↔s` vs `p2↔s2`. Equality + the
    /// parent/edge match is what keeps blocking sound under inverse roles (SHI).
    fn node_blocked(&self, g: &Graph, s: Node) -> bool {
        if !g.blockable[s] {
            return false;
        }
        if !self.pairwise && (self.number || !self.nominals.is_empty()) {
            // Equality blocking: sound for SHQ (number restrictions, no inverse)
            // and SHO/SHOQ (nominals, no inverse). Subset blocking is unsound
            // with number restrictions — a blocked node reusing a strictly
            // larger ancestor label can leave an at-most restriction unsatisfied
            // in the unravelling. Requiring L(s)=L(t) keeps cardinalities aligned;
            // it is a sound (stricter) choice for nominals too.
            return g
                .ancestors(s)
                .into_iter()
                .any(|t| g.blockable[t] && g.concepts[s] == g.concepts[t]);
        }
        if !self.pairwise {
            // Equality blocking (KM_HT_EQBLOCK) is complete for ALC(H)+⊔ where
            // subset blocking is not; it still terminates (finite label universe).
            if self.eqblock {
                return g
                    .ancestors(s)
                    .into_iter()
                    .any(|t| g.blockable[t] && g.concepts[s] == g.concepts[t]);
            }
            return g
                .ancestors(s)
                .into_iter()
                .any(|t| g.blockable[t] && g.concepts[s].is_subset(&g.concepts[t]));
        }
        let p = match g.pred[s] {
            Some(p) => p,
            None => return false, // a root's child has no parent-pair to match
        };
        let el_ps = g.edge_label(p, s);
        let el_sp = g.edge_label(s, p);
        g.ancestors(s).into_iter().any(|s2| {
            if !g.blockable[s2] {
                return false;
            }
            let p2 = match g.pred[s2] {
                Some(p2) => p2,
                None => return false,
            };
            g.concepts[s] == g.concepts[s2]
                && g.concepts[p] == g.concepts[p2]
                && el_ps == g.edge_label(p2, s2)
                && el_sp == g.edge_label(s2, p2)
        })
    }

    /// Can this clause possibly match `g`? (Necessary condition: every body
    /// predicate is present somewhere.) Cheap O(body) filter before the full
    /// substitution search.
    fn matchable(&self, info: &ClauseInfo, g: &Graph) -> bool {
        info.body_lits.iter().all(|l| g.present_lits.contains(l))
            && info.body_roles.iter().all(|r| g.present_roles.contains(r))
    }

    /// Is the knowledge base consistent given the initial concept assertions on a
    /// single fresh root individual? (Concept satisfiability of the conjunction of
    /// `root_label` w.r.t. the clauses.) Returns true iff a clash-free complete
    /// completion graph exists.
    pub fn consistent(&self, root_label: &[CLit]) -> bool {
        if std::env::var_os("KM_TAB_CACHE").is_some() && !self.careful() {
            if let Some(prog) = self.build_cprog() {
                return self.consistent_cached(root_label, &prog);
            }
        }
        self.find_model(root_label).is_some()
    }

    /// Build one clash-free complete completion graph for `root_label` (the root is
    /// a fresh non-blockable individual), or `None` if every branch clashes.
    fn find_model(&self, root_label: &[CLit]) -> Option<Graph> {
        let mut g = Graph::new();
        let a = g.new_node(None, false); // root individual, not blockable
        for l in root_label {
            g.add_concept(a, *l);
        }
        // Seed one non-blockable root per nominal `{o}`: the named individuals
        // exist in every model, so their ABox consequences (clauses
        // `__nom__o(x) → C(x)`) and any KB-level inconsistency are enforced even
        // when the tested concept never references `o`. Seeded with low ids
        // (right after the test root), so a blockable node that later acquires
        // `__nom__o` merges *into* this root (lower id survives, stays a root).
        for &nc in &self.nominals {
            let r = g.new_node(None, false);
            g.add_concept(r, CLit::pos(nc));
        }
        let found = if self.careful() {
            self.expand(&mut g)
        } else {
            // Non-careful path: incremental (semi-naive) saturation. A clash
            // directly in the root label is caught here (the root concepts were
            // added without going through the worklist's clash check); deeper
            // clashes are caught during saturation.
            let root_clash = root_label
                .iter()
                .any(|l| g.concepts[a].contains(&l.complement()));
            if root_clash {
                false
            } else {
                // Root-label facts are given, so they depend on no decision.
                for &l in root_label {
                    g.cdep[a].insert(l, DepSet::new());
                }
                let mut q: VecDeque<NewFact> = VecDeque::new();
                if self.seed_node(&mut g, a, &mut q).is_none() {
                    for &l in root_label {
                        q.push_back(NewFact::Concept(a, l));
                    }
                    let mut st = SearchState::new();
                    matches!(self.expand_inc(&mut g, q, 0, &mut st), Outcome::Sat)
                } else {
                    false
                }
            }
        };
        if std::env::var("KM_TAB_STATS").is_ok() {
            let (e, t, b) = STATS.with(|s| s.get());
            let (ua, uc) = UNITS.with(|s| s.get());
            eprintln!(
                "KM_TAB_STATS expands={e} branch_tries={t} backtracks={b} dod_units={ua} dod_clashes={uc} nodes={}",
                g.n()
            );
        }
        if found {
            Some(g)
        } else {
            None
        }
    }

    /// DFS over the search tree. Mutates `g` in place and returns `true` iff a
    /// clash-free complete leaf was reached (`g` then holds that model). On a
    /// branch, each alternative checkpoints the trail, applies its edit, recurses,
    /// and on failure rolls back before trying the next — so backtracking undoes
    /// edits instead of cloning the whole graph. The caller's own checkpoint
    /// covers the deterministic saturation `g` accumulates before branching, so a
    /// `false` return leaves `g` mutated; the caller restores it.
    fn expand(&self, g: &mut Graph) -> bool {
        stat_expand();
        if !self.careful() {
            // Inverse-free, number-free, nominal-free path: saturate Horn + the deterministic ∃
            // round in one pass (∃ never needs backtracking here), then branch on
            // a disjunction. Fast; unchanged from the indexed-saturation work.
            if !self.saturate(g) {
                return false;
            }
            if let Some((head, subst, _)) = self.find_disjunctive(g) {
                for v in &head {
                    stat_try();
                    let cp = g.checkpoint();
                    self.add_head_atom(g, v, &subst);
                    if self.expand(g) {
                        return true;
                    }
                    g.rollback_to(cp);
                    stat_backtrack();
                }
                return false;
            }
            return true;
        }
        // Careful path (number restrictions and/or inverse roles): saturate Horn
        // *including deterministic ≈-merges* (a single-eq head is a forced
        // merge), then take ONE branching decision. The Hyp-rule branch covers
        // disjunctions, including a ≤n head with several ≈ disjuncts (each branch
        // merges a different pair).
        if !self.horn_saturate(g) {
            return false;
        }
        if let Some((head, subst, _)) = self.find_disjunctive(g) {
            for v in &head {
                let cp = g.checkpoint();
                self.add_head_atom(g, v, &subst);
                if self.expand(g) {
                    return true;
                }
                g.rollback_to(cp);
            }
            return false;
        }
        if !self.pairwise {
            // Number-only path (SHQ, no inverse): no loop-back needed, so batch
            // generate a fresh successor for every unsatisfied ∃ obligation on a
            // live, non-blocked node, then recurse (which re-saturates and may
            // fire a ≤-rule merge). Equality blocking bounds the depth. This is a
            // deterministic round (no choice), so it just recurses on `g`.
            let mut changed = false;
            for s in 0..g.n() {
                if !g.alive(s) || self.node_blocked(g, s) {
                    continue;
                }
                let obls: Vec<(R, CLit)> = g.exobl[s].iter().copied().collect();
                for (r, fil) in obls {
                    let sat = g.out_edges[s]
                        .iter()
                        .any(|&(rr, t)| rr == r && g.alive(t) && g.concepts[t].contains(&fil));
                    if !sat {
                        let t = g.new_node(Some(s), true);
                        g.add_edge(r, s, t);
                        g.add_concept(t, fil);
                        changed = true;
                    }
                }
            }
            if changed {
                return self.expand(g);
            }
            return true;
        }
        // Inverse path (pairwise blocking). The ∃-rule becomes a CHOICE: an
        // `∃r.fil` obligation may be satisfied by looping back to an existing
        // ancestor (a cyclic model) or by a fresh successor. Trying loop-back
        // first terminates the `∀r⁻`-over-infinite-chain pattern that defeats
        // pure equality blocking, while the fresh-successor fallback keeps the
        // search complete (no model is pruned) and saturation keeps it sound (a
        // loop-back that violates a constraint just clashes and is abandoned).
        if !self.horn_saturate(g) {
            return false;
        }
        if let Some((head, subst, _)) = self.find_disjunctive(g) {
            for v in &head {
                let cp = g.checkpoint();
                self.add_head_atom(g, v, &subst);
                if self.expand(g) {
                    return true;
                }
                g.rollback_to(cp);
            }
            return false;
        }
        if let Some((s, r, fil)) = self.first_unsat_exists(g) {
            // 1. loop-back branches: reuse a matching ancestor as the successor.
            for t in self.loopback_targets(g, s, r, fil) {
                let cp = g.checkpoint();
                g.add_edge(r, s, t);
                if self.expand(g) {
                    return true;
                }
                g.rollback_to(cp);
            }
            // 2. fallback branch: a fresh successor (the last alternative).
            let cp = g.checkpoint();
            let t = g.new_node(Some(s), true);
            g.add_edge(r, s, t);
            g.add_concept(t, fil);
            if self.expand(g) {
                return true;
            }
            g.rollback_to(cp);
            return false;
        }
        true
    }

    /// Saturate Horn Hyp to a clash-free fixpoint (no ∃), interleaving the
    /// nominal o-rule (singleton merges). Returns `false` on clash (empty-head
    /// clause, or `A` and `¬A` on a node).
    fn horn_saturate(&self, g: &mut Graph) -> bool {
        let prog = std::env::var_os("KM_TAB_STATS").is_some();
        let mut hs_iter = 0u64;
        loop {
            hs_iter += 1;
            if prog && hs_iter % 200 == 0 {
                eprintln!(
                    "KM_TAB_STATS horn_saturate iter={} nodes={}",
                    hs_iter,
                    g.n()
                );
            }
            let mut changed = false;
            for info in &self.clauses {
                if info.disjunctive || !self.matchable(info, g) {
                    continue;
                }
                for subst in self.match_body(&info.cl, g) {
                    if info.cl.head.is_empty() {
                        return false; // body matched, empty head ⇒ ⊥
                    }
                    let v = &info.cl.head[0];
                    if !self.head_atom_present(g, v, &subst) {
                        self.add_head_atom(g, v, &subst);
                        changed = true;
                    }
                }
            }
            // o-rule: a nominal `{o}` is a singleton, so any two nodes carrying
            // `__nom__o` denote the same individual ⇒ merge them (deterministic,
            // no branch). Merging can union conflicting labels onto one node, so
            // a clash here abandons the branch (sound).
            if !self.nominals.is_empty() && self.apply_nominal_merges(g) {
                changed = true;
            }
            if g.clash() {
                return false;
            }
            if !changed {
                return true;
            }
        }
    }

    /// The nominal o-rule: for each nominal concept `{o}`, merge every node that
    /// carries `__nom__o` into the lowest-id carrier (a seeded root survives, so
    /// the merged individual stays a non-blockable named node). Returns `true`
    /// iff any merge happened.
    fn apply_nominal_merges(&self, g: &mut Graph) -> bool {
        let mut merged = false;
        for &nc in &self.nominals {
            let lit = CLit::pos(nc);
            let carriers: Vec<Node> = (0..g.n())
                .filter(|&u| g.alive(u) && g.concepts[u].contains(&lit))
                .collect();
            if carriers.len() < 2 {
                continue;
            }
            let keep = carriers[0];
            for &other in &carriers[1..] {
                if g.find(keep) != g.find(other) {
                    g.merge(keep, other);
                    merged = true;
                }
            }
        }
        merged
    }

    /// Inverse-free deterministic saturation: Horn Hyp to fixpoint, then a batched
    /// ∃ round (all unsatisfied obligations on non-blocked nodes get a fresh
    /// successor), repeated until a fixpoint. Sound + terminating for ALCH/SH.
    fn saturate(&self, g: &mut Graph) -> bool {
        let prog = std::env::var_os("KM_TAB_STATS").is_some();
        let mut sat_round = 0u64;
        loop {
            sat_round += 1;
            if prog {
                eprintln!(
                    "KM_TAB_STATS saturate round={} nodes={} (entering horn_saturate)",
                    sat_round,
                    g.n()
                );
            }
            if !self.horn_saturate(g) {
                return false;
            }
            let mut ex_changed = false;
            for s in 0..g.n() {
                if self.node_blocked(g, s) {
                    continue;
                }
                let obls: Vec<(R, CLit)> = g.exobl[s].iter().copied().collect();
                for (r, fil) in obls {
                    let satisfied = g.out_edges[s]
                        .iter()
                        .any(|&(rr, t)| rr == r && g.concepts[t].contains(&fil));
                    if !satisfied {
                        let t = g.new_node(Some(s), true);
                        g.add_edge(r, s, t);
                        g.add_concept(t, fil);
                        ex_changed = true;
                        if g.n() % 2_000 == 0 && std::env::var_os("KM_TAB_STATS").is_some() {
                            eprintln!("KM_TAB_STATS saturate nodes={}", g.n());
                        }
                    }
                }
            }
            if !ex_changed {
                return true;
            }
        }
    }

    /// First unsatisfied `∃r.fil` obligation on a non-blocked node (the next ∃
    /// choice point in the pairwise path).
    fn first_unsat_exists(&self, g: &Graph) -> Option<(Node, R, CLit)> {
        for s in 0..g.n() {
            if self.node_blocked(g, s) {
                continue;
            }
            for &(r, fil) in &g.exobl[s] {
                let satisfied = g.out_edges[s]
                    .iter()
                    .any(|&(rr, t)| rr == r && g.concepts[t].contains(&fil));
                if !satisfied {
                    return Some((s, r, fil));
                }
            }
        }
        None
    }

    /// Ancestors of `s` that can serve as a loop-back successor for `∃r.fil`:
    /// the filler is already present and `L(s) ⊆ L(t)` (so `t` is at least as
    /// constrained — a promising cyclic-model target). Nearest first. This is
    /// only a heuristic ordering; soundness rests on saturation (a bad loop-back
    /// clashes) and completeness on the fresh-successor fallback, so missing a
    /// target never causes a wrong answer.
    fn loopback_targets(&self, g: &Graph, s: Node, r: R, fil: CLit) -> Vec<Node> {
        let _ = r;
        g.ancestors(s)
            .into_iter()
            .filter(|&t| g.concepts[t].contains(&fil) && g.concepts[s].is_subset(&g.concepts[t]))
            .collect()
    }

    /// Find a disjunctive (≥2 head) clause whose body matches and none of whose
    /// head disjuncts is already present — a branching point. Also returns the
    /// matched body's dependency set (empty on the careful path, which does not
    /// track dependencies), for backjumping.
    fn find_disjunctive(&self, g: &Graph) -> Option<(Vec<Atom>, Subst, DepSet)> {
        // BLOCKSKIP: on the inverse-free subset-blocking path, a disjunction whose
        // every target node is blocked need not be branched — the blocker resolves
        // it and the unravelling copies that resolution. Sound only there.
        let blockskip = self.blockskip && !self.careful();
        // LAZY unfolding (KM_HT_LAZY): pick a *guarded* disjunction (non-empty
        // body — a node-specific constraint) before any *unguarded* ⊤-level one
        // (the excluded-middle/covering tautologies). Deferring the ⊤-disjunctions
        // until nothing guarded is pending lets the deterministic and guarded
        // structure resolve first, so far fewer ⊤-branches are ever opened. Pure
        // selection-order change ⇒ sound and complete.
        if self.lazy && !self.careful() {
            if let Some(r) = self.find_disjunctive_pass(g, blockskip, Some(true)) {
                return Some(r);
            }
            return self.find_disjunctive_pass(g, blockskip, Some(false));
        }
        self.find_disjunctive_pass(g, blockskip, None)
    }

    /// One scan for a usable disjunction. `guarded`: `Some(true)` = only clauses
    /// with a non-empty body, `Some(false)` = only empty-body (⊤-level) clauses,
    /// `None` = any (original behaviour).
    fn find_disjunctive_pass(
        &self,
        g: &Graph,
        blockskip: bool,
        guarded: Option<bool>,
    ) -> Option<(Vec<Atom>, Subst, DepSet)> {
        for info in &self.clauses {
            if !info.disjunctive || !self.matchable(info, g) {
                continue;
            }
            if let Some(want) = guarded {
                if info.cl.body.is_empty() == want {
                    continue;
                }
            }
            let mut found: Option<Subst> = None;
            self.match_visit(&info.cl, g, &mut |subst| {
                if info
                    .cl
                    .head
                    .iter()
                    .all(|v| !self.head_atom_present(g, v, subst))
                {
                    if blockskip && self.disj_all_blocked(g, &info.cl.head, subst) {
                        return true; // every target node blocked: skip, keep searching
                    }
                    found = Some(subst.clone());
                    false
                } else {
                    true
                }
            });
            if let Some(subst) = found {
                let bdep = self.body_dep(g, &info.cl, &subst);
                return Some((info.cl.head.clone(), subst, bdep));
            }
        }
        None
    }

    /// True iff every head atom of a disjunction targets a blocked node (so the
    /// disjunction need not be expanded — BLOCKSKIP).
    fn disj_all_blocked(&self, g: &Graph, head: &[Atom], subst: &Subst) -> bool {
        head.iter().all(|v| {
            let node = match v {
                Atom::Concept { t, .. } | Atom::Exists { t, .. } => g.find(subst.lookup(*t)),
                Atom::Role { s, .. } => g.find(subst.lookup(*s)),
                Atom::Eq { .. } => return false,
            };
            self.node_blocked(g, node)
        })
    }

    /// The primary node a disjunction acts on (the target of its first concept /
    /// existential head atom), used to key the within-search unsat-label cache.
    fn disj_node(&self, g: &Graph, head: &[Atom], subst: &Subst) -> Option<Node> {
        head.iter().find_map(|v| match v {
            Atom::Concept { t, .. } | Atom::Exists { t, .. } => Some(g.find(subst.lookup(*t))),
            _ => None,
        })
    }

    fn head_atom_present(&self, g: &Graph, v: &Atom, subst: &Subst) -> bool {
        match v {
            Atom::Concept { lit, t } => g.concepts[g.find(subst.lookup(*t))].contains(lit),
            Atom::Role { r, s, t } => {
                g.edges
                    .contains(&(*r, g.find(subst.lookup(*s)), g.find(subst.lookup(*t))))
            }
            Atom::Exists { r, fil, t } => {
                let s = g.find(subst.lookup(*t));
                g.exobl[s].contains(&(*r, *fil))
                    || g.out_edges[s]
                        .iter()
                        .any(|&(rr, u)| rr == *r && g.concepts[u].contains(fil))
            }
            // Already satisfied iff the two terms denote the same (merged) node.
            Atom::Eq { s, t } => g.find(subst.lookup(*s)) == g.find(subst.lookup(*t)),
        }
    }

    fn add_head_atom(&self, g: &mut Graph, v: &Atom, subst: &Subst) {
        match v {
            Atom::Concept { lit, t } => {
                let n = g.find(subst.lookup(*t));
                g.add_concept(n, *lit);
            }
            Atom::Role { r, s, t } => {
                let (a, b) = (g.find(subst.lookup(*s)), g.find(subst.lookup(*t)));
                g.add_edge(*r, a, b);
            }
            Atom::Exists { r, fil, t } => {
                let n = g.find(subst.lookup(*t));
                g.add_exobl(n, *r, *fil);
            }
            // Discharge ≈ by merging the two nodes (the ≤-rule / functional role).
            Atom::Eq { s, t } => {
                g.merge(subst.lookup(*s), subst.lookup(*t));
            }
        }
    }

    /// All substitutions binding every clause variable to a node such that every
    /// body atom holds. Unguarded variables (the center `x` when not bound by the
    /// body) range over all nodes. Prefer `match_visit` when you do not need the
    /// whole set materialised.
    fn match_body(&self, cl: &Clause, g: &Graph) -> Vec<Subst> {
        let mut out = Vec::new();
        self.match_visit(cl, g, &mut |s| {
            out.push(s.clone());
            true
        });
        out
    }

    /// Visit each body-satisfying substitution, calling `f`. Returning `false`
    /// from `f` stops the search early; `match_visit` then returns `false`.
    fn match_visit(&self, cl: &Clause, g: &Graph, f: &mut dyn FnMut(&Subst) -> bool) -> bool {
        let vars = clause_vars(cl);
        self.match_rec(cl, g, 0, &mut Subst::new(), &vars, f)
    }

    /// Recursive body matcher. Returns `false` iff `f` requested an early stop
    /// (so callers unwind without exploring the remaining branches).
    fn match_rec(
        &self,
        cl: &Clause,
        g: &Graph,
        i: usize,
        subst: &mut Subst,
        vars: &[Var],
        f: &mut dyn FnMut(&Subst) -> bool,
    ) -> bool {
        if i == cl.body.len() {
            // bind any still-unbound vars (e.g. unguarded center x) over all nodes
            if let Some(&v) = vars.iter().find(|v| !subst.contains(**v)) {
                for nd in 0..g.n() {
                    subst.insert(v, nd);
                    let cont = self.match_rec(cl, g, i, subst, vars, f);
                    subst.remove(v);
                    if !cont {
                        return false;
                    }
                }
            } else if !f(subst) {
                return false;
            }
            return true;
        }
        match &cl.body[i] {
            Atom::Concept { lit, t } => {
                if let Some(nd) = subst.get(*t) {
                    if g.concepts[nd].contains(lit) && !self.match_rec(cl, g, i + 1, subst, vars, f)
                    {
                        return false;
                    }
                } else {
                    for nd in 0..g.n() {
                        if g.concepts[nd].contains(lit) {
                            subst.insert(*t, nd);
                            let cont = self.match_rec(cl, g, i + 1, subst, vars, f);
                            subst.remove(*t);
                            if !cont {
                                return false;
                            }
                        }
                    }
                }
            }
            Atom::Role { r, s, t } => {
                if let Some(bs) = subst.get(*s) {
                    // Source already bound: scan only `bs`'s out-edges (each entry
                    // `(er, et)` is the edge `(er, bs, et)`), not all edges.
                    for &(er, et) in &g.out_edges[bs] {
                        if er != *r {
                            continue;
                        }
                        if let Some(bt) = subst.get(*t) {
                            if bt != et {
                                continue;
                            }
                        }
                        let ins_t = !subst.contains(*t);
                        subst.insert(*t, et);
                        let cont = self.match_rec(cl, g, i + 1, subst, vars, f);
                        if ins_t {
                            subst.remove(*t);
                        }
                        if !cont {
                            return false;
                        }
                    }
                } else {
                    // Source unbound: must consider every edge.
                    for &(er, es, et) in &g.edges {
                        if er != *r {
                            continue;
                        }
                        if let Some(bt) = subst.get(*t) {
                            if bt != et {
                                continue;
                            }
                        }
                        let ins_t = !subst.contains(*t);
                        subst.insert(*s, es);
                        subst.insert(*t, et);
                        let cont = self.match_rec(cl, g, i + 1, subst, vars, f);
                        subst.remove(*s);
                        if ins_t {
                            subst.remove(*t);
                        }
                        if !cont {
                            return false;
                        }
                    }
                }
            }
            Atom::Exists { .. } => {
                // ∃ atoms do not occur in bodies; skip.
                return self.match_rec(cl, g, i + 1, subst, vars, f);
            }
            Atom::Eq { s, t } => {
                // ≈ atoms are not emitted into bodies; when both ends are bound
                // (defensive), the atom holds iff they denote the same node.
                match (subst.get(*s), subst.get(*t)) {
                    (Some(a), Some(b)) if g.find(a) != g.find(b) => {}
                    _ => return self.match_rec(cl, g, i + 1, subst, vars, f),
                }
            }
        }
        true
    }

    // ---------------- incremental (semi-naive) saturation -----------------
    // The non-careful path (ALCH/SH, no merges) re-derived the whole Horn
    // closure from scratch on every `expand` call, even though each call only
    // adds one disjunct on top of an already-saturated parent. These methods
    // instead drive saturation from a worklist of newly-derived facts, firing
    // only the clauses each fact can trigger (via `lit_index` / `role_index`)
    // and binding the triggering variable so the matcher need not rescan all
    // nodes for it.

    /// Match `cl`'s body starting from a partial substitution `seed`.
    fn match_visit_from(
        &self,
        cl: &Clause,
        g: &Graph,
        seed: Subst,
        f: &mut dyn FnMut(&Subst) -> bool,
    ) -> bool {
        let vars = clause_vars(cl);
        let mut subst = seed;
        self.match_rec(cl, g, 0, &mut subst, &vars, f)
    }

    /// Union of the dependency sets of the facts a clause body matches under
    /// `subst` (the dependencies a head derived from this match inherits).
    fn body_dep(&self, g: &Graph, cl: &Clause, subst: &Subst) -> DepSet {
        let mut d = DepSet::new();
        for a in &cl.body {
            match a {
                Atom::Concept { lit, t } => {
                    let n = g.find(subst.lookup(*t));
                    if let Some(fd) = g.cdep[n].get(lit) {
                        d.union_with(fd);
                    }
                }
                Atom::Role { r, s, t } => {
                    let key = (*r, g.find(subst.lookup(*s)), g.find(subst.lookup(*t)));
                    if let Some(fd) = g.edep.get(&key) {
                        d.union_with(fd);
                    }
                }
                _ => {}
            }
        }
        d
    }

    /// Resolve a head atom under `subst` to the fact it asserts, tagged with `dep`.
    fn resolve_head(&self, g: &Graph, v: &Atom, subst: &Subst, dep: DepSet) -> PendHead {
        match v {
            Atom::Concept { lit, t } => PendHead::Concept(g.find(subst.lookup(*t)), *lit, dep),
            Atom::Role { r, s, t } => {
                PendHead::Edge(*r, g.find(subst.lookup(*s)), g.find(subst.lookup(*t)), dep)
            }
            Atom::Exists { r, fil, t } => PendHead::Exobl(g.find(subst.lookup(*t)), *r, *fil, dep),
            Atom::Eq { .. } => unreachable!("Eq head only occurs on the careful path"),
        }
    }

    /// Fire one non-disjunctive clause from a seed binding, collecting head facts
    /// not already present into `pending` (applied later, since the matcher holds
    /// `g` immutably). Returns `Some(conflict)` on an empty-head clause; the
    /// conflict is the dependency set of the matched body.
    fn fire_clause(
        &self,
        info: &ClauseInfo,
        g: &Graph,
        seed: Subst,
        pending: &mut Vec<PendHead>,
    ) -> Option<DepSet> {
        let mut conflict = None;
        self.match_visit_from(&info.cl, g, seed, &mut |subst| {
            let bd = self.body_dep(g, &info.cl, subst);
            if info.cl.head.is_empty() {
                conflict = Some(bd);
                return false;
            }
            let v = &info.cl.head[0];
            if !self.head_atom_present(g, v, subst) {
                pending.push(self.resolve_head(g, v, subst, bd));
            }
            true
        });
        conflict
    }

    /// Apply collected head facts, recording each fact's dependency set and
    /// enqueuing newly-added concepts/edges. Returns `Some(conflict)` if a concept
    /// meets its complement on a node (the conflict is the union of the two
    /// facts' dependency sets).
    fn apply_pending(
        &self,
        g: &mut Graph,
        pending: Vec<PendHead>,
        queue: &mut VecDeque<NewFact>,
    ) -> Option<DepSet> {
        for p in pending {
            match p {
                PendHead::Concept(n, lit, dep) => {
                    if g.add_concept(n, lit) {
                        if let Some(cd) = g.cdep[n].get(&lit.complement()) {
                            let mut c = dep.clone();
                            c.union_with(cd);
                            g.cdep[n].insert(lit, dep);
                            return Some(c);
                        }
                        g.cdep[n].insert(lit, dep);
                        queue.push_back(NewFact::Concept(n, lit));
                    }
                }
                PendHead::Edge(r, s, t, dep) => {
                    if g.add_edge(r, s, t) {
                        g.edep.insert((r, s, t), dep);
                        queue.push_back(NewFact::Edge(r, s, t));
                    }
                }
                PendHead::Exobl(n, r, fil, dep) => {
                    if g.add_exobl(n, r, fil) {
                        g.xdep[n].insert((r, fil), dep);
                    }
                }
            }
        }
        None
    }

    /// Fire the `node_triggered` clauses (e.g. `⊤ ⊑ C`) for a freshly created
    /// node `n`. Returns `Some(conflict)` on a clash.
    fn seed_node(&self, g: &mut Graph, n: Node, queue: &mut VecDeque<NewFact>) -> Option<DepSet> {
        let mut pending = Vec::new();
        for &(ci, var) in &self.node_triggered {
            let mut seed = Subst::new();
            seed.insert(var, n);
            if let Some(c) = self.fire_clause(&self.clauses[ci], g, seed, &mut pending) {
                return Some(c);
            }
        }
        self.apply_pending(g, pending, queue)
    }

    /// Drain the worklist, firing the Horn clauses each new fact can trigger to a
    /// fixpoint. Returns `Some(conflict)` on a clash.
    fn horn_inc(&self, g: &mut Graph, queue: &mut VecDeque<NewFact>) -> Option<DepSet> {
        while let Some(f) = queue.pop_front() {
            let mut pending = Vec::new();
            match f {
                NewFact::Concept(node, lit) => {
                    if let Some(es) = self.lit_index.get(&lit) {
                        for &(ci, var) in es {
                            let mut seed = Subst::new();
                            seed.insert(var, node);
                            if let Some(c) =
                                self.fire_clause(&self.clauses[ci], g, seed, &mut pending)
                            {
                                return Some(c);
                            }
                        }
                    }
                }
                NewFact::Edge(r, s, t) => {
                    if let Some(es) = self.role_index.get(&r) {
                        for &(ci, sv, tv) in es {
                            let mut seed = Subst::new();
                            seed.insert(sv, s);
                            seed.insert(tv, t);
                            if let Some(c) =
                                self.fire_clause(&self.clauses[ci], g, seed, &mut pending)
                            {
                                return Some(c);
                            }
                        }
                    }
                }
            }
            if let Some(c) = self.apply_pending(g, pending, queue) {
                return Some(c);
            }
        }
        None
    }

    /// Incremental analogue of `saturate` for the non-careful path: Horn closure
    /// from the worklist, then the (batched) ∃ round, repeated to a fixpoint.
    /// Returns `Some(conflict)` on a clash. ∃ successors inherit the obligation's
    /// dependency set.
    fn saturate_inc(&self, g: &mut Graph, mut queue: VecDeque<NewFact>) -> Option<DepSet> {
        let prog = std::env::var_os("KM_TAB_STATS").is_some();
        let mut inc_round = 0u64;
        loop {
            inc_round += 1;
            if prog {
                eprintln!(
                    "KM_TAB_STATS saturate_inc round={} nodes={} queue={} (entering horn_inc)",
                    inc_round,
                    g.n(),
                    queue.len()
                );
            }
            if let Some(c) = self.horn_inc(g, &mut queue) {
                return Some(c);
            }
            if prog {
                eprintln!(
                    "KM_TAB_STATS saturate_inc round={} horn_inc DONE nodes={}",
                    inc_round,
                    g.n()
                );
            }
            // Decision-on-demand: propagate forced disjunction survivors before any
            // ∃ round or branch. A unit survivor is a deterministic consequence, so
            // it must be drained by `horn_inc` (and may unit-propagate further)
            // before we generate successors — loop back when it changes the graph.
            if self.dod {
                match self.unit_prop_round(g, &mut queue) {
                    Err(c) => return Some(c),
                    Ok(true) => continue,
                    Ok(false) => {}
                }
            }
            let mut ex_changed = false;
            for s in 0..g.n() {
                if self.node_blocked(g, s) {
                    continue;
                }
                let obls: Vec<(R, CLit)> = g.exobl[s].iter().copied().collect();
                for (r, fil) in obls {
                    let satisfied = g.out_edges[s]
                        .iter()
                        .any(|&(rr, t)| rr == r && g.concepts[t].contains(&fil));
                    if !satisfied {
                        let odep = g.xdep[s].get(&(r, fil)).cloned().unwrap_or_default();
                        let t = g.new_node(Some(s), true);
                        if let Some(c) = self.seed_node(g, t, &mut queue) {
                            return Some(c);
                        }
                        g.add_edge(r, s, t);
                        g.edep.insert((r, s, t), odep.clone());
                        queue.push_back(NewFact::Edge(r, s, t));
                        if g.add_concept(t, fil) {
                            if let Some(cd) = g.cdep[t].get(&fil.complement()) {
                                let mut c = odep.clone();
                                c.union_with(cd);
                                g.cdep[t].insert(fil, odep);
                                return Some(c);
                            }
                            g.cdep[t].insert(fil, odep);
                            queue.push_back(NewFact::Concept(t, fil));
                        }
                        ex_changed = true;
                    }
                }
            }
            if !ex_changed {
                return None;
            }
        }
    }

    /// Decision-on-demand unit propagation (KM_HT_DOD). One semi-naive scan of the
    /// fired disjunctions, classifying each head disjunct against the target node's
    /// current label:
    ///   * *satisfied* (a disjunct already present) ⇒ the disjunction is true, skip;
    ///   * *refuted* (a Concept disjunct whose complement is present) ⇒ that branch
    ///     is dead, fold its dep into the running refute-dep;
    ///   * *open* (anything else; non-Concept disjuncts are never refutable here) ⇒
    ///     a still-possible branch.
    /// If a fired disjunction has **no** open disjunct it clashes now — return the
    /// conflict (body dep ∪ the refuting literals' deps). If it has **exactly one**
    /// open disjunct, that survivor is *forced* (resolution against the refuted
    /// ones), so assert it deterministically with dep = body dep ∪ refute-dep — no
    /// branch. Disjunctions with ≥2 open disjuncts are left for the branch point.
    ///
    /// Returns `Ok(true)` if any survivor was asserted (caller re-saturates),
    /// `Ok(false)` at a fixpoint, `Err(conflict)` on a clash. The dep bookkeeping
    /// matches `apply_pending`/`fire_clause`, so backjumping and no-good learning
    /// stay sound: a forced survivor depends on exactly the decisions that refuted
    /// its siblings plus the body's, never on a branch level.
    fn unit_prop_round(
        &self,
        g: &mut Graph,
        queue: &mut VecDeque<NewFact>,
    ) -> Result<bool, DepSet> {
        let mut pending: Vec<PendHead> = Vec::new();
        let mut conflict: Option<DepSet> = None;
        for info in &self.clauses {
            if !info.disjunctive || !self.matchable(info, g) {
                continue;
            }
            self.match_visit(&info.cl, g, &mut |subst| {
                let mut satisfied = false;
                let mut open: Option<usize> = None;
                let mut multi_open = false;
                let mut refute_dep = DepSet::new();
                for (i, v) in info.cl.head.iter().enumerate() {
                    if self.head_atom_present(g, v, subst) {
                        satisfied = true;
                        break;
                    }
                    match v {
                        Atom::Concept { lit, t } => {
                            let n = g.find(subst.lookup(*t));
                            if let Some(cd) = g.cdep[n].get(&lit.complement()) {
                                refute_dep.union_with(cd); // refuted
                            } else if open.is_none() {
                                open = Some(i);
                            } else {
                                multi_open = true;
                            }
                        }
                        // Edge / Exobl / Eq disjuncts are never refutable here, so
                        // they are always open.
                        _ => {
                            if open.is_none() {
                                open = Some(i);
                            } else {
                                multi_open = true;
                            }
                        }
                    }
                }
                if satisfied || multi_open {
                    return true; // already true, or a genuine branch — defer
                }
                let mut dep = self.body_dep(g, &info.cl, subst);
                dep.union_with(&refute_dep);
                match open {
                    // All disjuncts refuted: the disjunction cannot hold.
                    None => {
                        conflict = Some(dep);
                        false // stop the scan
                    }
                    // Exactly one open disjunct: it is forced. Assert it.
                    Some(i) => {
                        pending.push(self.resolve_head(g, &info.cl.head[i], subst, dep));
                        true
                    }
                }
            });
            if conflict.is_some() {
                break;
            }
        }
        if let Some(c) = conflict {
            stat_unit(0, true);
            return Err(c);
        }
        let changed = !pending.is_empty();
        stat_unit(pending.len() as u64, false);
        if let Some(c) = self.apply_pending(g, pending, queue) {
            return Err(c);
        }
        Ok(changed)
    }

    /// Incremental analogue of the non-careful `expand`, with dependency-directed
    /// backjumping. `dl` is the current decision level; the disjunction picked
    /// here introduces level `dl+1`. When a disjunct's subtree clashes with a
    /// conflict that does *not* mention `dl+1`, the choice is irrelevant, so the
    /// whole disjunction is abandoned and the conflict propagates up (skipping
    /// untried siblings and any irrelevant intervening decisions).
    ///
    /// Direction C — no-good (conflict-clause) learning (`st`): backjumping
    /// throws the clash reason away once it unwinds; with live disjunctions the
    /// same combination is then re-derived in countless sibling subtrees
    /// (measured: ore_ont_5303's first model build does 75k+ branch tries). `st`
    /// caches each clash's decision set as a learned no-good and prunes any later
    /// branch that re-asserts it. Sound on the non-careful path: it has no merges
    /// or inverse navigation, so a successor's node id is stable across sibling
    /// branches (`rollback` resets the node counter), and a learned no-good — a
    /// set of `(node, concept-literal)` decisions that provably clash — stays
    /// valid for any sibling that reaches the same decisions. (Disabled via
    /// `KM_TAB_NOLEARN` for A/B; inert on the careful path, which tracks no deps.)
    fn expand_inc(
        &self,
        g: &mut Graph,
        queue: VecDeque<NewFact>,
        dl: u32,
        st: &mut SearchState,
    ) -> Outcome {
        stat_expand();
        if let Some(c) = self.saturate_inc(g, queue) {
            return Outcome::Conflict(c);
        }
        if let Some((head, subst, bdep)) = self.find_disjunctive(g) {
            // UNSATCACHE query: if the disjunction's node already carries a label
            // proven intrinsically unsatisfiable, clash now without branching.
            if self.unsatcache {
                if let Some(node) = self.disj_node(g, &head, &subst) {
                    if let Some(d) = st.unsat_hit(&g.concepts[node], &g.cdep[node]) {
                        return Outcome::Conflict(d);
                    }
                }
            }
            let level = dl + 1;
            let mut accum = DepSet::new();
            for v in &head {
                // DOD: a refuted disjunct (Concept whose complement is present)
                // would clash on the spot. Skip it, but fold its refutation dep
                // into `accum` so the disjunction-failed conflict still records
                // exactly why this branch was dead (keeps backjumping/learning
                // sound). After unit propagation the surviving disjunction has
                // ≥2 open disjuncts, so at least two real branches remain.
                if self.dod {
                    if let Atom::Concept { lit, t } = v {
                        let n = g.find(subst.lookup(*t));
                        if let Some(cd) = g.cdep[n].get(&lit.complement()) {
                            accum.union_with(cd);
                            continue;
                        }
                    }
                }
                stat_try();
                st.n_try += 1;
                if st.stats && st.n_try % 20000 == 0 {
                    eprintln!(
                        "KM_TAB_STATS nogood heartbeat tries={} learned={} hits={} skips={} dl={}",
                        st.n_try, st.n_learn, st.n_hit, st.n_skip, dl
                    );
                }
                let cp = g.checkpoint();
                let mut ddep = bdep.clone();
                ddep.insert(level);
                let pend = self.resolve_head(g, v, &subst, ddep);
                // Decision literal for learning (Concept disjuncts, non-careful).
                let dlit = if st.on {
                    match &pend {
                        PendHead::Concept(n, l, _) => Some((*n, *l)),
                        _ => None,
                    }
                } else {
                    None
                };
                let conflict = if let Some(d) = dlit {
                    // No-good pruning: if asserting `d` completes a learned
                    // no-good, this branch is known to clash — skip its subtree.
                    if let Some(c) = st.check(d, level) {
                        st.n_hit += 1;
                        if st.stats && st.n_hit % 20000 == 0 {
                            eprintln!(
                                "KM_TAB_STATS nogood hits={} learned={} skips={}",
                                st.n_hit, st.n_learn, st.n_skip
                            );
                        }
                        Some(c)
                    } else {
                        st.push(level, Some(d));
                        let mut child: VecDeque<NewFact> = VecDeque::new();
                        let r = match self.apply_pending(g, vec![pend], &mut child) {
                            Some(c) => Some(c),
                            None => match self.expand_inc(g, child, level, st) {
                                // Model found: leave `g` intact for the caller.
                                Outcome::Sat => return Outcome::Sat,
                                Outcome::Conflict(c) => Some(c),
                            },
                        };
                        st.pop(level, Some(d));
                        r
                    }
                } else {
                    st.push(level, None);
                    let mut child: VecDeque<NewFact> = VecDeque::new();
                    let r = match self.apply_pending(g, vec![pend], &mut child) {
                        Some(c) => Some(c),
                        None => match self.expand_inc(g, child, level, st) {
                            Outcome::Sat => return Outcome::Sat,
                            Outcome::Conflict(c) => Some(c),
                        },
                    };
                    st.pop(level, None);
                    r
                };
                g.rollback_to(cp);
                stat_backtrack();
                let mut c = conflict.unwrap();
                if !c.contains(level) {
                    // This disjunction choice was irrelevant to the clash: every
                    // sibling would clash the same way. Backjump.
                    return Outcome::Conflict(c);
                }
                c.remove(level);
                accum.union_with(&c);
            }
            // Every disjunct failed at this level: the disjunction itself cannot
            // be satisfied given the earlier decisions in `accum` and the reasons
            // this disjunction fired (`bdep`).
            // UNSATCACHE populate: if the clash depended on NO other decision
            // (`accum` empty before folding in the body deps) and the disjunction
            // fired context-free (`bdep` empty), then this node's label is
            // intrinsically unsatisfiable — cache it for superset reuse.
            let intrinsic = self.unsatcache && accum.v.is_empty() && bdep.v.is_empty();
            accum.union_with(&bdep);
            if intrinsic {
                if let Some(node) = self.disj_node(g, &head, &subst) {
                    st.cache_unsat(&g.concepts[node]);
                }
            }
            // Learn the no-good: the decisions (at the levels in `accum`) that
            // together force this clash. Reused to prune sibling/cousin branches.
            if st.on {
                st.learn(&accum);
            }
            return Outcome::Conflict(accum);
        }
        Outcome::Sat
    }
}

/// Direction C no-good (conflict-clause) learning state for the non-careful
/// incremental DFS, rebuilt per `find_model`. A *decision* is a Concept disjunct
/// choice `(node, literal)`; a *no-good* is a set of decisions that provably
/// clash. Node ids are stable across sibling branches within one `find_model`
/// (rollback resets the node counter), so a no-good learned in one subtree
/// soundly prunes any sibling that reasserts the same combination.
struct SearchState {
    on: bool,
    /// level → the decision literal made at that level on the current path.
    level_lit: Vec<Option<(Node, CLit)>>,
    /// decision literal → the level at which it sits on the current path.
    lit_level: HashMap<(Node, CLit), u32>,
    /// the Concept decisions currently on the path (for subset checks).
    path_set: HashSet<(Node, CLit)>,
    /// learned no-goods (each a sorted, deduped decision set).
    learned: Vec<Vec<(Node, CLit)>>,
    /// literal → indices of learned no-goods containing it (watch index).
    by_lit: HashMap<(Node, CLit), Vec<usize>>,
    cap: usize,
    /// KM_TAB_MIN: drop a freshly learned no-good if an already-learned one is a
    /// subset of it (the shorter no-good is strictly stronger and fires earlier),
    /// keeping the no-good DB minimal so `check` prunes harder and the search
    /// converges instead of drowning in redundant weak no-goods.
    minimize: bool,
    n_learn: u64,
    n_hit: u64,
    n_skip: u64,
    n_try: u64,
    stats: bool,
    /// KM_HT_UNSATCACHE: node concept-labels proven *intrinsically* unsatisfiable
    /// (sorted, deduped). Inverse-free ⇒ a node's label alone decides its
    /// satisfiability, so any later node whose label is a superset clashes at once.
    unsat_on: bool,
    unsat_labels: Vec<Vec<CLit>>,
    n_unsat_hit: u64,
}

impl SearchState {
    fn new() -> Self {
        let on = std::env::var_os("KM_TAB_NOLEARN").is_none();
        let cap = std::env::var("KM_TAB_LEARN_CAP")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(500_000);
        SearchState {
            on,
            level_lit: Vec::new(),
            lit_level: HashMap::new(),
            path_set: HashSet::new(),
            learned: Vec::new(),
            by_lit: HashMap::new(),
            cap,
            minimize: std::env::var_os("KM_TAB_MIN").is_some(),
            n_learn: 0,
            n_hit: 0,
            n_skip: 0,
            n_try: 0,
            stats: std::env::var_os("KM_TAB_STATS").is_some(),
            unsat_on: std::env::var_os("KM_HT_UNSATCACHE").is_some(),
            unsat_labels: Vec::new(),
            n_unsat_hit: 0,
        }
    }

    /// Cache a node label proven intrinsically unsatisfiable (UNSATCACHE). Skips
    /// labels that already have a cached subset (which fires earlier and harder).
    fn cache_unsat(&mut self, concepts: &HashSet<CLit>) {
        if !self.unsat_on || self.unsat_labels.len() >= self.cap {
            return;
        }
        let mut label: Vec<CLit> = concepts.iter().copied().collect();
        label.sort_unstable();
        if self
            .unsat_labels
            .iter()
            .any(|u| u.iter().all(|x| label.binary_search(x).is_ok()))
        {
            return;
        }
        self.unsat_labels.push(label);
    }

    /// If the node's label is a superset of a cached unsat label, return the
    /// conflict — the union of the dependency sets of the literals that form that
    /// label on this node (so backjumping targets the decisions responsible).
    fn unsat_hit(
        &mut self,
        concepts: &HashSet<CLit>,
        cdep: &HashMap<CLit, DepSet>,
    ) -> Option<DepSet> {
        if !self.unsat_on || self.unsat_labels.is_empty() {
            return None;
        }
        for u in &self.unsat_labels {
            if u.iter().all(|l| concepts.contains(l)) {
                let mut d = DepSet::new();
                for l in u {
                    if let Some(cd) = cdep.get(l) {
                        d.union_with(cd);
                    }
                }
                self.n_unsat_hit += 1;
                return Some(d);
            }
        }
        None
    }

    fn push(&mut self, level: u32, d: Option<(Node, CLit)>) {
        if self.level_lit.len() <= level as usize {
            self.level_lit.resize(level as usize + 1, None);
        }
        self.level_lit[level as usize] = d;
        if let Some(l) = d {
            self.lit_level.insert(l, level);
            self.path_set.insert(l);
        }
    }

    fn pop(&mut self, level: u32, d: Option<(Node, CLit)>) {
        if let Some(l) = d {
            self.lit_level.remove(&l);
            self.path_set.remove(&l);
        }
        if (level as usize) < self.level_lit.len() {
            self.level_lit[level as usize] = None;
        }
    }

    /// If asserting decision `d` at `level` completes a learned no-good (all its
    /// other literals are already on the path), return the conflict `DepSet` —
    /// the levels of that no-good's decisions — so the branch clashes without
    /// exploring its subtree.
    fn check(&self, d: (Node, CLit), level: u32) -> Option<DepSet> {
        let idxs = self.by_lit.get(&d)?;
        for &i in idxs {
            let ng = &self.learned[i];
            if ng.iter().all(|l| *l == d || self.path_set.contains(l)) {
                let mut ds = DepSet::new();
                for l in ng {
                    if *l == d {
                        ds.insert(level);
                    } else if let Some(&lv) = self.lit_level.get(l) {
                        ds.insert(lv);
                    }
                }
                return Some(ds);
            }
        }
        None
    }

    /// Learn the no-good = the decision literals at the levels in `accum`. Skipped
    /// if any of those levels was a non-Concept decision (no stable literal to
    /// record) — sound, just learns less.
    fn learn(&mut self, accum: &DepSet) {
        if self.learned.len() >= self.cap || accum.v.is_empty() {
            return;
        }
        let mut ng: Vec<(Node, CLit)> = Vec::with_capacity(accum.v.len());
        for &lv in &accum.v {
            match self.level_lit.get(lv as usize).copied().flatten() {
                Some(l) => ng.push(l),
                None => {
                    self.n_skip += 1; // non-Concept decision at this level: don't learn
                    return;
                }
            }
        }
        ng.sort_unstable();
        ng.dedup();
        if ng.is_empty() {
            return;
        }
        // Forward subsumption: if a shorter learned no-good is already a subset of
        // `ng`, `ng` is redundant (the subset fires whenever `ng` would, sooner).
        // Candidates share at least one literal with `ng`, so scan only the watch
        // lists of `ng`'s literals.
        if self.minimize && !self.learned.is_empty() {
            let ngset: HashSet<(Node, CLit)> = ng.iter().copied().collect();
            let mut seen: HashSet<usize> = HashSet::new();
            for l in &ng {
                if let Some(idxs) = self.by_lit.get(l) {
                    for &i in idxs {
                        if !seen.insert(i) {
                            continue;
                        }
                        let other = &self.learned[i];
                        if other.len() <= ng.len() && other.iter().all(|x| ngset.contains(x)) {
                            self.n_skip += 1;
                            return;
                        }
                    }
                }
            }
        }
        self.n_learn += 1;
        let idx = self.learned.len();
        for l in &ng {
            self.by_lit.entry(*l).or_default().push(idx);
        }
        self.learned.push(ng);
    }
}

/// A newly-derived fact on the worklist that drives incremental saturation.
enum NewFact {
    Concept(Node, CLit),
    Edge(R, Node, Node),
}

/// A head atom resolved to concrete nodes and tagged with its dependency set,
/// collected during a match (when `g` is borrowed immutably) and applied after.
enum PendHead {
    Concept(Node, CLit, DepSet),
    Edge(R, Node, Node, DepSet),
    Exobl(Node, R, CLit, DepSet),
}

impl Tableau {
    /// Classify the named concepts. Returns `(consistent, unsatisfiable, subs)`:
    /// `consistent` = the ontology has a model; `unsatisfiable` = named concepts
    /// `A` with `A ⊑ ⊥`; `subs` = atomic subsumptions `A ⊑ B` (B ≠ A, both named).
    /// `A ⊑ B` iff `{A, ¬B}` has no model; `A` unsat iff `{A}` has no model.
    ///
    /// Model-based candidate pruning: a subsumer `B` of `A` holds in *every* model
    /// of `A`, hence in the root label of any single model `M_A`. So we build one
    /// model of `{A}` and only consider the named `B` present in `M_A`'s root,
    /// instead of all `n` concepts.
    ///
    /// Told-subsumer pruning (a CB-style hybrid, internal): on the dependency-
    /// tracking (non-careful) path, a root subsumer `B` derived with an *empty*
    /// dependency set was derived deterministically — no disjunction choice — so
    /// it holds in every model of `A` and `A ⊑ B` is definite. Those need no
    /// `{A, ¬B}` confirmation test; only choice-dependent candidates do. (On the
    /// careful path no dependencies are tracked, so every candidate is confirmed,
    /// exactly as before.)
    pub fn classify(&self, named: &[C]) -> (bool, Vec<C>, Vec<(C, C)>) {
        // Label-caching fast path (global caching) for the non-careful ALCH
        // fragment, when every clause fits the recognised shapes. Same answers as
        // the search-based `classify`, decided by caching instead of DFS.
        if std::env::var_os("KM_TAB_CACHE").is_some() && !self.careful() {
            if let Some(prog) = self.build_cprog() {
                return self.classify_cached(named, &prog);
            }
        }
        if std::env::var_os("KM_TAB_STATS").is_some() {
            eprintln!(
                "KM_TAB_STATS classify START: {} named, checking consistent([])",
                named.len()
            );
        }
        let consistent = self.consistent(&[]);
        if std::env::var_os("KM_TAB_STATS").is_some() {
            eprintln!("KM_TAB_STATS classify: consistent([])={}", consistent);
        }
        if !consistent {
            // everything is unsatisfiable; report all named as unsat.
            return (false, named.to_vec(), Vec::new());
        }
        // ---- P4: (un)satisfiability cache over root labels (KM_HT_CACHE) ----
        // Konclude keys SAT verdicts by a node-label signature and reuses them
        // across the whole classification: an UNSAT label makes every superset
        // unsat; a SAT label makes every subset sat. Sound — a model of a larger
        // constraint set satisfies any subset of it, and adding constraints to an
        // unsatisfiable set keeps it unsatisfiable. Off ⇒ no caching (default).
        struct SatCache {
            on: bool,
            exact: HashMap<Vec<CLit>, bool>,
            unsat: Vec<Vec<CLit>>, // sorted unsat cores (superset ⇒ unsat)
            sat: Vec<Vec<CLit>>,   // sorted sat labels (subset ⇒ sat)
            hits: u64,
        }
        // `a ⊆ b` for two sorted, deduped label vectors.
        fn subset(a: &[CLit], b: &[CLit]) -> bool {
            if a.len() > b.len() {
                return false;
            }
            let mut j = 0;
            for x in a {
                while j < b.len() && &b[j] < x {
                    j += 1;
                }
                if j >= b.len() || &b[j] != x {
                    return false;
                }
                j += 1;
            }
            true
        }
        impl SatCache {
            const CAP: usize = 1 << 15;
            fn key(label: &[CLit]) -> Vec<CLit> {
                let mut k = label.to_vec();
                k.sort_unstable();
                k.dedup();
                k
            }
            fn query(&mut self, key: &[CLit]) -> Option<bool> {
                if !self.on {
                    return None;
                }
                if let Some(&v) = self.exact.get(key) {
                    self.hits += 1;
                    return Some(v);
                }
                if self.unsat.iter().any(|u| subset(u, key)) {
                    self.hits += 1;
                    return Some(false);
                }
                if self.sat.iter().any(|s| subset(key, s)) {
                    self.hits += 1;
                    return Some(true);
                }
                None
            }
            fn insert(&mut self, key: Vec<CLit>, verdict: bool) {
                if !self.on {
                    return;
                }
                if self.exact.len() < Self::CAP {
                    self.exact.insert(key.clone(), verdict);
                }
                let bucket = if verdict {
                    &mut self.sat
                } else {
                    &mut self.unsat
                };
                if bucket.len() < Self::CAP {
                    bucket.push(key);
                }
            }
        }
        let mut cache = SatCache {
            on: std::env::var_os("KM_HT_CACHE").is_some(),
            exact: HashMap::new(),
            unsat: Vec::new(),
            sat: Vec::new(),
            hits: 0,
        };

        let named_set: HashSet<C> = named.iter().copied().collect();
        let mut unsat = Vec::new();
        let mut subs = Vec::new();
        // For each satisfiable A: record deterministic subsumers directly, and
        // keep only the choice-dependent ones for the confirmation test.
        let mut cand: Vec<(C, Vec<C>)> = Vec::new();
        // P2: full named-concept root label of one model of A (used by the
        // pseudo-model refutation below). Only populated under KM_HT_PMMERGE.
        let p2 = std::env::var_os("KM_HT_PMMERGE").is_some();
        // KM_HT_ALLCAND — completeness fix: the single-model candidate pruning
        // (consider only the named B in one model M_A's root) is *incomplete* for
        // ALC+⊔ — a real subsumer B can be absent from one particular model when
        // it is forced only across a disjunction split. Testing ALL named
        // candidates (paired with complete equality blocking) restores
        // completeness, at an O(n²)-test cost. Use on the small disjunction-family
        // ontologies where soundness+completeness matters more than test count.
        let allcand = std::env::var_os("KM_HT_ALLCAND").is_some();
        let mut lab: HashMap<C, HashSet<C>> = HashMap::new();
        let prog = std::env::var_os("KM_TAB_STATS").is_some();
        for (ai, &a) in named.iter().enumerate() {
            if prog && ai % 25 == 0 {
                eprintln!(
                    "KM_TAB_STATS classify phase1 concept {}/{} subs_so_far={}",
                    ai,
                    named.len(),
                    subs.len()
                );
            }
            let key = SatCache::key(&[CLit::pos(a)]);
            if cache.query(&key) == Some(false) {
                unsat.push(a);
                continue;
            }
            match self.find_model(&[CLit::pos(a)]) {
                None => {
                    cache.insert(key, false);
                    unsat.push(a)
                }
                Some(g) => {
                    cache.insert(key, true);
                    let mut uncertain = Vec::new();
                    let mut labset = HashSet::new();
                    let mut def_set = HashSet::new();
                    for l in g.concepts[0].iter() {
                        if l.neg || !named_set.contains(&l.c) {
                            continue;
                        }
                        if l.c == a {
                            continue;
                        }
                        if p2 {
                            labset.insert(l.c);
                        }
                        let definite = matches!(g.cdep[0].get(l), Some(d) if d.v.is_empty());
                        if definite {
                            subs.push((a, l.c));
                            def_set.insert(l.c);
                        } else {
                            uncertain.push(l.c);
                        }
                    }
                    if p2 {
                        lab.insert(a, labset);
                    }
                    if allcand {
                        // Test every named concept not already a definite super of A.
                        uncertain = named
                            .iter()
                            .copied()
                            .filter(|&b| b != a && !def_set.contains(&b))
                            .collect();
                    }
                    uncertain.sort_unstable();
                    cand.push((a, uncertain));
                }
            }
        }
        let definite = subs.len();
        let total_cand: usize = cand.iter().map(|(_, s)| s.len()).sum();
        if prog {
            eprintln!(
                "KM_TAB_STATS classify phase1 DONE: definite={} candidates_to_confirm={}",
                definite, total_cand
            );
        }

        // ---- P2: KPSet classification gate (KM_HT_PMMERGE) ----
        // Build the transitive closure of the *definite* (choice-free)
        // subsumptions found in phase 1. `tc[A]` = definite supers of A;
        // `tcrev[A]` = definite subs of A. These seed the known-subsumer set and
        // are the sound channels for propagation: confirmed `A⊑B` flows DOWN to
        // definite subs of A; refuted `A⋢B` flows UP to known supers of A.
        let mut tc: HashMap<C, HashSet<C>> = HashMap::new();
        let mut tcrev: HashMap<C, HashSet<C>> = HashMap::new();
        if p2 {
            for &(a, b) in &subs {
                tc.entry(a).or_default().insert(b);
            }
            loop {
                let mut changed = false;
                let keys: Vec<C> = tc.keys().copied().collect();
                for a in keys {
                    let supers: Vec<C> = tc[&a].iter().copied().collect();
                    for b in supers {
                        if let Some(bs) = tc.get(&b).cloned() {
                            let ea = tc.entry(a).or_default();
                            for x in bs {
                                if x != a && ea.insert(x) {
                                    changed = true;
                                }
                            }
                        }
                    }
                }
                if !changed {
                    break;
                }
            }
            for (a, sup) in &tc {
                for b in sup {
                    tcrev.entry(*b).or_default().insert(*a);
                }
            }
        }
        // `pos[A]` = known supers of A (definite TC, grows with confirmations);
        // `neg[A]` = known non-supers of A.
        let mut pos = tc.clone();
        let mut neg: HashMap<C, HashSet<C>> = HashMap::new();

        let mut confirmed = 0; // real tableau tests issued
        let (mut skipped_known, mut pm_refuted, mut prop) = (0u64, 0u64, 0u64);
        for (a, sup) in &cand {
            for &b in sup {
                if p2 {
                    if pos.get(a).is_some_and(|s| s.contains(&b)) {
                        // already entailed (TC or a prior confirmation): record it
                        // without a test.
                        subs.push((*a, b));
                        skipped_known += 1;
                        continue;
                    }
                    if neg.get(a).is_some_and(|s| s.contains(&b)) {
                        skipped_known += 1;
                        continue;
                    }
                    // pseudo-model refutation: if some definite super X of b is
                    // absent from a model of A, then A⋢X, so A⋢b (else A⊑b⊑X).
                    if let (Some(la), Some(bsup)) = (lab.get(a), tc.get(&b)) {
                        if bsup.iter().any(|x| *x != b && !la.contains(x)) {
                            neg.entry(*a).or_default().insert(b);
                            for &s in pos.get(a).into_iter().flatten() {
                                neg.entry(s).or_default().insert(b);
                            }
                            pm_refuted += 1;
                            continue;
                        }
                    }
                }
                confirmed += 1;
                if prog && confirmed % 200 == 0 {
                    eprintln!(
                        "KM_TAB_STATS classify phase2 confirm {}/{}",
                        confirmed, total_cand
                    );
                }
                let key = SatCache::key(&[CLit::pos(*a), CLit::neg(b)]);
                let sat = match cache.query(&key) {
                    Some(v) => v,
                    None => {
                        let v = self.consistent(&[CLit::pos(*a), CLit::neg(b)]);
                        cache.insert(key, v);
                        v
                    }
                };
                if !sat {
                    subs.push((*a, b));
                    if p2 {
                        // confirm A⊑b: transitivity + confirm-down to definite subs.
                        let bsup = pos.get(&b).cloned().unwrap_or_default();
                        let pa = pos.entry(*a).or_default();
                        pa.insert(b);
                        pa.extend(bsup.iter().copied());
                        for &d in tcrev.get(a).into_iter().flatten() {
                            if pos.entry(d).or_default().insert(b) {
                                subs.push((d, b));
                                prop += 1;
                            }
                        }
                    }
                } else if p2 {
                    // refute A⋢b: up to known supers of A.
                    neg.entry(*a).or_default().insert(b);
                    for &s in pos.get(a).into_iter().flatten() {
                        neg.entry(s).or_default().insert(b);
                    }
                }
            }
        }
        if p2 {
            subs.sort_unstable();
            subs.dedup();
        }
        if std::env::var("KM_TAB_STATS").is_ok() {
            eprintln!(
                "KM_TAB_STATS classify: definite_subs={definite} (no test) confirm_tests={confirmed} \
                 p2_skipped_known={skipped_known} p2_pseudomodel_refuted={pm_refuted} p2_propagated={prop} \
                 cache_hits={}",
                cache.hits
            );
        }
        (consistent, unsat, subs)
    }
}

// ============== label-caching tableau (global caching, KM_TAB_CACHE) ==============
//
// The non-careful `expand_inc` builds ONE global model by DFS over a single shared
// graph: a clash deep in the tree backtracks the whole path, and no-good learning
// over `(node, literal)` decisions does not generalise across the distinct deep
// nodes (measured on ore_ont_5303: a ~1840-node model, ~8600 sequential disjunction
// decisions, ~1% no-good hit rate). The fix is to decide satisfiability per *label*
// rather than per *node*: in ALCH WITHOUT inverse roles, number restrictions, or
// nominals, a node's satisfiability depends ONLY on its concept label (no
// information flows back up the tree), so a label proven (un)satisfiable stays so
// wherever it recurs — the result caches across every node AND across every classify
// query.
//
// This is global caching (Goré–Nguyen): build the finite AND–OR graph of reachable
// labels (states shared through a cache), then take the least fixpoint of "unsat"
// (equivalently the greatest fixpoint of "sat"), which is exactly sound blocking for
// ALCH+GCI cyclic models. Entered only when `!careful()` and every clause fits the
// recognised shapes — `build_cprog` returns `None` otherwise, so the caller falls
// back to the complete `expand_inc` and soundness is never at risk. Gated by
// `KM_TAB_CACHE`; the same answers as `expand_inc`, decided by caching instead of
// search.

/// A node-local label: the concept literals seeded on the node plus the
/// node-local clauses imposed on it by its parent's universals (`∀r.(…)`), each
/// `(body ⇒ head)` with head length 0 = ⊥, 1 = Horn, ≥2 = disjunction. Canonical
/// (all vectors sorted + deduped) so equal labels share one graph node.
#[derive(Clone, PartialEq, Eq, Hash)]
struct CKey {
    base: Vec<CLit>,
    imposed: Vec<(Vec<CLit>, Vec<CLit>)>,
}
impl CKey {
    fn canon(mut base: Vec<CLit>, mut imposed: Vec<(Vec<CLit>, Vec<CLit>)>) -> CKey {
        base.sort_unstable();
        base.dedup();
        for (b, h) in imposed.iter_mut() {
            b.sort_unstable();
            b.dedup();
            h.sort_unstable();
            h.dedup();
        }
        imposed.sort_unstable();
        imposed.dedup();
        CKey { base, imposed }
    }
}

/// A binary universal `xbody(x) ∧ r(x,y) ∧ ybody(y) → yhead(y)` (yhead len 0 = ⊥,
/// 1 = Horn fact/clause on the successor, ≥2 = a disjunction imposed on it).
struct Uni {
    xbody: Vec<CLit>,
    role: R,
    ybody: Vec<CLit>,
    yhead: Vec<CLit>,
}

/// The recognised ALCH program extracted from the clause set. `build_cprog`
/// returns `None` for any clause outside these shapes (⇒ fall back to the
/// complete path), so the cached checker is only ever run where it faithfully
/// reproduces the clause semantics.
struct CProg {
    node_horn: Vec<(Vec<CLit>, CLit)>,      // body(x) → head(x)
    node_clash: Vec<Vec<CLit>>,             // body(x) → ⊥
    node_disj: Vec<(Vec<CLit>, Vec<CLit>)>, // body(x) → ⊔ head(x)  (head.len ≥ 2)
    node_exists: Vec<(Vec<CLit>, R, CLit)>, // body(x) → ∃r.fil(x)
    uni: Vec<Uni>,
    domain: Vec<(R, CLit)>, // a node carrying an ∃r-obligation is a domain instance
    supers: HashMap<R, HashSet<R>>, // r → {s : r ⊑⁺ s} (proper transitive supers)
    // semi-naive Horn-closure index: a clause is (re)checked only when a body
    // literal it mentions is newly derived, instead of rescanning all clauses.
    horn_by_lit: HashMap<CLit, Vec<usize>>, // node_horn idx, keyed by each body lit
    horn_empty: Vec<CLit>,                  // heads of empty-body node_horn (⊤ ⊑ h)
    clash_by_lit: HashMap<CLit, Vec<usize>>, // node_clash idx, keyed by each body lit
    clash_empty: bool,                      // an empty-body ⊥-clause (KB ⊨ ⊥)
    // synthetic-marker metadata: marker concept id → role r of its `∀r.L`
    // disjunct. A marker disjunct asserts `∀r.L` (forbids `¬L` on r-successors);
    // when the node has no live r-obligation the disjunct is vacuous, so trying
    // it first finds a shallow model without forcing a successor chain.
    marker_role: HashMap<C, R>,
    // incremental ∃-pruning: literals whose addition can change obligations or
    // successors (see build_cprog). A DPLL step adding none can skip the check.
    trigger_lits: HashSet<CLit>,
    // build_succ index: obligation-role → applicable uni indices (role_le).
    uni_for_role: HashMap<R, Vec<usize>>,
    // Transitive roles (Konclude's epsilon self-loop in the role automaton).
    // A `∀R.C` Uni whose role is transitive self-propagates: the successor
    // inherits the ∀-obligation (the marker), so ∀R.C re-fires down the whole
    // R-chain — the clause-form of the automaton's endState→beginState epsilon
    // self-loop.  Without this, a ∀R.C Uni only fires on nodes carrying the
    // marker (the root that chose the ∀ disjunct), missing deeper generated
    // successors (ore_ont_14817's 71: ∀develops_from.¬UBERON_0000926 must
    // clash on a dev-successor reached through an anonymous chain).
    transitive: HashSet<R>,
    // upper bound on concept ids (real concepts + synthetic markers). Sizes the
    // per-concept VSIDS activity / phase-saving arrays.
    n_concepts: C,
}
impl CProg {
    /// `r0 ⊑* target` (an r0-edge is also a target-edge).
    fn role_le(&self, r0: R, target: R) -> bool {
        r0 == target || self.supers.get(&r0).is_some_and(|s| s.contains(&target))
    }
}

impl Tableau {
    /// Extract the recognised ALCH program, or `None` if any clause is outside
    /// the recognised shapes (caller must then use the complete `expand_inc`).
    fn build_cprog(&self) -> Option<CProg> {
        let mut node_horn = Vec::new();
        let mut node_clash = Vec::new();
        let mut node_disj = Vec::new();
        let mut node_exists = Vec::new();
        let mut uni = Vec::new();
        let mut domain = Vec::new();
        let mut subrole: Vec<(R, R)> = Vec::new();
        // synthetic marker concepts for universal disjuncts `∀r.L` (the
        // internalisation of `∃r.¬L ⊑ …`). Allocated past the real concept ids;
        // each carries a `Uni` that pushes `L` to its r-successors when chosen.
        let mut maxc: C = 0;
        for info in &self.clauses {
            for a in info.cl.body.iter().chain(info.cl.head.iter()) {
                match a {
                    Atom::Concept { lit, .. } => maxc = maxc.max(lit.c + 1),
                    Atom::Exists { fil, .. } => maxc = maxc.max(fil.c + 1),
                    _ => {}
                }
            }
        }
        let mut next_marker: C = maxc;
        let mut markers: HashMap<(R, CLit), C> = HashMap::new();
        let dbg = std::env::var_os("KM_TAB_STATS").is_some();
        // lazy-unfolding absorption (KM_TAB_LAZY): a node-local clause
        // `body → ⋁head` is logically `body ⊓ ⋀{¬l : l∈head, l negative} → ⋁{pos head}`.
        // Moving the negative head literals into the body GUARDS the disjunction so
        // it only fires when the guard holds (lazy), and collapses it to a Horn
        // rule (1 positive disjunct) or a clash (0) where possible — eliminating the
        // always-active covering disjunctions that drive the ∀+⊔ width explosion.
        // Sound (the clause is logically unchanged); off by default.
        let lazy = std::env::var_os("KM_TAB_LAZY").is_some();
        macro_rules! fence {
            ($ci:expr, $why:expr) => {{
                if dbg {
                    eprintln!(
                        "KM_TAB_STATS build_cprog FENCE clause#{} ({}): body={} head={}",
                        $ci,
                        $why,
                        self.clauses[$ci].cl.body.len(),
                        self.clauses[$ci].cl.head.len()
                    );
                }
                return None;
            }};
        }
        // route a node-local (body → ⋁head) clause into horn / clash / disj,
        // applying lazy absorption first when enabled.
        macro_rules! push_node_clause {
            ($body:expr, $head:expr) => {{
                let mut b: Vec<CLit> = $body;
                let mut h: Vec<CLit> = $head;
                if lazy {
                    let mut i = 0;
                    while i < h.len() {
                        if h[i].neg {
                            b.push(h[i].complement());
                            h.swap_remove(i);
                        } else {
                            i += 1;
                        }
                    }
                    b.sort_unstable();
                    b.dedup();
                }
                if h.is_empty() {
                    node_clash.push(b);
                } else if h.len() == 1 {
                    node_horn.push((b, h[0]));
                } else {
                    node_disj.push((b, h));
                }
            }};
        }

        for (ci, info) in self.clauses.iter().enumerate() {
            let cl = &info.cl;
            // ---- subrole detection: body=[Role], head=[Role], same direction ----
            if cl.body.len() == 1 && cl.head.len() == 1 {
                if let (
                    Atom::Role {
                        r: rb,
                        s: sb,
                        t: tb,
                    },
                    Atom::Role {
                        r: rh,
                        s: sh,
                        t: th,
                    },
                ) = (&cl.body[0], &cl.head[0])
                {
                    if sb == sh && tb == th {
                        subrole.push((*rb, *rh)); // r ⊑ s
                        continue;
                    }
                    fence!(ci, "inverse-role(reversed Role head)");
                }
            }
            // ---- partition the body into x-concepts, y-concepts, one role ----
            let mut bx: Vec<CLit> = Vec::new();
            let mut by: Vec<CLit> = Vec::new();
            let mut body_role: Option<R> = None;
            for a in &cl.body {
                match a {
                    Atom::Concept { lit, t } => {
                        if *t == 0 {
                            bx.push(*lit)
                        } else if *t == 1 {
                            by.push(*lit)
                        } else {
                            fence!(ci, "body concept var>=2");
                        }
                    }
                    Atom::Role { r, s, t } => {
                        if *s == 0 && *t == 1 && body_role.is_none() {
                            body_role = Some(*r)
                        } else {
                            fence!(ci, "body role not (x,y) or 2nd role");
                        }
                    }
                    _ => fence!(ci, "Eq/Exists in body"), // out of fragment
                }
            }
            // ---- existential head: body must be all-x concepts, no role ----
            if cl.head.len() == 1 {
                if let Atom::Exists { r, fil, t } = &cl.head[0] {
                    if *t == 0 && by.is_empty() && body_role.is_none() {
                        node_exists.push((bx, *r, *fil));
                        continue;
                    }
                    fence!(ci, "exists head with y-body or role-body");
                }
            }
            // ---- gather head concepts by variable ----
            let mut hx: Vec<CLit> = Vec::new();
            let mut hy: Vec<CLit> = Vec::new();
            for a in &cl.head {
                match a {
                    Atom::Concept { lit, t } => {
                        if *t == 0 {
                            hx.push(*lit)
                        } else if *t == 1 {
                            hy.push(*lit)
                        } else {
                            fence!(ci, "head concept var>=2");
                        }
                    }
                    _ => fence!(ci, "non-concept head (Role/Exists/Eq)"),
                }
            }
            match body_role {
                None => {
                    // node-local clause on x (body all-x, head all-x).
                    if !by.is_empty() || !hy.is_empty() {
                        fence!(ci, "node-local clause with y-atoms but no role");
                    }
                    push_node_clause!(bx, hx);
                }
                Some(r) => {
                    if !hx.is_empty() && !hy.is_empty() {
                        fence!(ci, "mixed-variable head (x and y)");
                    }
                    if !hx.is_empty() {
                        // head on the source x.
                        if by.is_empty() {
                            // pure `r(x,y) → D(x)` (single concept): domain.
                            if hx.len() != 1 {
                                fence!(ci, "disjunctive domain head");
                            }
                            domain.push((r, hx[0]));
                        } else {
                            // `bx(x) ∧ r(x,y) ∧ cy(y) → hx(x)` = `bx ⊓ ∃r.cy ⊑ ⊔hx`,
                            // internalised to the disjunction `hx ⊔ ∀r.¬cy` guarded
                            // by bx. The universal disjunct ∀r.¬cy is a synthetic
                            // marker concept carrying a Uni that pushes ¬cy to the
                            // node's r-successors when the marker is chosen.
                            if by.len() != 1 {
                                fence!(ci, "backward head with |Cy| != 1");
                            }
                            let neg_cy = by[0].complement();
                            let key = (r, neg_cy);
                            let m = if let Some(&m) = markers.get(&key) {
                                m
                            } else {
                                let id = next_marker;
                                next_marker += 1;
                                markers.insert(key, id);
                                uni.push(Uni {
                                    xbody: vec![CLit::pos(id)],
                                    role: r,
                                    ybody: vec![],
                                    yhead: vec![neg_cy],
                                });
                                id
                            };
                            let mut disjuncts = hx;
                            disjuncts.push(CLit::pos(m));
                            // marker is positive, so absorption can at most collapse
                            // this to `bx ⊓ ⋀¬hx → marker` (Horn), never a clash.
                            push_node_clause!(bx, disjuncts);
                        }
                    } else {
                        // universal `xbody(x) ∧ r ∧ ybody(y) → hy(y)` (hy empty = ⊥).
                        uni.push(Uni {
                            xbody: bx,
                            role: r,
                            ybody: by,
                            yhead: hy,
                        });
                    }
                }
            }
        }

        // reflexive-free transitive super-role closure from the subrole pairs.
        let mut supers: HashMap<R, HashSet<R>> = HashMap::new();
        let subs: HashSet<R> = subrole.iter().map(|&(a, _)| a).collect();
        for &r in &subs {
            let mut seen: HashSet<R> = HashSet::new();
            let mut frontier = vec![r];
            while let Some(cur) = frontier.pop() {
                for &(a, b) in &subrole {
                    if a == cur && seen.insert(b) {
                        frontier.push(b);
                    }
                }
            }
            seen.remove(&r);
            supers.insert(r, seen);
        }
        // semi-naive Horn-closure index.
        let mut horn_by_lit: HashMap<CLit, Vec<usize>> = HashMap::new();
        let mut horn_empty: Vec<CLit> = Vec::new();
        for (i, (b, h)) in node_horn.iter().enumerate() {
            if b.is_empty() {
                horn_empty.push(*h);
            } else {
                for &l in b {
                    let v = horn_by_lit.entry(l).or_default();
                    if !v.contains(&i) {
                        v.push(i);
                    }
                }
            }
        }
        let mut clash_by_lit: HashMap<CLit, Vec<usize>> = HashMap::new();
        let mut clash_empty = false;
        for (i, b) in node_clash.iter().enumerate() {
            if b.is_empty() {
                clash_empty = true;
            } else {
                for &l in b {
                    let v = clash_by_lit.entry(l).or_default();
                    if !v.contains(&i) {
                        v.push(i);
                    }
                }
            }
        }
        let marker_role: HashMap<C, R> = markers.iter().map(|(&(r, _), &m)| (m, r)).collect();
        // incremental ∃-pruning support: a literal is a *trigger* if adding it can
        // change a node's ∃-obligations (it completes a `node_exists` body) or its
        // successors (it fires a universal). The eager check can be skipped on any
        // DPLL step that added no trigger literal — successors are then unchanged.
        let mut trigger_lits: HashSet<CLit> = HashSet::new();
        for (b, _, _) in &node_exists {
            for &l in b {
                trigger_lits.insert(l);
            }
        }
        for u in &uni {
            for &l in &u.xbody {
                trigger_lits.insert(l);
            }
        }
        // per-role uni index: for each role used by an ∃-obligation, the uni
        // indices applicable over it (role_le), so build_succ skips the rest.
        let mut uni_for_role: HashMap<R, Vec<usize>> = HashMap::new();
        let obl_roles: HashSet<R> = node_exists.iter().map(|&(_, r, _)| r).collect();
        let role_le = |r0: R, target: R| -> bool {
            r0 == target || supers.get(&r0).is_some_and(|s| s.contains(&target))
        };
        for &r0 in &obl_roles {
            let v: Vec<usize> = uni
                .iter()
                .enumerate()
                .filter(|(_, u)| role_le(r0, u.role))
                .map(|(i, _)| i)
                .collect();
            uni_for_role.insert(r0, v);
        }
        // Detect transitive roles (Konclude's role-automaton epsilon self-loop).
        // Sources:
        //   (a) the raw transitivity axiom `R(x,y) ∧ R(y,z) → R(x,z)` (a
        //       2-role-body / 1-role-head clause with all three roles equal),
        //       when the frontend kept it (KM_ROLE_AUTOMATON path);
        //   (b) the standard transitivity encoding `R(x,y) ∧ P(y) → P(x)`
        //       where P is a `__trans__R__…` marker concept — the role R of
        //       such a clause is transitive.  This is the default-path encoding.
        // Either source marks R transitive; the Uni self-propagation below then
        // makes ∀R.C chase all R-successors (Konclude's endState→beginState
        // epsilon self-loop, in clause form).
        let mut transitive: HashSet<R> = HashSet::new();
        for info in &self.clauses {
            let cl = &info.cl;
            // (a) raw R∘R⊑R
            let rb: Vec<&Atom> = cl
                .body
                .iter()
                .filter(|a| matches!(a, Atom::Role { .. }))
                .collect();
            if cl.body.len() == 2
                && cl.head.len() == 1
                && matches!(cl.body[0], Atom::Role { .. })
                && matches!(cl.body[1], Atom::Role { .. })
                && matches!(cl.head[0], Atom::Role { .. })
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
                ) = (rb[0], rb[1], &cl.head[0])
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
            // (b) marker-propagation `R(x,y) ∧ P(y) → P(x)` with P a __trans__R__ marker.
            // The clause shape: body = [Role R x y, Concept P y], head = [Concept P x].
            // We cannot see concept NAMES here (Tableau carries only ids), so detect
            // the SHAPE: 2-body (1 role + 1 concept on the role target), 1-head concept
            // on the role source, where the body concept and head concept are the SAME
            // marker.  This is the transitive-propagation shape; its role is transitive.
            if cl.body.len() == 2
                && cl.head.len() == 1
                && matches!(cl.head[0], Atom::Concept { t: 0, .. })
            {
                let mut role_atom: Option<(&R, Var, Var)> = None;
                let mut body_con: Option<(&CLit, Var)> = None;
                for a in &cl.body {
                    match a {
                        Atom::Role { r, s, t } => role_atom = Some((r, *s, *t)),
                        Atom::Concept { lit, t } => body_con = Some((lit, *t)),
                        _ => {}
                    }
                }
                if let (Some((r, rs, rt)), Some((bl, bt))) = (role_atom, body_con) {
                    if let Atom::Concept { lit: hl, t: ht } = cl.head[0] {
                        if bl == &hl && bt == rt && ht == rs && rs != rt {
                            transitive.insert(*r);
                        }
                    }
                }
            }
        }
        // Apply the transitive self-loop: for each Uni whose role is transitive,
        // add the marker to its yhead so the ∀-obligation self-propagates to
        // the successor (the clause-form of Konclude's endState→beginState
        // epsilon self-loop).  Only the absorbed-marker Uni shape
        // (xbody=[marker], ybody=[], yhead=[neg_cy]) is extended; the marker is
        // the xbody's single positive concept.  The successor then carries the
        // marker, so ∀R.C re-fires on its own R-successors — the transitive
        // chase Konclude's automaton does natively.
        for u in uni.iter_mut() {
            if transitive.contains(&u.role) && u.xbody.len() == 1 && u.xbody[0].neg == false {
                let marker = u.xbody[0];
                if !u.yhead.contains(&marker) {
                    u.yhead.push(marker);
                }
            }
        }
        // Chain unfolding (Konclude generateRoleChainAutomatConcept, the
        // begin --R1--> mid --R2--> end path).  For a chain R1∘R2⊑R and a
        // ∀R.C absorbed-marker Uni (xbody=[M], role=R, yhead=[neg_cy]), a node
        // carrying M that gains an R1-successor must propagate a ∀R2.C
        // obligation onto that successor, so ∀R2.C fires on its R2-successors
        // (reaching C).  Realised by emitting a fresh marker M2 for ∀R2.C with
        // its own Uni { xbody:[M2], role:R2, yhead:[neg_cy] }, plus a Uni
        // { xbody:[M], role:R1, yhead:[M2] } that carries M2 across the R1-edge.
        // This is the clause-form of the automaton's R1∘R2 unfolding: ∀R.C ⇒
        // ∀R1.∀R2.C.  Sound (R1∘R2⊑R ⟹ ∀R.C ⊑ ∀R1.∀R2.C).  Chains detected from
        // the raw `R1∘R2⊑R` axiom (2-role-body / 1-role-head, not all-equal);
        // only present when the frontend kept them (KM_ROLE_AUTOMATON).
        let mut chains: Vec<(R, R, R)> = Vec::new();
        for info in &self.clauses {
            let cl = &info.cl;
            let rb: Vec<&Atom> = cl
                .body
                .iter()
                .filter(|a| matches!(a, Atom::Role { .. }))
                .collect();
            if cl.body.len() == 2
                && cl.head.len() == 1
                && matches!(cl.body[0], Atom::Role { .. })
                && matches!(cl.body[1], Atom::Role { .. })
                && matches!(cl.head[0], Atom::Role { .. })
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
                ) = (rb[0], rb[1], &cl.head[0])
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
        if !chains.is_empty() {
            // Collect the absorbed-marker Unis (xbody=[M], yhead=[neg_cy]) by role,
            // so each chain R1∘R2⊑R can find ∀R.C markers on R.
            // marker_by_role: R -> Vec<(M, neg_cy)>
            let mut marker_by_role: HashMap<R, Vec<(C, CLit)>> = HashMap::new();
            for u in &uni {
                if u.xbody.len() == 1 && !u.xbody[0].neg && u.ybody.is_empty() && u.yhead.len() == 1
                {
                    marker_by_role
                        .entry(u.role)
                        .or_default()
                        .push((u.xbody[0].c, u.yhead[0]));
                }
            }
            // sub-role closure (R ⊑* R'): a chain R1∘R2⊑U with U⊑*R also unfolds
            // ∀R.C (super_close(U) contains R).
            let super_close = |r: R| -> HashSet<R> {
                let mut out = HashSet::new();
                out.insert(r);
                let mut st = vec![r];
                while let Some(u) = st.pop() {
                    for &(a, b) in &subrole {
                        if a == u && out.insert(b) {
                            st.push(b);
                        }
                    }
                }
                out
            };
            let mut new_uni: Vec<Uni> = Vec::new();
            let mut chain_markers: HashMap<(R, R, CLit), C> = HashMap::new(); // (R2, M_parent, neg_cy) -> M2
            for (r1, r2, u) in &chains {
                let targets: Vec<(C, CLit)> = marker_by_role
                    .iter()
                    .filter(|(rr, _)| super_close(*u).contains(rr))
                    .flat_map(|(_, v)| v.iter().copied())
                    .collect();
                for (m_parent, neg_cy) in targets {
                    // M2 = marker for ∀R2.C, keyed by (R2, M_parent, neg_cy)
                    let m2 = *chain_markers
                        .entry((*r2, m_parent, neg_cy))
                        .or_insert_with(|| {
                            let id = next_marker;
                            next_marker += 1;
                            // ∀R2.C Uni: fires on R2-successors, pushes neg_cy.
                            new_uni.push(Uni {
                                xbody: vec![CLit::pos(id)],
                                role: *r2,
                                ybody: vec![],
                                yhead: vec![neg_cy],
                            });
                            // transitive R2: self-propagate (chain + transitivity compose)
                            if transitive.contains(r2) {
                                new_uni.push(Uni {
                                    xbody: vec![CLit::pos(id)],
                                    role: *r2,
                                    ybody: vec![],
                                    yhead: vec![CLit::pos(id)],
                                });
                            }
                            id
                        });
                    // carry M2 across the R1-edge: a node carrying M_parent, on
                    // gaining an R1-successor, imposes M2 on it.
                    new_uni.push(Uni {
                        xbody: vec![CLit::pos(m_parent)],
                        role: *r1,
                        ybody: vec![],
                        yhead: vec![CLit::pos(m2)],
                    });
                    // transitive R1: self-propagate M_parent (so the chain fires
                    // down an R1-chain too — R1∘R2⊑R composed with R1 transitive).
                    if transitive.contains(r1) {
                        new_uni.push(Uni {
                            xbody: vec![CLit::pos(m_parent)],
                            role: *r1,
                            ybody: vec![],
                            yhead: vec![CLit::pos(m_parent)],
                        });
                    }
                }
            }
            uni.extend(new_uni);
        }
        Some(CProg {
            node_horn,
            node_clash,
            node_disj,
            node_exists,
            uni,
            domain,
            supers,
            horn_by_lit,
            horn_empty,
            clash_by_lit,
            clash_empty,
            marker_role,
            trigger_lits,
            uni_for_role,
            transitive,
            n_concepts: next_marker,
        })
    }

    /// Cached single consistency check (used for direct `consistent` calls).
    fn consistent_cached(&self, root_label: &[CLit], prog: &CProg) -> bool {
        with_big_stack(|| {
            let mut run = CacheRun::new(self, prog);
            run.sat_seed(&CKey::canon(root_label.to_vec(), Vec::new()))
                .0
        })
    }

    /// Cached classification: one shared seed cache across every query (the
    /// `consistent([])`, each `{A}` satisfiability, and every `{A,¬B}`
    /// confirmation test reuse the same cache of ∃-successor satisfiability).
    /// Same output contract as `classify`.
    /// Told subsumers (KM_TAB_TOLD): subsumptions readable straight off the
    /// clause set without search — a unary Horn rule `A(x) → B(x)`
    /// (node_horn body `[A⁺]`, head `B⁺`) IS the axiom `A ⊑ B`, and a fact
    /// `⊤ → T⁺` (horn_empty) is `⊤ ⊑ T`. Transitively closed over all concepts
    /// (intermediates may be unnamed), emitting only named (a,b) pairs. These are
    /// genuine subsumptions, so the classifier can record them WITHOUT a sat-test
    /// (and they are a subset of the model-derived candidates, so the result is
    /// unchanged — just fewer confirmation queries).
    fn told_closure(&self, prog: &CProg, named: &HashSet<C>) -> HashMap<C, HashSet<C>> {
        // direct told edges A -> B.
        let mut succ: HashMap<C, Vec<C>> = HashMap::new();
        for (body, head) in &prog.node_horn {
            if body.len() == 1 && !body[0].neg && !head.neg && body[0].c != head.c {
                succ.entry(body[0].c).or_default().push(head.c);
            }
        }
        // ⊤ ⊑ T tops: a virtual edge from every concept to each top.
        let tops: Vec<C> = prog
            .horn_empty
            .iter()
            .filter(|l| !l.neg)
            .map(|l| l.c)
            .collect();
        let mut out: HashMap<C, HashSet<C>> = HashMap::new();
        for &a in named {
            let mut seen: HashSet<C> = HashSet::new();
            let mut stack = vec![a];
            while let Some(x) = stack.pop() {
                if let Some(ns) = succ.get(&x) {
                    for &b in ns {
                        if seen.insert(b) {
                            stack.push(b);
                        }
                    }
                }
            }
            let mut reach: HashSet<C> = seen.into_iter().filter(|b| named.contains(b)).collect();
            for &t in &tops {
                if t != a && named.contains(&t) {
                    reach.insert(t);
                }
            }
            reach.remove(&a);
            if !reach.is_empty() {
                out.insert(a, reach);
            }
        }
        out
    }

    fn classify_cached(&self, named: &[C], prog: &CProg) -> (bool, Vec<C>, Vec<(C, C)>) {
        with_big_stack(|| {
            let mut run = CacheRun::new(self, prog);
            if run.stats {
                eprintln!(
                    "KM_TAB_STATS cache: START prog node_horn={} node_disj={} node_exists={} uni={} domain={} clash={}",
                    prog.node_horn.len(), prog.node_disj.len(), prog.node_exists.len(),
                    prog.uni.len(), prog.domain.len(), prog.node_clash.len()
                );
            }
            // KM_TAB_ASSUME_CONSISTENT (diagnostic): skip the global consistent([])
            // sat_seed and assume the KB is consistent. Used to measure whether the
            // per-concept witness searches are tractable on the cache CDCL engine
            // when NOT bogged on the (separately-decidable) global model build. NOT
            // for production — global consistency must be proven elsewhere (Ht does).
            let consistent = if std::env::var_os("KM_TAB_ASSUME_CONSISTENT").is_some() {
                if run.stats {
                    eprintln!("KM_TAB_STATS cache: consistent([]) ASSUMED true (skipped)");
                }
                true
            } else {
                let c = run.sat_seed(&CKey::canon(Vec::new(), Vec::new())).0;
                if run.stats {
                    eprintln!(
                        "KM_TAB_STATS cache: consistent([])={} seeds={} branches={}",
                        c, run.n_seed, run.n_branch
                    );
                }
                c
            };
            if !consistent {
                return (false, named.to_vec(), Vec::new());
            }
            let named_set: HashSet<C> = named.iter().copied().collect();
            let mut unsat = Vec::new();
            let mut cand: Vec<(C, Vec<C>)> = Vec::new();
            for (ai, &a) in named.iter().enumerate() {
                if run.stats && ai % 25 == 0 {
                    eprintln!(
                        "KM_TAB_STATS cache: classify {}/{} seeds={} cache={} subs_cand={}",
                        ai,
                        named.len(),
                        run.n_seed,
                        run.cache.len(),
                        cand.iter().map(|(_, s)| s.len()).sum::<usize>()
                    );
                }
                match run.witness(&CKey::canon(vec![CLit::pos(a)], Vec::new())) {
                    None => unsat.push(a),
                    Some(cur) => {
                        // model-based candidate pruning: every subsumer of A is in
                        // this one model's completed root label; confirm with {A,¬B}.
                        let mut sup: Vec<C> = cur
                            .iter()
                            .filter(|l| !l.neg && l.c != a && named_set.contains(&l.c))
                            .map(|l| l.c)
                            .collect();
                        sup.sort_unstable();
                        sup.dedup();
                        cand.push((a, sup));
                    }
                }
            }
            let told = if std::env::var_os("KM_TAB_TOLD").is_some() {
                self.told_closure(prog, &named_set)
            } else {
                HashMap::new()
            };
            let mut n_told = 0usize;
            let mut subs = Vec::new();
            for (a, sup) in &cand {
                let told_a = told.get(a);
                for &b in sup {
                    // told subsumer: A ⊑ B is read off the clause set, no sat-test.
                    if told_a.map_or(false, |s| s.contains(&b)) {
                        subs.push((*a, b));
                        n_told += 1;
                        continue;
                    }
                    if !run
                        .sat_seed(&CKey::canon(vec![CLit::pos(*a), CLit::neg(b)], Vec::new()))
                        .0
                    {
                        subs.push((*a, b));
                    }
                }
            }
            if run.stats {
                eprintln!("KM_TAB_STATS cache: told_subsumers_used={}", n_told);
            }
            if run.stats {
                eprintln!(
                    "KM_TAB_STATS cache: DONE seeds={} cache={} unsat_named={} subs={}",
                    run.n_seed,
                    run.cache.len(),
                    unsat.len(),
                    subs.len()
                );
            }
            (consistent, unsat, subs)
        })
    }
}

/// Run `f` on a worker thread with a large stack: the recursive satisfiability
/// search can nest as deep as the model (thousands of frames on the
/// live-disjunction ontologies), which would overflow the default 8 MB stack.
fn with_big_stack<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(4 << 30)
            .spawn_scoped(s, f)
            .expect("spawn tableau worker")
            .join()
            .expect("tableau worker panicked")
    })
}

/// The two-level global-caching checker. Level 1 (per node): a transient
/// propositional DPLL over the node's disjunctions — never cached, so the
/// exponential partial-assignment space does not enter the cache. Level 2 (cached
/// across nodes AND queries): the satisfiability of each ∃-successor *seed* (its
/// filler plus the universals propagated onto it), keyed by `CKey`.
///
/// `cache` holds only *unconditional* verdicts. UNSAT is always cached (sound: a
/// seed unsatisfiable even under optimistic blocking is unsatisfiable in every
/// context). A SAT verdict is cached only when its witness used no blocking
/// assumption (`used == false`) — then it is a genuine finite model, sound to
/// reuse anywhere. SAT-via-blocking (a cycle) is returned but not cached, which
/// keeps the greatest-fixpoint semantics sound without an SCC pass.
struct CacheRun<'a> {
    tab: &'a Tableau,
    prog: &'a CProg,
    cache: HashMap<CKey, bool>,
    /// Conditional SAT cache (pseudo-model caching): a seed satisfiable only via
    /// blocking on an on-stack ancestor at level i. Valid exactly while that
    /// ancestor is on the stack — every lookup then happens inside the ancestor's
    /// subtree, which is discarded if the ancestor fails — so it is purged when the
    /// blocker frame pops (`cond_at[i]` lists the keys to drop). Maps key → blocker
    /// level. This caches the deep ∃-chain whose verdicts depend on a stable
    /// shallow ancestor, turning re-search into cache hits.
    cond: HashMap<CKey, usize>,
    cond_at: Vec<Vec<CKey>>,
    /// the ∃-successor ancestors currently being computed, each with its
    /// Horn-closed concept set, for subset blocking.
    stack: Vec<(CKey, Vec<CLit>)>,
    /// Learned no-goods: concept-literal sets proven jointly unsatisfiable (w.r.t.
    /// the global TBox). Because they range over concept literals, a single
    /// no-good prunes EVERY node whose label contains it — the cross-node
    /// generalisation node-instance learning lacked. Watched by their smallest
    /// literal (`ng_watch`).
    nogoods: Vec<Vec<CLit>>,
    ng_watch: HashMap<CLit, Vec<usize>>,
    learn_cap: usize,
    learn_max: usize,
    /// disjunct-ordering strategy (KM_TAB_ORD): 0 = program order (default);
    /// 1 = vacuous markers first (shallow-model bias); 2 = all markers first.
    ord: u8,
    /// stats heartbeat interval (KM_TAB_HB, default 200_000).
    hb: u64,
    /// eager ∃-pruning at every DPLL step (KM_TAB_EAGER, default true). When
    /// false, successors are checked only at propositional completion.
    eager: bool,
    // --- Tier 1 search heuristics (gated; pure decision-order / phase choice,
    //     so they cannot change the SAT/UNSAT verdict and need no Lean re-cert) ---
    /// VSIDS-style branching (KM_TAB_VSIDS): branch on the conflict-active
    /// disjunction / disjunct rather than program order, so the search focuses
    /// on the conflict-dense region instead of oscillating.
    vsids: bool,
    activity: Vec<f64>, // per-concept conflict activity (indexed by C)
    act_inc: f64,
    act_decay: f64,
    /// phase saving (KM_TAB_PHASE): prefer the last polarity that completed a
    /// model for a concept, so re-search after backjump repeats good choices.
    phase_save: bool,
    saved: Vec<i8>, // 0 = unset, 1 = prefer positive, -1 = prefer negative
    /// Luby restarts of the per-seed DPLL (KM_TAB_RESTART): abandon the current
    /// search tree once `conflicts_since >= restart_limit` and re-enter from the
    /// seed base. Learned no-goods + VSIDS activity persist, so the fresh search
    /// exploits them from the top instead of staying stuck deep in the ∃-chain.
    /// Sound: restarting only re-orders the (terminating, complete) DPLL search.
    restart: bool,
    restart_unit: u64, // restart_limit = luby_v * restart_unit
    luby_u: u64,       // Knuth reluctant-doubling state
    luby_v: u64,
    conflicts_since: u64, // conflicts since the last restart
    restart_limit: u64,
    restart_pending: bool,
    // --- Convergence control (KM_TAB_CONV / KM_TAB_DYNRESTART / KM_TAB_REDUCE):
    //     Glucose-style adaptive restart + no-good database reduction. All are
    //     pure search-order / redundant-lemma management (a learned no-good is
    //     an entailed lemma, so dropping it only loses pruning, never
    //     soundness; restart order cannot change the SAT/UNSAT verdict), so
    //     none of this needs Lean re-cert.
    /// Dynamic (Glucose) restart: restart when the *recent* learned-no-good
    /// quality (proxied by size — shorter prunes more) is worse than the global
    /// average, i.e. the search has stopped producing strong lemmas and is
    /// oscillating. A "blocking" rule suppresses the restart when the search is
    /// deep (near a model) so it does not throw away a deep ∃-chain's
    /// conditional cache just as it converges.
    dyn_restart: bool,
    qwin: std::collections::VecDeque<u32>, // recent no-good sizes (bounded)
    qwin_sum: u64,
    qwin_cap: usize,
    qglob_sum: u64,
    qglob_cnt: u64,
    dyn_margin: f64, // restart when recent_avg > dyn_margin * global_avg
    dwin: std::collections::VecDeque<u32>, // recent search depths (bounded)
    dwin_sum: u64,
    block_factor: f64, // suppress restart while depth > block_factor * avg_depth
    /// No-good DB reduction: when the store exceeds `reduce_at`, drop the
    /// longest (lowest-quality) half, always keeping size <= 2 "glue" lemmas,
    /// then rebuild the watch index. Keeps `check_nogood` (run every DPLL step)
    /// cheap and focused.
    reduce: bool,
    reduce_at: usize,
    n_restart: u64,
    n_reduce: u64,
    stats: bool,
    n_seed: u64,
    n_dpll: u64,
    max_depth: usize,
    n_branch: u64,
    n_learn: u64,
    n_nghit: u64,
    /// Subsumption SAT cache (KM_TAB_SUBCACHE): SAT is downward-closed in
    /// (base, imposed). A self-contained (unconditional) model for a MORE
    /// constrained key K is also a model for any key whose base ⊆ K.base and
    /// imposed ⊆ K.imposed: Horn closure is monotone (fewer inputs derive a
    /// subset), and the dropped universals / ∃-obligations were all already
    /// satisfied by K's model. So a seed subsumed by an unconditionally-SAT
    /// anchor is SAT without search. Anchors (the search-proven unconditional
    /// SAT keys, line 3280) are indexed by every base literal; a lookup scans the
    /// watch list of the seed's first base literal (capped at `subcache_scan`)
    /// for a base+imposed superset. Pure redundancy/caching — the SAT/UNSAT
    /// verdicts and derived subsumptions are unchanged, so no Lean re-cert.
    subcache: bool,
    sat_keys: Vec<CKey>,
    sat_watch: HashMap<CLit, Vec<usize>>,
    subcache_scan: usize,
    /// Semantic branching (KM_TAB_SEMBR): once a relevant disjunct `d`'s subtree
    /// is refuted, every model of this node's context has `¬d`, so assert it for
    /// the remaining sibling branches (instead of only undoing `d`). This is the
    /// n-ary DPLL semantic split — it lets the next disjuncts' Horn closure use
    /// `¬d`, pruning the incomparable-successor WIDTH that subsumption cannot.
    /// Pure search-order/pruning over the same complete branch set — verdicts
    /// unchanged, no Lean re-cert. Gated off by default.
    sembr: bool,
    /// Global structural node-type caching (KM_TAB_TYPECACHE): the exact-key
    /// `cache` is keyed by a seed's PRE-closure (base, imposed). But a node's
    /// satisfiability depends only on its STRUCTURAL TYPE — the Horn-CLOSED
    /// concept set `curv` plus the universals `imposed` on it (and the global
    /// program). Two seeds with different bases that close to the same
    /// (curv, imposed) are the same subproblem, so they share the verdict. This
    /// collapses distinct seeds onto one type — a stronger generalisation than
    /// the pre-close key. Unconditional verdicts only (mirrors `cache`).
    typecache: bool,
    type_cache: HashMap<(Vec<CLit>, Vec<(Vec<CLit>, Vec<CLit>)>), bool>,
}

/// `a ⊆ b` for sorted, deduped slices.
fn subset_sorted<T: Ord>(a: &[T], b: &[T]) -> bool {
    let mut j = 0;
    for x in a {
        while j < b.len() && &b[j] < x {
            j += 1;
        }
        if j >= b.len() || &b[j] != x {
            return false;
        }
        j += 1;
    }
    true
}

/// A *reason* is the sorted set of source concept literals (seed-base + disjunction
/// decisions) a derived literal or a conflict depends on. Conflict-directed
/// backjumping uses it to skip irrelevant decisions; a learned no-good is the
/// reason of a clash, and because it ranges over concept literals (not node
/// instances) it prunes any node whose label contains it.
fn merge_into(acc: &mut Vec<CLit>, src: &[CLit]) {
    for &l in src {
        if let Err(i) = acc.binary_search(&l) {
            acc.insert(i, l);
        }
    }
}
fn reason_of<'b>(cdep: &'b HashMap<CLit, Vec<CLit>>, l: CLit) -> &'b [CLit] {
    cdep.get(&l).map(|v| v.as_slice()).unwrap_or(&[])
}
fn union_reasons(lits: &[CLit], cdep: &HashMap<CLit, Vec<CLit>>) -> Vec<CLit> {
    let mut r = Vec::new();
    for &l in lits {
        merge_into(&mut r, reason_of(cdep, l));
    }
    r
}

/// Outcome of the per-node DPLL: either a conflict (with its source-literal
/// reason and taint flag) or a restart request that unwinds the recursion to the
/// enclosing `sat_seed`, which re-enters the search from the seed base.
enum SearchErr {
    Conflict(Vec<CLit>, bool),
    Restart,
}

impl<'a> CacheRun<'a> {
    fn new(tab: &'a Tableau, prog: &'a CProg) -> Self {
        // KM_TAB_CONV bundles the convergence stack (VSIDS + phase saving +
        // dynamic restart + no-good reduction) — the combination that closes
        // the oscillating ∀+⊔ family. Individual flags still override.
        let conv = std::env::var_os("KM_TAB_CONV").is_some();
        let env_on = |k: &str, d: bool| std::env::var(k).map(|s| s != "0").unwrap_or(d);
        CacheRun {
            tab,
            prog,
            cache: HashMap::new(),
            cond: HashMap::new(),
            cond_at: Vec::new(),
            stack: Vec::new(),
            nogoods: Vec::new(),
            ng_watch: HashMap::new(),
            learn_cap: std::env::var("KM_TAB_LEARN_CAP")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(2_000_000),
            learn_max: std::env::var("KM_TAB_LEARN_MAX")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(64),
            ord: std::env::var("KM_TAB_ORD")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(0),
            hb: std::env::var("KM_TAB_HB")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(200_000),
            eager: std::env::var("KM_TAB_EAGER")
                .map(|s| s != "0")
                .unwrap_or(true),
            vsids: env_on("KM_TAB_VSIDS", conv),
            activity: if env_on("KM_TAB_VSIDS", conv) {
                vec![0.0; prog.n_concepts as usize]
            } else {
                Vec::new()
            },
            act_inc: 1.0,
            act_decay: std::env::var("KM_TAB_VSIDS_DECAY")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(0.95),
            phase_save: env_on("KM_TAB_PHASE", conv),
            saved: if env_on("KM_TAB_PHASE", conv) {
                vec![0i8; prog.n_concepts as usize]
            } else {
                Vec::new()
            },
            restart: env_on("KM_TAB_RESTART", false),
            restart_unit: std::env::var("KM_TAB_RESTART_UNIT")
                .ok()
                .and_then(|s| s.parse().ok())
                .filter(|&u| u > 0)
                .unwrap_or(100),
            luby_u: 1,
            luby_v: 1,
            conflicts_since: 0,
            restart_limit: std::env::var("KM_TAB_RESTART_UNIT")
                .ok()
                .and_then(|s| s.parse().ok())
                .filter(|&u| u > 0)
                .unwrap_or(100),
            restart_pending: false,
            dyn_restart: env_on("KM_TAB_DYNRESTART", conv),
            qwin: std::collections::VecDeque::new(),
            qwin_sum: 0,
            qwin_cap: std::env::var("KM_TAB_DYN_WIN")
                .ok()
                .and_then(|s| s.parse().ok())
                .filter(|&u| u > 0)
                .unwrap_or(50),
            qglob_sum: 0,
            qglob_cnt: 0,
            dyn_margin: std::env::var("KM_TAB_DYN_MARGIN")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(0.8),
            dwin: std::collections::VecDeque::new(),
            dwin_sum: 0,
            block_factor: std::env::var("KM_TAB_DYN_BLOCK")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(1.4),
            reduce: env_on("KM_TAB_REDUCE", conv),
            reduce_at: std::env::var("KM_TAB_REDUCE_AT")
                .ok()
                .and_then(|s| s.parse().ok())
                .filter(|&u| u > 0)
                .unwrap_or(30_000),
            n_restart: 0,
            n_reduce: 0,
            stats: std::env::var_os("KM_TAB_STATS").is_some(),
            n_seed: 0,
            n_dpll: 0,
            max_depth: 0,
            n_branch: 0,
            n_learn: 0,
            n_nghit: 0,
            subcache: env_on("KM_TAB_SUBCACHE", false),
            sat_keys: Vec::new(),
            sat_watch: HashMap::new(),
            subcache_scan: std::env::var("KM_TAB_SUBCACHE_SCAN")
                .ok()
                .and_then(|s| s.parse().ok())
                .filter(|&u| u > 0)
                .unwrap_or(512),
            sembr: env_on("KM_TAB_SEMBR", false),
            typecache: env_on("KM_TAB_TYPECACHE", false),
            type_cache: HashMap::new(),
        }
    }

    /// Record a learned no-good (a clash reason), watched by its smallest literal.
    /// Skipped if empty (unconditional — handled by the consistency check), too
    /// large, or the cap is hit.
    fn learn(&mut self, conf: &[CLit]) {
        if conf.is_empty() || conf.len() > self.learn_max || self.nogoods.len() >= self.learn_cap {
            return;
        }
        let mut ng = conf.to_vec();
        ng.sort_unstable();
        ng.dedup();
        let idx = self.nogoods.len();
        self.ng_watch.entry(ng[0]).or_default().push(idx);
        self.nogoods.push(ng);
        self.n_learn += 1;
        self.maybe_reduce();
    }

    /// If `set` contains a learned no-good, return its clash reason (for
    /// backjumping); else `None`.
    fn check_nogood(
        &self,
        set: &HashSet<CLit>,
        cdep: &HashMap<CLit, Vec<CLit>>,
    ) -> Option<Vec<CLit>> {
        for l in set {
            if let Some(idxs) = self.ng_watch.get(l) {
                for &i in idxs {
                    if self.nogoods[i].iter().all(|x| set.contains(x)) {
                        return Some(union_reasons(&self.nogoods[i], cdep));
                    }
                }
            }
        }
        None
    }

    /// Like `check_nogood` but only reports whether a no-good fires (for the
    /// dependency-free witness path).
    fn has_nogood(&self, set: &HashSet<CLit>) -> bool {
        for l in set {
            if let Some(idxs) = self.ng_watch.get(l) {
                for &i in idxs {
                    if self.nogoods[i].iter().all(|x| set.contains(x)) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Cache a search-proven *unconditional*-SAT key and index it as a
    /// subsumption anchor (watched by every base literal) when KM_TAB_SUBCACHE
    /// is on. Only unconditional SAT keys become anchors — a conditional model
    /// (blocked on a stack ancestor) is not self-contained and would be unsound
    /// to reuse by subsumption.
    fn cache_sat(&mut self, key: &CKey) {
        self.cache.insert(key.clone(), true);
        if !self.subcache || key.base.is_empty() {
            return;
        }
        let idx = self.sat_keys.len();
        for &l in &key.base {
            self.sat_watch.entry(l).or_default().push(idx);
        }
        self.sat_keys.push(key.clone());
    }

    /// `true` iff some indexed SAT anchor K has `key.base ⊆ K.base` and
    /// `key.imposed ⊆ K.imposed` (so `key` is SAT by downward-closure, reusing
    /// K's self-contained model). Scans the watch list of `key`'s first base
    /// literal newest-first, capped at `subcache_scan`; a miss falls through to
    /// the full search (still sound, only loses the shortcut).
    fn subsumed_sat(&self, key: &CKey) -> bool {
        if !self.subcache || key.base.is_empty() {
            return false;
        }
        let l0 = key.base[0];
        if let Some(idxs) = self.sat_watch.get(&l0) {
            for &i in idxs.iter().rev().take(self.subcache_scan) {
                let k = &self.sat_keys[i];
                if key.base.len() <= k.base.len()
                    && key.imposed.len() <= k.imposed.len()
                    && subset_sorted(&key.base, &k.base)
                    && subset_sorted(&key.imposed, &k.imposed)
                {
                    return true;
                }
            }
        }
        false
    }

    /// Subset blocking (sound for ALCH without inverse / number / nominals): a node
    /// whose Horn-closed concept set is ⊆ an ancestor's, and whose imposed clauses
    /// are ⊆ that ancestor's, is at most as constrained, so it reuses the
    /// ancestor's model (the greatest-fixpoint blocking assumption). By Dickson's
    /// lemma this bounds every ∃-chain, giving termination.
    /// Returns the stack level of the *deepest* blocking ancestor (largest index,
    /// for maximal locality so self-contained cycles cache as early as possible),
    /// or `None` if the node is not blocked.
    fn blocked(&self, curv: &[CLit], imposed: &[(Vec<CLit>, Vec<CLit>)]) -> Option<usize> {
        self.stack
            .iter()
            .enumerate()
            .rev()
            .find(|(_, (ak, acur))| {
                curv.len() <= acur.len()
                    && imposed.len() <= ak.imposed.len()
                    && subset_sorted(curv, acur)
                    && subset_sorted(imposed, &ak.imposed)
            })
            .map(|(i, _)| i)
    }

    /// Horn-close `set` against the program and `imposed` clauses. Returns `true`
    /// iff it clashes (complementary pair, or a node-local/imposed ⊥-clause fires).
    fn close(&self, set: &mut HashSet<CLit>, imposed: &[(Vec<CLit>, Vec<CLit>)]) -> bool {
        let p = self.prog;
        if p.clash_empty {
            return true;
        }
        if set.iter().any(|l| !l.neg && set.contains(&l.complement())) {
            return true;
        }
        // empty-body Horn facts (⊤ ⊑ h) fire unconditionally.
        for &h in &p.horn_empty {
            set.insert(h);
        }
        // semi-naive worklist: a literal triggers only the clauses that mention it.
        let mut wl: Vec<CLit> = set.iter().copied().collect();
        loop {
            while let Some(l) = wl.pop() {
                if let Some(idxs) = p.horn_by_lit.get(&l) {
                    for &i in idxs {
                        let (b, h) = &p.node_horn[i];
                        if b.iter().all(|x| set.contains(x)) && set.insert(*h) {
                            if set.contains(&h.complement()) {
                                return true;
                            }
                            wl.push(*h);
                        }
                    }
                }
                if let Some(idxs) = p.clash_by_lit.get(&l) {
                    for &i in idxs {
                        if p.node_clash[i].iter().all(|x| set.contains(x)) {
                            return true;
                        }
                    }
                }
            }
            // imposed clauses + domain are few; rescan and re-seed the worklist
            // with anything they add.
            let mut added: Vec<CLit> = Vec::new();
            for (b, h) in imposed {
                if b.iter().all(|x| set.contains(x)) {
                    if h.is_empty() {
                        return true;
                    }
                    if h.len() == 1 && set.insert(h[0]) {
                        if set.contains(&h[0].complement()) {
                            return true;
                        }
                        added.push(h[0]);
                    }
                }
            }
            if !p.domain.is_empty() {
                let active: Vec<R> = p
                    .node_exists
                    .iter()
                    .filter(|(b, _, _)| b.iter().all(|x| set.contains(x)))
                    .map(|(_, r, _)| *r)
                    .collect();
                for (rd, dc) in &p.domain {
                    if active.iter().any(|&r0| p.role_le(r0, *rd)) && set.insert(*dc) {
                        added.push(*dc);
                    }
                }
            }
            if added.is_empty() {
                return false;
            }
            wl = added;
        }
    }

    /// Horn-close `set` with reason tracking (`cdep`: each derived literal → its
    /// source-literal reason) and per-literal taint tracking (`tlits`: literals
    /// whose derivation used an imposed, node-specific clause). Returns
    /// `Some(reason)` of the clash if one fires; sets `*tainted` iff *that clash*
    /// depends on an imposed clause. An untainted clash is a globally valid
    /// no-good (provable from the TBox alone), so the caller may learn it even at
    /// a node carrying imposed constraints — which a coarse "any imposed fired"
    /// flag would wrongly forbid. `tlits` persists across the seed's DPLL so taint
    /// propagates through later Horn steps; trailed literals are removed from it on
    /// undo (in the branch loop).
    fn close_dep(
        &self,
        set: &mut HashSet<CLit>,
        cdep: &mut HashMap<CLit, Vec<CLit>>,
        imposed: &[(Vec<CLit>, Vec<CLit>)],
        trail: &mut Vec<CLit>,
        tlits: &mut HashSet<CLit>,
        tainted: &mut bool,
    ) -> Option<Vec<CLit>> {
        let p = self.prog;
        if p.clash_empty {
            return Some(Vec::new());
        }
        let mut wl: Vec<CLit> = set.iter().copied().collect();
        for &h in &p.horn_empty {
            if set.insert(h) {
                cdep.insert(h, Vec::new());
                trail.push(h);
                wl.push(h);
            }
        }
        loop {
            while let Some(l) = wl.pop() {
                if set.contains(&l.complement()) {
                    *tainted = tlits.contains(&l) || tlits.contains(&l.complement());
                    let mut r = cdep.get(&l).cloned().unwrap_or_default();
                    merge_into(&mut r, reason_of(cdep, l.complement()));
                    return Some(r);
                }
                if let Some(idxs) = p.horn_by_lit.get(&l) {
                    for &i in idxs {
                        let (b, h) = &p.node_horn[i];
                        if b.iter().all(|x| set.contains(x)) && set.insert(*h) {
                            // trail FIRST, so the literal is undone even when it
                            // immediately clashes (else it leaks into siblings).
                            trail.push(*h);
                            let bt = b.iter().any(|x| tlits.contains(x));
                            if bt {
                                tlits.insert(*h);
                            }
                            let r = union_reasons(b, cdep);
                            if set.contains(&h.complement()) {
                                *tainted = bt || tlits.contains(&h.complement());
                                let mut rr = r;
                                merge_into(&mut rr, reason_of(cdep, h.complement()));
                                return Some(rr);
                            }
                            cdep.insert(*h, r);
                            wl.push(*h);
                        }
                    }
                }
                if let Some(idxs) = p.clash_by_lit.get(&l) {
                    for &i in idxs {
                        let b = &p.node_clash[i];
                        if b.iter().all(|x| set.contains(x)) {
                            *tainted = b.iter().any(|x| tlits.contains(x));
                            return Some(union_reasons(b, cdep));
                        }
                    }
                }
            }
            let mut more: Vec<CLit> = Vec::new();
            for (b, h) in imposed {
                if b.iter().all(|x| set.contains(x)) {
                    // imposed clause fired: its head/conflict is node-specific.
                    let r = union_reasons(b, cdep);
                    if h.is_empty() {
                        *tainted = true;
                        return Some(r);
                    }
                    if h.len() == 1 && set.insert(h[0]) {
                        trail.push(h[0]);
                        tlits.insert(h[0]);
                        if set.contains(&h[0].complement()) {
                            *tainted = true;
                            let mut rr = r;
                            merge_into(&mut rr, reason_of(cdep, h[0].complement()));
                            return Some(rr);
                        }
                        cdep.insert(h[0], r);
                        more.push(h[0]);
                    }
                }
            }
            if !p.domain.is_empty() {
                for (rd, dc) in &p.domain {
                    let src = p.node_exists.iter().find(|(b, r0, _)| {
                        p.role_le(*r0, *rd) && b.iter().all(|x| set.contains(x))
                    });
                    if let Some((b, _, _)) = src {
                        if set.insert(*dc) {
                            trail.push(*dc);
                            let bt = b.iter().any(|x| tlits.contains(x));
                            if bt {
                                tlits.insert(*dc);
                            }
                            let r = union_reasons(b, cdep);
                            if set.contains(&dc.complement()) {
                                *tainted = bt || tlits.contains(&dc.complement());
                                let mut rr = r;
                                merge_into(&mut rr, reason_of(cdep, dc.complement()));
                                return Some(rr);
                            }
                            cdep.insert(*dc, r);
                            more.push(*dc);
                        }
                    }
                }
            }
            if more.is_empty() {
                return None;
            }
            wl = more;
        }
    }

    /// The clash reason for an unsatisfiable `r0`-successor with filler `fil`: the
    /// reasons of the node literals that built the (unsatisfiable) successor seed —
    /// the obligation's body and every triggered universal's body.
    /// Returns `(reason, tainted)`: `tainted` iff the obligation or any triggered
    /// universal fires off an imposed-derived (node-specific) literal, so the
    /// successor's unsatisfiability is not a globally valid no-good.
    fn succ_conflict(
        &self,
        set: &HashSet<CLit>,
        cdep: &HashMap<CLit, Vec<CLit>>,
        tlits: &HashSet<CLit>,
        r0: R,
        fil: CLit,
    ) -> (Vec<CLit>, bool) {
        let p = self.prog;
        let mut r = Vec::new();
        let mut tainted = false;
        if let Some((b, _, _)) = p
            .node_exists
            .iter()
            .find(|(b, rr, ff)| *rr == r0 && *ff == fil && b.iter().all(|x| set.contains(x)))
        {
            tainted |= b.iter().any(|x| tlits.contains(x));
            merge_into(&mut r, &union_reasons(b, cdep));
        }
        for u in &p.uni {
            if p.role_le(r0, u.role) && u.xbody.iter().all(|x| set.contains(x)) {
                tainted |= u.xbody.iter().any(|x| tlits.contains(x));
                merge_into(&mut r, &union_reasons(&u.xbody, cdep));
            }
        }
        (r, tainted)
    }

    /// First unsatisfied disjunction active on `set`, returned as `(guard,
    /// disjuncts, from_imposed)`, or `None` if propositionally complete. A node-
    /// local disjunction is global; an imposed one is node-specific, so conflicts
    /// derived under it must not be learned globally (`from_imposed = true`).
    /// VSIDS: bump one concept's activity, rescaling all scores if it overflows.
    fn act_bump(&mut self, c: C) {
        let i = c as usize;
        if i >= self.activity.len() {
            return;
        }
        self.activity[i] += self.act_inc;
        if self.activity[i] > 1e100 {
            for a in self.activity.iter_mut() {
                *a *= 1e-100;
            }
            self.act_inc *= 1e-100;
        }
    }
    /// VSIDS: bump every concept mentioned in a conflict reason.
    fn act_bump_reason(&mut self, conf: &[CLit]) {
        if !self.vsids {
            return;
        }
        for l in conf {
            self.act_bump(l.c);
        }
    }
    /// VSIDS: age past activity (one decay step per resolved conflict).
    fn act_decay_step(&mut self) {
        if self.vsids && self.act_decay > 0.0 {
            self.act_inc /= self.act_decay;
        }
    }
    /// The activity of a disjunct (0 when VSIDS is off / out of range).
    fn act_of(&self, d: &CLit) -> f64 {
        if self.vsids {
            self.activity.get(d.c as usize).copied().unwrap_or(0.0)
        } else {
            0.0
        }
    }
    /// Advance the Luby reluctant-doubling sequence (1,1,2,1,1,2,4,...) and set
    /// the next restart threshold to `luby_v * restart_unit`.
    fn luby_step(&mut self) {
        if (self.luby_u & self.luby_u.wrapping_neg()) == self.luby_v {
            self.luby_u += 1;
            self.luby_v = 1;
        } else {
            self.luby_v = self.luby_v.saturating_mul(2);
        }
        self.restart_limit = self.luby_v.saturating_mul(self.restart_unit).max(1);
    }
    /// Count a resolved conflict (`conf_len` = size of its reason); arm a restart.
    /// Two policies, composable:
    ///   - static Luby (KM_TAB_RESTART): restart once `conflicts_since` hits the
    ///     Luby threshold.
    ///   - dynamic Glucose (KM_TAB_DYNRESTART): restart once the *recent* conflict
    ///     quality (size, smaller = better) is materially worse than the global
    ///     average — the signature of an oscillating search — unless the search is
    ///     currently deep (the blocking rule: it is building a large model, so do
    ///     not discard the deep ∃-chain's conditional cache).
    /// Driven off every resolved conflict (tainted or not) so it engages on the
    /// imposed-disjunction (∀+⊔) family where global learning rarely fires.
    fn note_conflict(&mut self, conf_len: usize) {
        if !(self.restart || self.dyn_restart) {
            return;
        }
        self.conflicts_since += 1;
        if self.dyn_restart {
            self.register_quality(conf_len as u32);
            if self.qwin.len() >= self.qwin_cap && self.qglob_cnt > 0 {
                let recent_avg = self.qwin_sum as f64 / self.qwin.len() as f64;
                let global_avg = self.qglob_sum as f64 / self.qglob_cnt as f64;
                let deep = if !self.dwin.is_empty() {
                    let avg_depth = self.dwin_sum as f64 / self.dwin.len() as f64;
                    (self.stack.len() as f64) > self.block_factor * avg_depth
                } else {
                    false
                };
                if !deep && recent_avg * self.dyn_margin > global_avg {
                    self.restart_pending = true;
                    self.n_restart += 1;
                    self.qwin.clear(); // fresh window: do not immediately re-trigger
                    self.qwin_sum = 0;
                }
            }
        }
        if self.restart && self.conflicts_since >= self.restart_limit {
            self.restart_pending = true;
            self.n_restart += 1;
        }
    }
    /// Feed one resolved-conflict size (and the current depth) into the rolling
    /// Glucose windows + the all-time averages.
    fn register_quality(&mut self, sz: u32) {
        self.qglob_sum += sz as u64;
        self.qglob_cnt += 1;
        self.qwin.push_back(sz);
        self.qwin_sum += sz as u64;
        if self.qwin.len() > self.qwin_cap {
            if let Some(old) = self.qwin.pop_front() {
                self.qwin_sum -= old as u64;
            }
        }
        let d = self.stack.len() as u32;
        self.dwin.push_back(d);
        self.dwin_sum += d as u64;
        if self.dwin.len() > self.qwin_cap {
            if let Some(old) = self.dwin.pop_front() {
                self.dwin_sum -= old as u64;
            }
        }
    }
    /// No-good DB reduction: when the store exceeds `reduce_at`, keep all "glue"
    /// (size <= 2) lemmas plus the shortest half, and rebuild the watch index.
    /// Sound (no-goods are entailed lemmas; dropping them only loses pruning) and
    /// the point of it: `check_nogood` runs on every DPLL step over the watch
    /// lists, so an unbounded store turns each step super-linear.
    fn maybe_reduce(&mut self) {
        if !self.reduce || self.nogoods.len() < self.reduce_at {
            return;
        }
        let mut idx: Vec<usize> = (0..self.nogoods.len()).collect();
        idx.sort_by_key(|&i| self.nogoods[i].len());
        let keep_n = (self.reduce_at / 2).max(1);
        let mut keep: Vec<Vec<CLit>> = Vec::with_capacity(keep_n + 16);
        for (rank, &i) in idx.iter().enumerate() {
            if self.nogoods[i].len() <= 2 || rank < keep_n {
                keep.push(std::mem::take(&mut self.nogoods[i]));
            }
        }
        self.nogoods = keep;
        self.ng_watch.clear();
        for (i, ng) in self.nogoods.iter().enumerate() {
            if let Some(&l0) = ng.first() {
                self.ng_watch.entry(l0).or_default().push(i);
            }
        }
        self.n_reduce += 1;
    }
    /// Phase saving: remember the polarity of a disjunct that completed a model.
    fn save_phase(&mut self, d: CLit) {
        if !self.phase_save {
            return;
        }
        if let Some(s) = self.saved.get_mut(d.c as usize) {
            *s = if d.neg { -1 } else { 1 };
        }
    }

    fn first_disj(
        &self,
        set: &HashSet<CLit>,
        imposed: &[(Vec<CLit>, Vec<CLit>)],
    ) -> Option<(Vec<CLit>, Vec<CLit>, bool)> {
        let p = self.prog;
        // VSIDS: among all applicable, unsatisfied disjunctions, branch on the one
        // whose most-active disjunct is highest (focus the search on the
        // conflict-dense region). Pure decision-order: any applicable disjunction
        // is a sound branch point, so this cannot change the verdict.
        if self.vsids {
            let mut best: Option<(f64, &Vec<CLit>, &Vec<CLit>, bool)> = None;
            for (b, h) in &p.node_disj {
                if b.iter().all(|l| set.contains(l)) && !h.iter().any(|d| set.contains(d)) {
                    let score = h
                        .iter()
                        .map(|d| self.act_of(d))
                        .fold(f64::NEG_INFINITY, f64::max);
                    if best.as_ref().map_or(true, |&(s, ..)| score > s) {
                        best = Some((score, b, h, false));
                    }
                }
            }
            for (b, h) in imposed {
                if h.len() >= 2
                    && b.iter().all(|l| set.contains(l))
                    && !h.iter().any(|d| set.contains(d))
                {
                    let score = h
                        .iter()
                        .map(|d| self.act_of(d))
                        .fold(f64::NEG_INFINITY, f64::max);
                    if best.as_ref().map_or(true, |&(s, ..)| score > s) {
                        best = Some((score, b, h, true));
                    }
                }
            }
            return best.map(|(_, b, h, imp)| (b.clone(), h.clone(), imp));
        }
        for (b, h) in &p.node_disj {
            if b.iter().all(|l| set.contains(l)) && !h.iter().any(|d| set.contains(d)) {
                return Some((b.clone(), h.clone(), false));
            }
        }
        for (b, h) in imposed {
            if h.len() >= 2
                && b.iter().all(|l| set.contains(l))
                && !h.iter().any(|d| set.contains(d))
            {
                return Some((b.clone(), h.clone(), true));
            }
        }
        None
    }

    /// The distinct ∃-obligations active on a complete `set`.
    fn obligations(&self, set: &HashSet<CLit>) -> Vec<(R, CLit)> {
        let mut obls: Vec<(R, CLit)> = Vec::new();
        for (b, r, fil) in &self.prog.node_exists {
            if b.iter().all(|l| set.contains(l)) {
                let o = (*r, *fil);
                if !obls.contains(&o) {
                    obls.push(o);
                }
            }
        }
        obls
    }

    /// Is there a live ∃-obligation over a sub-role of `r` in `set`? If not, a
    /// `∀r.L` marker is vacuous (it constrains no successor), so choosing it
    /// closes its disjunction without forcing a successor chain.
    fn has_obl_role(&self, set: &HashSet<CLit>, r: R) -> bool {
        for (b, r2, _) in &self.prog.node_exists {
            if self.prog.role_le(*r2, r) && b.iter().all(|l| set.contains(l)) {
                return true;
            }
        }
        false
    }

    /// Reorder a disjunction's disjuncts for the model-finding search. Pure
    /// reordering: cannot change the SAT/UNSAT verdict, only how fast a model is
    /// found. Strategy 1 floats *vacuous* `∀r.L` markers (no live r-obligation)
    /// to the front so the search prefers shallow models over forcing ∃-chains;
    /// strategy 2 floats all markers first. `disj` is taken by value and the
    /// reordered vector returned.
    fn order_disj(&self, set: &HashSet<CLit>, disj: Vec<CLit>) -> Vec<CLit> {
        // VSIDS / phase saving take precedence over the static KM_TAB_ORD strategy:
        // try the most conflict-active disjunct first, with a saved-phase match as
        // tie-break. Still a pure reordering — the verdict is unchanged.
        if self.vsids || self.phase_save {
            let phase_rank = |d: &CLit| -> u8 {
                if !self.phase_save {
                    return 1;
                }
                match self.saved.get(d.c as usize).copied().unwrap_or(0) {
                    s if s > 0 && !d.neg => 0,
                    s if s < 0 && d.neg => 0,
                    _ => 1,
                }
            };
            let mut v = disj;
            // sort by (descending activity, matching saved phase first); stable so
            // program order breaks remaining ties.
            v.sort_by(|a, b| {
                self.act_of(b)
                    .partial_cmp(&self.act_of(a))
                    .unwrap_or(std::cmp::Ordering::Equal)
                    .then(phase_rank(a).cmp(&phase_rank(b)))
            });
            return v;
        }
        if self.ord == 0 {
            return disj;
        }
        // rank: lower sorts earlier. stable sort preserves program order in ties.
        let rank = |d: &CLit| -> u8 {
            match (!d.neg).then(|| self.prog.marker_role.get(&d.c)).flatten() {
                Some(&r) => {
                    if self.ord >= 2 || !self.has_obl_role(set, r) {
                        0 // vacuous (or, in ord 2, any) marker: try first
                    } else {
                        2 // marker with a live r-obligation: try last
                    }
                }
                None => 1, // ordinary concept disjunct
            }
        };
        let mut v = disj;
        v.sort_by_key(|d| rank(d));
        v
    }

    /// The seed label of an `r0`-successor with filler `fil`: the filler plus every
    /// universal the parent's completed set triggers over a super-role of `r0`
    /// (forced facts folded into the base, conditional/disjunctive ones imposed).
    fn build_succ(&self, parent: &HashSet<CLit>, r0: R, fil: CLit) -> CKey {
        let p = self.prog;
        let mut base = vec![fil];
        let mut imposed: Vec<(Vec<CLit>, Vec<CLit>)> = Vec::new();
        let idxs = p.uni_for_role.get(&r0).map(|v| v.as_slice()).unwrap_or(&[]);
        for &i in idxs {
            let u = &p.uni[i];
            if u.xbody.iter().all(|l| parent.contains(l)) {
                if u.ybody.is_empty() && u.yhead.len() == 1 {
                    base.push(u.yhead[0]);
                } else {
                    imposed.push((u.ybody.clone(), u.yhead.clone()));
                }
            }
        }
        CKey::canon(base, imposed)
    }

    /// Is the seed `key` satisfiable? Returns `(sat, block_level)` where
    /// `block_level` is the shallowest stack level the SAT verdict depends on via
    /// blocking (`usize::MAX` if the model is self-contained / unconditional). A
    /// verdict is cached only when unconditional; a conditional one propagates its
    /// dependency to the caller so the dependency-owning ancestor can confirm it.
    fn sat_seed(&mut self, key: &CKey) -> (bool, usize) {
        if let Some(&s) = self.cache.get(key) {
            return (s, usize::MAX); // a cached verdict is unconditional (genuine)
        }
        if let Some(&i) = self.cond.get(key) {
            // conditional SAT, still valid (its blocker at level i is on the stack).
            return (true, i);
        }
        // subsumption SAT cache: an unconditionally-SAT anchor with a superset
        // base + imposed already proves this seed satisfiable (downward-closure).
        if self.subsumed_sat(key) {
            self.cache.insert(key.clone(), true);
            return (true, usize::MAX);
        }
        let mut set: HashSet<CLit> = key.base.iter().copied().collect();
        let mut cdep: HashMap<CLit, Vec<CLit>> = HashMap::with_capacity(key.base.len() * 2);
        for &l in &key.base {
            cdep.insert(l, vec![l]);
        }
        let mut tainted = false;
        let mut trail = Vec::new();
        let mut tlits: HashSet<CLit> = HashSet::new();
        if let Some(conf) = self.close_dep(
            &mut set,
            &mut cdep,
            &key.imposed,
            &mut trail,
            &mut tlits,
            &mut tainted,
        ) {
            self.cache.insert(key.clone(), false);
            if !tainted {
                self.learn(&conf);
            }
            return (false, usize::MAX);
        }
        let mut curv: Vec<CLit> = set.iter().copied().collect();
        curv.sort_unstable();
        // global structural node-type cache: a verdict for this CLOSED type
        // (curv + imposed) is unconditional and transfers to any seed that closes
        // to it. Captured `tkey` is re-used to store the verdict below.
        let tkey = if self.typecache {
            let k = (curv.clone(), key.imposed.clone());
            if let Some(&s) = self.type_cache.get(&k) {
                self.cache.insert(key.clone(), s);
                return (s, usize::MAX);
            }
            Some(k)
        } else {
            None
        };
        // this seed's stack level (index it will occupy once pushed).
        let my_level = self.stack.len();
        if let Some(i) = self.blocked(&curv, &key.imposed) {
            // blocked on ancestor at level i (< my_level): SAT, conditional on that
            // ancestor's model. Cache conditionally (purged when level i pops).
            self.cond.insert(key.clone(), i);
            self.cond_at[i].push(key.clone());
            return (true, i);
        }
        self.stack.push((key.clone(), curv));
        self.cond_at.push(Vec::new());
        self.n_seed += 1;
        if self.stats && self.n_seed % self.hb == 0 {
            eprintln!(
                "KM_TAB_STATS cache: seeds={} stack={} cache={} nogoods={} nghit={}",
                self.n_seed,
                self.stack.len(),
                self.cache.len(),
                self.nogoods.len(),
                self.n_nghit
            );
        }
        // seed entry: first DPLL step always does a full eager check (dirty).
        self.restart_pending = false;
        let mut res = self.local_search(key, &mut set, &mut cdep, &mut tlits, true, usize::MAX);
        // Luby restarts: re-enter the DPLL from the seed base when the conflict
        // budget is hit. Learned no-goods + VSIDS activity persist (they prune and
        // redirect the fresh search — the point of the restart). Conditional SAT
        // entries blocked on THIS frame are dropped: they were justified by the
        // partial model we are abandoning, so they must be re-derived. Cache
        // (unconditional SAT / all UNSAT) entries stay sound and are kept.
        while matches!(res, Err(SearchErr::Restart)) {
            self.luby_step();
            self.conflicts_since = 0;
            self.restart_pending = false;
            let stale: Vec<CKey> = std::mem::take(&mut self.cond_at[my_level]);
            for k in stale {
                self.cond.remove(&k);
            }
            set = key.base.iter().copied().collect();
            cdep = HashMap::with_capacity(key.base.len() * 2);
            for &l in &key.base {
                cdep.insert(l, vec![l]);
            }
            tlits = HashSet::new();
            let mut tr: Vec<CLit> = Vec::new();
            let mut tn = false;
            if let Some(conf) = self.close_dep(
                &mut set,
                &mut cdep,
                &key.imposed,
                &mut tr,
                &mut tlits,
                &mut tn,
            ) {
                // unreachable in practice (the base closed cleanly on first entry),
                // but handle defensively as a genuine unsat.
                res = Err(SearchErr::Conflict(conf, tn));
                break;
            }
            res = self.local_search(key, &mut set, &mut cdep, &mut tlits, true, usize::MAX);
        }
        self.stack.pop();
        // this frame is gone: drop the conditional entries that depended on it.
        for k in self.cond_at.pop().into_iter().flatten() {
            self.cond.remove(&k);
        }
        match res {
            Ok(bl) => {
                // `bl` = shallowest stack level any blocking in this subtree relied
                // on. If `bl >= my_level`, every back-edge stayed inside this seed's
                // subtree: a self-contained finite cyclic model, so the SAT verdict
                // is unconditional and cacheable (pseudo-model caching). If
                // `bl < my_level`, the model depends on an ancestor at level `bl`
                // above this seed — cache conditionally (valid while that ancestor
                // is on the stack) and propagate the dependency upward.
                if bl >= my_level {
                    self.cache_sat(key);
                    if let Some(k) = tkey {
                        self.type_cache.insert(k, true);
                    }
                    (true, usize::MAX)
                } else {
                    // conditional (depends on an ancestor's model): NOT a
                    // self-contained type verdict, so it must not enter type_cache.
                    self.cond.insert(key.clone(), bl);
                    self.cond_at[bl].push(key.clone());
                    (true, bl)
                }
            }
            Err(SearchErr::Conflict(conf, tainted)) => {
                self.cache.insert(key.clone(), false);
                if let Some(k) = tkey {
                    self.type_cache.insert(k, false);
                }
                if !tainted {
                    self.learn(&conf);
                }
                (false, usize::MAX)
            }
            Err(SearchErr::Restart) => unreachable!("restart consumed by the loop above"),
        }
    }

    /// Level-1 propositional DPLL on one node with conflict-directed backjumping +
    /// label-based no-good learning. `Ok(block_level)` = a clash-free complete
    /// assignment with all ∃-successors satisfiable, where `block_level` is the
    /// shallowest stack level any blocking in this subtree relied on (`usize::MAX`
    /// if none); `Err(reason)` = the node is unsatisfiable, `reason` the source-
    /// literal set responsible (drives backjump in the caller and may be learned).
    ///
    /// Eager ∃-pruning: every active obligation's successor is checked at *every*
    /// level (sound: a partial node-set imposes FEWER universals, so a partial
    /// successor that is unsatisfiable stays so). Backjumping: when asserting a
    /// disjunct `d` yields a conflict not mentioning `d`, `d` was irrelevant — the
    /// conflict is returned past the whole disjunction (skipping its siblings).
    fn local_search(
        &mut self,
        key: &CKey,
        set: &mut HashSet<CLit>,
        cdep: &mut HashMap<CLit, Vec<CLit>>,
        // persistent per-literal taint for this seed's DPLL (see close_dep).
        tlits: &mut HashSet<CLit>,
        // `dirty` = this DPLL step may have changed obligations/successors (a
        // trigger literal was added); when false the eager ∃-check is skipped and
        // `inherited_block` (the enclosing full check's blocker level) carries over.
        dirty: bool,
        inherited_block: usize,
    ) -> Result<usize, SearchErr> {
        self.n_dpll += 1;
        self.max_depth = self.max_depth.max(self.stack.len());
        // a restart was armed by a conflict elsewhere: abandon this branch and
        // unwind to the enclosing `sat_seed`, which re-enters from the seed base.
        if self.restart_pending {
            return Err(SearchErr::Restart);
        }
        if self.stats && self.n_dpll % self.hb == 0 {
            eprintln!(
                "KM_TAB_STATS cache: dpll={} branches={} seeds={} cache={} depth={}/{} nogoods={} nghit={} restarts={} reduces={}",
                self.n_dpll, self.n_branch, self.n_seed, self.cache.len(),
                self.stack.len(), self.max_depth, self.nogoods.len(), self.n_nghit,
                self.n_restart, self.n_reduce
            );
        }
        // label-based pruning: a learned no-good already in this label ⇒ unsat.
        // Learned no-goods are global, so this conflict is untainted.
        if let Some(r) = self.check_nogood(set, cdep) {
            self.n_nghit += 1;
            return Err(SearchErr::Conflict(r, false));
        }
        // eager: prune as soon as any active obligation's successor is unsat.
        // Incremental: when nothing trigger-relevant changed (`!dirty`), the
        // obligations and their successors are identical to the enclosing full
        // check, so reuse its blocking flag and skip the rescan entirely.
        // (KM_TAB_EAGER=0 defers this to propositional completion instead.)
        let mut block_min = inherited_block;
        if self.eager && dirty {
            block_min = usize::MAX;
            for (r0, fil) in self.obligations(set) {
                let succ = self.build_succ(set, r0, fil);
                let (sat, bl) = self.sat_seed(&succ);
                block_min = block_min.min(bl);
                if !sat {
                    let (c, t) = self.succ_conflict(set, cdep, tlits, r0, fil);
                    self.note_conflict(c.len());
                    return Err(SearchErr::Conflict(c, t));
                }
            }
        }
        let (guard, disj, from_imposed) = match self.first_disj(set, &key.imposed) {
            Some(gd) => gd,
            None => {
                // propositionally complete: every ∃-obligation's successor must
                // be satisfiable (checked here when eager pruning is off).
                if !self.eager {
                    for (r0, fil) in self.obligations(set) {
                        let succ = self.build_succ(set, r0, fil);
                        let (sat, bl) = self.sat_seed(&succ);
                        block_min = block_min.min(bl);
                        if !sat {
                            let (c, t) = self.succ_conflict(set, cdep, tlits, r0, fil);
                            self.note_conflict(c.len());
                            return Err(SearchErr::Conflict(c, t));
                        }
                    }
                }
                return Ok(block_min); // complete; all successors satisfiable
            }
        };
        self.n_branch += 1;
        if self.stats && self.n_branch % 2_000_000 == 0 {
            eprintln!(
                "KM_TAB_STATS cache: branches={} seeds={} cache={} stack={} nogoods={} nghit={}",
                self.n_branch,
                self.n_seed,
                self.cache.len(),
                self.stack.len(),
                self.nogoods.len(),
                self.n_nghit
            );
        }
        // a conflict derived under this disjunction is node-specific iff the
        // disjunction is imposed or fires off an imposed-derived guard literal.
        let disj_ctx_tainted = from_imposed || guard.iter().any(|l| tlits.contains(l));
        // the disjunction fires because of its guard; that is part of the conflict.
        let mut accum = union_reasons(&guard, cdep);
        let mut node_tainted = disj_ctx_tainted;
        // semantic branching (KM_TAB_SEMBR): ¬d literals asserted for this node's
        // remaining siblings once disjunct d is refuted. Undone when the node fails.
        let mut node_trail: Vec<CLit> = Vec::new();
        for d in self.order_disj(set, disj) {
            // assert `d` and Horn-close, recording every literal added on a trail
            // so the branch can be undone without cloning `set` / `cdep` / `tlits`.
            let mut trail: Vec<CLit> = Vec::new();
            if set.insert(d) {
                cdep.insert(d, vec![d]);
                trail.push(d);
            }
            let mut ctaint = false;
            let conf = match self.close_dep(set, cdep, &key.imposed, &mut trail, tlits, &mut ctaint)
            {
                Some(c) => Some(c),
                None => {
                    // the child step is dirty iff it added a trigger literal.
                    let child_dirty = trail.iter().any(|l| self.prog.trigger_lits.contains(l));
                    match self.local_search(key, set, cdep, tlits, child_dirty, block_min) {
                        // model found; leave `set` as is. Propagate the shallowest
                        // blocker level seen (this branch and the eager check).
                        Ok(bl) => {
                            // this disjunct completed a model: remember its phase.
                            self.save_phase(d);
                            return Ok(bl.min(block_min));
                        }
                        // restart armed: undo this branch and propagate upward so the
                        // enclosing `sat_seed` re-enters from the seed base.
                        Err(SearchErr::Restart) => {
                            for l in trail.iter().chain(node_trail.iter()) {
                                set.remove(l);
                                cdep.remove(l);
                                tlits.remove(l);
                            }
                            return Err(SearchErr::Restart);
                        }
                        Err(SearchErr::Conflict(c, t)) => {
                            ctaint = t;
                            Some(c)
                        }
                    }
                }
            };
            // undo this branch's additions before trying the next disjunct.
            for l in &trail {
                set.remove(l);
                cdep.remove(l);
                tlits.remove(l);
            }
            let conf = conf.unwrap();
            // VSIDS: this branch clashed — reward the literals responsible.
            self.act_bump_reason(&conf);
            let branch_taint = ctaint || disj_ctx_tainted;
            if conf.binary_search(&d).is_err() {
                // `d` is irrelevant to this clash — every sibling clashes the same
                // way. Backjump past the whole disjunction.
                for l in &node_trail {
                    set.remove(l);
                    cdep.remove(l);
                    tlits.remove(l);
                }
                self.note_conflict(conf.len());
                return Err(SearchErr::Conflict(conf, branch_taint));
            }
            node_tainted |= ctaint;
            for &x in &conf {
                if x != d {
                    merge_into(&mut accum, &[x]);
                }
            }
            // semantic branching: `d` is relevant to its clash and its subtree had
            // no model, so every model of this node's context has `¬d`. Assert it
            // for the remaining siblings (the next disjuncts' close_dep then
            // propagates its Horn consequences and clashes earlier). Reason = the
            // source literals (other than `d`) that refuted `d`, so `¬d` resolves
            // correctly in later conflict analysis; tainted iff that refutation was
            // node-specific (so downstream derivations from it stay node-local).
            if self.sembr {
                let nd = d.complement();
                if !set.contains(&nd) {
                    let mut ndr: Vec<CLit> = conf.iter().copied().filter(|&x| x != d).collect();
                    ndr.sort_unstable();
                    ndr.dedup();
                    set.insert(nd);
                    cdep.insert(nd, ndr);
                    if branch_taint {
                        tlits.insert(nd);
                    }
                    node_trail.push(nd);
                }
            }
        }
        // every disjunct failed: `accum` is this node's clash reason. Undo the
        // semantic-branching ¬d literals before unwinding (the node has no model).
        for l in &node_trail {
            set.remove(l);
            cdep.remove(l);
            tlits.remove(l);
        }
        // Learn it as a global no-good only if its derivation never used an imposed
        // (node-specific) clause; otherwise it holds only under this node's
        // constraints.
        if !node_tainted {
            self.learn(&accum);
        }
        // VSIDS: age activity once per resolved node conflict.
        self.act_decay_step();
        self.note_conflict(accum.len());
        Err(SearchErr::Conflict(accum, node_tainted))
    }

    /// Find one model of `key` and return its completed root concept set (for
    /// classify candidate extraction), or `None` if `key` is unsatisfiable.
    fn witness(&mut self, key: &CKey) -> Option<Vec<CLit>> {
        if let Some(&s) = self.cache.get(key) {
            if !s {
                return None;
            }
        }
        let mut set: HashSet<CLit> = key.base.iter().copied().collect();
        if self.close(&mut set, &key.imposed) {
            self.cache.insert(key.clone(), false);
            return None;
        }
        let mut curv: Vec<CLit> = set.iter().copied().collect();
        curv.sort_unstable();
        self.stack.push((key.clone(), curv));
        self.cond_at.push(Vec::new());
        let w = self.witness_rec(key, set);
        self.stack.pop();
        for k in self.cond_at.pop().into_iter().flatten() {
            self.cond.remove(&k);
        }
        w
    }

    fn witness_rec(&mut self, key: &CKey, set: HashSet<CLit>) -> Option<Vec<CLit>> {
        if self.has_nogood(&set) {
            return None;
        }
        for (r0, fil) in self.obligations(&set) {
            let succ = self.build_succ(&set, r0, fil);
            if !self.sat_seed(&succ).0 {
                return None;
            }
        }
        if let Some((_guard, disj, _imp)) = self.first_disj(&set, &key.imposed) {
            for d in disj {
                let mut s2 = set.clone();
                s2.insert(d);
                if self.close(&mut s2, &key.imposed) {
                    continue;
                }
                if let Some(w) = self.witness_rec(key, s2) {
                    return Some(w);
                }
            }
            return None;
        }
        Some(set.into_iter().collect())
    }
}

// ----------------------------- JSON driver --------------------------------

/// JSON atom: `{"k":"c","neg":b,"c":id,"t":var}` (concept), `{"k":"r","r":id,
/// "s":var,"t":var}` (role), `{"k":"e","r":id,"neg":b,"c":id,"t":var}` (∃ ≥1 R.B).
#[derive(Serialize, Deserialize)]
#[serde(tag = "k")]
pub enum JAtom {
    #[serde(rename = "c")]
    Concept { neg: bool, c: C, t: Var },
    #[serde(rename = "r")]
    Role { r: R, s: Var, t: Var },
    #[serde(rename = "e")]
    Exists { r: R, neg: bool, c: C, t: Var },
    #[serde(rename = "eq")]
    Eq { s: Var, t: Var },
}

#[derive(Serialize, Deserialize)]
pub struct JClause {
    pub body: Vec<JAtom>,
    pub head: Vec<JAtom>,
}

/// Input: integer-indexed clauses plus name tables and the named concepts to
/// classify. `concepts`/`roles` map id → IRI for output; `queries` are the named
/// concept ids to classify (default: all concepts).
#[derive(Deserialize)]
pub struct TInput {
    pub concepts: Vec<String>,
    pub roles: Vec<String>,
    pub clauses: Vec<JClause>,
    #[serde(default)]
    pub direct_projection_source: Option<Vec<crate::orchestrate::cb_to_ht::DirectProjectionClause>>,
    #[serde(default)]
    pub mixed_projection_source: Option<crate::orchestrate::cb_to_ht::MixedProjectionSource>,
    #[serde(default)]
    pub bundle_projection_source: Option<crate::orchestrate::cb_to_ht::BundleProjectionSource>,
    #[serde(default)]
    pub queries: Vec<C>,
    /// Converter omissions are part of the certification boundary. The
    /// ordinary measurement routes may defer around them, but a certified run
    /// must never treat the retained clause projection as the whole ontology.
    #[serde(default)]
    pub dropped: usize,
    #[serde(default)]
    pub fenced: Vec<serde_json::Value>,
    /// KB declares inverse roles ⇒ use pairwise blocking.
    #[serde(default)]
    pub inverse: bool,
    /// Source/RBox certificate that every number-role component is disjoint
    /// from inverse and non-simple roles.
    #[serde(default)]
    pub inverse_cardinality_role_separable: bool,
    /// KB has number restrictions / functional roles ⇒ merge-capable path +
    /// equality blocking.
    #[serde(default)]
    pub number: bool,
    /// Nominal concept ids (`__nom__a` proxies) ⇒ singleton o-rule + root
    /// seeding. Empty for nominal-free KBs (no behaviour change).
    #[serde(default)]
    pub nominals: Vec<C>,
    /// Complete numeric named-individual ABox produced by cb_to_ht.  Unknown
    /// fields used to be silently ignored here; retaining this typed field is
    /// what makes class/role assertions and DifferentIndividuals reach Ht.
    #[serde(default)]
    pub native_abox: crate::orchestrate::cb_to_ht::NativeAboxJson,
    /// KM_HT_CARD: first-class qualified number restrictions (marker → `≥n`/`≤n`).
    /// Empty for the clausal-pigeonhole path (no behaviour change).
    #[serde(default)]
    pub card_defs: Vec<JCardDef>,
    /// Exact-cardinality provenance checked at the source-projection boundary.
    #[serde(default)]
    pub cardinality_exact_pairs:
        Vec<crate::orchestrate::cb_to_ht::CardinalityExactPairJson>,
    #[serde(default)]
    pub cardinality_projection_complete: bool,
    /// KM_KEEP_CHAIN_AXIOMS: detected role chains (R1,R2,R) for R1∘R2⊑R, as side
    /// data (the raw axioms are excluded from `clauses` to avoid cb_to_ht bloat).
    /// Consumed by Ht::set_chains for the chain-unfolding ∀-propagation.
    #[serde(default)]
    pub chains: Vec<(C, C, C)>,
    /// KM_KEEP_CHAIN_AXIOMS: transitive roles (from R∘R⊑R axioms).
    #[serde(default)]
    pub transitive: Vec<C>,
}

/// KM_HT_CARD number restriction in the TInput (mirrors cb_to_ht::CardDefJson).
#[derive(Serialize, Deserialize)]
pub struct JCardDef {
    pub marker: C,
    pub min: bool,
    pub n: u32,
    pub role: R,
    pub filler: C,
    #[serde(default)]
    pub exact: bool,
}

#[derive(Serialize)]
pub struct TOutput {
    pub consistent: bool,
    pub unsatisfiable: Vec<String>,
    pub subsumptions: Vec<[String; 2]>,
}

/// Reconstruct the exact role-chain clauses removed from the ordinary clause
/// stream by `cb_to_ht`.  The Lean-certified path consumes these clauses
/// directly instead of relying on the optimized role-automaton side channel.
/// This keeps the certificate ontology equal to the source semantics: no
/// generated marker concept or unchecked compilation theorem is needed.
fn certified_role_chain_clauses(chains: &[(C, C, C)], transitive: &[C]) -> Vec<Clause> {
    let mut clauses = Vec::with_capacity(chains.len() + transitive.len());
    for &(first, second, head) in chains {
        clauses.push(Clause {
            body: vec![
                Atom::Role {
                    r: first,
                    s: X,
                    t: 1,
                },
                Atom::Role {
                    r: second,
                    s: 1,
                    t: 2,
                },
            ],
            head: vec![Atom::Role {
                r: head,
                s: X,
                t: 2,
            }],
        });
    }
    for &role in transitive {
        clauses.push(Clause {
            body: vec![
                Atom::Role {
                    r: role,
                    s: X,
                    t: 1,
                },
                Atom::Role {
                    r: role,
                    s: 1,
                    t: 2,
                },
            ],
            head: vec![Atom::Role {
                r: role,
                s: X,
                t: 2,
            }],
        });
    }
    clauses
}

fn atom_of(j: &JAtom) -> Atom {
    match *j {
        JAtom::Concept { neg, c, t } => Atom::Concept {
            lit: CLit { neg, c },
            t,
        },
        JAtom::Role { r, s, t } => Atom::Role { r, s, t },
        JAtom::Exists { r, neg, c, t } => Atom::Exists {
            r,
            fil: CLit { neg, c },
            t,
        },
        JAtom::Eq { s, t } => Atom::Eq { s, t },
    }
}

/// The KM_RULES_CONSISTENCY verdict for an already-parsed `TInput`: seed one
/// root per nominal (the rule route's `__nom__` ABox seeds), apply the o-rule,
/// and decide KB consistency on the default Tableau. Runs on a large stack
/// because the careful DFS can recurse deeply. Exposed separately from
/// `run_json` so the orchestrator's precheck contract is testable without the
/// env-var gate.
pub fn rules_consistency_verdict(inp: &TInput, ht_clauses: Vec<Clause>) -> Result<bool, String> {
    let inverse = inp.inverse;
    let number = inp.number || !inp.card_defs.is_empty();
    let noms = inp.nominals.clone();
    std::thread::Builder::new()
        .stack_size(4usize << 30)
        .spawn(move || {
            let mut t = Tableau::new(ht_clauses);
            t.set_pairwise(inverse);
            t.set_number(number);
            t.set_nominals(noms);
            t.consistent(&[])
        })
        .map_err(|e| e.to_string())?
        .join()
        .map_err(|_| "rules-consistency thread panicked".to_string())
}

/// Build the tableau clause vector from a parsed `TInput` (the deserialised
/// wire form the worker consumes).
pub fn clauses_of_tinput(inp: &TInput) -> Vec<Clause> {
    inp.clauses
        .iter()
        .map(|c| {
            Clause::new(
                c.body.iter().map(atom_of).collect(),
                c.head.iter().map(atom_of).collect(),
            )
        })
        .collect()
}

#[derive(Debug, Default)]
struct ValidatedNativeAbox {
    active: bool,
    individuals: Vec<(Vec<C>, Vec<C>)>,
    different: Vec<(usize, usize)>,
    role_assertions: Vec<(R, usize, usize)>,
    /// Exact negative-edge constraints reconstructed from the typed wire data
    /// when the producer-side guarded clause is absent. This makes the worker
    /// semantics independent of a redundant serialized clause.
    missing_negative_clauses: Vec<Clause>,
}

fn has_negative_edge_clash(inp: &TInput, role: R, source_proxy: C, target_proxy: C) -> bool {
    inp.clauses.iter().any(|clause| {
        matches!(
            (clause.body.as_slice(), clause.head.as_slice()),
            (
                [
                    JAtom::Concept { neg: false, c: source, t: 0 },
                    JAtom::Role { r, s: 0, t: 1 },
                    JAtom::Concept { neg: false, c: target, t: 1 },
                ],
                []
            ) if *source == source_proxy && *r == role && *target == target_proxy
        )
    })
}

/// Validate the complete producer-side native-ABox contract and convert its
/// usize wire ids to the compact worker ids. Every proxy has exactly one owner,
/// is in range, and is present in the nominal singleton set. Negative role
/// assertions are reconstructed as guarded clash clauses if the redundant
/// producer clause is missing, so this consumer never silently drops them.
fn validate_native_abox(inp: &TInput) -> Result<ValidatedNativeAbox, String> {
    use std::collections::HashSet;

    if inp.native_abox.is_empty() {
        return Ok(ValidatedNativeAbox::default());
    }
    if !inp.native_abox.complete {
        return Err("incomplete native ABox payload".to_string());
    }

    let nominal_set: HashSet<usize> = inp.nominals.iter().map(|&id| id as usize).collect();
    let mut proxy_owners = HashSet::new();
    let mut individuals = Vec::with_capacity(inp.native_abox.individuals.len());
    for individual in &inp.native_abox.individuals {
        if individual.proxies.is_empty() {
            return Err("native ABox individual has no singleton proxy".to_string());
        }
        let mut proxies = Vec::with_capacity(individual.proxies.len());
        for &id in &individual.proxies {
            if id >= inp.concepts.len() {
                return Err("native ABox concept id out of range".to_string());
            }
            if !nominal_set.contains(&id) {
                return Err("native ABox proxy is absent from nominals".to_string());
            }
            if !proxy_owners.insert(id) {
                return Err("native ABox proxy has duplicate ownership".to_string());
            }
            proxies
                .push(C::try_from(id).map_err(|_| "native ABox concept id overflow".to_string())?);
        }
        let mut assertions = Vec::with_capacity(individual.assertions.len());
        for &id in &individual.assertions {
            if id >= inp.concepts.len() {
                return Err("native ABox assertion id out of range".to_string());
            }
            assertions.push(
                C::try_from(id).map_err(|_| "native ABox assertion id overflow".to_string())?,
            );
        }
        individuals.push((proxies, assertions));
    }
    if proxy_owners != nominal_set {
        return Err(
            "native ABox does not assign every nominal proxy to exactly one individual"
                .to_string(),
        );
    }

    let in_individual_range =
        |left: usize, right: usize| left < individuals.len() && right < individuals.len();
    if inp
        .native_abox
        .different
        .iter()
        .any(|&(left, right)| !in_individual_range(left, right))
    {
        return Err("native ABox individual index out of range".to_string());
    }

    let resolve_role = |role: usize, source: usize, target: usize| -> Result<R, String> {
        if role >= inp.roles.len() || !in_individual_range(source, target) {
            return Err("native ABox role/individual index out of range".to_string());
        }
        R::try_from(role).map_err(|_| "native ABox role id overflow".to_string())
    };
    let mut role_assertions = Vec::with_capacity(inp.native_abox.role_assertions.len());
    for &(role, source, target) in &inp.native_abox.role_assertions {
        role_assertions.push((resolve_role(role, source, target)?, source, target));
    }

    let mut missing_negative_clauses = Vec::new();
    for &(role, source, target) in &inp.native_abox.negative_role_assertions {
        let role = resolve_role(role, source, target)?;
        let source_proxy = individuals[source].0[0];
        let target_proxy = individuals[target].0[0];
        if !has_negative_edge_clash(inp, role, source_proxy, target_proxy) {
            missing_negative_clauses.push(Clause::new(
                vec![
                    Atom::Concept {
                        lit: CLit::pos(source_proxy),
                        t: 0,
                    },
                    Atom::Role {
                        r: role,
                        s: 0,
                        t: 1,
                    },
                    Atom::Concept {
                        lit: CLit::pos(target_proxy),
                        t: 1,
                    },
                ],
                Vec::new(),
            ));
        }
    }

    Ok(ValidatedNativeAbox {
        active: !individuals.is_empty(),
        individuals,
        different: inp.native_abox.different.clone(),
        role_assertions,
        missing_negative_clauses,
    })
}

/// Read a `TInput` JSON string, classify, and return a `TOutput` JSON string.
pub fn run_json(input: &str) -> Result<String, String> {
    run_json_inner(input, None)
}

/// Read the global consistency verdict carried by a checker-ready HT
/// certificate. This does not replace the Lean checker. It prevents the caller
/// from publishing a separate Rust Boolean that disagrees with the evidence
/// which the checker accepted.
fn certified_ht_global_consistency(document: &serde_json::Value) -> Result<bool, String> {
    let version = document.get("version").and_then(serde_json::Value::as_u64);
    if matches!(version, Some(3 | 4)) {
        let payload = document
            .get("payload")
            .and_then(serde_json::Value::as_object)
            .ok_or_else(|| "normalized HT certificate omitted its payload".to_string())?;
        let mut certificates = ["plain", "equality", "cardinality", "regular"]
            .into_iter()
            .filter_map(|kind| payload.get(kind)?.get("certificate"));
        let certificate = certificates.next().ok_or_else(|| {
            "normalized HT certificate has no global evidence payload".to_string()
        })?;
        if certificates.next().is_some() {
            return Err("normalized HT certificate has multiple global evidence payloads".into());
        }
        return certified_ht_global_consistency(certificate);
    }
    // Version 5 is the SAT-only normalized anchored equality format. Its Lean
    // checker constructs a nonempty source model and has no UNSAT constructor.
    if version == Some(5) {
        if !document
            .get("certificate")
            .is_some_and(serde_json::Value::is_object)
        {
            return Err("normalized anchored HT certificate omitted its certificate".into());
        }
        return Ok(true);
    }
    // Cardinality version 2 wraps equality evidence in `certificate`.
    if document.get("definitions").is_some() {
        return certified_ht_global_consistency(
            document
                .get("certificate")
                .ok_or_else(|| "cardinality HT certificate omitted its evidence".to_string())?,
        );
    }
    let evidence = document
        .get("evidence")
        .ok_or_else(|| "HT certificate omitted global evidence".to_string())?;
    if evidence == "sat" {
        return Ok(true);
    }
    let evidence = evidence
        .as_object()
        .ok_or_else(|| "HT certificate has a non-global evidence tag".to_string())?;
    let sat = evidence.contains_key("regular_sat")
        || evidence.contains_key("finite_sat")
        || evidence.contains_key("sat");
    let unsat = evidence.contains_key("unsat") || evidence.contains_key("finite_unsat");
    match (sat, unsat) {
        (true, false) => Ok(true),
        (false, true) => Ok(false),
        _ => Err("HT certificate has ambiguous or non-global evidence".to_string()),
    }
}

#[derive(Serialize)]
struct DirectProjectionLit {
    concept: usize,
    neg: bool,
}

#[derive(Serialize)]
#[serde(rename_all = "snake_case")]
enum DirectProjectionTargetAtom {
    Concept {
        literal: DirectProjectionLit,
        node: usize,
    },
    Role {
        role: usize,
        source: usize,
        target: usize,
    },
    Exists_ {
        role: usize,
        filler: DirectProjectionLit,
        node: usize,
    },
    Eq {
        left: usize,
        right: usize,
    },
}

#[derive(Serialize)]
struct DirectProjectionTargetClause {
    body: Vec<DirectProjectionTargetAtom>,
    head: Vec<DirectProjectionTargetAtom>,
}

#[derive(Serialize)]
struct DirectProjectionDocument<'a> {
    variable_count: usize,
    concepts: &'a [String],
    roles: &'a [String],
    source: &'a [crate::orchestrate::cb_to_ht::DirectProjectionClause],
    target: Vec<DirectProjectionTargetClause>,
}

#[derive(Serialize)]
struct MixedProjectionDocument<'a> {
    variable_count: usize,
    concepts: &'a [String],
    roles: &'a [String],
    functions: &'a [String],
    direct: &'a [crate::orchestrate::cb_to_ht::DirectProjectionClause],
    pairs: &'a [crate::orchestrate::cb_to_ht::SkolemProjectionPair],
    target: Vec<DirectProjectionTargetClause>,
}

#[derive(Serialize)]
struct BundleProjectionDocument<'a> {
    variable_count: usize,
    source_concepts: &'a [String],
    concepts: &'a [String],
    roles: &'a [String],
    functions: &'a [String],
    direct: &'a [crate::orchestrate::cb_to_ht::DirectProjectionClause],
    bundles: &'a [crate::orchestrate::cb_to_ht::SkolemProjectionBundle],
    domain_extras: &'a [crate::orchestrate::cb_to_ht::BundleProjectionDomainExtra],
    target: Vec<DirectProjectionTargetClause>,
}

#[derive(Serialize)]
struct DirectCardinalityProjectionDocument<'a> {
    variable_count: usize,
    concepts: &'a [String],
    roles: &'a [String],
    source: &'a [crate::orchestrate::cb_to_ht::DirectProjectionClause],
    target: Vec<DirectProjectionTargetClause>,
    definitions: &'a [JCardDef],
    exact_pairs: &'a [crate::orchestrate::cb_to_ht::CardinalityExactPairJson],
}

#[derive(Serialize)]
struct BundleCardinalityProjectionDocument<'a> {
    bundle: BundleProjectionDocument<'a>,
    definitions: Vec<JCardDef>,
    exact_pairs: &'a [crate::orchestrate::cb_to_ht::CardinalityExactPairJson],
}

#[derive(Serialize)]
struct MixedCardinalityProjectionDocument<'a> {
    mixed: MixedProjectionDocument<'a>,
    definitions: &'a [JCardDef],
    exact_pairs: &'a [crate::orchestrate::cb_to_ht::CardinalityExactPairJson],
}

#[derive(Serialize)]
struct NativeAboxProjectionDocument<'a> {
    complete: bool,
    concepts: &'a [String],
    roles: &'a [String],
    nominals: &'a [C],
    individuals: &'a [crate::orchestrate::cb_to_ht::NativeIndividualJson],
    different: &'a [(usize, usize)],
    role_assertions: &'a [(usize, usize, usize)],
    negative_role_assertions: &'a [(usize, usize, usize)],
}

fn bundle_cardinality_definitions(
    inp: &TInput,
    source: &crate::orchestrate::cb_to_ht::BundleProjectionSource,
) -> Result<Vec<JCardDef>, String> {
    let source_index = |target: C, kind: &str| -> Result<C, String> {
        let name = inp
            .concepts
            .get(target as usize)
            .ok_or_else(|| format!("HT cardinality {kind} index is out of range"))?;
        let index = source
            .source_concepts
            .iter()
            .position(|candidate| candidate == name)
            .ok_or_else(|| format!("HT cardinality {kind} is absent from bundle source concepts"))?;
        C::try_from(index).map_err(|_| format!("HT cardinality {kind} source index overflow"))
    };
    inp.card_defs
        .iter()
        .map(|definition| {
            Ok(JCardDef {
                marker: source_index(definition.marker, "marker")?,
                min: definition.min,
                n: definition.n,
                role: definition.role,
                filler: source_index(definition.filler, "filler")?,
                exact: definition.exact,
            })
        })
        .collect()
}

fn direct_projection_target_atom(atom: &Atom) -> DirectProjectionTargetAtom {
    match *atom {
        Atom::Concept { lit, t } => DirectProjectionTargetAtom::Concept {
            literal: DirectProjectionLit {
                concept: lit.c as usize,
                neg: lit.neg,
            },
            node: t as usize,
        },
        Atom::Role { r, s, t } => DirectProjectionTargetAtom::Role {
            role: r as usize,
            source: s as usize,
            target: t as usize,
        },
        Atom::Exists { r, fil, t } => DirectProjectionTargetAtom::Exists_ {
            role: r as usize,
            filler: DirectProjectionLit {
                concept: fil.c as usize,
                neg: fil.neg,
            },
            node: t as usize,
        },
        Atom::Eq { s, t } => DirectProjectionTargetAtom::Eq {
            left: s as usize,
            right: t as usize,
        },
    }
}

fn direct_projection_target_clause(clause: &Clause) -> DirectProjectionTargetClause {
    DirectProjectionTargetClause {
        body: clause
            .body
            .iter()
            .map(direct_projection_target_atom)
            .collect(),
        head: clause
            .head
            .iter()
            .map(direct_projection_target_atom)
            .collect(),
    }
}

fn direct_projection_variable_count(clauses: &[Clause]) -> usize {
    clauses
        .iter()
        .map(|clause| {
            clause
                .body
                .iter()
                .chain(&clause.head)
                .map(|atom| match atom {
                    Atom::Concept { t, .. } | Atom::Exists { t, .. } => *t as usize,
                    Atom::Role { s, t, .. } | Atom::Eq { s, t } => (*s).max(*t) as usize,
                })
                .max()
                .unwrap_or(0)
                + 1
        })
        .max()
        .unwrap_or(0)
}

static HT_PROJECTION_TEMP_SEQUENCE: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

fn run_ht_projection_checker(
    encoded: &[u8],
    checker: &std::path::Path,
    document_kind: &str,
) -> Result<(), String> {
    let sequence = HT_PROJECTION_TEMP_SEQUENCE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "km-ht-{document_kind}-projection-{}-{sequence}.json",
        std::process::id()
    ));
    std::fs::write(&path, encoded)
        .map_err(|error| format!("cannot write HT {document_kind} projection: {error}"))?;
    let status = std::process::Command::new(checker)
        .arg(&path)
        .stdout(std::process::Stdio::null())
        .status()
        .map_err(|error| {
            format!(
                "cannot execute HT projection checker {}: {error}",
                checker.display()
            )
        });
    let _ = std::fs::remove_file(&path);
    let status = status?;
    if !status.success() {
        return Err(format!(
            "HT {document_kind} projection checker {} rejected the conversion ({status})",
            checker.display()
        ));
    }
    Ok(())
}

fn check_native_abox_projection(
    inp: &TInput,
    checker: &std::path::Path,
) -> Result<(), String> {
    let encoded = serde_json::to_vec(&NativeAboxProjectionDocument {
        complete: inp.native_abox.complete,
        concepts: &inp.concepts,
        roles: &inp.roles,
        nominals: &inp.nominals,
        individuals: &inp.native_abox.individuals,
        different: &inp.native_abox.different,
        role_assertions: &inp.native_abox.role_assertions,
        negative_role_assertions: &inp.native_abox.negative_role_assertions,
    })
    .map_err(|error| format!("cannot encode HT native ABox projection: {error}"))?;
    run_ht_projection_checker(&encoded, checker, "native-abox")
}

fn native_abox_refutation_value(
    inp: &TInput,
    normalized_refutation: &str,
) -> Result<serde_json::Value, String> {
    let mut refutation: serde_json::Value = serde_json::from_str(normalized_refutation)
        .map_err(|error| format!("invalid normalized native ABox refutation: {error}"))?;
    let initial = refutation
        .get_mut("initial")
        .and_then(serde_json::Value::as_object_mut)
        .ok_or_else(|| "normalized native ABox refutation omitted its initial state".to_string())?;
    initial.insert(
        "abox".to_string(),
        serde_json::to_value(NativeAboxProjectionDocument {
            complete: inp.native_abox.complete,
            concepts: &inp.concepts,
            roles: &inp.roles,
            nominals: &inp.nominals,
            individuals: &inp.native_abox.individuals,
            different: &inp.native_abox.different,
            role_assertions: &inp.native_abox.role_assertions,
            negative_role_assertions: &inp.native_abox.negative_role_assertions,
        })
        .map_err(|error| format!("cannot encode joint native ABox payload: {error}"))?,
    );
    Ok(refutation)
}

fn direct_native_abox_refutation_document(
    inp: &TInput,
    normalized_refutation: &str,
) -> Result<Vec<u8>, String> {
    if !inp.card_defs.is_empty()
        || inp.bundle_projection_source.is_some()
        || inp.mixed_projection_source.is_some()
    {
        return Err(
            "joint direct native ABox refutation does not cover transformed source clauses"
                .to_string(),
        );
    }
    let source = inp.direct_projection_source.as_deref().ok_or_else(|| {
        "joint native ABox refutation has no complete direct source projection".to_string()
    })?;
    let refutation = native_abox_refutation_value(inp, normalized_refutation)?;
    serde_json::to_vec(&serde_json::json!({
        "source": source,
        "refutation": refutation,
    }))
    .map_err(|error| format!("cannot encode joint direct native ABox refutation: {error}"))
}

fn direct_native_abox_cardinality_refutation_document(
    inp: &TInput,
    clauses: &[Clause],
    normalized_refutation: &str,
) -> Result<Vec<u8>, String> {
    if inp.card_defs.is_empty()
        || inp.bundle_projection_source.is_some()
        || inp.mixed_projection_source.is_some()
    {
        return Err(
            "joint direct native ABox cardinality refutation requires only direct source projection"
                .to_string(),
        );
    }
    let source = inp.direct_projection_source.as_deref().ok_or_else(|| {
        "joint native ABox cardinality refutation has no complete direct source projection"
            .to_string()
    })?;
    let target = clauses
        .iter()
        .map(direct_projection_target_clause)
        .collect::<Vec<_>>();
    let refutation = native_abox_refutation_value(inp, normalized_refutation)?;
    serde_json::to_vec(&serde_json::json!({
        "source": source,
        "target": target,
        "definitions": &inp.card_defs,
        "exact_pairs": &inp.cardinality_exact_pairs,
        "refutation": refutation,
    }))
    .map_err(|error| {
        format!("cannot encode joint direct native ABox cardinality refutation: {error}")
    })
}

fn mixed_native_abox_refutation_document(
    inp: &TInput,
    normalized_refutation: &str,
) -> Result<Vec<u8>, String> {
    if !inp.card_defs.is_empty() || inp.bundle_projection_source.is_some() {
        return Err(
            "joint mixed native ABox refutation does not cover bundle or cardinality projection"
                .to_string(),
        );
    }
    let source = inp.mixed_projection_source.as_ref().ok_or_else(|| {
        "joint native ABox refutation has no complete mixed source projection".to_string()
    })?;
    let refutation = native_abox_refutation_value(inp, normalized_refutation)?;
    serde_json::to_vec(&serde_json::json!({
        "functions": &source.functions,
        "direct": &source.direct,
        "pairs": &source.pairs,
        "refutation": refutation,
    }))
    .map_err(|error| format!("cannot encode joint mixed native ABox refutation: {error}"))
}

fn mixed_native_abox_cardinality_refutation_document(
    inp: &TInput,
    normalized_refutation: &str,
) -> Result<Vec<u8>, String> {
    if inp.card_defs.is_empty() || inp.bundle_projection_source.is_some() {
        return Err(
            "joint mixed native ABox cardinality refutation does not cover bundle projection"
                .to_string(),
        );
    }
    let source = inp.mixed_projection_source.as_ref().ok_or_else(|| {
        "joint native ABox cardinality refutation has no complete mixed source projection"
            .to_string()
    })?;
    let refutation = native_abox_refutation_value(inp, normalized_refutation)?;
    serde_json::to_vec(&serde_json::json!({
        "functions": &source.functions,
        "direct": &source.direct,
        "pairs": &source.pairs,
        "definitions": &inp.card_defs,
        "exact_pairs": &inp.cardinality_exact_pairs,
        "refutation": refutation,
    }))
    .map_err(|error| {
        format!("cannot encode joint mixed native ABox cardinality refutation: {error}")
    })
}

fn bundle_native_abox_refutation_document(
    inp: &TInput,
    normalized_refutation: &str,
) -> Result<Vec<u8>, String> {
    if !inp.card_defs.is_empty() {
        return Err(
            "joint bundle native ABox refutation does not yet cover cardinality projection"
                .to_string(),
        );
    }
    let source = inp.bundle_projection_source.as_ref().ok_or_else(|| {
        "joint native ABox refutation has no complete bundle source projection".to_string()
    })?;
    if source.source_concepts.is_empty() {
        return Err("bundle native ABox projection has no source concepts".to_string());
    }
    let abox_source_map: Vec<usize> = inp
        .concepts
        .iter()
        .map(|target| {
            source
                .source_concepts
                .iter()
                .position(|candidate| candidate == target)
                .unwrap_or(0)
        })
        .collect();
    let refutation = native_abox_refutation_value(inp, normalized_refutation)?;
    serde_json::to_vec(&serde_json::json!({
        "source_concepts": &source.source_concepts,
        "functions": &source.functions,
        "direct": &source.direct,
        "bundles": &source.bundles,
        "domain_extras": &source.domain_extras,
        "abox_source_map": abox_source_map,
        "refutation": refutation,
    }))
    .map_err(|error| format!("cannot encode joint bundle native ABox refutation: {error}"))
}

fn bundle_native_abox_cardinality_refutation_document(
    inp: &TInput,
    normalized_refutation: &str,
) -> Result<Vec<u8>, String> {
    if inp.card_defs.is_empty() {
        return Err(
            "joint bundle native ABox cardinality refutation requires cardinality definitions"
                .to_string(),
        );
    }
    let source = inp.bundle_projection_source.as_ref().ok_or_else(|| {
        "joint native ABox cardinality refutation has no complete bundle source projection"
            .to_string()
    })?;
    if source.source_concepts.is_empty() {
        return Err("bundle native ABox projection has no source concepts".to_string());
    }
    let abox_source_map: Vec<usize> = inp
        .concepts
        .iter()
        .map(|target| {
            source
                .source_concepts
                .iter()
                .position(|candidate| candidate == target)
                .unwrap_or(0)
        })
        .collect();
    let definitions = bundle_cardinality_definitions(inp, source)?;
    let refutation = native_abox_refutation_value(inp, normalized_refutation)?;
    serde_json::to_vec(&serde_json::json!({
        "source_concepts": &source.source_concepts,
        "functions": &source.functions,
        "direct": &source.direct,
        "bundles": &source.bundles,
        "domain_extras": &source.domain_extras,
        "definitions": definitions,
        "exact_pairs": &inp.cardinality_exact_pairs,
        "abox_source_map": abox_source_map,
        "refutation": refutation,
    }))
    .map_err(|error| {
        format!("cannot encode joint bundle native ABox cardinality refutation: {error}")
    })
}

fn native_abox_source_map(
    inp: &TInput,
    source_concepts: &[String],
) -> Result<Vec<usize>, String> {
    if source_concepts.is_empty() {
        return Err("bundle native ABox projection has no source concepts".to_string());
    }
    inp.concepts
        .iter()
        .map(|target| {
            Ok(source_concepts
                .iter()
                .position(|candidate| candidate == target)
                // Definer-only target concepts have no source counterpart. The
                // Lean checker requires exact round-tripping for every concept
                // that actually occurs in the native ABox.
                .unwrap_or(0))
        })
        .collect()
}

/// Bind one checked native-ABox verdict to the exact source projection used to
/// create its HT ontology.  The resulting document is checked by a theorem
/// whose conclusion is SAT/UNSAT of the source theory, rather than by two
/// independent checks with an unproved relationship between their payloads.
fn native_abox_source_decision_document(
    inp: &TInput,
    clauses: &[Clause],
    normalized_decision: &str,
    consistent: bool,
) -> Result<Vec<u8>, String> {
    let decision: serde_json::Value = serde_json::from_str(normalized_decision)
        .map_err(|error| format!("invalid normalized native ABox decision: {error}"))?;
    let evidence = decision
        .get("evidence")
        .and_then(serde_json::Value::as_object)
        .ok_or_else(|| "normalized native ABox decision omitted its evidence".to_string())?;
    let (tag, target_key, mut target_value) = if consistent {
        let value = evidence
            .get("sat")
            .and_then(|sat| sat.get("certificate"))
            .cloned()
            .ok_or_else(|| {
                "consistent native ABox decision omitted its SAT certificate".to_string()
            })?;
        ("sat", "certificate", value)
    } else {
        let value = evidence
            .get("unsat")
            .and_then(|unsat| unsat.get("refutation"))
            .cloned()
            .ok_or_else(|| {
                "inconsistent native ABox decision omitted its UNSAT refutation".to_string()
            })?;
        ("unsat", "refutation", value)
    };
    let seed = if consistent {
        target_value.get_mut("seed")
    } else {
        target_value.get_mut("initial")
    }
    .and_then(serde_json::Value::as_object_mut)
    .ok_or_else(|| "native ABox source decision omitted its seed".to_string())?;
    seed.insert(
        "abox".to_string(),
        serde_json::to_value(NativeAboxProjectionDocument {
            complete: inp.native_abox.complete,
            concepts: &inp.concepts,
            roles: &inp.roles,
            nominals: &inp.nominals,
            individuals: &inp.native_abox.individuals,
            different: &inp.native_abox.different,
            role_assertions: &inp.native_abox.role_assertions,
            negative_role_assertions: &inp.native_abox.negative_role_assertions,
        })
        .map_err(|error| format!("cannot encode source-decision native ABox: {error}"))?,
    );

    let payload = if let Some(source) = inp.bundle_projection_source.as_ref() {
        if source.source_concepts.is_empty() {
            return Err("bundle native ABox projection has no source concepts".to_string());
        }
        let mut payload = serde_json::json!({
            "source_concepts": &source.source_concepts,
            "functions": &source.functions,
            "direct": &source.direct,
            "bundles": &source.bundles,
            "domain_extras": &source.domain_extras,
            "abox_source_map": native_abox_source_map(inp, &source.source_concepts)?,
        });
        if !inp.card_defs.is_empty() {
            payload["definitions"] =
                serde_json::to_value(bundle_cardinality_definitions(inp, source)?)
                    .map_err(|error| format!("cannot encode bundle cardinality definitions: {error}"))?;
            payload["exact_pairs"] = serde_json::to_value(&inp.cardinality_exact_pairs)
                .map_err(|error| format!("cannot encode bundle exact pairs: {error}"))?;
        }
        payload[target_key] = target_value;
        payload
    } else if let Some(source) = inp.mixed_projection_source.as_ref() {
        let mut payload = serde_json::json!({
            "functions": &source.functions,
            "direct": &source.direct,
            "pairs": &source.pairs,
        });
        if !inp.card_defs.is_empty() {
            payload["definitions"] = serde_json::to_value(&inp.card_defs)
                .map_err(|error| format!("cannot encode mixed cardinality definitions: {error}"))?;
            payload["exact_pairs"] = serde_json::to_value(&inp.cardinality_exact_pairs)
                .map_err(|error| format!("cannot encode mixed exact pairs: {error}"))?;
        }
        payload[target_key] = target_value;
        payload
    } else {
        let source = inp.direct_projection_source.as_deref().ok_or_else(|| {
            "native ABox decision has no complete source projection".to_string()
        })?;
        let mut payload = serde_json::json!({ "source": source });
        if !inp.card_defs.is_empty() {
            payload["target"] = serde_json::to_value(
                clauses.iter().map(direct_projection_target_clause).collect::<Vec<_>>(),
            )
            .map_err(|error| format!("cannot encode direct cardinality target: {error}"))?;
            payload["definitions"] = serde_json::to_value(&inp.card_defs)
                .map_err(|error| format!("cannot encode direct cardinality definitions: {error}"))?;
            payload["exact_pairs"] = serde_json::to_value(&inp.cardinality_exact_pairs)
                .map_err(|error| format!("cannot encode direct exact pairs: {error}"))?;
        }
        payload[target_key] = target_value;
        payload
    };
    let mut constructor = serde_json::Map::new();
    constructor.insert(target_key.to_string(), payload);
    let mut evidence = serde_json::Map::new();
    evidence.insert(tag.to_string(), serde_json::Value::Object(constructor));
    serde_json::to_vec(&serde_json::json!({
        "version": 1,
        "evidence": evidence,
    }))
    .map_err(|error| format!("cannot encode source-composed native ABox decision: {error}"))
}

fn native_abox_source_taxonomy_document(
    inp: &TInput,
    clauses: &[Clause],
    normalized_taxonomy: &str,
) -> Result<Vec<u8>, String> {
    let mut matrix: serde_json::Value = serde_json::from_str(normalized_taxonomy)
        .map_err(|error| format!("invalid normalized native ABox taxonomy: {error}"))?;
    let abox = serde_json::to_value(NativeAboxProjectionDocument {
        complete: inp.native_abox.complete,
        concepts: &inp.concepts,
        roles: &inp.roles,
        nominals: &inp.nominals,
        individuals: &inp.native_abox.individuals,
        different: &inp.native_abox.different,
        role_assertions: &inp.native_abox.role_assertions,
        negative_role_assertions: &inp.native_abox.negative_role_assertions,
    })
    .map_err(|error| format!("cannot encode taxonomy native ABox: {error}"))?;

    let mut replace_cell_abox = |cell: &mut serde_json::Value| -> Result<(), String> {
        let evidence = cell
            .get_mut("evidence")
            .and_then(serde_json::Value::as_object_mut)
            .ok_or_else(|| "native ABox taxonomy cell omitted evidence".to_string())?;
        let seed = if let Some(sat) = evidence.get_mut("sat") {
            sat.get_mut("certificate").and_then(|certificate| certificate.get_mut("seed"))
        } else if let Some(unsat) = evidence.get_mut("unsat") {
            unsat.get_mut("initial")
        } else {
            None
        }
        .and_then(serde_json::Value::as_object_mut)
        .ok_or_else(|| "native ABox taxonomy cell omitted its finite seed".to_string())?;
        seed.insert("abox".to_string(), abox.clone());
        Ok(())
    };
    for cell in matrix
        .get_mut("concepts")
        .and_then(serde_json::Value::as_array_mut)
        .ok_or_else(|| "native ABox taxonomy omitted concept cells".to_string())?
    {
        replace_cell_abox(cell)?;
    }
    for row in matrix
        .get_mut("subsumptions")
        .and_then(serde_json::Value::as_array_mut)
        .ok_or_else(|| "native ABox taxonomy omitted subsumption rows".to_string())?
    {
        for cell in row
            .as_array_mut()
            .ok_or_else(|| "native ABox taxonomy subsumption row is not an array".to_string())?
        {
            replace_cell_abox(cell)?;
        }
    }
    let payload = if !inp.card_defs.is_empty() {
        if let Some(source) = inp.bundle_projection_source.as_ref() {
            serde_json::json!({
                "version": 1,
                "projection": {
                    "source_concepts": &source.source_concepts,
                    "functions": &source.functions,
                    "direct": &source.direct,
                    "bundles": &source.bundles,
                    "domain_extras": &source.domain_extras,
                    "definitions": bundle_cardinality_definitions(inp, source)?,
                    "exact_pairs": &inp.cardinality_exact_pairs,
                    "abox_source_map": native_abox_source_map(inp, &source.source_concepts)?,
                },
                "matrix": matrix,
            })
        } else if let Some(source) = inp.mixed_projection_source.as_ref() {
            serde_json::json!({
                "version": 1,
                "projection": {
                    "functions": &source.functions,
                    "direct": &source.direct,
                    "pairs": &source.pairs,
                    "definitions": &inp.card_defs,
                    "exact_pairs": &inp.cardinality_exact_pairs,
                },
                "matrix": matrix,
            })
        } else {
            let source = inp.direct_projection_source.as_deref().ok_or_else(|| {
                "native ABox cardinality taxonomy has no complete direct source projection"
                    .to_string()
            })?;
            serde_json::json!({
                "version": 1,
                "projection": {
                    "source": source,
                    "target": clauses.iter().map(direct_projection_target_clause)
                        .collect::<Vec<_>>(),
                    "definitions": &inp.card_defs,
                    "exact_pairs": &inp.cardinality_exact_pairs,
                },
                "matrix": matrix,
            })
        }
    } else if let Some(source) = inp.bundle_projection_source.as_ref() {
        serde_json::json!({
            "version": 1,
            "source_concepts": &source.source_concepts,
            "functions": &source.functions,
            "direct": &source.direct,
            "bundles": &source.bundles,
            "domain_extras": &source.domain_extras,
            "abox_source_map": native_abox_source_map(inp, &source.source_concepts)?,
            "matrix": matrix,
        })
    } else if let Some(source) = inp.mixed_projection_source.as_ref() {
        serde_json::json!({
            "version": 1,
            "functions": &source.functions,
            "direct": &source.direct,
            "pairs": &source.pairs,
            "matrix": matrix,
        })
    } else {
        let source = inp.direct_projection_source.as_deref().ok_or_else(|| {
            "native ABox taxonomy has no complete direct source projection".to_string()
        })?;
        serde_json::json!({
            "version": 1,
            "source": source,
            "matrix": matrix,
        })
    };
    serde_json::to_vec(&payload)
    .map_err(|error| format!("cannot encode source-composed native ABox taxonomy: {error}"))
}

fn native_abox_source_constructor(inp: &TInput) -> &'static str {
    if inp.bundle_projection_source.is_some() {
        "bundle"
    } else if inp.mixed_projection_source.is_some() {
        "mixed"
    } else {
        "direct"
    }
}

fn source_bound_native_abox_document(
    inp: &TInput,
    source_document: &[u8],
    production_key: &str,
    mut production: serde_json::Value,
) -> Result<Vec<u8>, String> {
    let source: serde_json::Value = serde_json::from_slice(source_document)
        .map_err(|error| format!("invalid native ABox source document: {error}"))?;
    if production_key == "run" {
        let evidence = source
            .get("evidence")
            .and_then(serde_json::Value::as_object)
            .ok_or_else(|| "native ABox source decision omitted evidence".to_string())?;
        let target = if let Some(sat) = evidence.get("sat") {
            let certificate = sat
                .get("certificate")
                .and_then(|payload| payload.get("certificate"))
                .cloned()
                .ok_or_else(|| "native ABox source SAT decision omitted target".to_string())?;
            serde_json::json!({
                "version": source.get("version").cloned().unwrap_or_else(|| serde_json::json!(1)),
                "evidence": { "sat": { "certificate": certificate } },
            })
        } else if let Some(unsat) = evidence.get("unsat") {
            let refutation = unsat
                .get("refutation")
                .and_then(|payload| payload.get("refutation"))
                .cloned()
                .ok_or_else(|| "native ABox source UNSAT decision omitted target".to_string())?;
            serde_json::json!({
                "version": source.get("version").cloned().unwrap_or_else(|| serde_json::json!(1)),
                "evidence": { "unsat": { "refutation": refutation } },
            })
        } else {
            return Err("native ABox source decision has no SAT or UNSAT branch".to_string());
        };
        production["terminal"] = target;
    } else if production_key == "runs" {
        let matrix = source
            .get("matrix")
            .and_then(serde_json::Value::as_object)
            .ok_or_else(|| "native ABox source taxonomy omitted its target matrix".to_string())?;
        let concepts = matrix
            .get("concepts")
            .and_then(serde_json::Value::as_array)
            .ok_or_else(|| "native ABox source taxonomy omitted concept cells".to_string())?;
        let concept_runs = production
            .get_mut("concept_runs")
            .and_then(serde_json::Value::as_array_mut)
            .ok_or_else(|| "native ABox run matrix omitted concept runs".to_string())?;
        if concept_runs.len() != concepts.len() {
            return Err("native ABox source taxonomy and run matrix concept lengths differ".to_string());
        }
        for (run, terminal) in concept_runs.iter_mut().zip(concepts) {
            run["terminal"] = terminal.clone();
        }
        let subsumptions = matrix
            .get("subsumptions")
            .and_then(serde_json::Value::as_array)
            .ok_or_else(|| "native ABox source taxonomy omitted subsumption rows".to_string())?;
        let subsumption_runs = production
            .get_mut("subsumption_runs")
            .and_then(serde_json::Value::as_array_mut)
            .ok_or_else(|| "native ABox run matrix omitted subsumption runs".to_string())?;
        if subsumption_runs.len() != subsumptions.len() {
            return Err("native ABox source taxonomy and run matrix row counts differ".to_string());
        }
        for (run_row, terminal_row) in subsumption_runs.iter_mut().zip(subsumptions) {
            let run_row = run_row
                .as_array_mut()
                .ok_or_else(|| "native ABox run-matrix row is not an array".to_string())?;
            let terminal_row = terminal_row
                .as_array()
                .ok_or_else(|| "native ABox taxonomy row is not an array".to_string())?;
            if run_row.len() != terminal_row.len() {
                return Err("native ABox source taxonomy and run matrix row lengths differ".to_string());
            }
            for (run, terminal) in run_row.iter_mut().zip(terminal_row) {
                run["terminal"] = terminal.clone();
            }
        }
    }
    let mut constructor = serde_json::Map::new();
    constructor.insert("source".to_string(), source);
    let mut tagged = serde_json::Map::new();
    tagged.insert(
        native_abox_source_constructor(inp).to_string(),
        serde_json::Value::Object(constructor),
    );
    let mut document = serde_json::Map::new();
    document.insert("version".to_string(), serde_json::json!(1));
    document.insert("source".to_string(), serde_json::Value::Object(tagged));
    document.insert(production_key.to_string(), production);
    serde_json::to_vec(&serde_json::Value::Object(document))
        .map_err(|error| format!("cannot encode source-bound native ABox document: {error}"))
}

/// Bind the global source decision and complete source taxonomy to one shared
/// source projection and one shared native ABox.  The existing decision,
/// matrix, source-decision, and source-taxonomy checks remain independent
/// prerequisites; this document adds the cross-document identity check.
fn native_abox_joint_source_classification_document(
    inp: &TInput,
    clauses: &[Clause],
    normalized_decision: &str,
    normalized_taxonomy: &str,
) -> Result<Vec<u8>, String> {
    let global: serde_json::Value = serde_json::from_str(normalized_decision)
        .map_err(|error| format!("invalid joint native ABox global decision: {error}"))?;
    if !global.is_object() {
        return Err("joint native ABox global decision is not an object".to_string());
    }
    let taxonomy: serde_json::Value = serde_json::from_str(normalized_taxonomy)
        .map_err(|error| format!("invalid joint native ABox taxonomy: {error}"))?;
    if !taxonomy.is_object() {
        return Err("joint native ABox taxonomy is not an object".to_string());
    }
    let abox = NativeAboxProjectionDocument {
        complete: inp.native_abox.complete,
        concepts: &inp.concepts,
        roles: &inp.roles,
        nominals: &inp.nominals,
        individuals: &inp.native_abox.individuals,
        different: &inp.native_abox.different,
        role_assertions: &inp.native_abox.role_assertions,
        negative_role_assertions: &inp.native_abox.negative_role_assertions,
    };

    let document = if !inp.card_defs.is_empty() {
        let projection = if let Some(source) = inp.bundle_projection_source.as_ref() {
            serde_json::json!({
                "source_concepts": &source.source_concepts,
                "functions": &source.functions,
                "direct": &source.direct,
                "bundles": &source.bundles,
                "domain_extras": &source.domain_extras,
                "definitions": bundle_cardinality_definitions(inp, source)?,
                "exact_pairs": &inp.cardinality_exact_pairs,
                "abox_source_map": native_abox_source_map(inp, &source.source_concepts)?,
            })
        } else if let Some(source) = inp.mixed_projection_source.as_ref() {
            serde_json::json!({
                "functions": &source.functions,
                "direct": &source.direct,
                "pairs": &source.pairs,
                "definitions": &inp.card_defs,
                "exact_pairs": &inp.cardinality_exact_pairs,
            })
        } else {
            let source = inp.direct_projection_source.as_deref().ok_or_else(|| {
                "joint native ABox cardinality classification has no complete source projection"
                    .to_string()
            })?;
            serde_json::json!({
                "source": source,
                "target": clauses.iter().map(direct_projection_target_clause)
                    .collect::<Vec<_>>(),
                "definitions": &inp.card_defs,
                "exact_pairs": &inp.cardinality_exact_pairs,
            })
        };
        serde_json::json!({
            "version": 1,
            "projection": projection,
            "abox": abox,
            "global": global,
            "taxonomy": taxonomy,
        })
    } else if let Some(source) = inp.bundle_projection_source.as_ref() {
        serde_json::json!({
            "version": 1,
            "source_concepts": &source.source_concepts,
            "functions": &source.functions,
            "direct": &source.direct,
            "bundles": &source.bundles,
            "domain_extras": &source.domain_extras,
            "abox_source_map": native_abox_source_map(inp, &source.source_concepts)?,
            "abox": abox,
            "global": global,
            "taxonomy": taxonomy,
        })
    } else if let Some(source) = inp.mixed_projection_source.as_ref() {
        serde_json::json!({
            "version": 1,
            "functions": &source.functions,
            "direct": &source.direct,
            "pairs": &source.pairs,
            "abox": abox,
            "global": global,
            "taxonomy": taxonomy,
        })
    } else {
        let source = inp.direct_projection_source.as_deref().ok_or_else(|| {
            "joint native ABox source classification has no complete source projection".to_string()
        })?;
        serde_json::json!({
            "version": 1,
            "source": source,
            "abox": abox,
            "global": global,
            "taxonomy": taxonomy,
        })
    };
    serde_json::to_vec(&document)
        .map_err(|error| format!("cannot encode joint native ABox classification: {error}"))
}


fn check_direct_ht_projection(
    inp: &TInput,
    clauses: &[Clause],
    checker: &std::path::Path,
) -> Result<(), String> {
    let variable_count = direct_projection_variable_count(clauses);
    let target = || {
        clauses
            .iter()
            .map(direct_projection_target_clause)
            .collect::<Vec<_>>()
    };
    if inp.card_defs.is_empty() && !inp.cardinality_exact_pairs.is_empty() {
        return Err("HT cardinality projection has exact pairs but no definitions".to_string());
    }
    let encoded = if !inp.card_defs.is_empty() {
        if !inp.cardinality_projection_complete {
            return Err(
                "HT cardinality projection lacks complete frontend expansion evidence".to_string(),
            );
        }
        if let Some(source) = inp.bundle_projection_source.as_ref() {
            serde_json::to_vec(&BundleCardinalityProjectionDocument {
                bundle: BundleProjectionDocument {
                    variable_count: variable_count.max(2),
                    source_concepts: &source.source_concepts,
                    concepts: &inp.concepts,
                    roles: &inp.roles,
                    functions: &source.functions,
                    direct: &source.direct,
                    bundles: &source.bundles,
                    domain_extras: &source.domain_extras,
                    target: target(),
                },
                definitions: bundle_cardinality_definitions(inp, source)?,
                exact_pairs: &inp.cardinality_exact_pairs,
            })
        } else if let Some(source) = inp.mixed_projection_source.as_ref() {
            serde_json::to_vec(&MixedCardinalityProjectionDocument {
                mixed: MixedProjectionDocument {
                    variable_count,
                    concepts: &inp.concepts,
                    roles: &inp.roles,
                    functions: &source.functions,
                    direct: &source.direct,
                    pairs: &source.pairs,
                    target: target(),
                },
                definitions: &inp.card_defs,
                exact_pairs: &inp.cardinality_exact_pairs,
            })
        } else {
            let source = inp.direct_projection_source.as_deref().ok_or_else(|| {
                "HT Lean certification has no combined direct/cardinality projection".to_string()
            })?;
            serde_json::to_vec(&DirectCardinalityProjectionDocument {
                variable_count,
                concepts: &inp.concepts,
                roles: &inp.roles,
                source,
                target: target(),
                definitions: &inp.card_defs,
                exact_pairs: &inp.cardinality_exact_pairs,
            })
        }
    } else if let Some(source) = inp.bundle_projection_source.as_ref() {
        serde_json::to_vec(&BundleProjectionDocument {
            variable_count: variable_count.max(2),
            source_concepts: &source.source_concepts,
            concepts: &inp.concepts,
            roles: &inp.roles,
            functions: &source.functions,
            direct: &source.direct,
            bundles: &source.bundles,
            domain_extras: &source.domain_extras,
            target: target(),
        })
    } else if let Some(source) = inp.mixed_projection_source.as_ref() {
        serde_json::to_vec(&MixedProjectionDocument {
            variable_count,
            concepts: &inp.concepts,
            roles: &inp.roles,
            functions: &source.functions,
            direct: &source.direct,
            pairs: &source.pairs,
            target: target(),
        })
    } else {
        let source = inp.direct_projection_source.as_deref().ok_or_else(|| {
            "HT Lean certification has no proved source-to-HT projection".to_string()
        })?;
        serde_json::to_vec(&DirectProjectionDocument {
            variable_count,
            concepts: &inp.concepts,
            roles: &inp.roles,
            source,
            target: target(),
        })
    }
    .map_err(|error| format!("cannot encode HT direct projection: {error}"))?;
    run_ht_projection_checker(&encoded, checker, "source")
}

fn check_certified_ht_input_coverage(inp: &TInput, native_abox_active: bool) -> Result<(), String> {
    if inp.dropped != 0 || !inp.fenced.is_empty() {
        return Err(format!(
            "HT Lean certification requires a complete clause projection (dropped={}, fenced={})",
            inp.dropped,
            inp.fenced.len()
        ));
    }
    if !inp.nominals.is_empty() && !native_abox_active {
        return Err(
            "HT Lean certification requires every nominal to be represented by the checked native ABox"
                .into(),
        );
    }
    if inp.inverse && inp.number && !inp.inverse_cardinality_role_separable {
        return Err("HT Lean certification requires inverse/cardinality role separation".into());
    }
    Ok(())
}

/// Whether this invocation requested proof-carrying HT publication. Keep this
/// test outside the individual worker branches: rules consistency, the
/// Konclude bridge, and the legacy tableau all precede or follow the fast-Ht
/// arm and must not bypass its Lean checker boundary.
const HT_LEAN_CERTIFICATION_ENV: &[&str] = &[
    "KM_HT_LEAN_CERT_OUT",
    "KM_HT_LEAN_CERT_CHECKER",
    "KM_HT_LEAN_PROJECTION_CHECKER",
    "KM_HT_LEAN_NATIVE_ABOX_DECISION_CHECKER",
    "KM_HT_LEAN_NATIVE_ABOX_SOURCE_DECISION_CHECKER",
    "KM_HT_LEAN_TAXONOMY_CERT_OUT",
    "KM_HT_LEAN_TAXONOMY_CERT_CHECKER",
    "KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_MATRIX_CHECKER",
    "KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_MATRIX_CHECKER",
    "KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_SOURCE_CHECKER",
    "KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_SOURCE_CHECKER",
    "KM_HT_LEAN_NATIVE_ABOX_JOINT_SOURCE_CLASSIFICATION_CHECKER",
    "KM_HT_LEAN_FRONTIER_CHECKER",
    "KM_HT_LEAN_DOUBLING_TRACE_CHECKER",
    "KM_HT_LEAN_CARDINALITY_DOUBLING_TRACE_CHECKER",
    "KM_HT_LEAN_ROOTED_CARDINALITY_DOUBLING_TRACE_CHECKER",
    "KM_HT_LEAN_ORDINARY_PRODUCTION_RUN_CHECKER",
    "KM_HT_LEAN_ORDINARY_UNSAT_PRODUCTION_RUN_CHECKER",
    "KM_HT_LEAN_CARDINALITY_PRODUCTION_RUN_CHECKER",
    "KM_HT_LEAN_ROOTED_CARDINALITY_PRODUCTION_RUN_CHECKER",
    "KM_HT_LEAN_ROOTED_ORDINARY_PRODUCTION_RUN_CHECKER",
    "KM_HT_LEAN_ROOTED_ORDINARY_TAXONOMY_PRODUCTION_RUN_CHECKER",
    "KM_HT_LEAN_ROOTED_CARDINALITY_TAXONOMY_PRODUCTION_RUN_CHECKER",
    "KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_RUN_MATRIX_CHECKER",
    "KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_RUN_MATRIX_CHECKER",
    "KM_HT_LEAN_CARDINALITY_FRONTIER_CHECKER",
    "KM_HT_LEAN_ROOTED_CARDINALITY_FRONTIER_CHECKER",
    "KM_HT_LEAN_PRODUCTION_BLOCKING_CHECKER",
    "KM_HT_LEAN_PRODUCTION_TRACE_CHECKER",
    "KM_HT_LEAN_FINITE_PRODUCTION_TERMINAL_CHECKER",
    "KM_HT_LEAN_REGULAR_PRODUCTION_TERMINAL_CHECKER",
    "KM_HT_LEAN_EQUALITY_PRODUCTION_BLOCKING_CHECKER",
    "KM_HT_LEAN_EQUALITY_PRODUCTION_TERMINAL_CHECKER",
    "KM_HT_LEAN_EQUALITY_PRODUCTION_TRACE_CHECKER",
];

fn ht_lean_certification_requested() -> bool {
    HT_LEAN_CERTIFICATION_ENV
    .iter()
    .any(|name| std::env::var_os(name).is_some())
}

/// `forced_ht` is used only by the wire-contract regression tests. Production
/// always passes `None` and reads the selected mechanism from the environment.
fn run_json_inner(input: &str, forced_ht: Option<bool>) -> Result<String, String> {
    let inp: TInput = serde_json::from_str(input).map_err(|e| e.to_string())?;
    let native_abox = validate_native_abox(&inp)?;
    let native_abox_active = native_abox.active;
    let ht_enabled = forced_ht.unwrap_or_else(|| std::env::var_os("KM_HT").is_some());
    let lean_cert_requested = ht_lean_certification_requested();
    if lean_cert_requested && !ht_enabled {
        return Err("HT Lean certification requires the hypertableau mechanism".to_string());
    }
    if native_abox_active && (!ht_enabled || std::env::var_os("KM_RULES_CONSISTENCY").is_some()) {
        return Err("native ABox requires the hypertableau mechanism".to_string());
    }
    let native_individuals = native_abox.individuals;
    let native_different = native_abox.different;
    let native_roles = native_abox.role_assertions;
    let mut clauses: Vec<Clause> = clauses_of_tinput(&inp);
    clauses.extend(native_abox.missing_negative_clauses);
    let queries: Vec<C> = if inp.queries.is_empty() {
        (0..inp.concepts.len() as C).collect()
    } else {
        inp.queries.clone()
    };

    // KM_RULES_CONSISTENCY (KM_HT_RULES Stage 2): a CONSISTENCY-ONLY check over the
    // ABox-seeded named-individual graph (the nominal roots in `inp.nominals` plus
    // the rule clauses). We only need the KB-level verdict, so skip the (expensive)
    // per-concept subsumption classification and run `consistent(&[])` on the
    // default Tableau (whose `find_model` seeds one root per nominal and applies the
    // o-rule). Run on a large stack since the careful DFS can recurse deeply.
    if std::env::var_os("KM_RULES_CONSISTENCY").is_some() {
        if lean_cert_requested {
            return Err(
                "HT Lean certification cannot publish the unchecked rules-consistency route"
                    .to_string(),
            );
        }
        let consistent = rules_consistency_verdict(&inp, clauses.clone())?;
        let out = TOutput {
            consistent,
            unsatisfiable: Vec::new(),
            subsumptions: Vec::new(),
        };
        return serde_json::to_string(&out).map_err(|e| e.to_string());
    }

    // KM_HT: route ALC(H) KBs (no number restrictions / nominals / inverses) to
    // the ported HermiT hypertableau engine. Run on a large stack since the DFS
    // recurses once per active branching point. Falls back to the legacy
    // tableau if the KB is out of the ALC(H) fragment or the engine reports an
    // out-of-fragment construct (returns None).
    // KM_HT_FORCE bypasses the in-fragment gate so the Ht engine (incl. the
    // experimental SHIQ inverse/number merge path + KM_HT_QO) actually runs on
    // inverse/number onts for measurement — otherwise such onts fall through to
    // the legacy tableau here, never reaching Ht.
    // KM_HT_BRIDGE: route the KB to the konclude_ht bridge (the Rust port of
    // Konclude's completion kernel). Sound+complete on its fragment by
    // construction: deterministic subjects answer by canonical-model read-off,
    // non-deterministic ones by candidate extraction + pairwise unsat probes.
    // `None` ⇒ DEFER (unsupported clause shape / nominals / a STOPped drive):
    // fall through to the other arms — the bridge only ever ADDS coverage.
    if std::env::var_os("KM_HT_BRIDGE").is_some() && !lean_cert_requested {
        // The bridge consumes the producer-side TInput (cb_to_ht) — same wire
        // format as this worker's TInput; re-parse the raw input for it.
        let tin_bridge: crate::orchestrate::cb_to_ht::TInput =
            serde_json::from_str(input).map_err(|e| e.to_string())?;
        let res = std::thread::Builder::new()
            .stack_size(4usize << 30)
            .spawn(move || crate::konclude_ht::bridge::bridged_classify(&tin_bridge))
            .map_err(|e| e.to_string())?
            .join()
            .map_err(|_| "konclude_ht bridge thread panicked".to_string())?;
        if let Some(r) = res {
            let subs: Vec<(C, C)> = r
                .subsumptions
                .iter()
                .map(|&(a, b)| (a as C, b as C))
                .collect();
            // `bridged_classify` publishes only a complete taxonomy (or defers),
            // so its relation is already transitively closed.  The generic Ht
            // closure repair below is needed for model-label candidate output,
            // but repeating it here scans million-pair bridge taxonomies to add
            // nothing (ORE14817).  Keep the certified bridge result directly.
            let name = |c: C| {
                inp.concepts
                    .get(c as usize)
                    .cloned()
                    .unwrap_or_else(|| format!("C{c}"))
            };
            let out = TOutput {
                consistent: r.consistent,
                unsatisfiable: r.unsatisfiable.iter().map(|&c| name(c as C)).collect(),
                subsumptions: subs.iter().map(|&(a, b)| [name(a), name(b)]).collect(),
            };
            return serde_json::to_string(&out).map_err(|e| e.to_string());
        }
        // The bridge declined. If it was the ONLY route this worker was
        // spawned for (KM_HT_BRIDGE_ONLY, set by spawn_ht), emit NO answer —
        // the legacy tableau below is not validated on this fragment and the
        // orchestrator's CB arm must decide. Otherwise fall through to the
        // route the worker was actually spawned for (monotone-safe).
        if std::env::var_os("KM_HT_BRIDGE_ONLY").is_some() {
            return Err("konclude_ht bridge defer".to_string());
        }
    }

    let ht_force = forced_ht == Some(true) || std::env::var_os("KM_HT_FORCE").is_some();
    // KM_HT_NOMINALS: route nominal (but inverse-free) KBs — SHOQ / SHON — to the
    // fast Ht, which now carries the nominal o-rule (`set_nominals`) composed with
    // the ≤n merge (qmerge) and pairwise blocking. Inverse stays fenced (SHOIQ
    // needs the NN-rule, not yet ported).
    let ht_nom = forced_ht == Some(true) || std::env::var_os("KM_HT_NOMINALS").is_some();
    let ht_route_selected = ht_enabled
        && (ht_force
            || (!inp.number && !inp.inverse && inp.nominals.is_empty())
            || (ht_nom && !inp.inverse));
    if lean_cert_requested && !ht_route_selected {
        return Err(
            "HT Lean certification has no certified hypertableau route for this input"
                .to_string(),
        );
    }
    if ht_route_selected {
        let mut ht_clauses = clauses.clone();
        let q = queries.clone();
        let noms = inp.nominals.clone();
        let abox_individuals = native_individuals.clone();
        let abox_different = native_different.clone();
        let abox_roles = native_roles.clone();
        let ht_number = inp.number;
        let lean_cert_path = std::env::var_os("KM_HT_LEAN_CERT_OUT").map(std::path::PathBuf::from);
        let lean_cert_checker =
            std::env::var_os("KM_HT_LEAN_CERT_CHECKER").map(std::path::PathBuf::from);
        let lean_native_abox_decision_checker =
            std::env::var_os("KM_HT_LEAN_NATIVE_ABOX_DECISION_CHECKER")
                .map(std::path::PathBuf::from);
        let lean_native_abox_source_decision_checker =
            std::env::var_os("KM_HT_LEAN_NATIVE_ABOX_SOURCE_DECISION_CHECKER")
                .map(std::path::PathBuf::from);
        let lean_source_bound_native_abox_global_checker = if inp.card_defs.is_empty() {
            std::env::var_os("KM_HT_LEAN_SOURCE_BOUND_NATIVE_ABOX_GLOBAL_CHECKER")
                .map(std::path::PathBuf::from)
        } else {
            std::env::var_os(
                "KM_HT_LEAN_SOURCE_BOUND_NATIVE_ABOX_CARDINALITY_GLOBAL_CHECKER",
            )
            .map(std::path::PathBuf::from)
        };
        let lean_native_abox_taxonomy_matrix_checker = if inp.card_defs.is_empty() {
            std::env::var_os("KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_MATRIX_CHECKER")
                .map(std::path::PathBuf::from)
        } else {
            std::env::var_os(
                "KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_MATRIX_CHECKER",
            )
            .map(std::path::PathBuf::from)
        };
        let lean_native_abox_taxonomy_source_checker = if inp.card_defs.is_empty() {
            std::env::var_os("KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_SOURCE_CHECKER")
                .map(std::path::PathBuf::from)
        } else {
            std::env::var_os(
                "KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_SOURCE_CHECKER",
            )
            .map(std::path::PathBuf::from)
        };
        let lean_source_bound_native_abox_taxonomy_checker = if inp.card_defs.is_empty() {
            std::env::var_os("KM_HT_LEAN_SOURCE_BOUND_NATIVE_ABOX_TAXONOMY_CHECKER")
                .map(std::path::PathBuf::from)
        } else {
            std::env::var_os(
                "KM_HT_LEAN_SOURCE_BOUND_NATIVE_ABOX_CARDINALITY_TAXONOMY_CHECKER",
            )
            .map(std::path::PathBuf::from)
        };
        let lean_native_abox_joint_source_classification_checker = std::env::var_os(
            "KM_HT_LEAN_NATIVE_ABOX_JOINT_SOURCE_CLASSIFICATION_CHECKER",
        )
        .map(std::path::PathBuf::from);
        let lean_projection_checker =
            std::env::var_os("KM_HT_LEAN_PROJECTION_CHECKER").map(std::path::PathBuf::from);
        let lean_taxonomy_path =
            std::env::var_os("KM_HT_LEAN_TAXONOMY_CERT_OUT").map(std::path::PathBuf::from);
        let lean_taxonomy_checker =
            std::env::var_os("KM_HT_LEAN_TAXONOMY_CERT_CHECKER").map(std::path::PathBuf::from);
        let lean_taxonomy_requested = lean_taxonomy_path.is_some()
            || lean_taxonomy_checker.is_some()
            || lean_native_abox_taxonomy_matrix_checker.is_some()
            || lean_native_abox_taxonomy_source_checker.is_some()
            || (native_abox_active
                && lean_source_bound_native_abox_taxonomy_checker.is_some())
            || lean_native_abox_joint_source_classification_checker.is_some();
        if lean_cert_requested {
            if std::env::var_os("KM_HT_GLOBAL").is_none() {
                return Err(
                    "HT Lean certification requires the global consistency route".to_string(),
                );
            }
            let frontier_checker = if inp.card_defs.is_empty() {
                "KM_HT_LEAN_FRONTIER_CHECKER"
            } else {
                "KM_HT_LEAN_CARDINALITY_FRONTIER_CHECKER"
            };
            if std::env::var_os(frontier_checker).is_none() {
                return Err(format!(
                    "HT Lean certification requires {frontier_checker} for every inconclusive search round"
                ));
            }
            if std::env::var_os("KM_HT_LEAN_DOUBLING_TRACE_CHECKER").is_none() {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_DOUBLING_TRACE_CHECKER for complete ordinary frontier histories"
                        .to_string(),
                );
            }
            if std::env::var_os("KM_HT_LEAN_ORDINARY_PRODUCTION_RUN_CHECKER").is_none() {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_ORDINARY_PRODUCTION_RUN_CHECKER to bind ordinary SAT terminals to their complete runs"
                        .to_string(),
                );
            }
            if std::env::var_os("KM_HT_LEAN_CARDINALITY_PRODUCTION_RUN_CHECKER").is_none() {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_CARDINALITY_PRODUCTION_RUN_CHECKER to bind cardinality terminals to their complete runs"
                        .to_string(),
                );
            }
            if std::env::var_os("KM_HT_LEAN_ROOTED_CARDINALITY_PRODUCTION_RUN_CHECKER").is_none() {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_ROOTED_CARDINALITY_PRODUCTION_RUN_CHECKER to bind native ABox cardinality terminals to their complete runs"
                        .to_string(),
                );
            }
            if !native_individuals.is_empty()
                && inp.card_defs.is_empty()
                && std::env::var_os("KM_HT_LEAN_ROOTED_ORDINARY_PRODUCTION_RUN_CHECKER")
                    .is_none()
            {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_ROOTED_ORDINARY_PRODUCTION_RUN_CHECKER to bind native ABox terminals to their complete runs"
                        .to_string(),
                );
            }
            if !native_individuals.is_empty()
                && !inp.card_defs.is_empty()
                && std::env::var_os(
                    "KM_HT_LEAN_ROOTED_CARDINALITY_TAXONOMY_PRODUCTION_RUN_CHECKER",
                )
                .is_none()
            {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_ROOTED_CARDINALITY_TAXONOMY_PRODUCTION_RUN_CHECKER to bind native ABox cardinality taxonomy cells to their complete runs"
                        .to_string(),
                );
            }
            if !native_individuals.is_empty()
                && !inp.card_defs.is_empty()
                && std::env::var_os(
                    "KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_RUN_MATRIX_CHECKER",
                )
                .is_none()
            {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_RUN_MATRIX_CHECKER to certify the complete run-derived native ABox cardinality taxonomy matrix"
                        .to_string(),
                );
            }
            if !native_individuals.is_empty()
                && inp.card_defs.is_empty()
                && std::env::var_os(
                    "KM_HT_LEAN_ROOTED_ORDINARY_TAXONOMY_PRODUCTION_RUN_CHECKER",
                )
                .is_none()
            {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_ROOTED_ORDINARY_TAXONOMY_PRODUCTION_RUN_CHECKER to bind native ABox taxonomy cells to their complete runs"
                        .to_string(),
                );
            }
            if !native_individuals.is_empty()
                && inp.card_defs.is_empty()
                && std::env::var_os(
                    "KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_RUN_MATRIX_CHECKER",
                )
                .is_none()
            {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_RUN_MATRIX_CHECKER to certify the complete run-derived native ABox taxonomy matrix"
                        .to_string(),
                );
            }
            if std::env::var_os("KM_HT_LEAN_ORDINARY_UNSAT_PRODUCTION_RUN_CHECKER").is_none() {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_ORDINARY_UNSAT_PRODUCTION_RUN_CHECKER to bind ordinary UNSAT terminals to their complete runs"
                        .to_string(),
                );
            }
            if !inp.card_defs.is_empty()
                && native_individuals.is_empty()
                && std::env::var_os("KM_HT_LEAN_CARDINALITY_DOUBLING_TRACE_CHECKER")
                    .is_none()
            {
                return Err(
                    "cardinality HT Lean certification requires KM_HT_LEAN_CARDINALITY_DOUBLING_TRACE_CHECKER"
                        .to_string(),
                );
            }
            if !inp.card_defs.is_empty()
                && !native_individuals.is_empty()
                && std::env::var_os(
                    "KM_HT_LEAN_ROOTED_CARDINALITY_DOUBLING_TRACE_CHECKER",
                )
                .is_none()
            {
                return Err(
                    "native-ABox cardinality HT Lean certification requires KM_HT_LEAN_ROOTED_CARDINALITY_DOUBLING_TRACE_CHECKER"
                        .to_string(),
                );
            }
            if !native_individuals.is_empty()
                && std::env::var_os("KM_HT_LEAN_ROOTED_CARDINALITY_FRONTIER_CHECKER")
                    .is_none()
            {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_ROOTED_CARDINALITY_FRONTIER_CHECKER for native-ABox frontier rounds"
                        .to_string(),
                );
            }
            if std::env::var_os("KM_HT_LEAN_PRODUCTION_BLOCKING_CHECKER").is_none() {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_PRODUCTION_BLOCKING_CHECKER for exhausted equality-free blocker assignments"
                        .to_string(),
                );
            }
            if std::env::var_os("KM_HT_LEAN_PRODUCTION_TRACE_CHECKER").is_none() {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_PRODUCTION_TRACE_CHECKER for complete equality-free blocker-learning histories"
                        .to_string(),
                );
            }
            if std::env::var_os("KM_HT_LEAN_FINITE_PRODUCTION_TERMINAL_CHECKER").is_none() {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_FINITE_PRODUCTION_TERMINAL_CHECKER for finite equality-free SAT publication"
                        .to_string(),
                );
            }
            if std::env::var_os("KM_HT_LEAN_REGULAR_PRODUCTION_TERMINAL_CHECKER").is_none() {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_REGULAR_PRODUCTION_TERMINAL_CHECKER for regular equality-free SAT publication"
                        .to_string(),
                );
            }
            if std::env::var_os("KM_HT_LEAN_EQUALITY_PRODUCTION_BLOCKING_CHECKER").is_none() {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_EQUALITY_PRODUCTION_BLOCKING_CHECKER for exhausted equality-aware blocker assignments"
                        .to_string(),
                );
            }
            if std::env::var_os("KM_HT_LEAN_EQUALITY_PRODUCTION_TERMINAL_CHECKER").is_none() {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_EQUALITY_PRODUCTION_TERMINAL_CHECKER for equality-aware SAT publication"
                        .to_string(),
                );
            }
            if std::env::var_os("KM_HT_LEAN_EQUALITY_PRODUCTION_TRACE_CHECKER").is_none() {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_EQUALITY_PRODUCTION_TRACE_CHECKER for complete equality-aware blocker-learning histories"
                        .to_string(),
                );
            }
            check_certified_ht_input_coverage(&inp, native_abox_active)?;
            if lean_projection_checker.is_none() {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_PROJECTION_CHECKER".to_string(),
                );
            }
            if native_abox_active && lean_native_abox_decision_checker.is_none() {
                return Err(
                    "native ABox HT certification requires KM_HT_LEAN_NATIVE_ABOX_DECISION_CHECKER"
                        .to_string(),
                );
            }
            if native_abox_active && lean_native_abox_source_decision_checker.is_none() {
                return Err(
                    "native ABox HT certification requires KM_HT_LEAN_NATIVE_ABOX_SOURCE_DECISION_CHECKER"
                        .to_string(),
                );
            }
            if native_abox_active && lean_source_bound_native_abox_global_checker.is_none() {
                return Err(
                    "native ABox HT certification requires its source-bound global Lean checker"
                        .to_string(),
                );
            }
            if !native_abox_active && lean_cert_checker.is_none() {
                return Err(
                    "HT Lean certification requires KM_HT_LEAN_CERT_CHECKER".to_string(),
                );
            }
            if native_abox_active && lean_taxonomy_requested {
                if lean_native_abox_taxonomy_matrix_checker.is_none() {
                    return Err(
                        "native ABox HT taxonomy certification requires its complete-matrix Lean checker"
                            .to_string(),
                    );
                }
                if lean_native_abox_taxonomy_source_checker.is_none() {
                    return Err(
                        "native ABox HT taxonomy certification requires its source-composition Lean checker"
                            .to_string(),
                    );
                }
                if lean_source_bound_native_abox_taxonomy_checker.is_none() {
                    return Err(
                        "native ABox HT taxonomy certification requires its source-bound taxonomy Lean checker"
                            .to_string(),
                    );
                }
                if lean_native_abox_joint_source_classification_checker.is_none() {
                    return Err(
                        "native ABox HT taxonomy certification requires KM_HT_LEAN_NATIVE_ABOX_JOINT_SOURCE_CLASSIFICATION_CHECKER"
                            .to_string(),
                    );
                }
            }
            if std::env::var_os("KM_HT_QO").is_some() {
                return Err("HT Lean certificate v1 does not certify the QO route".to_string());
            }
            if !native_abox_active && lean_taxonomy_requested && lean_taxonomy_checker.is_none() {
                return Err(
                    "certified HT taxonomy publication requires both the global and taxonomy Lean checkers"
                        .to_string(),
                );
            }
        }
        if lean_cert_requested {
            // The optimized route keeps these source axioms in typed side data.
            // For certification, restore their exact clausal semantics and let
            // the ordinary HT evidence plus Lean's exhaustive checker account
            // for them directly.
            ht_clauses.extend(certified_role_chain_clauses(&inp.chains, &inp.transitive));
            check_direct_ht_projection(
                &inp,
                &ht_clauses,
                lean_projection_checker
                    .as_deref()
                    .expect("certified projection checker was required above"),
            )?;
        }
        // KM_HT_CARD: first-class number restrictions to install on the Ht.
        let card_raw: Vec<(C, bool, u32, R, C, bool)> = inp
            .card_defs
            .iter()
            .map(|d| (d.marker, d.min, d.n, d.role, d.filler, d.exact))
            .collect();
        let ht_chains = inp.chains.clone();
        let ht_transitive = inp.transitive.clone();
        let source_decision_clauses = ht_clauses.clone();
        let res = std::thread::Builder::new()
            // 4 GiB virtual stack (lazily paged): the DFS recurses once per active
            // branch level; SHOQ number+nominal search can nest tens of thousands
            // deep, overflowing the prior 1 GiB reservation. Virtual, so the unused
            // tail costs nothing.
            .stack_size(4usize << 30)
            .spawn(move || {
                let mut ht = if lean_cert_requested {
                    hypertableau::Ht::new_certified(ht_clauses)
                } else {
                    hypertableau::Ht::new(ht_clauses)
                };
                ht.set_nominals(noms);
                ht.set_native_abox(abox_individuals, abox_different, abox_roles);
                // KM_KEEP_CHAIN_AXIOMS: install the detected role chains for the
                // Ht chain-unfolding (faithful Konclude generateRoleChainAutomat
                // Concept).  The chains are side data in the TInput (the raw
                // axioms are excluded from the clause set to avoid cb_to_ht bloat).
                if !lean_cert_requested && (!ht_chains.is_empty() || !ht_transitive.is_empty()) {
                    ht.set_chains(ht_chains, ht_transitive);
                }
                // A number KB routed to the fast Ht (e.g. under KM_HT_FORCE or the
                // nominal route) must run the qualified-cardinality rules (≤n / ≥n
                // recognition / functional) rather than bailing `unsupported`.
                ht.set_number(ht_number);
                // KM_HT_CARD first-class number rules run on the BRANCHING classify
                // only; the QO certify path's apply_head does not handle the kept
                // cardinality recognition Eq-heads. cb_to_ht only emits `card_defs`
                // for the card-routable fragment (which never takes the QO route),
                // so this is belt-and-suspenders against a future routing change.
                if !card_raw.is_empty() && std::env::var_os("KM_HT_QO").is_none() {
                    ht.set_card_defs_raw(&card_raw);
                }
                if lean_cert_requested {
                    // The certification-only route obtains its verdict and its
                    // evidence from the same total certificate search. The
                    // optimized tableau is not an oracle at this trust boundary.
                    let (consistent, certificate, native_global_run) =
                        ht.lean_global_decision_certificate_and_native_run_json()?;
                    let taxonomy = if lean_taxonomy_requested {
                        if native_abox_active {
                            let (certificate, run) =
                                ht.lean_native_abox_taxonomy_certificate_and_run_json(&q)?;
                            Some((certificate, Some(run)))
                        } else {
                            Some((ht.lean_taxonomy_certificate_json(&q)?, None))
                        }
                    } else {
                        None
                    };
                    return Ok::<_, String>(Some((
                        (consistent, Vec::new(), Vec::new()),
                        Some((certificate, native_global_run, taxonomy)),
                    )));
                }
                let classification = if std::env::var_os("KM_HT_QO").is_some() {
                    match ht.quasi_order_classify(&q) {
                        Some(r) => Some(r),
                        // QO bailed. In router mode (KM_HT_QO_CERTIFY_ONLY) this is
                        // a DEFER: do NOT fall back to the branching classify (whose
                        // soundness on this inverse fragment is not certified) —
                        // return None so the worker emits no answer and the
                        // orchestrator's CB engine (sound+complete) decides.
                        // Otherwise (non-router) keep the historical behaviour:
                        // fall back to Ht's branching classify so QO only adds.
                        None => {
                            if std::env::var_os("KM_HT_QO_CERTIFY_ONLY").is_some() {
                                None
                            } else {
                                ht.classify(&q)
                            }
                        }
                    }
                } else {
                    ht.classify(&q)
                };
                Ok::<_, String>(classification.map(|classification| (classification, None)))
            })
            .map_err(|e| e.to_string())?
            .join()
            .map_err(|_| "hypertableau thread panicked".to_string())??;
        if std::env::var_os("KM_HT_TRACE").is_some() {
            eprintln!("TR run_json: thread joined (Ht dropped inside thread)");
        }
        if let Some(((consistent, unsat, subs), lean_certificate)) = res {
            let mut validated_taxonomy = None;
            if let Some((certificate, native_global_run, taxonomy_certificate)) = lean_certificate {
                let certificate_value: serde_json::Value = serde_json::from_str(&certificate)
                    .map_err(|error| format!("KM_HT_LEAN_CERT produced invalid JSON: {error}"))?;
                let evidence_consistent = certified_ht_global_consistency(&certificate_value)?;
                if evidence_consistent != consistent {
                    return Err(format!(
                        "HT certified verdict mismatch: search returned {consistent}, certificate evidence returned {evidence_consistent}"
                    ));
                }
                let temporary_path;
                let path = if let Some(path) = lean_cert_path.as_deref() {
                    path
                } else {
                    temporary_path = std::env::temp_dir()
                        .join(format!("km-ht-cert-{}.json", std::process::id()));
                    temporary_path.as_path()
                };
                if let Err(error) = std::fs::write(path, &certificate) {
                    return Err(format!(
                        "KM_HT_LEAN_CERT cannot write {}: {error}",
                        path.display()
                    ));
                }
                let verdict_checker = if native_abox_active {
                    lean_native_abox_decision_checker.as_deref()
                } else {
                    lean_cert_checker.as_deref()
                };
                if let Some(checker) = verdict_checker {
                    let status = std::process::Command::new(checker)
                        .arg(path)
                        .stdout(std::process::Stdio::null())
                        .status()
                        .map_err(|error| {
                            format!(
                                "KM_HT_LEAN_CERT cannot execute {}: {error}",
                                checker.display()
                            )
                        })?;
                    if lean_cert_path.is_none() {
                        let _ = std::fs::remove_file(path);
                    }
                    if !status.success() {
                        return Err(format!(
                            "KM_HT_LEAN_CERT checker {} rejected the certificate ({status})",
                            checker.display()
                        ));
                    }
                }
                if native_abox_active {
                    let checker = lean_native_abox_source_decision_checker
                        .as_deref()
                        .ok_or_else(|| {
                            "missing native ABox source-decision Lean checker".to_string()
                        })?;
                    let source_decision =
                        native_abox_source_decision_document(
                            &inp,
                            &source_decision_clauses,
                            &certificate,
                            consistent,
                        )?;
                    run_ht_projection_checker(
                        &source_decision,
                        checker,
                        "native-abox-source-decision",
                    )?;
                    let native_global_run = native_global_run.ok_or_else(|| {
                        "native ABox HT certification omitted its retained global run".to_string()
                    })?;
                    let source_bound = source_bound_native_abox_document(
                        &inp,
                        &source_decision,
                        "run",
                        native_global_run,
                    )?;
                    let checker = lean_source_bound_native_abox_global_checker
                        .as_deref()
                        .ok_or_else(|| {
                            "missing source-bound native ABox global Lean checker".to_string()
                        })?;
                    run_ht_projection_checker(
                        &source_bound,
                        checker,
                        "source-bound-native-abox-global",
                    )?;
                }
                if let Some((taxonomy_certificate, native_taxonomy_runs)) = taxonomy_certificate {
                    let taxonomy_value: serde_json::Value =
                        serde_json::from_str(&taxonomy_certificate).map_err(|error| {
                            format!("KM_HT_LEAN_TAXONOMY_CERT produced invalid JSON: {error}")
                        })?;
                    let temporary_taxonomy_path;
                    let taxonomy_path = if let Some(path) = lean_taxonomy_path.as_deref() {
                        path
                    } else {
                        temporary_taxonomy_path = std::env::temp_dir()
                            .join(format!("km-ht-taxonomy-cert-{}.json", std::process::id()));
                        temporary_taxonomy_path.as_path()
                    };
                    std::fs::write(taxonomy_path, &taxonomy_certificate).map_err(|error| {
                        format!(
                            "KM_HT_LEAN_TAXONOMY_CERT cannot write {}: {error}",
                            taxonomy_path.display()
                        )
                    })?;
                    let checker = if native_abox_active {
                        lean_native_abox_taxonomy_matrix_checker.as_deref()
                    } else {
                        lean_taxonomy_checker.as_deref()
                    }
                    .ok_or_else(|| "missing HT taxonomy Lean checker".to_string())?;
                    let status = std::process::Command::new(checker)
                        .arg(taxonomy_path)
                        .stdout(std::process::Stdio::null())
                        .status()
                        .map_err(|error| {
                            format!(
                                "KM_HT_LEAN_TAXONOMY_CERT cannot execute {}: {error}",
                                checker.display()
                            )
                        })?;
                    if lean_taxonomy_path.is_none() {
                        let _ = std::fs::remove_file(taxonomy_path);
                    }
                    if !status.success() {
                        return Err(format!(
                            "KM_HT_LEAN_TAXONOMY_CERT checker {} rejected the certificate ({status})",
                            checker.display()
                        ));
                    }
                    if native_abox_active {
                        let source_checker = lean_native_abox_taxonomy_source_checker
                            .as_deref()
                            .ok_or_else(|| {
                                "missing native ABox taxonomy source Lean checker".to_string()
                            })?;
                        let source_taxonomy = native_abox_source_taxonomy_document(
                            &inp,
                            &source_decision_clauses,
                            &taxonomy_certificate,
                        )?;
                        run_ht_projection_checker(
                            &source_taxonomy,
                            source_checker,
                            "native-abox-taxonomy-source",
                        )?;
                        let native_taxonomy_runs = native_taxonomy_runs.ok_or_else(|| {
                            "native ABox HT taxonomy certification omitted its retained run matrix"
                                .to_string()
                        })?;
                        let source_bound = source_bound_native_abox_document(
                            &inp,
                            &source_taxonomy,
                            "runs",
                            native_taxonomy_runs,
                        )?;
                        let checker = lean_source_bound_native_abox_taxonomy_checker
                            .as_deref()
                            .ok_or_else(|| {
                                "missing source-bound native ABox taxonomy Lean checker".to_string()
                            })?;
                        run_ht_projection_checker(
                            &source_bound,
                            checker,
                            "source-bound-native-abox-taxonomy",
                        )?;
                        let joint_checker = lean_native_abox_joint_source_classification_checker
                            .as_deref()
                            .ok_or_else(|| {
                                "missing native ABox joint source-classification Lean checker"
                                    .to_string()
                            })?;
                        let joint_classification =
                            native_abox_joint_source_classification_document(
                                &inp,
                                &source_decision_clauses,
                                &certificate,
                                &taxonomy_certificate,
                            )?;
                        run_ht_projection_checker(
                            &joint_classification,
                            joint_checker,
                            "native-abox-joint-source-classification",
                        )?;
                    }
                    let taxonomy_version = taxonomy_value["version"].as_u64();
                    let checked_payload = if matches!(taxonomy_version, Some(6 | 7)) {
                        taxonomy_value["certificate"]
                            .as_object()
                            .map(|_| taxonomy_value["certificate"].clone())
                            .ok_or_else(|| {
                                "checked normalized cardinality taxonomy omitted its certificate"
                                    .to_string()
                            })?
                    } else if matches!(taxonomy_version, Some(3 | 4)) {
                        taxonomy_value["payload"]["plain"]["certificate"]
                            .as_object()
                            .map(|_| taxonomy_value["payload"]["plain"]["certificate"].clone())
                            .or_else(|| {
                                taxonomy_value["payload"]["mixed"]["certificate"]
                                    .as_object()
                                    .map(|_| {
                                        taxonomy_value["payload"]["mixed"]["certificate"].clone()
                                    })
                            })
                            .ok_or_else(|| {
                                "checked normalized HT taxonomy omitted its payload".to_string()
                            })?
                    } else {
                        taxonomy_value
                    };
                    validated_taxonomy = Some(checked_payload);
                }
            }
            if let Some(taxonomy) = validated_taxonomy {
                let named = taxonomy["named"]
                    .as_array()
                    .ok_or_else(|| "checked HT taxonomy omitted named classes".to_string())?;
                let concepts = taxonomy["concepts"]
                    .as_array()
                    .ok_or_else(|| "checked HT taxonomy omitted concept evidence".to_string())?;
                let rows = taxonomy["subsumptions"].as_array().ok_or_else(|| {
                    "checked HT taxonomy omitted subsumption evidence".to_string()
                })?;
                let ids: Vec<C> = named
                    .iter()
                    .map(|id| {
                        id.as_u64()
                            .and_then(|id| C::try_from(id).ok())
                            .ok_or_else(|| {
                                "checked HT taxonomy has an invalid class id".to_string()
                            })
                    })
                    .collect::<Result<_, _>>()?;
                fn evidence(entry: &serde_json::Value) -> Option<&serde_json::Value> {
                    entry
                        .get("evidence")
                        .or_else(|| entry.get("plain")?.get("payload")?.get("evidence"))
                        .or_else(|| entry.get("equality")?.get("evidence"))
                }
                let certified_unsat: Vec<C> = concepts
                    .iter()
                    .zip(ids.iter().copied())
                    .filter_map(|(entry, id)| {
                        evidence(entry)?["unsatisfiable_concept"]
                            .is_object()
                            .then_some(id)
                    })
                    .collect();
                let mut certified_subs = Vec::new();
                for (sub, row) in ids.iter().copied().zip(rows) {
                    let row = row
                        .as_array()
                        .ok_or_else(|| "checked HT taxonomy has a non-array row".to_string())?;
                    for (sup, entry) in ids.iter().copied().zip(row) {
                        if evidence(entry)
                            .is_some_and(|evidence| evidence["subsumption"].is_object())
                        {
                            certified_subs.push((sub, sup));
                        }
                    }
                }
                let name = |c: C| {
                    inp.concepts
                        .get(c as usize)
                        .cloned()
                        .unwrap_or_else(|| format!("C{c}"))
                };
                let out = TOutput {
                    consistent,
                    unsatisfiable: certified_unsat.into_iter().map(|c| name(c)).collect(),
                    subsumptions: certified_subs
                        .into_iter()
                        .map(|(sub, sup)| [name(sub), name(sup)])
                        .collect(),
                };
                return serde_json::to_string(&out).map_err(|error| error.to_string());
            }
            // The per-concept model-label candidate sets can miss an entailed
            // A ⊑ C when A ⊑ B ⊑ C and C is absent from A's one captured model
            // (inferred, non-told subsumers via domain/range etc.). Subsumption
            // is transitive, so closing the confirmed relation is unconditionally
            // sound and only ADDS entailed pairs (ore_ont_7499: recovers 3297
            // BFO/CHEBI upper-ontology links, byte-exact to gold). Applied once
            // here so every hypertableau variant (branching + QO certify) is
            // covered at the serialization boundary.
            let subs = hypertableau::transitive_close_subs(subs);
            let name = |c: C| {
                inp.concepts
                    .get(c as usize)
                    .cloned()
                    .unwrap_or_else(|| format!("C{c}"))
            };
            let out = TOutput {
                consistent,
                unsatisfiable: unsat.iter().map(|&c| name(c)).collect(),
                subsumptions: subs.iter().map(|&(a, b)| [name(a), name(b)]).collect(),
            };
            return serde_json::to_string(&out).map_err(|e| e.to_string());
        }
        if lean_cert_requested {
            return Err(
                "HT Lean certificate producer deferred; no unchecked fallback published"
                    .to_string(),
            );
        }
        // None ⇒ out-of-fragment. In router mode this is a DEFER: do NOT fall to
        // the legacy Tableau (unsound/may hang on this inverse fragment) — signal
        // no-answer so the orchestrator races to CB.
        if std::env::var_os("KM_HT_QO_CERTIFY_ONLY").is_some() {
            return Err("QO router defer (not certified)".to_string());
        }
        // The legacy Tableau does not consume the typed native-ABox state.  A
        // fast-Ht defer must therefore propagate as a route defer rather than
        // silently answering from a partial ABox.
        if native_abox_active {
            return Err("native ABox hypertableau defer".to_string());
        }
        // otherwise fall through to the legacy tableau.
    }

    let mut t = Tableau::new(clauses);
    t.set_pairwise(inp.inverse);
    t.set_number(inp.number);
    t.set_nominals(inp.nominals.clone());
    let (consistent, unsat, subs) = t.classify(&queries);
    // Same transitive-closure completion as the hypertableau path (sound: only
    // adds entailed pairs). The legacy tableau's per-concept candidate sets have
    // the same model-label incompleteness for inferred (non-told) subsumers.
    let subs = hypertableau::transitive_close_subs(subs);
    let name = |c: C| {
        inp.concepts
            .get(c as usize)
            .cloned()
            .unwrap_or_else(|| format!("C{c}"))
    };
    let out = TOutput {
        consistent,
        unsatisfiable: unsat.iter().map(|&c| name(c)).collect(),
        subsumptions: subs.iter().map(|&(a, b)| [name(a), name(b)]).collect(),
    };
    serde_json::to_string(&out).map_err(|e| e.to_string())
}

#[cfg(test)]
pub(crate) fn run_json_for_native_ht_test(input: &str) -> Result<String, String> {
    run_json_inner(input, Some(true))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn certified_global_verdict_is_derived_from_the_checked_evidence_shape() {
        let plain_sat = serde_json::json!({"version": 1, "evidence": "sat"});
        let equality_unsat = serde_json::json!({"version": 2, "evidence": {"unsat": {}}});
        let cardinality_sat = serde_json::json!({
            "version": 2,
            "definitions": [],
            "certificate": plain_sat,
        });
        let normalized_unsat = serde_json::json!({
            "version": 4,
            "payload": {"equality": {"certificate": equality_unsat}},
        });
        let regular_sat = serde_json::json!({"version": 1, "evidence": {"regular_sat": {}}});
        let finite_sat = serde_json::json!({"version": 1, "evidence": {"finite_sat": {}}});
        let native_sat = serde_json::json!({"version": 1, "evidence": {"sat": {}}});
        let native_unsat = serde_json::json!({"version": 1, "evidence": {"unsat": {}}});
        assert_eq!(certified_ht_global_consistency(&cardinality_sat), Ok(true));
        assert_eq!(
            certified_ht_global_consistency(&normalized_unsat),
            Ok(false)
        );
        assert_eq!(certified_ht_global_consistency(&regular_sat), Ok(true));
        assert_eq!(certified_ht_global_consistency(&finite_sat), Ok(true));
        assert_eq!(certified_ht_global_consistency(&native_sat), Ok(true));
        assert_eq!(certified_ht_global_consistency(&native_unsat), Ok(false));
        assert_eq!(
            certified_ht_global_consistency(&serde_json::json!({
                "version": 5,
                "certificate": {},
            })),
            Ok(true)
        );
        assert!(certified_ht_global_consistency(&serde_json::json!({
            "version": 2,
            "evidence": {"subsumption": {}},
        }))
        .is_err());
        assert!(certified_ht_global_consistency(&serde_json::json!({
            "version": 3,
            "payload": {
                "plain": {"certificate": {"version": 1, "evidence": "sat"}},
                "regular": {"certificate": {
                    "version": 1,
                    "evidence": {"finite_unsat": {}},
                }},
            },
        }))
        .is_err());
    }

    #[test]
    fn certified_input_coverage_rejects_converter_omissions_and_unsafe_combinations() {
        let mut producer = crate::orchestrate::cb_to_ht::TInput::default();
        let complete = consumer_input(&producer);
        assert!(check_certified_ht_input_coverage(&complete, false).is_ok());

        producer.dropped = 1;
        assert!(
            check_certified_ht_input_coverage(&consumer_input(&producer), false)
                .unwrap_err()
                .contains("complete clause projection")
        );
        producer.dropped = 0;
        producer.fenced.push(crate::orchestrate::cb_to_ht::Fenced {
            reason: "unsupported".into(),
            detail: "test".into(),
        });
        assert!(check_certified_ht_input_coverage(&consumer_input(&producer), false).is_err());
        producer.fenced.clear();

        producer.inverse = true;
        assert!(check_certified_ht_input_coverage(&consumer_input(&producer), false).is_ok());
        producer.number = true;
        assert!(
            check_certified_ht_input_coverage(&consumer_input(&producer), false)
                .unwrap_err()
                .contains("role separation")
        );
        producer.inverse_cardinality_role_separable = true;
        assert!(check_certified_ht_input_coverage(&consumer_input(&producer), false).is_ok());

        producer.nominals.push(0);
        assert!(check_certified_ht_input_coverage(&consumer_input(&producer), false).is_err());
        assert!(check_certified_ht_input_coverage(&consumer_input(&producer), true).is_ok());
        producer.nominals.clear();
        assert!(check_certified_ht_input_coverage(&consumer_input(&producer), true).is_ok());
    }

    #[test]
    fn certified_input_coverage_matches_the_lean_truth_table() {
        for dropped in [0, 1] {
            for fenced in [false, true] {
                for inverse in [false, true] {
                    for number in [false, true] {
                        for separated in [false, true] {
                            for nominals in [false, true] {
                                for native_abox in [false, true] {
                                    let mut producer =
                                        crate::orchestrate::cb_to_ht::TInput::default();
                                    producer.dropped = dropped;
                                    producer.inverse = inverse;
                                    producer.number = number;
                                    producer.inverse_cardinality_role_separable = separated;
                                    if fenced {
                                        producer.fenced.push(
                                            crate::orchestrate::cb_to_ht::Fenced {
                                                reason: "truth-table".into(),
                                                detail: "test".into(),
                                            },
                                        );
                                    }
                                    if nominals {
                                        producer.nominals.push(0);
                                    }
                                    let accepted = check_certified_ht_input_coverage(
                                        &consumer_input(&producer),
                                        native_abox,
                                    )
                                    .is_ok();
                                    let lean_valid = dropped == 0
                                        && !fenced
                                        && (!nominals || native_abox)
                                        && (!inverse || !number || separated);
                                    assert_eq!(
                                        accepted, lean_valid,
                                        "dropped={dropped} fenced={fenced} inverse={inverse} \
                                         number={number} separated={separated} \
                                         nominals={nominals} native_abox={native_abox}",
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn every_ht_lean_interface_enters_the_fail_closed_certification_boundary() {
        for required in [
            "KM_HT_LEAN_CERT_OUT",
            "KM_HT_LEAN_CERT_CHECKER",
            "KM_HT_LEAN_PROJECTION_CHECKER",
            "KM_HT_LEAN_NATIVE_ABOX_DECISION_CHECKER",
            "KM_HT_LEAN_NATIVE_ABOX_SOURCE_DECISION_CHECKER",
            "KM_HT_LEAN_TAXONOMY_CERT_OUT",
            "KM_HT_LEAN_TAXONOMY_CERT_CHECKER",
            "KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_MATRIX_CHECKER",
            "KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_MATRIX_CHECKER",
            "KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_SOURCE_CHECKER",
            "KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_SOURCE_CHECKER",
            "KM_HT_LEAN_NATIVE_ABOX_JOINT_SOURCE_CLASSIFICATION_CHECKER",
            "KM_HT_LEAN_FRONTIER_CHECKER",
            "KM_HT_LEAN_DOUBLING_TRACE_CHECKER",
            "KM_HT_LEAN_CARDINALITY_DOUBLING_TRACE_CHECKER",
            "KM_HT_LEAN_ROOTED_CARDINALITY_DOUBLING_TRACE_CHECKER",
            "KM_HT_LEAN_ORDINARY_PRODUCTION_RUN_CHECKER",
            "KM_HT_LEAN_ORDINARY_UNSAT_PRODUCTION_RUN_CHECKER",
            "KM_HT_LEAN_CARDINALITY_PRODUCTION_RUN_CHECKER",
            "KM_HT_LEAN_ROOTED_CARDINALITY_PRODUCTION_RUN_CHECKER",
            "KM_HT_LEAN_ROOTED_ORDINARY_PRODUCTION_RUN_CHECKER",
            "KM_HT_LEAN_ROOTED_ORDINARY_TAXONOMY_PRODUCTION_RUN_CHECKER",
            "KM_HT_LEAN_ROOTED_CARDINALITY_TAXONOMY_PRODUCTION_RUN_CHECKER",
            "KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_RUN_MATRIX_CHECKER",
            "KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_RUN_MATRIX_CHECKER",
            "KM_HT_LEAN_CARDINALITY_FRONTIER_CHECKER",
            "KM_HT_LEAN_ROOTED_CARDINALITY_FRONTIER_CHECKER",
            "KM_HT_LEAN_PRODUCTION_BLOCKING_CHECKER",
            "KM_HT_LEAN_PRODUCTION_TRACE_CHECKER",
            "KM_HT_LEAN_FINITE_PRODUCTION_TERMINAL_CHECKER",
            "KM_HT_LEAN_REGULAR_PRODUCTION_TERMINAL_CHECKER",
            "KM_HT_LEAN_EQUALITY_PRODUCTION_BLOCKING_CHECKER",
            "KM_HT_LEAN_EQUALITY_PRODUCTION_TERMINAL_CHECKER",
            "KM_HT_LEAN_EQUALITY_PRODUCTION_TRACE_CHECKER",
        ] {
            assert!(
                HT_LEAN_CERTIFICATION_ENV.contains(&required),
                "{required} must not permit unchecked HT publication",
            );
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

    // concept ids: A=0,B=1,C=2,D=3 ; role r=0
    const A: C = 0;
    const B: C = 1;
    const D: C = 3;
    const R0: R = 0;

    fn native_wire_input() -> crate::orchestrate::cb_to_ht::TInput {
        use crate::orchestrate::cb_to_ht::{NativeAboxJson, NativeIndividualJson};
        crate::orchestrate::cb_to_ht::TInput {
            concepts: vec!["NA".into(), "NB".into(), "A".into()],
            roles: vec!["r".into()],
            nominals: vec![0, 1],
            native_abox: NativeAboxJson {
                complete: true,
                individuals: vec![
                    NativeIndividualJson {
                        proxies: vec![0],
                        assertions: vec![2],
                    },
                    NativeIndividualJson {
                        proxies: vec![1],
                        assertions: Vec::new(),
                    },
                ],
                different: vec![(0, 1)],
                role_assertions: vec![(0, 0, 1)],
                negative_role_assertions: Vec::new(),
            },
            ..crate::orchestrate::cb_to_ht::TInput::default()
        }
    }

    fn consumer_input(producer: &crate::orchestrate::cb_to_ht::TInput) -> TInput {
        serde_json::from_slice(&serde_json::to_vec(producer).unwrap()).unwrap()
    }

    fn checked_joint_native_abox_classification(
        checker: &std::path::Path,
        producer: &crate::orchestrate::cb_to_ht::TInput,
        clauses: Vec<Clause>,
        queries: &[C],
        label: &str,
    ) -> Vec<u8> {
        let inp = consumer_input(producer);
        let mut reasoner = hypertableau::Ht::new_certified(clauses.clone());
        reasoner.set_nominals(inp.nominals.clone());
        reasoner.set_native_abox(
            inp.native_abox
                .individuals
                .iter()
                .map(|individual| {
                    (
                        individual
                            .proxies
                            .iter()
                            .map(|&concept| concept as C)
                            .collect(),
                        individual
                            .assertions
                            .iter()
                            .map(|&concept| concept as C)
                            .collect(),
                    )
                })
                .collect(),
            inp.native_abox.different.clone(),
            inp.native_abox
                .role_assertions
                .iter()
                .map(|&(role, source, target)| (role as R, source, target))
                .collect(),
        );
        if !inp.card_defs.is_empty() {
            reasoner.set_number(true);
            reasoner.set_card_defs_raw(
                &inp.card_defs
                    .iter()
                    .map(|definition| {
                        (
                            definition.marker as C,
                            definition.min,
                            definition.n,
                            definition.role as R,
                            definition.filler as C,
                            definition.exact,
                        )
                    })
                    .collect::<Vec<_>>(),
            );
        }
        let (consistent, global, global_run) = reasoner
            .lean_global_decision_certificate_and_native_run_json()
            .expect("normalized native ABox global decision");
        let global_run = global_run.expect("native ABox global run");
        let (taxonomy, taxonomy_runs) = reasoner
            .lean_native_abox_taxonomy_certificate_and_run_json(queries)
            .expect("normalized native ABox taxonomy matrix");
        let source_global = native_abox_source_decision_document(
            &inp,
            &clauses,
            &global,
            consistent,
        )
        .expect("compose source native ABox global decision");
        let source_taxonomy = native_abox_source_taxonomy_document(&inp, &clauses, &taxonomy)
            .expect("compose source native ABox taxonomy matrix");
        let (global_checker, taxonomy_checker) = if inp.card_defs.is_empty() {
            (
                "KM_HT_TEST_LEAN_SOURCE_BOUND_NATIVE_ABOX_GLOBAL_CHECKER",
                "KM_HT_TEST_LEAN_SOURCE_BOUND_NATIVE_ABOX_TAXONOMY_CHECKER",
            )
        } else {
            (
                "KM_HT_TEST_LEAN_SOURCE_BOUND_NATIVE_ABOX_CARDINALITY_GLOBAL_CHECKER",
                "KM_HT_TEST_LEAN_SOURCE_BOUND_NATIVE_ABOX_CARDINALITY_TAXONOMY_CHECKER",
            )
        };
        let global_checker = std::env::var_os(global_checker)
            .expect("source-bound native ABox global checker");
        let taxonomy_checker = std::env::var_os(taxonomy_checker)
            .expect("source-bound native ABox taxonomy checker");
        let source_bound_global = source_bound_native_abox_document(
            &inp,
            &source_global,
            "run",
            global_run,
        )
        .expect("compose source-bound native ABox global decision");
        run_ht_projection_checker(
            &source_bound_global,
            std::path::Path::new(&global_checker),
            label,
        )
        .expect("source-bound native ABox global checker accepts production evidence");
        let source_bound_taxonomy = source_bound_native_abox_document(
            &inp,
            &source_taxonomy,
            "runs",
            taxonomy_runs,
        )
        .expect("compose source-bound native ABox taxonomy");
        run_ht_projection_checker(
            &source_bound_taxonomy,
            std::path::Path::new(&taxonomy_checker),
            label,
        )
        .expect("source-bound native ABox taxonomy checker accepts production evidence");
        let document =
            native_abox_joint_source_classification_document(&inp, &clauses, &global, &taxonomy)
                .expect("compose joint native ABox classification");
        run_ht_projection_checker(&document, checker, label)
            .expect("joint source-classification checker accepts production evidence");
        document
    }


    #[test]
    fn mixed_skolem_projection_passes_the_real_lean_checker_and_rejects_omission() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_PROJECTION_CHECKER") else {
            return;
        };
        use crate::json_io::{JAtom as SourceAtom, JClause as SourceClause, JTerm};
        let x = || JTerm::Var { name: "x".into() };
        let fx = || JTerm::Fun {
            function: "f".into(),
            arg: Box::new(x()),
        };
        let body = || {
            vec![SourceAtom::Concept {
                concept: "A".into(),
                term: x(),
            }]
        };
        let source = vec![
            SourceClause {
                body: body(),
                head: vec![SourceAtom::Role {
                    role: "r".into(),
                    source: x(),
                    target: fx(),
                }],
            },
            SourceClause {
                body: body(),
                head: vec![SourceAtom::Concept {
                    concept: "C".into(),
                    term: fx(),
                }],
            },
        ];
        let mut producer = crate::orchestrate::cb_to_ht::convert(
            &source,
            None,
            &std::collections::HashSet::new(),
            &[],
            &[],
            &[],
            false,
            &[],
            false,
        );
        assert!(producer.mixed_projection_source.is_some());
        let consumer = consumer_input(&producer);
        let projected = clauses_of_tinput(&consumer);
        check_direct_ht_projection(&consumer, &projected, std::path::Path::new(&checker))
            .expect("the real mixed Lean checker accepts production evidence");

        let mut omitted = projected.clone();
        omitted.pop();
        assert!(
            check_direct_ht_projection(&consumer, &omitted, std::path::Path::new(&checker))
                .unwrap_err()
                .contains("rejected")
        );

        let maximum = producer.concepts.len();
        producer.concepts.push("Qmax".into());
        let minimum = producer.concepts.len();
        producer.concepts.push("Qmin".into());
        let filler = producer
            .concepts
            .iter()
            .position(|concept| concept == "C")
            .expect("mixed projection filler");
        producer.card_defs = vec![
            crate::orchestrate::cb_to_ht::CardDefJson {
                marker: maximum,
                min: false,
                n: 1,
                role: 0,
                filler,
                exact: true,
            },
            crate::orchestrate::cb_to_ht::CardDefJson {
                marker: minimum,
                min: true,
                n: 2,
                role: 0,
                filler,
                exact: true,
            },
        ];
        producer.cardinality_exact_pairs = vec![
            crate::orchestrate::cb_to_ht::CardinalityExactPairJson {
                maximum: 0,
                minimum: 1,
            },
        ];
        producer.cardinality_projection_complete = true;
        let combined = consumer_input(&producer);
        check_direct_ht_projection(&combined, &projected, std::path::Path::new(&checker))
            .expect("the joint mixed/cardinality checker accepts complete evidence");

        producer.card_defs[1].exact = false;
        let forged = consumer_input(&producer);
        assert!(check_direct_ht_projection(&forged, &projected, std::path::Path::new(&checker))
            .unwrap_err()
            .contains("rejected"));
    }

    #[test]
    fn cardinality_projection_passes_the_real_lean_checker_and_rejects_false_exactness() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_PROJECTION_CHECKER") else {
            return;
        };
        let mut producer = crate::orchestrate::cb_to_ht::TInput {
            concepts: vec![
                "Qmax".into(),
                "Qmin".into(),
                "C".into(),
                "positive".into(),
                "A".into(),
                "B".into(),
            ],
            roles: vec!["r".into()],
            direct_projection_source: Some(vec![
                crate::orchestrate::cb_to_ht::DirectProjectionClause {
                    variable_names: vec!["x".into()],
                    body: vec![crate::orchestrate::cb_to_ht::DirectProjectionAtom::Con {
                        concept: "A".into(),
                        node: "x".into(),
                        neg: false,
                    }],
                    head: vec![crate::orchestrate::cb_to_ht::DirectProjectionAtom::Con {
                        concept: "B".into(),
                        node: "x".into(),
                        neg: false,
                    }],
                },
            ]),
            card_defs: vec![
                crate::orchestrate::cb_to_ht::CardDefJson {
                    marker: 0,
                    min: false,
                    n: 1,
                    role: 0,
                    filler: 2,
                    exact: true,
                },
                crate::orchestrate::cb_to_ht::CardDefJson {
                    marker: 1,
                    min: true,
                    n: 2,
                    role: 0,
                    filler: 2,
                    exact: true,
                },
                crate::orchestrate::cb_to_ht::CardDefJson {
                    marker: 3,
                    min: true,
                    n: 3,
                    role: 0,
                    filler: 2,
                    exact: false,
                },
            ],
            cardinality_exact_pairs: vec![
                crate::orchestrate::cb_to_ht::CardinalityExactPairJson {
                    maximum: 0,
                    minimum: 1,
                },
            ],
            cardinality_projection_complete: true,
            ..crate::orchestrate::cb_to_ht::TInput::default()
        };
        let consumer = consumer_input(&producer);
        let projected = vec![Clause {
            body: vec![con(false, 4, 0)],
            head: vec![con(false, 5, 0)],
        }];
        check_direct_ht_projection(&consumer, &projected, std::path::Path::new(&checker))
            .expect("the combined Lean checker accepts the residual and cardinality projection");

        producer.card_defs[2].exact = true;
        let malformed = consumer_input(&producer);
        assert!(
            check_direct_ht_projection(&malformed, &projected, std::path::Path::new(&checker))
                .unwrap_err()
                .contains("rejected")
        );
    }

    #[test]
    fn multi_filler_bundle_projection_passes_the_real_lean_checker_and_rejects_omission() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_PROJECTION_CHECKER") else {
            return;
        };
        use crate::json_io::{JAtom as SourceAtom, JClause as SourceClause, JTerm};
        let x = || JTerm::Var { name: "x".into() };
        let fx = || JTerm::Fun {
            function: "f".into(),
            arg: Box::new(x()),
        };
        let body = || {
            vec![SourceAtom::Concept {
                concept: "A".into(),
                term: x(),
            }]
        };
        let source = vec![
            SourceClause {
                body: body(),
                head: vec![SourceAtom::Role {
                    role: "r".into(),
                    source: x(),
                    target: fx(),
                }],
            },
            SourceClause {
                body: body(),
                head: vec![SourceAtom::Concept {
                    concept: "C".into(),
                    term: fx(),
                }],
            },
            SourceClause {
                body: body(),
                head: vec![SourceAtom::Concept {
                    concept: "D".into(),
                    term: fx(),
                }],
            },
        ];
        let rbox = vec![
            vec!["subrole".into(), "r".into(), "s".into()],
            vec!["subrole".into(), "s".into(), "t".into()],
            vec!["domain".into(), "t".into(), "E".into()],
        ];
        let producer = crate::orchestrate::cb_to_ht::convert(
            &source,
            Some(&rbox),
            &std::collections::HashSet::new(),
            &[],
            &[],
            &[],
            false,
            &[],
            false,
        );
        let evidence = producer
            .bundle_projection_source
            .as_ref()
            .expect("bundle projection evidence");
        assert_eq!(evidence.domain_extras.len(), 1);
        assert_eq!(evidence.domain_extras[0].path, ["s", "t"]);
        let consumer = consumer_input(&producer);
        let projected = clauses_of_tinput(&consumer);
        check_direct_ht_projection(&consumer, &projected, std::path::Path::new(&checker))
            .expect("the real bundle Lean checker accepts production evidence");

        let mut omitted = projected.clone();
        omitted.pop();
        assert!(
            check_direct_ht_projection(&consumer, &omitted, std::path::Path::new(&checker))
                .unwrap_err()
                .contains("rejected")
        );

        let mut false_path = consumer;
        false_path
            .bundle_projection_source
            .as_mut()
            .expect("bundle evidence")
            .domain_extras[0]
            .path = vec!["t".into()];
        assert!(check_direct_ht_projection(
            &false_path,
            &projected,
            std::path::Path::new(&checker)
        )
        .unwrap_err()
        .contains("rejected"));

        let mut combined_producer = producer;
        let maximum = combined_producer.concepts.len();
        combined_producer.concepts.push("Qmax".into());
        let minimum = combined_producer.concepts.len();
        combined_producer.concepts.push("Qmin".into());
        let filler = combined_producer
            .concepts
            .iter()
            .position(|concept| concept == "C")
            .expect("bundle filler concept");
        let combined_source = combined_producer
            .bundle_projection_source
            .as_mut()
            .expect("bundle projection evidence");
        combined_source.source_concepts.push("Qmax".into());
        combined_source.source_concepts.push("Qmin".into());
        combined_producer.card_defs = vec![
            crate::orchestrate::cb_to_ht::CardDefJson {
                marker: maximum,
                min: false,
                n: 1,
                role: 0,
                filler,
                exact: true,
            },
            crate::orchestrate::cb_to_ht::CardDefJson {
                marker: minimum,
                min: true,
                n: 2,
                role: 0,
                filler,
                exact: true,
            },
        ];
        combined_producer.cardinality_exact_pairs = vec![
            crate::orchestrate::cb_to_ht::CardinalityExactPairJson {
                maximum: 0,
                minimum: 1,
            },
        ];
        combined_producer.cardinality_projection_complete = true;
        let combined = consumer_input(&combined_producer);
        check_direct_ht_projection(&combined, &projected, std::path::Path::new(&checker))
            .expect("the joint bundle/cardinality checker accepts complete evidence");

        let mut missing_source_name = consumer_input(&combined_producer);
        missing_source_name
            .bundle_projection_source
            .as_mut()
            .expect("bundle evidence")
            .source_concepts
            .retain(|concept| concept != "Qmin");
        assert!(check_direct_ht_projection(
            &missing_source_name,
            &projected,
            std::path::Path::new(&checker)
        )
        .unwrap_err()
        .contains("absent from bundle source concepts"));

        combined_producer.card_defs[1].exact = false;
        let forged = consumer_input(&combined_producer);
        assert!(check_direct_ht_projection(&forged, &projected, std::path::Path::new(&checker))
            .unwrap_err()
            .contains("rejected"));
    }

    #[test]
    fn native_abox_wire_contract_rejects_empty_duplicate_or_unowned_nominal_proxies() {
        let mut empty = native_wire_input();
        empty.native_abox.individuals[0].proxies.clear();
        assert!(validate_native_abox(&consumer_input(&empty))
            .unwrap_err()
            .contains("no singleton proxy"));

        let mut duplicate = native_wire_input();
        duplicate.native_abox.individuals[1].proxies = vec![0];
        assert!(validate_native_abox(&consumer_input(&duplicate))
            .unwrap_err()
            .contains("duplicate ownership"));

        let mut absent = native_wire_input();
        absent.nominals.retain(|&id| id != 1);
        assert!(validate_native_abox(&consumer_input(&absent))
            .unwrap_err()
            .contains("absent from nominals"));

        let mut unowned = native_wire_input();
        unowned.nominals.push(2);
        assert!(validate_native_abox(&consumer_input(&unowned))
            .unwrap_err()
            .contains("every nominal proxy"));
    }

    #[test]
    fn native_abox_projection_passes_real_lean_checker_and_rejects_forgery() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_PROJECTION_CHECKER") else {
            return;
        };
        let valid = consumer_input(&native_wire_input());
        check_native_abox_projection(&valid, std::path::Path::new(&checker))
            .expect("complete native ABox projection passes Lean");

        let mut duplicate = native_wire_input();
        duplicate.native_abox.individuals[1].proxies = vec![0];
        assert!(check_native_abox_projection(
            &consumer_input(&duplicate),
            std::path::Path::new(&checker)
        )
        .unwrap_err()
        .contains("rejected"));

        let mut missing_nominal = native_wire_input();
        missing_nominal.nominals.pop();
        assert!(check_native_abox_projection(
            &consumer_input(&missing_nominal),
            std::path::Path::new(&checker)
        )
        .unwrap_err()
        .contains("rejected"));
    }

    #[test]
    fn direct_native_abox_refutation_passes_real_lean_checker() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_PROJECTION_CHECKER") else {
            return;
        };
        use crate::orchestrate::cb_to_ht::{DirectProjectionAtom, DirectProjectionClause};
        let mut producer = native_wire_input();
        producer.direct_projection_source = Some(vec![DirectProjectionClause {
            variable_names: vec!["x".into()],
            body: vec![DirectProjectionAtom::Con {
                concept: "A".into(),
                node: "x".into(),
                neg: false,
            }],
            head: Vec::new(),
        }]);
        let inp = consumer_input(&producer);
        let mut reasoner = hypertableau::Ht::new_certified(vec![Clause::new(
            vec![con(false, 2, 0)],
            Vec::new(),
        )]);
        reasoner.set_nominals(inp.nominals.clone());
        reasoner.set_native_abox(
            vec![(vec![0], vec![2]), (vec![1], Vec::new())],
            vec![(0, 1)],
            vec![(0, 0, 1)],
        );
        let normalized = reasoner
            .lean_native_abox_unsat_refutation_json()
            .expect("normalized native ABox refutation");
        let document = direct_native_abox_refutation_document(&inp, &normalized)
            .expect("compose direct source and native ABox refutation");
        run_ht_projection_checker(
            &document,
            std::path::Path::new(&checker),
            "direct-native-abox-refutation",
        )
        .expect("combined direct source/native ABox refutation passes Lean");

        if let Some(source_checker) =
            std::env::var_os("KM_HT_TEST_LEAN_NATIVE_ABOX_SOURCE_DECISION_CHECKER")
        {
            let refutation: serde_json::Value = serde_json::from_str(&normalized).unwrap();
            let decision = serde_json::json!({
                "version": 1,
                "evidence": { "unsat": { "refutation": refutation } },
            })
            .to_string();
            let source_decision = native_abox_source_decision_document(
                &inp,
                &clauses_of_tinput(&inp),
                &decision,
                false,
            )
                .expect("compose direct native ABox source decision");
            run_ht_projection_checker(
                &source_decision,
                std::path::Path::new(&source_checker),
                "direct-native-abox-source-decision",
            )
            .expect("direct native ABox source decision passes Lean");

            let mut forged: serde_json::Value =
                serde_json::from_slice(&source_decision).unwrap();
            forged["evidence"]["unsat"]["refutation"]["source"] =
                serde_json::json!([]);
            assert!(run_ht_projection_checker(
                &serde_json::to_vec(&forged).unwrap(),
                std::path::Path::new(&source_checker),
                "forged-direct-native-abox-source-decision",
            )
            .unwrap_err()
            .contains("rejected"));
        }

        let mut forged: serde_json::Value = serde_json::from_slice(&document).unwrap();
        forged["source"] = serde_json::json!([]);
        assert!(run_ht_projection_checker(
            &serde_json::to_vec(&forged).unwrap(),
            std::path::Path::new(&checker),
            "forged-direct-native-abox-refutation",
        )
        .unwrap_err()
        .contains("rejected"));
    }

    #[test]
    fn direct_native_abox_sat_source_decision_passes_real_lean_checker() {
        let Some(checker) =
            std::env::var_os("KM_HT_TEST_LEAN_NATIVE_ABOX_SOURCE_DECISION_CHECKER")
        else {
            return;
        };
        let mut producer = native_wire_input();
        producer.direct_projection_source = Some(Vec::new());
        let inp = consumer_input(&producer);
        let mut reasoner = hypertableau::Ht::new_certified(Vec::new());
        reasoner.set_nominals(inp.nominals.clone());
        reasoner.set_native_abox(
            vec![(vec![0], vec![2]), (vec![1], Vec::new())],
            vec![(0, 1)],
            vec![(0, 0, 1)],
        );
        let (consistent, decision) = reasoner
            .lean_native_abox_decision_certificate_json()
            .expect("native ABox SAT decision");
        assert!(consistent);
        let source_decision = native_abox_source_decision_document(
            &inp,
            &clauses_of_tinput(&inp),
            &decision,
            true,
        )
            .expect("compose direct native ABox SAT source decision");
        run_ht_projection_checker(
            &source_decision,
            std::path::Path::new(&checker),
            "direct-native-abox-sat-source-decision",
        )
        .expect("direct native ABox SAT source decision passes Lean");

        let mut forged: serde_json::Value = serde_json::from_slice(&source_decision).unwrap();
        forged["evidence"]["sat"]["certificate"]["source"] = serde_json::json!([{
            "variable_names": ["x"],
            "body": [{"concept": "A", "node": "x", "neg": false}],
            "head": [],
        }]);
        assert!(run_ht_projection_checker(
            &serde_json::to_vec(&forged).unwrap(),
            std::path::Path::new(&checker),
            "forged-direct-native-abox-sat-source-decision",
        )
        .unwrap_err()
        .contains("rejected"));
    }

    #[test]
    fn direct_native_abox_taxonomy_source_matrix_passes_real_lean_checker() {
        let Some(checker) =
            std::env::var_os("KM_HT_TEST_LEAN_NATIVE_ABOX_TAXONOMY_SOURCE_CHECKER")
        else {
            return;
        };
        let mut producer = native_wire_input();
        producer.direct_projection_source = Some(Vec::new());
        let inp = consumer_input(&producer);
        let mut reasoner = hypertableau::Ht::new_certified(Vec::new());
        reasoner.set_nominals(inp.nominals.clone());
        reasoner.set_native_abox(
            vec![(vec![0], vec![2]), (vec![1], Vec::new())],
            vec![(0, 1)],
            vec![(0, 0, 1)],
        );
        let (normalized, runs) = reasoner
            .lean_native_abox_taxonomy_certificate_and_run_json(&[2])
            .expect("normalized native ABox taxonomy matrix");
        let source_taxonomy = native_abox_source_taxonomy_document(
            &inp,
            &clauses_of_tinput(&inp),
            &normalized,
        )
            .expect("compose direct source with native ABox taxonomy matrix");
        run_ht_projection_checker(
            &source_taxonomy,
            std::path::Path::new(&checker),
            "direct-native-abox-taxonomy-source",
        )
        .expect("direct source native ABox taxonomy passes Lean");

        let source_bound_checker = std::env::var_os(
            "KM_HT_TEST_LEAN_SOURCE_BOUND_NATIVE_ABOX_TAXONOMY_CHECKER",
        )
        .expect("source-bound native ABox taxonomy checker");
        let source_bound = source_bound_native_abox_document(
            &inp,
            &source_taxonomy,
            "runs",
            runs,
        )
        .expect("compose source-bound native ABox taxonomy");
        run_ht_projection_checker(
            &source_bound,
            std::path::Path::new(&source_bound_checker),
            "source-bound-direct-native-abox-taxonomy",
        )
        .expect("source-bound direct native ABox taxonomy passes Lean");

        let mut detached: serde_json::Value = serde_json::from_slice(&source_bound).unwrap();
        detached["runs"]["concept_runs"][0]["terminal"]["query"] =
            serde_json::json!({"concept":{"root":0,"concept":999}});
        assert!(run_ht_projection_checker(
            &serde_json::to_vec(&detached).unwrap(),
            std::path::Path::new(&source_bound_checker),
            "detached-direct-native-abox-taxonomy",
        )
        .unwrap_err()
        .contains("rejected"));

        let mut forged: serde_json::Value =
            serde_json::from_slice(&source_taxonomy).unwrap();
        forged["source"] = serde_json::json!([{
            "variable_names": ["x"],
            "body": [{"concept": "A", "node": "x", "neg": false}],
            "head": [],
        }]);
        assert!(run_ht_projection_checker(
            &serde_json::to_vec(&forged).unwrap(),
            std::path::Path::new(&checker),
            "forged-direct-native-abox-taxonomy-source",
        )
        .unwrap_err()
        .contains("rejected"));
    }

    #[test]
    fn joint_native_abox_classification_carries_one_source_and_abox() {
        let mut producer = native_wire_input();
        producer.direct_projection_source = Some(Vec::new());
        let inp = consumer_input(&producer);
        let clauses = clauses_of_tinput(&inp);
        let mut reasoner = hypertableau::Ht::new_certified(clauses.clone());
        reasoner.set_nominals(inp.nominals.clone());
        reasoner.set_native_abox(
            vec![(vec![0], vec![2]), (vec![1], Vec::new())],
            vec![(0, 1)],
            vec![(0, 0, 1)],
        );
        let (consistent, global) = reasoner
            .lean_native_abox_decision_certificate_json()
            .expect("normalized native ABox decision");
        assert!(consistent);
        let taxonomy = reasoner
            .lean_taxonomy_certificate_json(&[2])
            .expect("normalized native ABox taxonomy matrix");
        let document =
            native_abox_joint_source_classification_document(&inp, &clauses, &global, &taxonomy)
                .expect("compose joint native ABox classification");
        let wire: serde_json::Value = serde_json::from_slice(&document).unwrap();
        assert_eq!(wire["version"], 1);
        assert_eq!(wire["source"], serde_json::json!([]));
        assert_eq!(wire["abox"]["complete"], true);
        assert_eq!(
            wire["abox"]["individuals"],
            serde_json::to_value(&inp.native_abox.individuals).unwrap()
        );
        assert_eq!(
            wire["global"],
            serde_json::from_str::<serde_json::Value>(&global).unwrap()
        );
        assert_eq!(
            wire["taxonomy"],
            serde_json::from_str::<serde_json::Value>(&taxonomy).unwrap()
        );
    }

    #[test]
    fn joint_native_abox_source_matrix_passes_real_lean_checker_on_all_six_routes() {
        use crate::orchestrate::cb_to_ht::{
            BundleProjectionLit, BundleProjectionSource, CardDefJson, DirectProjectionAtom,
            DirectProjectionClause, MixedProjectionSource, NativeAboxJson, NativeIndividualJson,
            SkolemProjectionBundle, SkolemProjectionPair,
        };
        let checker = std::env::var_os("KM_HT_TEST_LEAN_JOINT_NATIVE_ABOX_CLASSIFICATION_CHECKER")
            .expect("the HT certification gate must provide the real joint Lean checker");
        let checker = std::path::Path::new(&checker);
        let body = || {
            vec![DirectProjectionAtom::Con {
                concept: "A".into(),
                node: "x".into(),
                neg: false,
            }]
        };
        let direct_clause = || DirectProjectionClause {
            variable_names: vec!["x".into()],
            body: body(),
            head: Vec::new(),
        };

        let mut direct = native_wire_input();
        direct.direct_projection_source = Some(Vec::new());
        let direct_document = checked_joint_native_abox_classification(
            checker,
            &direct,
            Vec::new(),
            &[2],
            "joint-direct-native-abox-classification",
        );

        let mut mixed = native_wire_input();
        mixed.concepts.push("C".into());
        mixed.mixed_projection_source = Some(MixedProjectionSource {
            functions: vec!["f".into()],
            direct: vec![direct_clause()],
            pairs: vec![SkolemProjectionPair {
                variable_names: vec!["x".into()],
                body: body(),
                source: "x".into(),
                function: "f".into(),
                role: "r".into(),
                filler: "C".into(),
                neg: false,
            }],
        });
        checked_joint_native_abox_classification(
            checker,
            &mixed,
            vec![
                Clause::new(vec![con(false, 2, 0)], Vec::new()),
                Clause::new(vec![con(false, 2, 0)], vec![exists(0, false, 3, 0)]),
            ],
            &[2, 3],
            "joint-mixed-native-abox-classification",
        );

        let mut bundle = native_wire_input();
        bundle.concepts.extend(["D".into(), "C".into()]);
        bundle.bundle_projection_source = Some(BundleProjectionSource {
            source_concepts: vec!["NA".into(), "NB".into(), "A".into(), "C".into()],
            functions: vec!["f".into()],
            direct: vec![direct_clause()],
            bundles: vec![SkolemProjectionBundle {
                variable_names: vec!["x".into()],
                body: body(),
                source: "x".into(),
                function: "f".into(),
                role: "r".into(),
                fillers: vec![BundleProjectionLit {
                    concept: "C".into(),
                    neg: false,
                }],
                definer: "D".into(),
            }],
            domain_extras: Vec::new(),
        });
        checked_joint_native_abox_classification(
            checker,
            &bundle,
            vec![
                Clause::new(vec![con(false, 2, 0)], Vec::new()),
                Clause::new(vec![con(false, 2, 0)], vec![exists(0, false, 3, 0)]),
                Clause::new(vec![con(false, 3, 0)], vec![con(false, 4, 0)]),
            ],
            &[2, 4],
            "joint-bundle-native-abox-classification",
        );

        let direct_cardinality = crate::orchestrate::cb_to_ht::TInput {
            concepts: vec!["marker".into(), "filler".into(), "nominal".into()],
            roles: vec!["r".into()],
            nominals: vec![2],
            native_abox: NativeAboxJson {
                complete: true,
                individuals: vec![NativeIndividualJson {
                    proxies: vec![2],
                    assertions: vec![0],
                }],
                ..NativeAboxJson::default()
            },
            direct_projection_source: Some(Vec::new()),
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 1,
                role: 0,
                filler: 1,
                exact: false,
            }],
            cardinality_projection_complete: true,
            ..crate::orchestrate::cb_to_ht::TInput::default()
        };
        checked_joint_native_abox_classification(
            checker,
            &direct_cardinality,
            Vec::new(),
            &[0, 1],
            "joint-direct-native-abox-cardinality-classification",
        );

        let mut mixed_cardinality = mixed;
        mixed_cardinality.concepts.push("marker".into());
        mixed_cardinality.card_defs = vec![CardDefJson {
            marker: 4,
            min: false,
            n: 1,
            role: 0,
            filler: 3,
            exact: false,
        }];
        mixed_cardinality.cardinality_projection_complete = true;
        checked_joint_native_abox_classification(
            checker,
            &mixed_cardinality,
            vec![
                Clause::new(vec![con(false, 2, 0)], Vec::new()),
                Clause::new(vec![con(false, 2, 0)], vec![exists(0, false, 3, 0)]),
            ],
            &[2, 3],
            "joint-mixed-native-abox-cardinality-classification",
        );

        let mut bundle_cardinality = bundle;
        bundle_cardinality.concepts.push("M".into());
        bundle_cardinality
            .bundle_projection_source
            .as_mut()
            .unwrap()
            .source_concepts
            .push("M".into());
        bundle_cardinality.card_defs = vec![CardDefJson {
            marker: 5,
            min: false,
            n: 1,
            role: 0,
            filler: 4,
            exact: false,
        }];
        bundle_cardinality.cardinality_projection_complete = true;
        checked_joint_native_abox_classification(
            checker,
            &bundle_cardinality,
            vec![
                Clause::new(vec![con(false, 2, 0)], Vec::new()),
                Clause::new(vec![con(false, 2, 0)], vec![exists(0, false, 3, 0)]),
                Clause::new(vec![con(false, 3, 0)], vec![con(false, 4, 0)]),
            ],
            &[2, 4],
            "joint-bundle-native-abox-cardinality-classification",
        );

        let mut forged_source: serde_json::Value =
            serde_json::from_slice(&direct_document).unwrap();
        forged_source["source"] = serde_json::json!([{
            "variableNames": ["x"],
            "body": [{"con": {"concept": "A", "node": "x", "neg": false}}],
            "head": []
        }]);
        assert!(run_ht_projection_checker(
            &serde_json::to_vec(&forged_source).unwrap(),
            checker,
            "forged-joint-native-abox-source",
        )
        .unwrap_err()
        .contains("rejected"));

        let mut forged_abox: serde_json::Value = serde_json::from_slice(&direct_document).unwrap();
        forged_abox["abox"]["individuals"][0]["assertions"] = serde_json::json!([1]);
        assert!(run_ht_projection_checker(
            &serde_json::to_vec(&forged_abox).unwrap(),
            checker,
            "forged-joint-native-abox-shared-abox",
        )
        .unwrap_err()
        .contains("rejected"));
    }


    #[test]
    fn direct_native_abox_cardinality_taxonomy_source_matrix_passes_real_lean_checker() {
        let Some(checker) = std::env::var_os(
            "KM_HT_TEST_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_SOURCE_CHECKER",
        ) else {
            return;
        };
        use crate::orchestrate::cb_to_ht::{
            CardDefJson, NativeAboxJson, NativeIndividualJson,
        };
        let producer = crate::orchestrate::cb_to_ht::TInput {
            concepts: vec!["marker".into(), "filler".into(), "nominal".into()],
            roles: vec!["r".into()],
            nominals: vec![2],
            native_abox: NativeAboxJson {
                complete: true,
                individuals: vec![NativeIndividualJson {
                    proxies: vec![2],
                    assertions: vec![0],
                }],
                different: Vec::new(),
                role_assertions: Vec::new(),
                negative_role_assertions: Vec::new(),
            },
            direct_projection_source: Some(Vec::new()),
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 1,
                role: 0,
                filler: 1,
                exact: false,
            }],
            cardinality_projection_complete: true,
            ..crate::orchestrate::cb_to_ht::TInput::default()
        };
        let inp = consumer_input(&producer);
        let clauses = Vec::<Clause>::new();
        let mut reasoner = hypertableau::Ht::new_certified(clauses.clone());
        reasoner.set_nominals(inp.nominals.clone());
        reasoner.set_native_abox(vec![(vec![2], vec![0])], Vec::new(), Vec::new());
        reasoner.set_number(true);
        reasoner.set_card_defs_raw(&[(0, false, 1, 0, 1, false)]);
        let normalized = reasoner
            .lean_taxonomy_certificate_json(&[0, 1])
            .expect("normalized native ABox cardinality taxonomy matrix");
        let source_taxonomy = native_abox_source_taxonomy_document(
            &inp,
            &clauses,
            &normalized,
        )
        .expect("compose direct source with native ABox cardinality taxonomy");
        run_ht_projection_checker(
            &source_taxonomy,
            std::path::Path::new(&checker),
            "direct-native-abox-cardinality-taxonomy-source",
        )
        .expect("direct source native ABox cardinality taxonomy passes Lean");

        let mut forged: serde_json::Value =
            serde_json::from_slice(&source_taxonomy).unwrap();
        forged["projection"]["definitions"][0]["n"] = serde_json::json!(2);
        assert!(run_ht_projection_checker(
            &serde_json::to_vec(&forged).unwrap(),
            std::path::Path::new(&checker),
            "forged-direct-native-abox-cardinality-taxonomy-source",
        )
        .unwrap_err()
        .contains("rejected"));
    }

    #[test]
    fn mixed_native_abox_cardinality_taxonomy_source_matrix_passes_real_lean_checker() {
        let Some(checker) = std::env::var_os(
            "KM_HT_TEST_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_SOURCE_CHECKER",
        ) else {
            return;
        };
        use crate::orchestrate::cb_to_ht::{
            CardDefJson, DirectProjectionAtom, DirectProjectionClause,
            MixedProjectionSource, SkolemProjectionPair,
        };
        let mut producer = native_wire_input();
        producer.concepts.extend(["C".into(), "marker".into()]);
        let body = vec![DirectProjectionAtom::Con {
            concept: "A".into(),
            node: "x".into(),
            neg: false,
        }];
        producer.mixed_projection_source = Some(MixedProjectionSource {
            functions: vec!["f".into()],
            direct: vec![DirectProjectionClause {
                variable_names: vec!["x".into()],
                body: body.clone(),
                head: Vec::new(),
            }],
            pairs: vec![SkolemProjectionPair {
                variable_names: vec!["x".into()],
                body,
                source: "x".into(),
                function: "f".into(),
                role: "r".into(),
                filler: "C".into(),
                neg: false,
            }],
        });
        producer.card_defs = vec![CardDefJson {
            marker: 4,
            min: false,
            n: 1,
            role: 0,
            filler: 3,
            exact: false,
        }];
        producer.cardinality_projection_complete = true;
        let inp = consumer_input(&producer);
        let clauses = vec![
            Clause::new(vec![con(false, 2, 0)], Vec::new()),
            Clause::new(vec![con(false, 2, 0)], vec![exists(0, false, 3, 0)]),
        ];
        let mut reasoner = hypertableau::Ht::new_certified(clauses.clone());
        reasoner.set_nominals(inp.nominals.clone());
        reasoner.set_native_abox(
            vec![(vec![0], vec![2]), (vec![1], Vec::new())],
            vec![(0, 1)],
            vec![(0, 0, 1)],
        );
        reasoner.set_number(true);
        reasoner.set_card_defs_raw(&[(4, false, 1, 0, 3, false)]);
        let normalized = reasoner
            .lean_taxonomy_certificate_json(&[2, 3])
            .expect("normalized mixed native ABox cardinality taxonomy matrix");
        let source_taxonomy = native_abox_source_taxonomy_document(
            &inp,
            &clauses,
            &normalized,
        )
        .expect("compose mixed source with native ABox cardinality taxonomy");
        run_ht_projection_checker(
            &source_taxonomy,
            std::path::Path::new(&checker),
            "mixed-native-abox-cardinality-taxonomy-source",
        )
        .expect("mixed source native ABox cardinality taxonomy passes Lean");

        let mut forged: serde_json::Value =
            serde_json::from_slice(&source_taxonomy).unwrap();
        forged["projection"]["pairs"] = serde_json::json!([]);
        assert!(run_ht_projection_checker(
            &serde_json::to_vec(&forged).unwrap(),
            std::path::Path::new(&checker),
            "forged-mixed-native-abox-cardinality-taxonomy-source",
        )
        .unwrap_err()
        .contains("rejected"));
    }

    #[test]
    fn bundle_native_abox_cardinality_taxonomy_source_matrix_passes_real_lean_checker() {
        let Some(checker) = std::env::var_os(
            "KM_HT_TEST_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_SOURCE_CHECKER",
        ) else {
            return;
        };
        use crate::orchestrate::cb_to_ht::{
            BundleProjectionLit, BundleProjectionSource, CardDefJson,
            DirectProjectionAtom, DirectProjectionClause, SkolemProjectionBundle,
        };
        let mut producer = native_wire_input();
        producer.concepts.extend(["D".into(), "C".into(), "M".into()]);
        let body = vec![DirectProjectionAtom::Con {
            concept: "A".into(),
            node: "x".into(),
            neg: false,
        }];
        producer.bundle_projection_source = Some(BundleProjectionSource {
            source_concepts: vec![
                "NA".into(), "NB".into(), "A".into(), "C".into(), "M".into(),
            ],
            functions: vec!["f".into()],
            direct: vec![DirectProjectionClause {
                variable_names: vec!["x".into()],
                body: body.clone(),
                head: Vec::new(),
            }],
            bundles: vec![SkolemProjectionBundle {
                variable_names: vec!["x".into()],
                body,
                source: "x".into(),
                function: "f".into(),
                role: "r".into(),
                fillers: vec![BundleProjectionLit {
                    concept: "C".into(),
                    neg: false,
                }],
                definer: "D".into(),
            }],
            domain_extras: Vec::new(),
        });
        producer.card_defs = vec![CardDefJson {
            marker: 5,
            min: false,
            n: 1,
            role: 0,
            filler: 4,
            exact: false,
        }];
        producer.cardinality_projection_complete = true;
        let inp = consumer_input(&producer);
        let clauses = vec![
            Clause::new(vec![con(false, 2, 0)], Vec::new()),
            Clause::new(vec![con(false, 2, 0)], vec![exists(0, false, 3, 0)]),
            Clause::new(vec![con(false, 3, 0)], vec![con(false, 4, 0)]),
        ];
        let mut reasoner = hypertableau::Ht::new_certified(clauses.clone());
        reasoner.set_nominals(inp.nominals.clone());
        reasoner.set_native_abox(
            vec![(vec![0], vec![2]), (vec![1], Vec::new())],
            vec![(0, 1)],
            vec![(0, 0, 1)],
        );
        reasoner.set_number(true);
        reasoner.set_card_defs_raw(&[(5, false, 1, 0, 4, false)]);
        let normalized = reasoner
            .lean_taxonomy_certificate_json(&[2, 4])
            .expect("normalized bundle native ABox cardinality taxonomy matrix");
        let source_taxonomy = native_abox_source_taxonomy_document(
            &inp,
            &clauses,
            &normalized,
        )
        .expect("compose bundle source with native ABox cardinality taxonomy");
        run_ht_projection_checker(
            &source_taxonomy,
            std::path::Path::new(&checker),
            "bundle-native-abox-cardinality-taxonomy-source",
        )
        .expect("bundle source native ABox cardinality taxonomy passes Lean");

        let mut forged: serde_json::Value =
            serde_json::from_slice(&source_taxonomy).unwrap();
        forged["projection"]["abox_source_map"][2] = serde_json::json!(3);
        assert!(run_ht_projection_checker(
            &serde_json::to_vec(&forged).unwrap(),
            std::path::Path::new(&checker),
            "forged-bundle-native-abox-cardinality-taxonomy-source",
        )
        .unwrap_err()
        .contains("rejected"));
    }

    #[test]
    fn mixed_native_abox_taxonomy_source_matrix_passes_real_lean_checker() {
        let Some(checker) =
            std::env::var_os("KM_HT_TEST_LEAN_NATIVE_ABOX_TAXONOMY_SOURCE_CHECKER")
        else {
            return;
        };
        use crate::orchestrate::cb_to_ht::{
            DirectProjectionAtom, DirectProjectionClause, MixedProjectionSource,
            SkolemProjectionPair,
        };
        let mut producer = native_wire_input();
        producer.concepts.push("C".into());
        let body = vec![DirectProjectionAtom::Con {
            concept: "A".into(),
            node: "x".into(),
            neg: false,
        }];
        producer.mixed_projection_source = Some(MixedProjectionSource {
            functions: vec!["f".into()],
            direct: vec![DirectProjectionClause {
                variable_names: vec!["x".into()],
                body: body.clone(),
                head: Vec::new(),
            }],
            pairs: vec![SkolemProjectionPair {
                variable_names: vec!["x".into()],
                body,
                source: "x".into(),
                function: "f".into(),
                role: "r".into(),
                filler: "C".into(),
                neg: false,
            }],
        });
        let inp = consumer_input(&producer);
        let mut reasoner = hypertableau::Ht::new_certified(vec![
            Clause::new(vec![con(false, 2, 0)], Vec::new()),
            Clause::new(vec![con(false, 2, 0)], vec![exists(0, false, 3, 0)]),
        ]);
        reasoner.set_nominals(inp.nominals.clone());
        reasoner.set_native_abox(
            vec![(vec![0], vec![2]), (vec![1], Vec::new())],
            vec![(0, 1)],
            vec![(0, 0, 1)],
        );
        let normalized = reasoner
            .lean_taxonomy_certificate_json(&[2, 3])
            .expect("normalized mixed native ABox taxonomy matrix");
        let source_taxonomy = native_abox_source_taxonomy_document(
            &inp,
            &clauses_of_tinput(&inp),
            &normalized,
        )
            .expect("compose mixed source with native ABox taxonomy matrix");
        run_ht_projection_checker(
            &source_taxonomy,
            std::path::Path::new(&checker),
            "mixed-native-abox-taxonomy-source",
        )
        .expect("mixed source native ABox taxonomy passes Lean");

        let mut forged: serde_json::Value =
            serde_json::from_slice(&source_taxonomy).unwrap();
        forged["pairs"] = serde_json::json!([]);
        assert!(run_ht_projection_checker(
            &serde_json::to_vec(&forged).unwrap(),
            std::path::Path::new(&checker),
            "forged-mixed-native-abox-taxonomy-source",
        )
        .unwrap_err()
        .contains("rejected"));
    }

    #[test]
    fn bundle_native_abox_taxonomy_source_matrix_passes_real_lean_checker() {
        let Some(checker) =
            std::env::var_os("KM_HT_TEST_LEAN_NATIVE_ABOX_TAXONOMY_SOURCE_CHECKER")
        else {
            return;
        };
        use crate::orchestrate::cb_to_ht::{
            BundleProjectionLit, BundleProjectionSource, DirectProjectionAtom,
            DirectProjectionClause, SkolemProjectionBundle,
        };
        let mut producer = native_wire_input();
        producer.concepts.extend(["D".into(), "C".into()]);
        let body = vec![DirectProjectionAtom::Con {
            concept: "A".into(),
            node: "x".into(),
            neg: false,
        }];
        producer.bundle_projection_source = Some(BundleProjectionSource {
            source_concepts: vec!["NA".into(), "NB".into(), "A".into(), "C".into()],
            functions: vec!["f".into()],
            direct: vec![DirectProjectionClause {
                variable_names: vec!["x".into()],
                body: body.clone(),
                head: Vec::new(),
            }],
            bundles: vec![SkolemProjectionBundle {
                variable_names: vec!["x".into()],
                body,
                source: "x".into(),
                function: "f".into(),
                role: "r".into(),
                fillers: vec![BundleProjectionLit {
                    concept: "C".into(),
                    neg: false,
                }],
                definer: "D".into(),
            }],
            domain_extras: Vec::new(),
        });
        let inp = consumer_input(&producer);
        let mut reasoner = hypertableau::Ht::new_certified(vec![
            Clause::new(vec![con(false, 2, 0)], Vec::new()),
            Clause::new(vec![con(false, 2, 0)], vec![exists(0, false, 3, 0)]),
            Clause::new(vec![con(false, 3, 0)], vec![con(false, 4, 0)]),
        ]);
        reasoner.set_nominals(inp.nominals.clone());
        reasoner.set_native_abox(
            vec![(vec![0], vec![2]), (vec![1], Vec::new())],
            vec![(0, 1)],
            vec![(0, 0, 1)],
        );
        let normalized = reasoner
            .lean_taxonomy_certificate_json(&[2, 4])
            .expect("normalized bundle native ABox taxonomy matrix");
        let source_taxonomy = native_abox_source_taxonomy_document(
            &inp,
            &clauses_of_tinput(&inp),
            &normalized,
        )
            .expect("compose bundle source with native ABox taxonomy matrix");
        run_ht_projection_checker(
            &source_taxonomy,
            std::path::Path::new(&checker),
            "bundle-native-abox-taxonomy-source",
        )
        .expect("bundle source native ABox taxonomy passes Lean");

        let mut forged: serde_json::Value =
            serde_json::from_slice(&source_taxonomy).unwrap();
        forged["abox_source_map"][4] = serde_json::json!(0);
        assert!(run_ht_projection_checker(
            &serde_json::to_vec(&forged).unwrap(),
            std::path::Path::new(&checker),
            "forged-bundle-native-abox-taxonomy-source",
        )
        .unwrap_err()
        .contains("rejected"));
    }

    #[test]
    fn direct_native_abox_cardinality_refutation_passes_real_lean_checker() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_PROJECTION_CHECKER") else {
            return;
        };
        use crate::orchestrate::cb_to_ht::{
            CardDefJson, NativeAboxJson, NativeIndividualJson,
        };
        let mut producer = crate::orchestrate::cb_to_ht::TInput {
            concepts: vec![
                "subject".into(),
                "left".into(),
                "right".into(),
                "marker".into(),
                "filler".into(),
            ],
            roles: vec!["r".into()],
            nominals: vec![0, 1, 2],
            native_abox: NativeAboxJson {
                complete: true,
                individuals: vec![
                    NativeIndividualJson {
                        proxies: vec![0],
                        assertions: vec![3],
                    },
                    NativeIndividualJson {
                        proxies: vec![1],
                        assertions: vec![4],
                    },
                    NativeIndividualJson {
                        proxies: vec![2],
                        assertions: vec![4],
                    },
                ],
                different: vec![(1, 2)],
                role_assertions: vec![(0, 0, 1), (0, 0, 2)],
                negative_role_assertions: Vec::new(),
            },
            direct_projection_source: Some(Vec::new()),
            card_defs: vec![CardDefJson {
                marker: 3,
                min: false,
                n: 1,
                role: 0,
                filler: 4,
                exact: false,
            }],
            cardinality_projection_complete: true,
            ..crate::orchestrate::cb_to_ht::TInput::default()
        };
        let inp = consumer_input(&producer);
        let clauses = Vec::<Clause>::new();
        let mut reasoner = hypertableau::Ht::new_certified(clauses.clone());
        reasoner.set_nominals(inp.nominals.clone());
        reasoner.set_native_abox(
            vec![
                (vec![0], vec![3]),
                (vec![1], vec![4]),
                (vec![2], vec![4]),
            ],
            vec![(1, 2)],
            vec![(0, 0, 1), (0, 0, 2)],
        );
        reasoner.set_card_defs_raw(&[(3, false, 1, 0, 4, false)]);
        let normalized = reasoner
            .lean_native_abox_cardinality_unsat_refutation_json()
            .expect("normalized native ABox cardinality refutation");
        let document = direct_native_abox_cardinality_refutation_document(
            &inp,
            &clauses,
            &normalized,
        )
        .expect("compose direct source and native ABox cardinality refutation");
        run_ht_projection_checker(
            &document,
            std::path::Path::new(&checker),
            "direct-native-abox-cardinality-refutation",
        )
        .expect("combined direct cardinality/native ABox refutation passes Lean");

        if let Some(source_checker) =
            std::env::var_os("KM_HT_TEST_LEAN_NATIVE_ABOX_SOURCE_DECISION_CHECKER")
        {
            let refutation: serde_json::Value = serde_json::from_str(&normalized).unwrap();
            let decision = serde_json::json!({
                "version": 1,
                "evidence": { "unsat": { "refutation": refutation } },
            })
            .to_string();
            let source_decision = native_abox_source_decision_document(
                &inp,
                &clauses,
                &decision,
                false,
            )
            .expect("compose direct cardinality source decision");
            run_ht_projection_checker(
                &source_decision,
                std::path::Path::new(&source_checker),
                "direct-native-abox-cardinality-source-decision",
            )
            .expect("direct cardinality source decision passes Lean");
        }

        producer.card_defs[0].n = 2;
        let forged_input = consumer_input(&producer);
        let forged = direct_native_abox_cardinality_refutation_document(
            &forged_input,
            &clauses,
            &normalized,
        )
        .expect("serialize forged definition");
        assert!(run_ht_projection_checker(
            &forged,
            std::path::Path::new(&checker),
            "forged-direct-native-abox-cardinality-refutation",
        )
        .unwrap_err()
        .contains("rejected"));
    }

    #[test]
    fn direct_native_abox_cardinality_sat_source_decision_passes_real_lean_checker() {
        let Some(checker) =
            std::env::var_os("KM_HT_TEST_LEAN_NATIVE_ABOX_SOURCE_DECISION_CHECKER")
        else {
            return;
        };
        use crate::orchestrate::cb_to_ht::{
            CardDefJson, NativeAboxJson, NativeIndividualJson,
        };
        let producer = crate::orchestrate::cb_to_ht::TInput {
            concepts: vec!["marker".into(), "filler".into(), "nominal".into()],
            roles: vec!["r".into()],
            nominals: vec![2],
            native_abox: NativeAboxJson {
                complete: true,
                individuals: vec![NativeIndividualJson {
                    proxies: vec![2],
                    assertions: Vec::new(),
                }],
                different: Vec::new(),
                role_assertions: Vec::new(),
                negative_role_assertions: Vec::new(),
            },
            direct_projection_source: Some(Vec::new()),
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 1,
                role: 0,
                filler: 1,
                exact: false,
            }],
            cardinality_projection_complete: true,
            ..crate::orchestrate::cb_to_ht::TInput::default()
        };
        let inp = consumer_input(&producer);
        let clauses = Vec::<Clause>::new();
        let mut reasoner = hypertableau::Ht::new_certified(clauses.clone());
        reasoner.set_nominals(inp.nominals.clone());
        reasoner.set_native_abox(vec![(vec![2], Vec::new())], Vec::new(), Vec::new());
        reasoner.set_number(true);
        reasoner.set_card_defs_raw(&[(0, false, 1, 0, 1, false)]);
        let (consistent, decision) = reasoner
            .lean_native_abox_cardinality_decision_certificate_json()
            .expect("native ABox cardinality SAT decision");
        assert!(consistent);
        let source_decision = native_abox_source_decision_document(
            &inp,
            &clauses,
            &decision,
            true,
        )
        .expect("compose direct cardinality SAT source decision");
        run_ht_projection_checker(
            &source_decision,
            std::path::Path::new(&checker),
            "direct-native-abox-cardinality-sat-source-decision",
        )
        .expect("direct cardinality SAT source decision passes Lean");

        let mut forged: serde_json::Value = serde_json::from_slice(&source_decision).unwrap();
        forged["evidence"]["sat"]["certificate"]["definitions"][0]["n"] =
            serde_json::json!(2);
        assert!(run_ht_projection_checker(
            &serde_json::to_vec(&forged).unwrap(),
            std::path::Path::new(&checker),
            "forged-direct-native-abox-cardinality-sat-source-decision",
        )
        .unwrap_err()
        .contains("rejected"));
    }

    #[test]
    fn mixed_native_abox_refutation_passes_real_lean_checker() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_PROJECTION_CHECKER") else {
            return;
        };
        use crate::orchestrate::cb_to_ht::{
            DirectProjectionAtom, DirectProjectionClause, MixedProjectionSource,
            SkolemProjectionPair,
        };
        let mut producer = native_wire_input();
        producer.concepts.push("C".into());
        let body = vec![DirectProjectionAtom::Con {
            concept: "A".into(),
            node: "x".into(),
            neg: false,
        }];
        producer.mixed_projection_source = Some(MixedProjectionSource {
            functions: vec!["f".into()],
            direct: vec![DirectProjectionClause {
                variable_names: vec!["x".into()],
                body: body.clone(),
                head: Vec::new(),
            }],
            pairs: vec![SkolemProjectionPair {
                variable_names: vec!["x".into()],
                body,
                source: "x".into(),
                function: "f".into(),
                role: "r".into(),
                filler: "C".into(),
                neg: false,
            }],
        });
        let inp = consumer_input(&producer);
        let mut reasoner = hypertableau::Ht::new_certified(vec![
            Clause::new(vec![con(false, 2, 0)], Vec::new()),
            Clause::new(vec![con(false, 2, 0)], vec![exists(0, false, 3, 0)]),
        ]);
        reasoner.set_nominals(inp.nominals.clone());
        reasoner.set_native_abox(
            vec![(vec![0], vec![2]), (vec![1], Vec::new())],
            vec![(0, 1)],
            vec![(0, 0, 1)],
        );
        let normalized = reasoner
            .lean_native_abox_unsat_refutation_json()
            .expect("normalized mixed native ABox refutation");
        let document = mixed_native_abox_refutation_document(&inp, &normalized)
            .expect("compose mixed source and native ABox refutation");
        run_ht_projection_checker(
            &document,
            std::path::Path::new(&checker),
            "mixed-native-abox-refutation",
        )
        .expect("combined mixed source/native ABox refutation passes Lean");

        if let Some(source_checker) =
            std::env::var_os("KM_HT_TEST_LEAN_NATIVE_ABOX_SOURCE_DECISION_CHECKER")
        {
            let refutation: serde_json::Value = serde_json::from_str(&normalized).unwrap();
            let decision = serde_json::json!({
                "version": 1,
                "evidence": { "unsat": { "refutation": refutation } },
            })
            .to_string();
            let source_decision = native_abox_source_decision_document(
                &inp,
                &clauses_of_tinput(&inp),
                &decision,
                false,
            )
                .expect("compose mixed native ABox source decision");
            run_ht_projection_checker(
                &source_decision,
                std::path::Path::new(&source_checker),
                "mixed-native-abox-source-decision",
            )
            .expect("mixed native ABox source decision passes Lean");
        }

        let mut forged: serde_json::Value = serde_json::from_slice(&document).unwrap();
        forged["pairs"] = serde_json::json!([]);
        assert!(run_ht_projection_checker(
            &serde_json::to_vec(&forged).unwrap(),
            std::path::Path::new(&checker),
            "forged-mixed-native-abox-refutation",
        )
        .unwrap_err()
        .contains("rejected"));
    }

    #[test]
    fn mixed_native_abox_cardinality_refutation_passes_real_lean_checker() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_PROJECTION_CHECKER") else {
            return;
        };
        use crate::orchestrate::cb_to_ht::{
            CardDefJson, DirectProjectionAtom, MixedProjectionSource, NativeAboxJson,
            NativeIndividualJson, SkolemProjectionPair,
        };
        let pair = SkolemProjectionPair {
            variable_names: vec!["x".into()],
            body: vec![DirectProjectionAtom::Con {
                concept: "marker".into(),
                node: "x".into(),
                neg: false,
            }],
            source: "x".into(),
            function: "f".into(),
            role: "r".into(),
            filler: "filler".into(),
            neg: false,
        };
        let mut producer = crate::orchestrate::cb_to_ht::TInput {
            concepts: vec![
                "subject".into(),
                "left".into(),
                "right".into(),
                "marker".into(),
                "filler".into(),
            ],
            roles: vec!["r".into()],
            nominals: vec![0, 1, 2],
            native_abox: NativeAboxJson {
                complete: true,
                individuals: vec![
                    NativeIndividualJson {
                        proxies: vec![0],
                        assertions: vec![3],
                    },
                    NativeIndividualJson {
                        proxies: vec![1],
                        assertions: vec![4],
                    },
                    NativeIndividualJson {
                        proxies: vec![2],
                        assertions: vec![4],
                    },
                ],
                different: vec![(1, 2)],
                role_assertions: vec![(0, 0, 1), (0, 0, 2)],
                negative_role_assertions: Vec::new(),
            },
            mixed_projection_source: Some(MixedProjectionSource {
                functions: vec!["f".into()],
                direct: Vec::new(),
                pairs: vec![pair],
            }),
            card_defs: vec![CardDefJson {
                marker: 3,
                min: false,
                n: 1,
                role: 0,
                filler: 4,
                exact: false,
            }],
            cardinality_projection_complete: true,
            ..crate::orchestrate::cb_to_ht::TInput::default()
        };
        let inp = consumer_input(&producer);
        let clauses = vec![Clause::new(
            vec![con(false, 3, 0)],
            vec![exists(0, false, 4, 0)],
        )];
        let mut reasoner = hypertableau::Ht::new_certified(clauses);
        reasoner.set_nominals(inp.nominals.clone());
        reasoner.set_native_abox(
            vec![
                (vec![0], vec![3]),
                (vec![1], vec![4]),
                (vec![2], vec![4]),
            ],
            vec![(1, 2)],
            vec![(0, 0, 1), (0, 0, 2)],
        );
        reasoner.set_card_defs_raw(&[(3, false, 1, 0, 4, false)]);
        let normalized = reasoner
            .lean_native_abox_cardinality_unsat_refutation_json()
            .expect("normalized mixed native ABox cardinality refutation");
        let document =
            mixed_native_abox_cardinality_refutation_document(&inp, &normalized)
                .expect("compose mixed source and native ABox cardinality refutation");
        run_ht_projection_checker(
            &document,
            std::path::Path::new(&checker),
            "mixed-native-abox-cardinality-refutation",
        )
        .expect("combined mixed cardinality/native ABox refutation passes Lean");

        if let Some(source_checker) =
            std::env::var_os("KM_HT_TEST_LEAN_NATIVE_ABOX_SOURCE_DECISION_CHECKER")
        {
            let refutation: serde_json::Value = serde_json::from_str(&normalized).unwrap();
            let decision = serde_json::json!({
                "version": 1,
                "evidence": { "unsat": { "refutation": refutation } },
            })
            .to_string();
            let source_decision = native_abox_source_decision_document(
                &inp,
                &clauses_of_tinput(&inp),
                &decision,
                false,
            )
            .expect("compose mixed cardinality source decision");
            run_ht_projection_checker(
                &source_decision,
                std::path::Path::new(&source_checker),
                "mixed-native-abox-cardinality-source-decision",
            )
            .expect("mixed cardinality source decision passes Lean");
        }

        producer
            .mixed_projection_source
            .as_mut()
            .unwrap()
            .pairs
            .clear();
        let forged_input = consumer_input(&producer);
        let forged =
            mixed_native_abox_cardinality_refutation_document(&forged_input, &normalized)
                .expect("serialize forged mixed projection");
        assert!(run_ht_projection_checker(
            &forged,
            std::path::Path::new(&checker),
            "forged-mixed-native-abox-cardinality-refutation",
        )
        .unwrap_err()
        .contains("rejected"));
    }

    #[test]
    fn bundle_native_abox_refutation_passes_real_lean_checker() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_PROJECTION_CHECKER") else {
            return;
        };
        use crate::orchestrate::cb_to_ht::{
            BundleProjectionLit, BundleProjectionSource, DirectProjectionAtom,
            DirectProjectionClause, SkolemProjectionBundle,
        };
        let mut producer = native_wire_input();
        producer.concepts.extend(["D".into(), "C".into()]);
        let body = vec![DirectProjectionAtom::Con {
            concept: "A".into(),
            node: "x".into(),
            neg: false,
        }];
        producer.bundle_projection_source = Some(BundleProjectionSource {
            source_concepts: vec!["NA".into(), "NB".into(), "A".into(), "C".into()],
            functions: vec!["f".into()],
            direct: vec![DirectProjectionClause {
                variable_names: vec!["x".into()],
                body: body.clone(),
                head: Vec::new(),
            }],
            bundles: vec![SkolemProjectionBundle {
                variable_names: vec!["x".into()],
                body,
                source: "x".into(),
                function: "f".into(),
                role: "r".into(),
                fillers: vec![BundleProjectionLit {
                    concept: "C".into(),
                    neg: false,
                }],
                definer: "D".into(),
            }],
            domain_extras: Vec::new(),
        });
        let inp = consumer_input(&producer);
        let mut reasoner = hypertableau::Ht::new_certified(vec![
            Clause::new(vec![con(false, 2, 0)], Vec::new()),
            Clause::new(vec![con(false, 2, 0)], vec![exists(0, false, 3, 0)]),
            Clause::new(vec![con(false, 3, 0)], vec![con(false, 4, 0)]),
        ]);
        reasoner.set_nominals(inp.nominals.clone());
        reasoner.set_native_abox(
            vec![(vec![0], vec![2]), (vec![1], Vec::new())],
            vec![(0, 1)],
            vec![(0, 0, 1)],
        );
        let normalized = reasoner
            .lean_native_abox_unsat_refutation_json()
            .expect("normalized bundle native ABox refutation");
        let document = bundle_native_abox_refutation_document(&inp, &normalized)
            .expect("compose bundle source and native ABox refutation");
        run_ht_projection_checker(
            &document,
            std::path::Path::new(&checker),
            "bundle-native-abox-refutation",
        )
        .expect("combined bundle source/native ABox refutation passes Lean");

        if let Some(source_checker) =
            std::env::var_os("KM_HT_TEST_LEAN_NATIVE_ABOX_SOURCE_DECISION_CHECKER")
        {
            let refutation: serde_json::Value = serde_json::from_str(&normalized).unwrap();
            let decision = serde_json::json!({
                "version": 1,
                "evidence": { "unsat": { "refutation": refutation } },
            })
            .to_string();
            let source_decision = native_abox_source_decision_document(
                &inp,
                &clauses_of_tinput(&inp),
                &decision,
                false,
            )
                .expect("compose bundle native ABox source decision");
            run_ht_projection_checker(
                &source_decision,
                std::path::Path::new(&source_checker),
                "bundle-native-abox-source-decision",
            )
            .expect("bundle native ABox source decision passes Lean");
        }

        let mut forged: serde_json::Value = serde_json::from_slice(&document).unwrap();
        forged["abox_source_map"][2] = serde_json::json!(3);
        assert!(run_ht_projection_checker(
            &serde_json::to_vec(&forged).unwrap(),
            std::path::Path::new(&checker),
            "forged-bundle-native-abox-refutation",
        )
        .unwrap_err()
        .contains("rejected"));
    }

    #[test]
    fn bundle_native_abox_cardinality_refutation_passes_real_lean_checker() {
        let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_PROJECTION_CHECKER") else {
            return;
        };
        use crate::orchestrate::cb_to_ht::{
            BundleProjectionLit, BundleProjectionSource, CardDefJson, DirectProjectionAtom,
            NativeAboxJson, NativeIndividualJson, SkolemProjectionBundle,
        };
        let body = vec![DirectProjectionAtom::Con {
            concept: "marker".into(),
            node: "x".into(),
            neg: false,
        }];
        let mut producer = crate::orchestrate::cb_to_ht::TInput {
            concepts: vec![
                "subject".into(),
                "left".into(),
                "right".into(),
                "marker".into(),
                "D".into(),
                "filler".into(),
            ],
            roles: vec!["r".into()],
            nominals: vec![0, 1, 2],
            native_abox: NativeAboxJson {
                complete: true,
                individuals: vec![
                    NativeIndividualJson {
                        proxies: vec![0],
                        assertions: vec![3],
                    },
                    NativeIndividualJson {
                        proxies: vec![1],
                        assertions: vec![5],
                    },
                    NativeIndividualJson {
                        proxies: vec![2],
                        assertions: vec![5],
                    },
                ],
                different: vec![(1, 2)],
                role_assertions: vec![(0, 0, 1), (0, 0, 2)],
                negative_role_assertions: Vec::new(),
            },
            bundle_projection_source: Some(BundleProjectionSource {
                source_concepts: vec![
                    "subject".into(),
                    "left".into(),
                    "right".into(),
                    "marker".into(),
                    "filler".into(),
                ],
                functions: vec!["f".into()],
                direct: Vec::new(),
                bundles: vec![SkolemProjectionBundle {
                    variable_names: vec!["x".into()],
                    body,
                    source: "x".into(),
                    function: "f".into(),
                    role: "r".into(),
                    fillers: vec![BundleProjectionLit {
                        concept: "filler".into(),
                        neg: false,
                    }],
                    definer: "D".into(),
                }],
                domain_extras: Vec::new(),
            }),
            card_defs: vec![CardDefJson {
                marker: 3,
                min: false,
                n: 1,
                role: 0,
                filler: 5,
                exact: false,
            }],
            cardinality_projection_complete: true,
            ..crate::orchestrate::cb_to_ht::TInput::default()
        };
        let inp = consumer_input(&producer);
        let clauses = vec![
            Clause::new(
                vec![con(false, 3, 0)],
                vec![exists(0, false, 4, 0)],
            ),
            Clause::new(vec![con(false, 4, 0)], vec![con(false, 5, 0)]),
        ];
        let mut reasoner = hypertableau::Ht::new_certified(clauses);
        reasoner.set_nominals(inp.nominals.clone());
        reasoner.set_native_abox(
            vec![
                (vec![0], vec![3]),
                (vec![1], vec![5]),
                (vec![2], vec![5]),
            ],
            vec![(1, 2)],
            vec![(0, 0, 1), (0, 0, 2)],
        );
        reasoner.set_card_defs_raw(&[(3, false, 1, 0, 5, false)]);
        let normalized = reasoner
            .lean_native_abox_cardinality_unsat_refutation_json()
            .expect("normalized bundle native ABox cardinality refutation");
        let document =
            bundle_native_abox_cardinality_refutation_document(&inp, &normalized)
                .expect("compose bundle source and native ABox cardinality refutation");
        run_ht_projection_checker(
            &document,
            std::path::Path::new(&checker),
            "bundle-native-abox-cardinality-refutation",
        )
        .expect("combined bundle cardinality/native ABox refutation passes Lean");

        if let Some(source_checker) =
            std::env::var_os("KM_HT_TEST_LEAN_NATIVE_ABOX_SOURCE_DECISION_CHECKER")
        {
            let refutation: serde_json::Value = serde_json::from_str(&normalized).unwrap();
            let decision = serde_json::json!({
                "version": 1,
                "evidence": { "unsat": { "refutation": refutation } },
            })
            .to_string();
            let source_decision = native_abox_source_decision_document(
                &inp,
                &clauses_of_tinput(&inp),
                &decision,
                false,
            )
            .expect("compose bundle cardinality source decision");
            run_ht_projection_checker(
                &source_decision,
                std::path::Path::new(&source_checker),
                "bundle-native-abox-cardinality-source-decision",
            )
            .expect("bundle cardinality source decision passes Lean");
        }

        producer.card_defs[0].filler = 3;
        let forged_input = consumer_input(&producer);
        let forged =
            bundle_native_abox_cardinality_refutation_document(&forged_input, &normalized)
                .expect("serialize forged bundle cardinality projection");
        assert!(run_ht_projection_checker(
            &forged,
            std::path::Path::new(&checker),
            "forged-bundle-native-abox-cardinality-refutation",
        )
        .unwrap_err()
        .contains("rejected"));
    }

    #[test]
    fn native_negative_role_wire_fact_reconstructs_a_missing_exact_clash_clause() {
        let mut producer = native_wire_input();
        producer
            .native_abox
            .negative_role_assertions
            .push((0, 0, 1));
        let parsed = consumer_input(&producer);
        let validated = validate_native_abox(&parsed).expect("complete native ABox validates");
        assert_eq!(validated.missing_negative_clauses.len(), 1);

        producer
            .clauses
            .push(crate::orchestrate::cb_to_ht::HtClause {
                body: vec![
                    crate::orchestrate::cb_to_ht::HAtom::Concept {
                        neg: false,
                        c: 0,
                        t: 0,
                    },
                    crate::orchestrate::cb_to_ht::HAtom::Role { r: 0, s: 0, t: 1 },
                    crate::orchestrate::cb_to_ht::HAtom::Concept {
                        neg: false,
                        c: 1,
                        t: 1,
                    },
                ],
                head: Vec::new(),
            });
        let validated =
            validate_native_abox(&consumer_input(&producer)).expect("exact guard validates");
        assert!(validated.missing_negative_clauses.is_empty());
    }

    #[test]
    fn native_abox_never_falls_through_to_legacy_tableau_without_ht() {
        let input = serde_json::to_string(&native_wire_input()).unwrap();
        let error = run_json_inner(&input, Some(false)).unwrap_err();
        assert!(error.contains("requires the hypertableau mechanism"));
    }

    #[test]
    fn certified_role_chain_side_data_reconstructs_exact_source_clauses() {
        let clauses = certified_role_chain_clauses(&[(R0, R1, 2)], &[3]);
        assert_eq!(clauses.len(), 2);
        assert!(matches!(
            clauses[0].body.as_slice(),
            [
                Atom::Role { r: R0, s: X, t: 1 },
                Atom::Role { r: R1, s: 1, t: 2 }
            ]
        ));
        assert!(matches!(
            clauses[0].head.as_slice(),
            [Atom::Role { r: 2, s: X, t: 2 }]
        ));
        assert!(matches!(
            clauses[1].body.as_slice(),
            [
                Atom::Role { r: 3, s: X, t: 1 },
                Atom::Role { r: 3, s: 1, t: 2 }
            ]
        ));
        assert!(matches!(
            clauses[1].head.as_slice(),
            [Atom::Role { r: 3, s: X, t: 2 }]
        ));
    }

    #[test]
    fn certified_raw_role_chain_participates_in_ht_refutation() {
        let mut clauses = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, B, X)], vec![exists(R1, false, D, X)]),
            Clause::new(
                vec![con(false, A, X), role(2, X, 1)],
                vec![con(false, 2, 1)],
            ),
            Clause::new(vec![con(false, D, X)], vec![con(true, 2, X)]),
        ];
        clauses.extend(certified_role_chain_clauses(&[(R0, R1, 2)], &[]));
        let mut ht = hypertableau::Ht::new(clauses);
        assert_eq!(ht.consistent(&[CLit::pos(A)]), Some(false));
        let document = ht
            .lean_unsatisfiable_concept_certificate_json(A)
            .expect("raw role-chain refutation has finite Lean evidence");
        if let Some(checker) = std::env::var_os("KM_HT_TEST_LEAN_CHECKER") {
            let path = std::env::temp_dir().join(format!(
                "km-ht-raw-chain-cert-{}-{}.json",
                std::process::id(),
                std::thread::current().name().unwrap_or("test")
            ));
            std::fs::write(&path, &document).unwrap();
            let output = std::process::Command::new(checker)
                .arg(&path)
                .output()
                .expect("run native Lean checker on raw role-chain refutation");
            let _ = std::fs::remove_file(path);
            assert!(
                output.status.success(),
                "Lean rejected raw role-chain evidence: {}\n{}",
                String::from_utf8_lossy(&output.stderr),
                document
            );
        }
    }

    #[test]
    fn clash_a_and_not_a() {
        // {A, ¬A} on the root is inconsistent.
        let t = Tableau::new(vec![]);
        assert!(!t.consistent(&[CLit::pos(A), CLit::neg(A)]));
    }

    #[test]
    fn simple_sat() {
        // A alone is satisfiable.
        let t = Tableau::new(vec![]);
        assert!(t.consistent(&[CLit::pos(A)]));
    }

    #[test]
    fn existential_then_universal_clash() {
        // A ⊑ ∃r.B,  A ⊑ ∀r.¬B  ⇒ A unsatisfiable.
        // clauses: A(x) → ∃r.B(x) ;  A(x) ∧ r(x,y) → ¬B(y)  ... but ¬B(y) head clashes with B(y).
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(
                vec![con(false, A, X), role(R0, X, 1)],
                vec![con(true, B, 1)],
            ),
        ];
        let t = Tableau::new(cls);
        assert!(!t.consistent(&[CLit::pos(A)]));
    }

    #[test]
    fn existential_universal_consistent() {
        // A ⊑ ∃r.B, A ⊑ ∀r.D  is satisfiable (successor gets B and D, no clash).
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(
                vec![con(false, A, X), role(R0, X, 1)],
                vec![con(false, D, 1)],
            ),
        ];
        let t = Tableau::new(cls);
        assert!(t.consistent(&[CLit::pos(A)]));
    }

    #[test]
    fn disjunction_branch() {
        // A ⊑ B ⊔ D, A ⊑ ¬B, A ⊑ ¬D ⇒ A unsat (both branches clash).
        let cls = vec![
            Clause::new(
                vec![con(false, A, X)],
                vec![con(false, B, X), con(false, D, X)],
            ),
            Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
            Clause::new(vec![con(false, A, X)], vec![con(true, D, X)]),
        ];
        let t = Tableau::new(cls);
        assert!(!t.consistent(&[CLit::pos(A)]));
    }

    #[test]
    fn disjunction_one_branch_open() {
        // A ⊑ B ⊔ D, A ⊑ ¬B ⇒ A still satisfiable (via the D branch).
        let cls = vec![
            Clause::new(
                vec![con(false, A, X)],
                vec![con(false, B, X), con(false, D, X)],
            ),
            Clause::new(vec![con(false, A, X)], vec![con(true, B, X)]),
        ];
        let t = Tableau::new(cls);
        assert!(t.consistent(&[CLit::pos(A)]));
    }

    #[test]
    fn infinite_chain_blocks_and_terminates() {
        // A ⊑ ∃r.A : an infinite r-chain of A's; blocking must make this terminate
        // and report satisfiable.
        let cls = vec![Clause::new(
            vec![con(false, A, X)],
            vec![exists(R0, false, A, X)],
        )];
        let t = Tableau::new(cls);
        assert!(t.consistent(&[CLit::pos(A)]));
    }

    fn eq(s: Var, t: Var) -> Atom {
        Atom::Eq { s, t }
    }

    // Extra concept ids for the ALCQ tests: E=4, F=5, P=6, Q=7, S0=8, S1=9, C2=2.
    const E: C = 4;
    const F: C = 5;
    const P: C = 6;
    const Q: C = 7;
    const S0: C = 8;
    const S1: C = 9;
    const C2: C = 2;

    #[test]
    fn at_most_one_merge_clash_unsat() {
        // A ⊑ ∃r.(B⊓E), A ⊑ ∃r.(B⊓F), E⊓F ⊑ ⊥, A ⊑ ≤1 r.B  ⇒  A unsat:
        // the two r-successors are both B, so ≤1 merges them, and the merged node
        // carries E and F at once — a clash.
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, P, X)]),
            Clause::new(vec![con(false, P, X)], vec![con(false, B, X)]),
            Clause::new(vec![con(false, P, X)], vec![con(false, E, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, Q, X)]),
            Clause::new(vec![con(false, Q, X)], vec![con(false, B, X)]),
            Clause::new(vec![con(false, Q, X)], vec![con(false, F, X)]),
            Clause::new(vec![con(false, E, X), con(false, F, X)], vec![]),
            // ≤1 r.B : A(x) ∧ r(x,1) ∧ B(1) ∧ r(x,2) ∧ B(2) → ≈(1,2)
            Clause::new(
                vec![
                    con(false, A, X),
                    role(R0, X, 1),
                    con(false, B, 1),
                    role(R0, X, 2),
                    con(false, B, 2),
                ],
                vec![eq(1, 2)],
            ),
        ];
        let mut t = Tableau::new(cls);
        t.set_number(true);
        assert!(!t.consistent(&[CLit::pos(A)]));
    }

    #[test]
    fn at_most_one_merge_consistent() {
        // Same minus the E⊓F clash: the merge is harmless, so A is satisfiable.
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, P, X)]),
            Clause::new(vec![con(false, P, X)], vec![con(false, B, X)]),
            Clause::new(vec![con(false, P, X)], vec![con(false, E, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, Q, X)]),
            Clause::new(vec![con(false, Q, X)], vec![con(false, B, X)]),
            Clause::new(vec![con(false, Q, X)], vec![con(false, F, X)]),
            Clause::new(
                vec![
                    con(false, A, X),
                    role(R0, X, 1),
                    con(false, B, 1),
                    role(R0, X, 2),
                    con(false, B, 2),
                ],
                vec![eq(1, 2)],
            ),
        ];
        let mut t = Tableau::new(cls);
        t.set_number(true);
        assert!(t.consistent(&[CLit::pos(A)]));
    }

    #[test]
    fn ge2_with_le1_unsat_via_slots() {
        // ExactCardinality-style: ≥2 r.C ⊓ ≤1 r.C ⇒ unsat. ≥2 is two existentials
        // with disjoint slots S0,S1; ≤1 tries to merge the two C-successors but
        // their disjoint slots clash, so no branch survives.
        let cls = vec![
            // ≥2 r.C as two slotted existentials
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, S0, X)]),
            Clause::new(vec![con(false, S0, X)], vec![con(false, C2, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, S1, X)]),
            Clause::new(vec![con(false, S1, X)], vec![con(false, C2, X)]),
            Clause::new(vec![con(false, S0, X), con(false, S1, X)], vec![]), // slot disjointness
            // ≤1 r.C
            Clause::new(
                vec![
                    con(false, A, X),
                    role(R0, X, 1),
                    con(false, C2, 1),
                    role(R0, X, 2),
                    con(false, C2, 2),
                ],
                vec![eq(1, 2)],
            ),
        ];
        let mut t = Tableau::new(cls);
        t.set_number(true);
        assert!(!t.consistent(&[CLit::pos(A)]));
    }

    #[test]
    fn ge2_alone_consistent_and_terminates() {
        // ≥2 r.C alone (two disjoint-slot successors, no at-most) is satisfiable
        // and must terminate.
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, S0, X)]),
            Clause::new(vec![con(false, S0, X)], vec![con(false, C2, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, S1, X)]),
            Clause::new(vec![con(false, S1, X)], vec![con(false, C2, X)]),
            Clause::new(vec![con(false, S0, X), con(false, S1, X)], vec![]),
        ];
        let mut t = Tableau::new(cls);
        t.set_number(true);
        assert!(t.consistent(&[CLit::pos(A)]));
    }

    #[test]
    fn le2_three_successors_merges_consistent() {
        // ≤2 r.C with three C-successors (no forced distinctness) is satisfiable:
        // the ≤2 branch merges one pair, leaving two, no clash.
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, P, X)]),
            Clause::new(vec![con(false, P, X)], vec![con(false, C2, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, Q, X)]),
            Clause::new(vec![con(false, Q, X)], vec![con(false, C2, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, E, X)]),
            Clause::new(vec![con(false, E, X)], vec![con(false, C2, X)]),
            // ≤2 r.C : A ∧ 3×(r,C) → ≈(1,2) ∨ ≈(1,3) ∨ ≈(2,3)
            Clause::new(
                vec![
                    con(false, A, X),
                    role(R0, X, 1),
                    con(false, C2, 1),
                    role(R0, X, 2),
                    con(false, C2, 2),
                    role(R0, X, 3),
                    con(false, C2, 3),
                ],
                vec![eq(1, 2), eq(1, 3), eq(2, 3)],
            ),
        ];
        let mut t = Tableau::new(cls);
        t.set_number(true);
        assert!(t.consistent(&[CLit::pos(A)]));
    }

    // Nominal concept {a} = N, second role t = R1.
    const N: C = 10;
    const R1: R = 1;

    #[test]
    fn nominal_singleton_merge_unsat() {
        // A ⊑ ∃s.{a}, A ⊑ ∃t.{a}, A ⊑ ∀s.C, A ⊑ ∀t.¬C ⇒ A unsat: the s- and
        // t-successors are both the singleton {a}, so the o-rule merges them and
        // the merged node carries C and ¬C — a clash. WITHOUT the singleton
        // merge the two successors are distinct (one C, one ¬C) and A would look
        // satisfiable, so this is the test that distinguishes real nominal
        // reasoning from passing __nom__a through as a free concept name.
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, N, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R1, false, N, X)]),
            Clause::new(
                vec![con(false, A, X), role(R0, X, 1)],
                vec![con(false, C2, 1)],
            ),
            Clause::new(
                vec![con(false, A, X), role(R1, X, 1)],
                vec![con(true, C2, 1)],
            ),
        ];
        let mut t = Tableau::new(cls);
        t.set_nominals(vec![N]);
        assert!(!t.consistent(&[CLit::pos(A)]));
    }

    #[test]
    fn nominal_singleton_merge_consistent() {
        // Same minus the conflict (∀t.C instead of ∀t.¬C): merging the two
        // {a}-successors is harmless, so A is satisfiable.
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, N, X)]),
            Clause::new(vec![con(false, A, X)], vec![exists(R1, false, N, X)]),
            Clause::new(
                vec![con(false, A, X), role(R0, X, 1)],
                vec![con(false, C2, 1)],
            ),
            Clause::new(
                vec![con(false, A, X), role(R1, X, 1)],
                vec![con(false, C2, 1)],
            ),
        ];
        let mut t = Tableau::new(cls);
        t.set_nominals(vec![N]);
        assert!(t.consistent(&[CLit::pos(A)]));
    }

    #[test]
    fn nominal_abox_subsumption() {
        // Q ≡ {a}, {a} ⊑ C  (the ABox fact C(a) lifted). Then Q ⊑ C: testing
        // {Q, ¬C} must be unsat (Q forces __nom__a, which merges into the seeded
        // nominal root and inherits C, clashing with ¬C). But C ⊑ Q is false:
        // {C, ¬Q} is satisfiable (C may have non-{a} instances).
        let cls = vec![
            Clause::new(vec![con(false, Q, X)], vec![con(false, N, X)]), // Q ⊑ {a}
            Clause::new(vec![con(false, N, X)], vec![con(false, Q, X)]), // {a} ⊑ Q
            Clause::new(vec![con(false, N, X)], vec![con(false, C2, X)]), // {a} ⊑ C
        ];
        let mut t = Tableau::new(cls);
        t.set_nominals(vec![N]);
        assert!(!t.consistent(&[CLit::pos(Q), CLit::neg(C2)])); // Q ⊑ C
        assert!(t.consistent(&[CLit::pos(C2), CLit::neg(Q)])); // C ⋢ Q
    }

    #[test]
    fn nominal_abox_global_inconsistency() {
        // {a} ⊑ C and {a} ⊑ ¬C make the named individual a contradictory, so the
        // whole KB is inconsistent — every concept (even one unrelated to a) is
        // unsatisfiable. Caught only because find_model seeds the nominal root.
        let cls = vec![
            Clause::new(vec![con(false, N, X)], vec![con(false, C2, X)]),
            Clause::new(vec![con(false, N, X)], vec![con(true, C2, X)]),
        ];
        let mut t = Tableau::new(cls);
        t.set_nominals(vec![N]);
        assert!(!t.consistent(&[])); // KB inconsistent
        assert!(!t.consistent(&[CLit::pos(A)])); // hence A unsat too
    }
}
