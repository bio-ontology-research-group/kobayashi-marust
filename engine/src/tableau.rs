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
            eprintln!("KM_TAB_STATS progress expands={} branch_tries={} backtracks={}", e + 1, t, b);
        }
    });
}
#[inline]
fn stat_try() {
    STATS.with(|s| { let (e, t, b) = s.get(); s.set((e, t + 1, b)); });
}
#[inline]
fn stat_backtrack() {
    STATS.with(|s| { let (e, t, b) = s.get(); s.set((e, t, b + 1)); });
}

/// Atomic concept id, atomic role id, clause variable, completion-graph node.
pub type C = u32;
pub type R = u32;
pub type Var = u32;
pub type Node = usize;

/// The center variable `x` of every HT-clause.
pub const X: Var = 0;

/// A concept literal `A` or `¬A` (post-NNF, so concepts are atomic).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
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
        CLit { neg: !self.neg, c: self.c }
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
            if let Some(i) = self.out_edges[s].iter().position(|&(rr, tt)| rr == r && tt == t) {
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
        let MergeUndo { keep, gone, moved_concepts, moved_exobl, moved_edges, moved_pred } = m;
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
        self.get(k).expect("unbound clause variable in substitution")
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
}

impl Tableau {
    pub fn new(clauses: Vec<Clause>) -> Tableau {
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
                ClauseInfo { cl, body_lits, body_roles, disjunctive }
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
                    matches!(self.expand_inc(&mut g, q, 0), Outcome::Sat)
                } else {
                    false
                }
            }
        };
        if std::env::var("KM_TAB_STATS").is_ok() {
            let (e, t, b) = STATS.with(|s| s.get());
            eprintln!(
                "KM_TAB_STATS expands={e} branch_tries={t} backtracks={b} nodes={}",
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
                eprintln!("KM_TAB_STATS horn_saturate iter={} nodes={}", hs_iter, g.n());
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
            let carriers: Vec<Node> =
                (0..g.n()).filter(|&u| g.alive(u) && g.concepts[u].contains(&lit)).collect();
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
                eprintln!("KM_TAB_STATS saturate round={} nodes={} (entering horn_saturate)", sat_round, g.n());
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
        for info in &self.clauses {
            if !info.disjunctive || !self.matchable(info, g) {
                continue;
            }
            // Only the first usable match is needed, so visit with early exit
            // instead of materialising every solution.
            let mut found: Option<Subst> = None;
            self.match_visit(&info.cl, g, &mut |subst| {
                if info.cl.head.iter().all(|v| !self.head_atom_present(g, v, subst)) {
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

    fn head_atom_present(&self, g: &Graph, v: &Atom, subst: &Subst) -> bool {
        match v {
            Atom::Concept { lit, t } => g.concepts[g.find(subst.lookup(*t))].contains(lit),
            Atom::Role { r, s, t } => {
                g.edges.contains(&(*r, g.find(subst.lookup(*s)), g.find(subst.lookup(*t))))
            }
            Atom::Exists { r, fil, t } => {
                let s = g.find(subst.lookup(*t));
                g.exobl[s].contains(&(*r, *fil))
                    || g.out_edges[s].iter().any(|&(rr, u)| rr == *r && g.concepts[u].contains(fil))
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
                    if g.concepts[nd].contains(lit) && !self.match_rec(cl, g, i + 1, subst, vars, f) {
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
                            if let Some(c) = self.fire_clause(&self.clauses[ci], g, seed, &mut pending)
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
                            if let Some(c) = self.fire_clause(&self.clauses[ci], g, seed, &mut pending)
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
                eprintln!("KM_TAB_STATS saturate_inc round={} nodes={} queue={} (entering horn_inc)", inc_round, g.n(), queue.len());
            }
            if let Some(c) = self.horn_inc(g, &mut queue) {
                return Some(c);
            }
            if prog {
                eprintln!("KM_TAB_STATS saturate_inc round={} horn_inc DONE nodes={}", inc_round, g.n());
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

    /// Incremental analogue of the non-careful `expand`, with dependency-directed
    /// backjumping. `dl` is the current decision level; the disjunction picked
    /// here introduces level `dl+1`. When a disjunct's subtree clashes with a
    /// conflict that does *not* mention `dl+1`, the choice is irrelevant, so the
    /// whole disjunction is abandoned and the conflict propagates up (skipping
    /// untried siblings and any irrelevant intervening decisions).
    fn expand_inc(&self, g: &mut Graph, queue: VecDeque<NewFact>, dl: u32) -> Outcome {
        stat_expand();
        if let Some(c) = self.saturate_inc(g, queue) {
            return Outcome::Conflict(c);
        }
        if let Some((head, subst, bdep)) = self.find_disjunctive(g) {
            let level = dl + 1;
            let mut accum = DepSet::new();
            for v in &head {
                stat_try();
                let cp = g.checkpoint();
                let mut ddep = bdep.clone();
                ddep.insert(level);
                let pend = self.resolve_head(g, v, &subst, ddep);
                let mut child: VecDeque<NewFact> = VecDeque::new();
                let conflict = match self.apply_pending(g, vec![pend], &mut child) {
                    Some(c) => Some(c),
                    None => match self.expand_inc(g, child, level) {
                        Outcome::Sat => return Outcome::Sat,
                        Outcome::Conflict(c) => Some(c),
                    },
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
            accum.union_with(&bdep);
            return Outcome::Conflict(accum);
        }
        Outcome::Sat
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
        if std::env::var_os("KM_TAB_STATS").is_some() {
            eprintln!("KM_TAB_STATS classify START: {} named, checking consistent([])", named.len());
        }
        let consistent = self.consistent(&[]);
        if std::env::var_os("KM_TAB_STATS").is_some() {
            eprintln!("KM_TAB_STATS classify: consistent([])={}", consistent);
        }
        if !consistent {
            // everything is unsatisfiable; report all named as unsat.
            return (false, named.to_vec(), Vec::new());
        }
        let named_set: HashSet<C> = named.iter().copied().collect();
        let mut unsat = Vec::new();
        let mut subs = Vec::new();
        // For each satisfiable A: record deterministic subsumers directly, and
        // keep only the choice-dependent ones for the confirmation test.
        let mut cand: Vec<(C, Vec<C>)> = Vec::new();
        let prog = std::env::var_os("KM_TAB_STATS").is_some();
        for (ai, &a) in named.iter().enumerate() {
            if prog && ai % 25 == 0 {
                eprintln!("KM_TAB_STATS classify phase1 concept {}/{} subs_so_far={}", ai, named.len(), subs.len());
            }
            match self.find_model(&[CLit::pos(a)]) {
                None => unsat.push(a),
                Some(g) => {
                    let mut uncertain = Vec::new();
                    for l in g.concepts[0].iter() {
                        if l.neg || l.c == a || !named_set.contains(&l.c) {
                            continue;
                        }
                        let definite = matches!(g.cdep[0].get(l), Some(d) if d.v.is_empty());
                        if definite {
                            subs.push((a, l.c));
                        } else {
                            uncertain.push(l.c);
                        }
                    }
                    uncertain.sort_unstable();
                    cand.push((a, uncertain));
                }
            }
        }
        let definite = subs.len();
        let total_cand: usize = cand.iter().map(|(_, s)| s.len()).sum();
        if prog {
            eprintln!("KM_TAB_STATS classify phase1 DONE: definite={} candidates_to_confirm={}", definite, total_cand);
        }
        let mut confirmed = 0;
        for (a, sup) in &cand {
            for &b in sup {
                confirmed += 1;
                if prog && confirmed % 200 == 0 {
                    eprintln!("KM_TAB_STATS classify phase2 confirm {}/{}", confirmed, total_cand);
                }
                if !self.consistent(&[CLit::pos(*a), CLit::neg(b)]) {
                    subs.push((*a, b));
                }
            }
        }
        if std::env::var("KM_TAB_STATS").is_ok() {
            eprintln!(
                "KM_TAB_STATS classify: definite_subs={definite} (no test) confirm_tests={confirmed}"
            );
        }
        (consistent, unsat, subs)
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
    pub queries: Vec<C>,
    /// KB declares inverse roles ⇒ use pairwise blocking.
    #[serde(default)]
    pub inverse: bool,
    /// KB has number restrictions / functional roles ⇒ merge-capable path +
    /// equality blocking.
    #[serde(default)]
    pub number: bool,
    /// Nominal concept ids (`__nom__a` proxies) ⇒ singleton o-rule + root
    /// seeding. Empty for nominal-free KBs (no behaviour change).
    #[serde(default)]
    pub nominals: Vec<C>,
}

#[derive(Serialize)]
pub struct TOutput {
    pub consistent: bool,
    pub unsatisfiable: Vec<String>,
    pub subsumptions: Vec<[String; 2]>,
}

fn atom_of(j: &JAtom) -> Atom {
    match *j {
        JAtom::Concept { neg, c, t } => Atom::Concept { lit: CLit { neg, c }, t },
        JAtom::Role { r, s, t } => Atom::Role { r, s, t },
        JAtom::Exists { r, neg, c, t } => Atom::Exists { r, fil: CLit { neg, c }, t },
        JAtom::Eq { s, t } => Atom::Eq { s, t },
    }
}

/// Read a `TInput` JSON string, classify, and return a `TOutput` JSON string.
pub fn run_json(input: &str) -> Result<String, String> {
    let inp: TInput = serde_json::from_str(input).map_err(|e| e.to_string())?;
    let clauses: Vec<Clause> = inp
        .clauses
        .iter()
        .map(|c| Clause::new(c.body.iter().map(atom_of).collect(), c.head.iter().map(atom_of).collect()))
        .collect();
    let mut t = Tableau::new(clauses);
    t.set_pairwise(inp.inverse);
    t.set_number(inp.number);
    t.set_nominals(inp.nominals.clone());
    let queries: Vec<C> = if inp.queries.is_empty() {
        (0..inp.concepts.len() as C).collect()
    } else {
        inp.queries.clone()
    };
    let (consistent, unsat, subs) = t.classify(&queries);
    let name = |c: C| inp.concepts.get(c as usize).cloned().unwrap_or_else(|| format!("C{c}"));
    let out = TOutput {
        consistent,
        unsatisfiable: unsat.iter().map(|&c| name(c)).collect(),
        subsumptions: subs.iter().map(|&(a, b)| [name(a), name(b)]).collect(),
    };
    serde_json::to_string(&out).map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn con(neg: bool, c: C, t: Var) -> Atom {
        Atom::Concept { lit: CLit { neg, c }, t }
    }
    fn role(r: R, s: Var, t: Var) -> Atom {
        Atom::Role { r, s, t }
    }
    fn exists(r: R, neg: bool, c: C, t: Var) -> Atom {
        Atom::Exists { r, fil: CLit { neg, c }, t }
    }

    // concept ids: A=0,B=1,C=2,D=3 ; role r=0
    const A: C = 0;
    const B: C = 1;
    const D: C = 3;
    const R0: R = 0;

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
            Clause::new(vec![con(false, A, X), role(R0, X, 1)], vec![con(true, B, 1)]),
        ];
        let t = Tableau::new(cls);
        assert!(!t.consistent(&[CLit::pos(A)]));
    }

    #[test]
    fn existential_universal_consistent() {
        // A ⊑ ∃r.B, A ⊑ ∀r.D  is satisfiable (successor gets B and D, no clash).
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![exists(R0, false, B, X)]),
            Clause::new(vec![con(false, A, X), role(R0, X, 1)], vec![con(false, D, 1)]),
        ];
        let t = Tableau::new(cls);
        assert!(t.consistent(&[CLit::pos(A)]));
    }

    #[test]
    fn disjunction_branch() {
        // A ⊑ B ⊔ D, A ⊑ ¬B, A ⊑ ¬D ⇒ A unsat (both branches clash).
        let cls = vec![
            Clause::new(vec![con(false, A, X)], vec![con(false, B, X), con(false, D, X)]),
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
            Clause::new(vec![con(false, A, X)], vec![con(false, B, X), con(false, D, X)]),
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
                vec![con(false, A, X), role(R0, X, 1), con(false, B, 1), role(R0, X, 2), con(false, B, 2)],
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
                vec![con(false, A, X), role(R0, X, 1), con(false, B, 1), role(R0, X, 2), con(false, B, 2)],
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
                vec![con(false, A, X), role(R0, X, 1), con(false, C2, 1), role(R0, X, 2), con(false, C2, 2)],
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
                    role(R0, X, 1), con(false, C2, 1),
                    role(R0, X, 2), con(false, C2, 2),
                    role(R0, X, 3), con(false, C2, 3),
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
            Clause::new(vec![con(false, A, X), role(R0, X, 1)], vec![con(false, C2, 1)]),
            Clause::new(vec![con(false, A, X), role(R1, X, 1)], vec![con(true, C2, 1)]),
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
            Clause::new(vec![con(false, A, X), role(R0, X, 1)], vec![con(false, C2, 1)]),
            Clause::new(vec![con(false, A, X), role(R1, X, 1)], vec![con(false, C2, 1)]),
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
