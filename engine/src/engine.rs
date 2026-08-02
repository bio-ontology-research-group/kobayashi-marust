//! The disjunctive context calculus engine (single-threaded), a faithful port
//! of Sequoia's `context/Context.scala`, `context/Rules.scala`, and
//! `context/ContextState.scala`.
//!
//! Rules implemented: Core, Hyper, Pred, Succ, Eq, Ineq, Elim (redundancy).
//! Expansion strategy: a *pay-as-you-go* strategy — one successor context per
//! function symbol `f` (`successor_for`), instead of the trivial strategy's
//! single shared empty-core context for every anonymous successor.  Both are
//! sound and complete (the trivial one is Simančík et al.); the per-`f` variant
//! avoids piling every existential's successor into one context, which is what
//! blows up under disjunction (≈45× on a distinct-skolem disjunctive stress
//! test).  Soundness is re-checked per run by the Lean certificate checker;
//! completeness is validated against the HermiT oracle and scaffolded in
//! `lean/ContextCalculus/CompletenessStrategy.lean`.  The flag-gated nominal
//! extension implements Join, r-Succ, r-Pred, and Nom; its soundness lemmas and
//! finite covering bound live in `lean/ContextCalculus/Nominals.lean`.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::sync::Arc;

use smallvec::SmallVec;

use crate::calc::*;
use crate::clause::*;

/// Posting list for the per-context head indexes.  Most head keys in a context
/// resolve to a single clause id (unit heads dominate), so inlining up to two
/// ids avoids a heap allocation (and its allocator rounding) per key.  On the
/// big throughput onts the head indexes are the #1 context-memory category
/// (≈37-50% of RSS), almost all of it Vec-header + heap-alloc overhead for
/// singleton postings; SmallVec collapses that.  Output-identical: a posting is
/// the same id sequence, stored inline below the spill threshold.
type Posting = SmallVec<[u32; 2]>;

/// Remove one clause id from a `worked_off` head-index posting, dropping the
/// key when its posting becomes empty.  This is the incremental inverse of the
/// per-key `.push(cid)` in `index_clause`: applied for every key that clause
/// would have been inserted under, it reproduces exactly the state a full
/// `rebuild_head_index` would leave (each surviving id kept once, in work-off
/// order, and no empty postings), at O(keys-of-one-clause) instead of
/// O(worked_off) cost.
fn posting_remove<K: std::hash::Hash + Eq>(map: &mut HashMap<K, Posting>, key: K, cid: u32) {
    if let Some(posting) = map.get_mut(&key) {
        posting.retain(|candidate| *candidate != cid);
        if posting.is_empty() {
            map.remove(&key);
        }
    }
}

/// `posting_remove` for the `Vec<u32>`-valued indexes (`ground_body_index`,
/// `bridge_index`) — same incremental-inverse semantics as above.
fn vec_posting_remove<K: std::hash::Hash + Eq>(
    map: &mut HashMap<K, Vec<u32>>,
    key: K,
    cid: u32,
) {
    if let Some(posting) = map.get_mut(&key) {
        posting.retain(|candidate| *candidate != cid);
        if posting.is_empty() {
            map.remove(&key);
        }
    }
}

// --------------------- shared per-clause index facets -----------------------

/// One key a worked-off clause is filed under in the per-context head indexes.
///
/// `index_clause` / `unindex_clause` used to re-derive this key list from the
/// clause itself, once per (context, clause) pair.  The clause arena is
/// content-interned, so on replication-heavy ontologies the same arena entry is
/// worked off in many contexts at once (ORE 1194: ≈189.5k distinct interned
/// clauses filling ≈6.3M context slots, a ≈33x replication factor), and the
/// derivation — two maximal-head-predicate walks, a maximal-head-literal walk,
/// a body walk, each with quadratic small-vector dedup, and the whole thing
/// again on every back-subsumption unindex — was paid once per *slot* rather
/// than once per *clause*.
///
/// A clause's key list is a pure function of its (immutable) `body` / `head` /
/// `max_head_mask`, so it is derived once when the clause is interned and
/// shared by every context that files it.  Filing then walks one flat slice of
/// `Copy` keys instead of re-traversing two heap vectors.
///
/// Driving both directions from the same list also makes the "`unindex_clause`
/// mirrors `index_clause` key for key" invariant structural rather than a
/// hand-maintained duplication of two ~90-line derivations: a key that is
/// inserted is by construction the key that is removed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Facet {
    /// distinct concept iri among the maximal head predicates
    HeadConcept(Iri),
    /// distinct role iri among the maximal head predicates
    HeadRole(Iri),
    /// one maximal head predicate (already distinct: `head` is sorted+deduped,
    /// so two head literals never carry the same predicate)
    MaxPred(Pred),
    /// maximal head role whose source endpoint is an individual or `f(o)`
    GroundRoleSource(Iri, Term),
    /// maximal head role whose target endpoint is an individual or `f(o)`
    GroundRoleTarget(Iri, Term),
    /// distinct term at a rewrite position of a maximal head literal
    RewriteTerm(Term),
    /// distinct ground body atom (Join rule; empty without individuals)
    GroundBody(Pred),
    /// `x ≈ o` bridge premise of an empty-bodied clause, keyed by `o`
    Bridge(Term),
    /// the head carries a merge-form literal (r-Succ side condition)
    Merge,
}

/// Per-clause propagation-pool eligibility, the other quantity the work-off and
/// seeding paths re-derived per (context, clause).  The `seed_*` pair is
/// `seed_worked_off`'s test, the `sat_*` triple the saturation loop's; the two
/// Pred/Succ tests genuinely differ (seeding predates the nominal equality and
/// root-succ forms), so both are recorded rather than merged.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ClauseFlags {
    seed_pred: bool,
    seed_succ: bool,
    sat_pred: bool,
    sat_succ: bool,
    sat_rsucc: bool,
}

/// Flat, append-only side table of `Facet` lists and `ClauseFlags`, one entry
/// per `cc_arena` clause and always the same length — the same mirror
/// discipline as `cc_sig`.  Keys live in one contiguous `Vec` addressed by a
/// prefix-offset array rather than a `Vec` per clause, so filing a clause walks
/// a cache-resident slice and the table costs no per-clause allocation.  Size
/// is O(distinct clauses), not O(context slots): it is ≈33x smaller than
/// anything stored per (context, clause) on the ontology it targets.
#[derive(Clone)]
struct FacetTable {
    /// `keys[starts[i] .. starts[i + 1]]` are clause `i`'s keys; `starts` always
    /// has one more element than `flags` (it opens with the sentinel `0`).
    starts: Vec<u32>,
    keys: Vec<Facet>,
    flags: Vec<ClauseFlags>,
}

impl FacetTable {
    fn new() -> FacetTable {
        FacetTable {
            starts: vec![0],
            keys: Vec::new(),
            flags: Vec::new(),
        }
    }

    fn len(&self) -> usize {
        self.flags.len()
    }

    #[inline]
    fn keys_of(&self, cid: u32) -> &[Facet] {
        let i = cid as usize;
        &self.keys[self.starts[i] as usize..self.starts[i + 1] as usize]
    }

    #[inline]
    fn flags_of(&self, cid: u32) -> ClauseFlags {
        self.flags[cid as usize]
    }

    /// Append the entry for a clause being interned.  Must be called exactly
    /// once per arena push, before or after the arena push but never
    /// out of order: entry `i` describes arena clause `i`.
    fn push_clause(&mut self, c: &ContextClause, sig: &Sig) {
        facet_keys(c, &mut self.keys);
        self.starts.push(
            u32::try_from(self.keys.len())
                .expect("per-clause facet table exceeds the u32 offset domain"),
        );
        self.flags.push(clause_flags(c, sig));
    }
}

/// Derive a clause's index keys, appending them to `out`.
///
/// The emission order reproduces the order in which the old inline derivation
/// pushed into the indexes.  Order across keys is in fact immaterial (distinct
/// keys address distinct postings, and each key receives `cid` at most once per
/// clause), but keeping it identical makes the equivalence checkable by
/// inspection as well as by the differential tests.
fn facet_keys(c: &ContextClause, out: &mut Vec<Facet>) {
    let mut concept_iris: SmallVec<[Iri; 2]> = SmallVec::new();
    let mut role_iris: SmallVec<[Iri; 1]> = SmallVec::new();
    for (p, _) in c.max_head_predicates() {
        match p {
            Pred::Concept { iri, .. } => {
                if !concept_iris.contains(&iri) {
                    concept_iris.push(iri);
                }
            }
            Pred::Role { iri, .. } => {
                if !role_iris.contains(&iri) {
                    role_iris.push(iri);
                }
            }
        }
    }
    out.extend(concept_iris.into_iter().map(Facet::HeadConcept));
    out.extend(role_iris.into_iter().map(Facet::HeadRole));
    for (p, _) in c.max_head_predicates() {
        out.push(Facet::MaxPred(p));
        if let Pred::Role { iri, s, t } = p {
            if is_individual(s) || is_comp(s) {
                out.push(Facet::GroundRoleSource(iri, s));
            }
            if is_individual(t) || is_comp(t) {
                out.push(Facet::GroundRoleTarget(iri, t));
            }
        }
    }
    let mut rewrite_terms: SmallVec<[Term; 2]> = SmallVec::new();
    for l in c.max_head() {
        match l {
            Lit::P(Pred::Concept { t, .. }) => {
                if !rewrite_terms.contains(&t) {
                    rewrite_terms.push(t);
                }
            }
            Lit::P(Pred::Role { s, t, .. }) => {
                if !rewrite_terms.contains(&s) {
                    rewrite_terms.push(s);
                }
                if !rewrite_terms.contains(&t) {
                    rewrite_terms.push(t);
                }
            }
            Lit::Eq { s, .. } | Lit::Ineq { s, .. } => {
                if !rewrite_terms.contains(&s) {
                    rewrite_terms.push(s);
                }
            }
        }
    }
    out.extend(rewrite_terms.into_iter().map(Facet::RewriteTerm));
    // `body` is sorted+deduped, so the ground atoms are already distinct; the
    // guard mirrors the old posting-level `!contains(cid)` check so the emitted
    // key multiset cannot depend on that assumption.
    let ground_start = out.len();
    for p in &c.body {
        if p.is_ground() && !out[ground_start..].contains(&Facet::GroundBody(*p)) {
            out.push(Facet::GroundBody(*p));
        }
    }
    if c.body.is_empty() {
        for l in c.max_head() {
            if let Lit::Eq { s, t } = l {
                if is_individual(s) && t == X {
                    out.push(Facet::Bridge(s));
                }
            }
        }
    }
    if c.head.iter().any(is_merge_lit) {
        out.push(Facet::Merge);
    }
}

/// Derive a clause's propagation-pool eligibility bits.
///
/// The only signature-dependent bit is `sat_rsucc` (`sig.rsucc` and
/// `sig.is_reach`).  Both are stable for an already-interned clause:
/// `insert_ontology_clauses_retained` copies `rsucc` across verbatim and
/// asserts the concept-name prefix is preserved, and `concept_reach` is a
/// function of the concept name alone.  Caching a signature-derived bit per
/// interned clause is the same discipline `ContextClause::max_head_mask`
/// already follows.
fn clause_flags(c: &ContextClause, sig: &Sig) -> ClauseFlags {
    ClauseFlags {
        seed_pred: c
            .head
            .iter()
            .all(|l| l.is_function_free() && matches!(l, Lit::P(_))),
        seed_succ: c
            .max_head_predicates()
            .any(|(p, _)| is_function(p.max_term())),
        sat_pred: c.head.iter().all(|l| {
            l.is_function_free()
                && match l {
                    Lit::P(_) => true,
                    Lit::Eq { s, t } => {
                        is_individual(*s) && (*t == X || *t == Y || is_individual(*t))
                    }
                    Lit::Ineq { .. } => false,
                }
        }),
        sat_succ: c
            .max_head_predicates()
            .any(|(p, _)| is_function(p.max_term()) || root_succ_form(&p).is_some()),
        sat_rsucc: sig.rsucc
            && c.max_head_predicates().any(|(p, _)| match p {
                Pred::Concept { iri, t } => is_central(t) && sig.is_reach(iri),
                _ => false,
            }),
    }
}

/// One component of Sequoia's context-clause redundancy-trie key.  Sequoia
/// encodes every head literal below every body predicate (by setting the sign
/// bit on head UIDs), then sorts the two regions.  Keeping the exact values in
/// an enum gives the same lexicographic key without relying on a collision-prone
/// numeric hash: `Head` is declared first, so all sorted head literals precede
/// all sorted body predicates.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum RedundancyKey {
    Head(Lit),
    Body(Pred),
}

#[derive(Default)]
struct RedundancyTrieNode {
    value: Option<u32>,
    children: BTreeMap<RedundancyKey, RedundancyTrieNode>,
}

/// Faithful Rust port of Sequoia's `TrieContextClauseRedundancyIndex` and the
/// subset/superset operations of `TrieSearchTree`.  A context clause maps to
/// the sorted set key `head ++ body`; key inclusion is therefore exactly
/// `ContextClause::test_strengthening` in both components.
#[derive(Default)]
struct RedundancyTrie {
    root: RedundancyTrieNode,
}

impl RedundancyTrie {
    fn key(clause: &ContextClause) -> Vec<RedundancyKey> {
        let mut key = Vec::with_capacity(clause.head.len() + clause.body.len());
        key.extend(clause.head.iter().copied().map(RedundancyKey::Head));
        key.extend(clause.body.iter().copied().map(RedundancyKey::Body));
        key
    }

    fn insert(&mut self, clause: &ContextClause, cid: u32) {
        let key = Self::key(clause);
        let mut node = &mut self.root;
        for component in key {
            node = node.children.entry(component).or_default();
        }
        debug_assert!(node.value.is_none() || node.value == Some(cid));
        node.value = Some(cid);
    }

    /// Does the trie contain a clause key that is a subset of `clause`'s key?
    /// `exclude` is used only by the work-off recheck: the queued clause itself
    /// is already in Sequoia's active redundancy index and must not subsume
    /// itself, while any different value on a shorter path is a true subsumer.
    fn contains_subset(&self, clause: &ContextClause, exclude: Option<u32>) -> bool {
        let key = Self::key(clause);
        Self::contains_subset_from(&self.root, &key, 0, exclude)
    }

    fn contains_subset_from(
        node: &RedundancyTrieNode,
        pattern: &[RedundancyKey],
        start: usize,
        exclude: Option<u32>,
    ) -> bool {
        if node.value.is_some() && node.value != exclude {
            return true;
        }
        // A subset path can take only components present in the pattern, in
        // order. Iterating the (usually short) pattern and doing exact child
        // lookups is the same search as Sequoia's ordered-child traversal.
        for i in start..pattern.len() {
            if let Some(child) = node.children.get(&pattern[i]) {
                if Self::contains_subset_from(child, pattern, i + 1, exclude) {
                    return true;
                }
            }
        }
        false
    }

    /// Remove and return every clause whose key is a superset of `clause`'s
    /// key.  Extra components smaller than the next required component remain
    /// admissible; once a child component is larger, the sorted path can no
    /// longer contain that requirement.  This is Sequoia's
    /// `removeKeySuperset` traversal.
    fn remove_supersets(&mut self, clause: &ContextClause) -> Vec<u32> {
        let key = Self::key(clause);
        let mut removed = Vec::new();
        Self::remove_supersets_from(&mut self.root, &key, 0, &mut removed);
        removed
    }

    fn remove_supersets_from(
        node: &mut RedundancyTrieNode,
        pattern: &[RedundancyKey],
        pattern_index: usize,
        removed: &mut Vec<u32>,
    ) -> bool {
        if pattern_index == pattern.len() {
            Self::take_all(node, removed);
            return true;
        }
        let required = pattern[pattern_index];
        let candidates: Vec<RedundancyKey> =
            node.children.range(..=required).map(|(&k, _)| k).collect();
        for component in candidates {
            let next_pattern = pattern_index + usize::from(component == required);
            let empty = {
                let child = node.children.get_mut(&component).unwrap();
                Self::remove_supersets_from(child, pattern, next_pattern, removed)
            };
            if empty {
                node.children.remove(&component);
            }
        }
        node.value.is_none() && node.children.is_empty()
    }

    fn take_all(node: &mut RedundancyTrieNode, removed: &mut Vec<u32>) {
        if let Some(cid) = node.value.take() {
            removed.push(cid);
        }
        let children = std::mem::take(&mut node.children);
        for (_, mut child) in children {
            Self::take_all(&mut child, removed);
        }
    }
}

thread_local! {
    /// Hyper-call counter (only read under KM_STATS). Thread-local because
    /// `hyper` takes `&self`; reset per Engine run via `reset_hyper_calls`.
    static HYPER_CALLS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// Per-rule cumulative wall time (ns), populated only under `KM_PROF_TIME`.
    /// Splits the saturation loop's cost across its phases so CB-throughput
    /// optimisation (the beat-Konclude lever) can target the actual bottleneck
    /// instead of guessing. Reset per Engine run via `reset_hyper_calls`.
    static SUBSUME_NS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static HYPER_NS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static ADDCLAUSE_NS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static PREDLOCAL_NS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static EQRULE_NS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static PROPAGATE_NS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// Pred message delivery, split into the receiver-independent sender half
    /// (`pred_payload`: back-substitution + intern) and the receiver half
    /// (`apply_pred_payload`: dedup + the Pred Cartesian join + `add_clause`).
    /// The split says whether a broadcast hub's cost is the payload it rebuilds
    /// per predecessor or the join each predecessor runs.
    static PREDPAYLOAD_NS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static PREDARRIVAL_NS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// `add_clause` split into its four phases, so the dominant clause-insertion
    /// cost can be attributed to interning, forward subsumption, back
    /// subsumption, or index maintenance.
    static ADD_LOOKUP_NS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static ADD_FWDSUB_NS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static ADD_BACKSUB_NS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static ADD_INDEX_NS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// Whole-`saturate` wall time.  Subtracting the per-rule cells from it
    /// exposes the work-off loop's own overhead (todo pop, arena clause clone,
    /// maximal-literal decode), which no rule cell accounts for.
    static SATURATE_NS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// Back-subsumption head-index maintenance (read under KM_PROF). `EVENTS`
    /// counts back-subsume calls that removed at least one worked-off clause
    /// (each such call previously triggered a full `rebuild_head_index`).
    /// `REINDEX_AVOIDED` sums the surviving worked-off clauses those rebuilds
    /// would have re-indexed but the incremental `unindex_clause` path skips.
    /// Together they quantify the rebuild work this optimisation removes on the
    /// disjunction-heavy contexts. Process-lifetime counters (KM runs one engine
    /// process per ontology), so they read as the per-ontology totals.
    static BACKSUB_UNINDEX_EVENTS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static BACKSUB_REINDEX_AVOIDED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Add `t.elapsed()` ns to a per-rule profiling cell (no-op cost is a branch on
/// the cached `prof_time` flag at the call site).
#[inline(always)]
fn prof_add(cell: &'static std::thread::LocalKey<std::cell::Cell<u64>>, t: std::time::Instant) {
    cell.with(|c| c.set(c.get() + t.elapsed().as_nanos() as u64));
}

/// `KM_PRED_PRODUCT=N`: print the first Pred Cartesian products with at least
/// N combinations. Gated diagnostic only; cached so normal reasoning pays one
/// predictable branch.
fn pred_product_threshold() -> Option<usize> {
    static THRESHOLD: std::sync::OnceLock<Option<usize>> = std::sync::OnceLock::new();
    *THRESHOLD.get_or_init(|| {
        std::env::var("KM_PRED_PRODUCT")
            .ok()
            .map(|v| v.parse().unwrap_or(10_000))
    })
}

fn trace_pred_product(
    phase: &str,
    id: usize,
    max: Option<Pred>,
    pc: &PredClause,
    ground: &[Pred],
    candidates: &[Vec<(usize, Pred)>],
) {
    let Some(threshold) = pred_product_threshold() else {
        return;
    };
    let product = candidates
        .iter()
        .fold(1usize, |n, c| n.saturating_mul(c.len()));
    if product < threshold {
        return;
    }
    static PRINTED: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let serial = PRINTED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    if serial >= 64 {
        return;
    }
    let widths: Vec<usize> = candidates.iter().map(Vec::len).collect();
    eprintln!(
        "KM_PRED_PRODUCT phase={} serial={} ctx={} max={:?} body_len={} ground_len={} widths={:?} product={} body={:?}",
        phase,
        serial,
        id,
        max,
        pc.body.len(),
        ground.len(),
        widths,
        product,
        pc.body,
    );
}

// ----------------------------- substitutions -------------------------------

/// Central substitution used by Hyper: maps ontology variables (x, z_i) to
/// context terms.  `x -> x` always; function terms map to themselves.
///
/// The bindings are stored as an inline association list rather than a
/// `HashMap`.  Body atoms are in DL normal form, so one Hyper match binds only
/// the central variable (under the `X` key) and the clause's few neighbour
/// variables — an inline `SmallVec` holds every real substitution without
/// touching the heap.  Keys stay unique by construction (`add` only pushes a
/// key it does not already hold), so the list is a faithful finite map:
/// `get`/`apply` return the same value for every queried key that the `HashMap`
/// returned, independent of insertion order.
///
/// Because `add` is strictly *append-only*, the list doubles as a backtracking
/// trail: Hyper's join (`hyper_join`) extends it in place for a candidate and
/// restores it with `mark`/`rollback` (a `truncate`) instead of cloning the
/// substitution once per candidate per depth.  Rolling back to a marked length
/// reproduces the exact prior bindings, so every resolvent Hyper builds is
/// byte-identical to the clone-per-candidate enumeration it replaces.
#[derive(Clone)]
struct CentralSubst {
    map: SmallVec<[(Term, Term); 4]>,
    /// Grounded Hyper (σ(x) ∈ Σo, arXiv:1805.01396): permitted only in the
    /// ground (nominal root) context — everywhere else the central variable
    /// maps to itself, as before. Binding x in one ground match and to X in
    /// another is rejected either way (a worked-off provider's residues are
    /// copied unsubstituted, so mixing the two would be unsound).
    allow_ground: bool,
}
impl CentralSubst {
    fn new(allow_ground: bool) -> Self {
        CentralSubst {
            map: SmallVec::new(),
            allow_ground,
        }
    }
    /// Look up the term bound to key `k` (the `X` slot holds the central
    /// binding).  Linear over the handful of bound variables.
    #[inline]
    fn lookup(&self, k: Term) -> Option<Term> {
        self.map.iter().find(|(key, _)| *key == k).map(|&(_, v)| v)
    }
    fn add(&mut self, i: Term, o: Term) -> bool {
        if is_central(i) {
            if o == X || (self.allow_ground && is_individual(o)) {
                return match self.lookup(X) {
                    Some(e) => e == o,
                    None => {
                        self.map.push((X, o));
                        true
                    }
                };
            }
            return false;
        }
        match self.lookup(i) {
            Some(existing) => existing == o,
            None => {
                self.map.push((i, o));
                true
            }
        }
    }
    fn apply(&self, v: Term) -> Term {
        if v == X {
            return self.lookup(X).unwrap_or(X);
        }
        if is_function(v) {
            // f(x) under a grounded central becomes the composite f(o).
            if let Some(b) = self.lookup(X) {
                if b != X {
                    return comp_term(v, b);
                }
            }
            return v;
        }
        self.lookup(v).unwrap_or(v)
    }
    fn get(&self, v: Term) -> Option<Term> {
        self.lookup(v)
    }
    /// Current binding count — the mark for a backtracking trail.  Paired with
    /// `rollback`, it lets Hyper's join extend and undo the substitution in
    /// place instead of cloning it per candidate.  This is sound because `add`
    /// is strictly *append-only*: it only ever `push`es a new `(key, value)`
    /// and never mutates or removes an existing entry, so the bindings present
    /// at a given length are exactly the first `len` entries, in order.
    #[inline]
    fn mark(&self) -> usize {
        self.map.len()
    }
    /// Undo every binding appended since `mark` was taken, restoring the exact
    /// prior substitution (same entries, same order).  Faithful because `add`
    /// only appends: truncating to the marked length is a byte-for-byte revert
    /// of the intervening `add`/`unify` calls, so the substitution passed to
    /// `build_hyper_resolvent` is identical to the clone-based join's.
    #[inline]
    fn rollback(&mut self, mark: usize) {
        self.map.truncate(mark);
    }
}

/// Symmetric-group pruning for the Hyper join: for each exchange-invariant
/// neighbour-variable group of `oc`, require the bound members' terms to be
/// sorted in group order (strictly when the head carries an equality for every
/// pair of the group — an equal-term assignment then makes some head equality
/// trivially true, a tautology `build_hyper_resolvent` would drop anyway).
/// Every pruned full assignment is a permutation of exactly one kept one and
/// produces the identical canonical resolvent, so the derived set is
/// unchanged; only duplicate (and tautological) enumeration is skipped.
/// Variables occurring in the side-clause body position are exempt: the side
/// clause is pinned to that position, so its binding is not interchangeable
/// with the worked-off candidates.
fn sym_groups_ok(oc: &OntologyClause, exempt: &[Term], sigma: &CentralSubst) -> bool {
    for (g, strict) in &oc.sym_groups {
        let mut prev: Option<Term> = None;
        for &v in g {
            if exempt.contains(&v) {
                continue;
            }
            let t = match sigma.get(v) {
                Some(t) => t,
                None => continue,
            };
            if let Some(p) = prev {
                if *strict {
                    // Ground context: an equal assignment to y is the Nom
                    // trigger (the head equality becomes y≈y, which the Nom
                    // rule replaces with the additional-nominal disjunction
                    // rather than dropping as a tautology), so the
                    // tautology-based strict pruning must not discard it.
                    if sigma.allow_ground && p == t && t == Y {
                        // keep
                    } else if p >= t {
                        return false;
                    }
                } else if p > t {
                    return false;
                }
            }
            prev = Some(t);
        }
    }
    true
}

/// Su^r detection (arXiv:1805.01396): a max-head atom about an individual —
/// `B(o)`, `S(x,o)`, `S(o,x)` — whose y-form (`B(o)`, `S(y,o)`, `S(o,y)`) is
/// pushed to the ground context by r-Succ, labelled by the individual.
fn root_succ_form(p: &Pred) -> Option<(Pred, Term)> {
    match *p {
        Pred::Concept { iri, t } if is_individual(t) => Some((Pred::Concept { iri, t }, t)),
        Pred::Role { iri, s, t } => {
            if is_central(s) && is_individual(t) {
                Some((Pred::Role { iri, s: Y, t }, t))
            } else if is_individual(s) && is_central(t) {
                Some((Pred::Role { iri, s, t: Y }, s))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// r-Succ reach extraction: the CENTRAL reachability predicates
/// (`__trans__`/`__chain__(x)`) contributed by the clauses at arena ids `pool`,
/// in first-occurrence order, WITHOUT cross-call dedup (the caller folds the
/// result into a persistent ordered-unique accumulator).  Shared by
/// `propagate_inner`'s semi-naive r-Succ scan and its invariance test, so the
/// test certifies the exact predicate production uses.
fn rsucc_reach_tail(arena: &[ContextClause], pool: &[u32], sig: &Sig) -> Vec<Pred> {
    let mut out: Vec<Pred> = Vec::new();
    for &ci in pool {
        for (p, _) in arena[ci as usize].max_head_predicates() {
            if let Pred::Concept { iri, t } = p {
                if is_central(t) && sig.is_reach(iri) {
                    out.push(p);
                }
            }
        }
    }
    out
}

/// Fold a reach-tail (see [`rsucc_reach_tail`]) into a persistent ordered-unique
/// accumulator: append each predicate not already present, first occurrence
/// winning; `set` mirrors `acc` for O(1) membership.  Folding successive tails
/// of an append-only pool reproduces exactly the ordered-unique list a single
/// full rescan of the concatenated pool would build (the reach extraction never
/// consults `clause_keys`, so pool entries are effectively immutable once
/// appended) — the invariant the semi-naive r-Succ scan relies on.
fn fold_reach_unique(acc: &mut Vec<Pred>, set: &mut HashSet<Pred>, tail: Vec<Pred>) {
    for p in tail {
        if set.insert(p) {
            acc.push(p);
        }
    }
}

/// Semi-naive r-Succ cross-product for ONE `propagate` round: emit, for each
/// current successor edge `(f, target)`, the reach preds it has not yet been
/// offered (`reach[hwm(edge)..]`), gated by the persistent `pushed` dedup set;
/// then advance each visited edge's hwm to `reach.len()`.
///
/// `reach` is append-only (grown only by `fold_reach_unique`), so for any edge
/// the preds in `reach[..hwm(edge)]` were all offered to `pushed` in a prior
/// round the edge was visited — `pushed.insert` returned `false`/`true` for them
/// then and would return `false` now.  Skipping that prefix therefore drops only
/// work the gate already rejected: the fired triples (and their order:
/// successors outer, reach inner) are byte-for-byte what the former full
/// `successors × reach` rescan produced, so the emitted `Msg::Succ` set and
/// order — hence the saturation fixpoint — is identical.  Shared by
/// `propagate_inner` and its invariance test so the test certifies the exact
/// production the engine uses.
fn rsucc_cross_step(
    successors: &[(Term, usize)],
    reach: &[Pred],
    hwm: &mut HashMap<(Term, usize), usize>,
    pushed: &mut HashSet<(Term, usize, Pred)>,
) -> Vec<(Term, usize, Pred)> {
    let nreach = reach.len();
    let mut fired: Vec<(Term, usize, Pred)> = Vec::new();
    for &(f, target) in successors {
        let start = hwm.get(&(f, target)).copied().unwrap_or(0);
        for &p in &reach[start..nreach] {
            if pushed.insert((f, target, p)) {
                fired.push((f, target, p));
            }
        }
        hwm.insert((f, target), nreach);
    }
    fired
}

/// Merge-form literal of the r-Succ side condition (*): `x ≈ o`, `y ≈ o`, or
/// `x ≈ y` (canonical `Lit::eq` puts the larger term first: individuals sit
/// above x above y).  A clause `Γ'' → Δ'' ∨ ⋁ L_i` of merge-form `L_i` with
/// `Γ'' ⊆ Γ`, `Δ'' ⊆ Δ` *blocks* the r-Succ push of `Γ → Δ ∨ Aσ`: the
/// context's element may itself be a nominal (or merge with its predecessor),
/// so the calculus defers to equality reasoning instead of creating the edge.
fn is_merge_lit(l: &Lit) -> bool {
    matches!(*l, Lit::Eq { s, t } if (is_individual(s) && (t == X || t == Y)) || (s == X && t == Y))
}

/// r-Succ side condition (*): the push of the maximal head atom `a` from
/// clause `c` (`Γ → Δ ∨ Aσ` with `Γ = c.body`, `Δ = c.head \ {Aσ}`) is
/// *blocked* when the context holds a clause `Γ'' → Δ'' ∨ ⋁ L_i` with
/// `Γ'' ⊆ Γ`, `Δ'' ⊆ Δ`, and every `L_i` a merge-form literal (≥ 1 of them) —
/// the element may itself be a nominal or merge with its predecessor, so the
/// calculus defers to equality reasoning instead of creating the edge.
fn rsucc_blocked(ctx: &Context, arena: &[ContextClause], c: &ContextClause, a: &Pred) -> bool {
    'cand: for &mi in &ctx.merge_clauses {
        let m = &arena[mi as usize];
        if !m.body.iter().all(|b| c.body.contains(b)) {
            continue;
        }
        let mut has_merge = false;
        for l in &m.head {
            if is_merge_lit(l) {
                has_merge = true;
                continue;
            }
            if *l == Lit::P(*a) || !c.head.contains(l) {
                continue 'cand;
            }
        }
        if has_merge {
            return true;
        }
    }
    false
}

/// `true` if the clause mentions the central variable x anywhere (such
/// ground-context clauses are instantiated per individual-labelled edge by the
/// Pred back-substitution, so they keep the per-edge propagation path).
fn cc_mentions_x(c: &ContextClause) -> bool {
    fn px(p: &Pred) -> bool {
        match *p {
            Pred::Concept { t, .. } => t == X,
            Pred::Role { s, t, .. } => s == X || t == X,
        }
    }
    c.body.iter().any(px)
        || c.head.iter().any(|l| match *l {
            Lit::P(p) => px(&p),
            Lit::Eq { s, t } | Lit::Ineq { s, t } => s == X || t == X,
        })
}

/// Collect the individuals mentioned by a predicate (decoding `f(o)`
/// composites) into `out`, deduplicated.
fn pred_inds(p: &Pred, out: &mut Vec<Term>) {
    fn push(t: Term, out: &mut Vec<Term>) {
        let t = if is_comp(t) { comp_parts(t).1 } else { t };
        if is_individual(t) && !out.contains(&t) {
            out.push(t);
        }
    }
    match *p {
        Pred::Concept { t, .. } => push(t, out),
        Pred::Role { s, t, .. } => {
            push(s, out);
            push(t, out);
        }
    }
}

fn lit_inds(l: &Lit, out: &mut Vec<Term>) {
    match l {
        Lit::P(p) => pred_inds(p, out),
        Lit::Eq { s, t } | Lit::Ineq { s, t } => {
            for &v in &[*s, *t] {
                let v = if is_comp(v) { comp_parts(v).1 } else { v };
                if is_individual(v) && !out.contains(&v) {
                    out.push(v);
                }
            }
        }
    }
}

/// Forward inter-context mapping for Succ: {f(x) -> x, x -> y}; for a
/// grounded edge labelled by a composite `f(o)` it is {f(o) -> x, o -> y}
/// (the parent of the `f(o)` element is the individual o, not the sender's
/// central element — arXiv:1805.01396 root-context Succ).
fn forwards(f: Term, v: Term) -> Term {
    if v == f {
        return X;
    }
    if is_comp(f) {
        let (_, o) = comp_parts(f);
        return if v == o { Y } else { v };
    }
    if v == X {
        Y
    } else {
        // neighbour/other terms do not occur in a succ trigger predicate
        v
    }
}
/// Backward inter-context substitution for Pred: {y -> x, x -> f(x)}; for a
/// grounded edge labelled `f(o)` it is {y -> o, x -> f(o)} — conclusions
/// about the parent are conclusions about the individual o, and they arrive
/// ground.
fn backwards(f: Term, v: Term) -> Term {
    if is_comp(f) {
        let (_, o) = comp_parts(f);
        return if v == Y {
            o
        } else if v == X {
            f
        } else {
            v
        };
    }
    if v == Y {
        X
    } else if v == X {
        f
    } else {
        v
    }
}

// ------------------------------- unification -------------------------------

/// Whether `term` has a fixed image under the substitution already supplied
/// by Hyper's side premise. In the ground context an unbound `x` is still a
/// wildcard over named individuals, and an unbound `f(x)` may become any
/// `f(o)`; elsewhere `x` and `f(x)` are syntactically fixed. Neighbour
/// variables are fixed only after an earlier premise binds them.
fn hyper_term_determined(term: Term, sigma: &CentralSubst) -> bool {
    if is_central(term) {
        return !sigma.allow_ground || sigma.get(X).is_some();
    }
    if is_neighbour(term) {
        return sigma.get(term).is_some();
    }
    if is_function(term) && !is_comp(term) {
        return !sigma.allow_ground || sigma.get(X).is_some();
    }
    true
}

/// Optional diagnostic threshold for logging Hyper's pre-join Cartesian upper
/// bound. Cached because Hyper is the hottest rule and reading the environment
/// per invocation would perturb the profile being measured.
fn hyper_product_trace_threshold() -> Option<u128> {
    static THRESHOLD: std::sync::OnceLock<Option<u128>> = std::sync::OnceLock::new();
    *THRESHOLD.get_or_init(|| {
        std::env::var("KM_TRACE_HYPER_PRODUCT")
            .ok()
            .and_then(|value| value.parse().ok())
    })
}

fn can_unify(body: &Pred, head_max: &Pred) -> bool {
    // A central body term must match a central head term or — grounded Hyper
    // of the nominal calculus — an individual; a neighbour body term (e.g.
    // C(y) in `R(x,y) ∧ C(y) -> D(x)`) may bind to any head term, including a
    // function term C(f(x)).  (Pure syntactic unification — sound regardless
    // of the body term's role.)
    fn central_ok(b: Term, h: Term) -> bool {
        !is_central(b) || is_central(h) || is_individual(h)
    }
    match (body, head_max) {
        (Pred::Concept { iri: i1, t: t1 }, Pred::Concept { iri: i2, t: t2 }) => {
            i1 == i2 && central_ok(*t1, *t2)
        }
        (
            Pred::Role {
                iri: i1,
                s: s1,
                t: t1,
            },
            Pred::Role {
                iri: i2,
                s: s2,
                t: t2,
            },
        ) => i1 == i2 && central_ok(*s1, *s2) && central_ok(*t1, *t2),
        _ => false,
    }
}

fn unify(sigma: &mut CentralSubst, body: &Pred, head: &Pred) -> bool {
    match (body, head) {
        (Pred::Concept { iri: i1, t: t1 }, Pred::Concept { iri: i2, t: t2 }) => {
            i1 == i2 && sigma.add(*t1, *t2)
        }
        (
            Pred::Role {
                iri: i1,
                s: s1,
                t: t1,
            },
            Pred::Role {
                iri: i2,
                s: s2,
                t: t2,
            },
        ) => i1 == i2 && sigma.add(*s1, *s2) && sigma.add(*t1, *t2),
        _ => false,
    }
}

// ------------------- Hyper join: exact candidate narrowing -------------------
//
// Qualified at-most cardinality clauses
//   `G(x) ∧ R(x,y1) ∧ C(y1) ∧ … ∧ R(x,yk) ∧ C(yk) → ⋁_{i<j} yi ≈ yj`
// are the worst shape for the generic Hyper join.  Each body position gets its
// own candidate posting — every maximal `C(·)` head for the fillers, every
// maximal `R(x,·)` head for the edges — and those postings are built
// INDEPENDENTLY: the filler position does not know which terms actually carry
// an R-edge, and the edge position does not know which targets actually carry
// C.  The backtracking join then binds `y1 … yk` from the (wide) concept
// postings before it ever consults an edge position, so the enumeration is
// `|C-postings|^k` even though only the R-successors that are C can appear in
// any resolvent.  Measured on ORE 1194: raw per-firing candidate-width products
// of 1M-12M, hundreds of firings during post-Pred context saturation.
//
// Two exact narrowings fix that, both of which preserve the resolvent multiset
// AND its enumeration order (see `reduce_hyper_candidates` and the determined
// fast path in `hyper_join`):
//
//   1. a *semijoin reduction* (relational arc consistency) over the candidate
//      lists: a candidate that binds a shared body variable to a term no other
//      position mentioning that variable can supply cannot occur in ANY
//      unifiable combination, so it is dropped before the join.  For the
//      cardinality shape this intersects the R-target postings with the
//      C-filler postings and leaves exactly the witnesses of `∃R.C`;
//   2. an *indexed lookup* at join positions whose body atom is already fully
//      determined by the bindings made so far, replacing the linear rescan of
//      the whole posting with a hash probe for the one instantiated predicate.
//
// Neither changes the calculus: the derived resolvents, the literal ordering,
// redundancy and the Nom/ground special cases are untouched, so no Lean
// re-certification is needed (this is candidate enumeration, not derivation).

/// Cap on semijoin-reduction rounds.  Each round strictly shrinks some
/// candidate list, so the loop terminates on its own; the cap only bounds the
/// worst-case rescan cost of a pathological clause.  Stopping early leaves
/// *more* candidates, never fewer, so the join result is unaffected.
const HYPER_REDUCE_MAX_ROUNDS: usize = 8;

/// Raw Cartesian width product below which the reduction is skipped: the pass
/// is linear in the total posting length, which is not worth paying for the
/// two- and three-candidate joins that dominate saturation.  Purely a cost
/// gate — running or skipping it yields the identical resolvent sequence.
const HYPER_REDUCE_MIN_PRODUCT: u128 = 1 << 10;

/// Candidate-list length from which a fully determined body position builds a
/// hash index instead of scanning the list for the instantiated predicate.
const HYPER_DETERMINED_INDEX_MIN: usize = 16;

/// `KM_NO_HYPER_NARROW`: restore the pre-patch generic Hyper join (no semijoin
/// reduction, no determined-position index).  Both narrowings are exact, so
/// this exists only as an A/B kill switch for corpus measurements.
fn hyper_narrow_default() -> bool {
    static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *FLAG.get_or_init(|| std::env::var_os("KM_NO_HYPER_NARROW").is_none())
}

thread_local! {
    /// Per-thread narrowing state, seeded from the environment on first use.
    /// Thread-local (like `BRANCH_ORDERED`) so the differential tests can flip
    /// it around a single `hyper` call without an env race between tests.
    static HYPER_NARROW: std::cell::Cell<Option<bool>> = const { std::cell::Cell::new(None) };
}

#[inline]
fn hyper_narrow() -> bool {
    HYPER_NARROW.with(|flag| match flag.get() {
        Some(on) => on,
        None => {
            let on = hyper_narrow_default();
            flag.set(Some(on));
            on
        }
    })
}

/// Test hook for the on/off differential of the narrowing (see `hyper_narrow`).
#[cfg(test)]
fn set_hyper_narrow(on: bool) {
    HYPER_NARROW.with(|flag| flag.set(Some(on)));
}

/// The image `unify` would force on `term`, or `None` when `term` is still a
/// free join key (`unify` would bind it to whatever the candidate supplies).
///
/// This mirrors `CentralSubst::add` exactly, which is what the join tests:
/// the central variable is keyed under `X` and, outside the ground context,
/// is pinned to `X` even before any premise binds it; every other body term
/// (neighbour variable, individual, function symbol) is its own key and is
/// determined only once some premise has bound it.  Deliberately NOT
/// `sigma.apply`, which resolves an unbound `f(x)` to `f(o)` under a grounded
/// central — `add` does not, and the join follows `add`.
#[inline]
fn hyper_bound_image(term: Term, sigma: &CentralSubst) -> Option<Term> {
    if is_central(term) {
        return match sigma.get(X) {
            Some(image) => Some(image),
            // Non-ground contexts: `add(X, o)` accepts only `o == X`.
            None => (!sigma.allow_ground).then_some(X),
        };
    }
    sigma.get(term)
}

/// The single predicate a body atom can still match, when `sigma` already
/// determines every one of its terms.  `unify(sigma, body, p)` then succeeds
/// exactly for `p == hyper_determined_instance(body, sigma).unwrap()`, and
/// binds nothing new (both directions follow from `hyper_bound_image` mirroring
/// `CentralSubst::add`).  `None` when some term is still a free join key.
#[inline]
fn hyper_determined_instance(body: &Pred, sigma: &CentralSubst) -> Option<Pred> {
    Some(match *body {
        Pred::Concept { iri, t } => Pred::Concept {
            iri,
            t: hyper_bound_image(t, sigma)?,
        },
        Pred::Role { iri, s, t } => Pred::Role {
            iri,
            s: hyper_bound_image(s, sigma)?,
            t: hyper_bound_image(t, sigma)?,
        },
    })
}

/// The term `matched` forces on join key `key`, or `None` if this body atom
/// does not constrain that key.  A body atom mentioning the key twice
/// (`R(y,y)`) can only have been matched by a candidate that agrees on both
/// positions, so returning the first is exact.
#[inline]
fn hyper_induced_value(body: &Pred, matched: &Pred, key: Term) -> Option<Term> {
    match (body, matched) {
        (Pred::Concept { t, .. }, Pred::Concept { t: value, .. }) => (*t == key).then_some(*value),
        (
            Pred::Role { s, t, .. },
            Pred::Role {
                s: source,
                t: target,
                ..
            },
        ) => {
            if *s == key {
                Some(*source)
            } else if *t == key {
                Some(*target)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Exact semijoin reduction ("witness intersection") of Hyper's per-position
/// candidate lists.  Returns `false` when a position is emptied, i.e. the
/// clause provably has no resolvent at all for this side premise.
///
/// For every body term still free after the side unification, the candidates at
/// each position mentioning it induce a *domain* of possible images.  A
/// complete assignment must pick one image per key, consistent across every
/// position, so any candidate whose induced image lies outside the intersection
/// of those domains is in no unifiable combination and cannot contribute a
/// resolvent.  Dropping it is therefore result-preserving, not an
/// approximation; the removals are iterated because a removal can shrink a
/// domain and expose further dead candidates.
///
/// The lists are filtered in place and stay SUBSEQUENCES of the originals.
/// That, plus the caller keeping the position order keyed on the *raw* widths,
/// is what makes the narrowed join emit exactly the generic join's resolvents
/// in exactly the generic join's order (a dropped candidate contributes no
/// leaf, so it contributes nothing to the sequence either).
///
/// On the qualified at-most cardinality shape this is precisely the direct
/// enumeration of `(role target, filler concept)` witnesses: the filler
/// position keeps only terms carrying an R-edge from the (already bound)
/// central source, and the edge position keeps only edges whose target carries
/// the filler concept.
fn reduce_hyper_candidates(
    oc: &OntologyClause,
    candidates: &mut [Vec<(usize, Pred)>],
    sigma: &CentralSubst,
) -> bool {
    debug_assert_eq!(candidates.len(), oc.body.len());
    // Free join keys, with the body positions that constrain each.
    let mut keys: SmallVec<[Term; 4]> = SmallVec::new();
    let mut key_positions: SmallVec<[SmallVec<[usize; 4]>; 4]> = SmallVec::new();
    for (position, atom) in oc.body.iter().enumerate() {
        let terms: [Option<Term>; 2] = match *atom {
            Pred::Concept { t, .. } => [Some(t), None],
            Pred::Role { s, t, .. } => [Some(s), Some(t)],
        };
        for term in terms.into_iter().flatten() {
            // Terms the side premise already pinned need no cross-position
            // intersection: every candidate list was built by unifying against
            // that same substitution, so all of them already agree there.
            if hyper_bound_image(term, sigma).is_some() {
                continue;
            }
            match keys.iter().position(|&key| key == term) {
                Some(known) => {
                    if !key_positions[known].contains(&position) {
                        key_positions[known].push(position);
                    }
                }
                None => {
                    keys.push(term);
                    let mut positions: SmallVec<[usize; 4]> = SmallVec::new();
                    positions.push(position);
                    key_positions.push(positions);
                }
            }
        }
    }
    // A key confined to one position carries no cross-position information.
    if !key_positions.iter().any(|positions| positions.len() >= 2) {
        return true;
    }
    let mut live: SmallVec<[Vec<bool>; 8]> = candidates
        .iter()
        .map(|list| vec![true; list.len()])
        .collect();
    let mut counts: SmallVec<[usize; 8]> = candidates.iter().map(Vec::len).collect();
    let mut allowed: Vec<Term> = Vec::new();
    let mut domain: Vec<Term> = Vec::new();
    let mut narrowed = false;
    for _round in 0..HYPER_REDUCE_MAX_ROUNDS {
        let mut changed = false;
        for (key_index, positions) in key_positions.iter().enumerate() {
            if positions.len() < 2 {
                continue;
            }
            let key = keys[key_index];
            allowed.clear();
            for (slot, &position) in positions.iter().enumerate() {
                domain.clear();
                for (entry, &(_, matched)) in candidates[position].iter().enumerate() {
                    if !live[position][entry] {
                        continue;
                    }
                    if let Some(value) = hyper_induced_value(&oc.body[position], &matched, key) {
                        domain.push(value);
                    }
                }
                domain.sort_unstable();
                domain.dedup();
                if slot == 0 {
                    allowed.clone_from(&domain);
                } else {
                    // `allowed` stays sorted: `retain` preserves order.
                    allowed.retain(|value| domain.binary_search(value).is_ok());
                }
                if allowed.is_empty() {
                    break;
                }
            }
            for &position in positions.iter() {
                for (entry, &(_, matched)) in candidates[position].iter().enumerate() {
                    if !live[position][entry] {
                        continue;
                    }
                    if let Some(value) = hyper_induced_value(&oc.body[position], &matched, key) {
                        if allowed.binary_search(&value).is_err() {
                            live[position][entry] = false;
                            counts[position] -= 1;
                            changed = true;
                        }
                    }
                }
                if counts[position] == 0 {
                    return false;
                }
            }
        }
        narrowed |= changed;
        if !changed {
            break;
        }
    }
    if narrowed {
        for (position, list) in candidates.iter_mut().enumerate() {
            if counts[position] == list.len() {
                continue;
            }
            let keep = &live[position];
            let mut entry = 0usize;
            list.retain(|_| {
                let live_entry = keep[entry];
                entry += 1;
                live_entry
            });
        }
    }
    true
}

/// Lazily built per-position index from an instantiated predicate to the
/// entries of that position's candidate list carrying it, used by the join at
/// body positions whose terms `sigma` already determines.  Entry ids stay in
/// candidate-list order, so probing the index visits exactly the candidates a
/// linear rescan would accept, in the same order.
struct DeterminedIndex {
    enabled: bool,
    /// Per body position: how many times it has been probed, and its index once
    /// built.  Empty until a long list is probed (see `hits`).
    per_position: Vec<(u32, Option<HashMap<Pred, SmallVec<[u32; 2]>>>)>,
}

impl DeterminedIndex {
    /// Allocation-free when narrowing is off or no position is ever probed.
    fn new(enabled: bool) -> DeterminedIndex {
        DeterminedIndex {
            enabled,
            per_position: Vec::new(),
        }
    }

    /// Collect the entries of `candidates[position]` matching `wanted`.
    ///
    /// Short lists are scanned: an equality test per entry is cheaper than
    /// hashing, and still strictly less work than the generic join's `unify`
    /// per entry.  A long list is indexed, but only from its SECOND probe on —
    /// a position probed once (typically one bound from the exact-predicate
    /// posting, where every entry carries the same predicate anyway) would pay
    /// a full hash build to answer a single question.  Both branches return the
    /// same entries in the same order, so this is a pure cost choice.
    fn hits(
        &mut self,
        position: usize,
        candidates: &[Vec<(usize, Pred)>],
        wanted: &Pred,
        out: &mut SmallVec<[u32; 4]>,
    ) {
        let list = &candidates[position];
        let scan = |out: &mut SmallVec<[u32; 4]>| {
            for (entry, &(_, matched)) in list.iter().enumerate() {
                if matched == *wanted {
                    out.push(entry as u32);
                }
            }
        };
        if list.len() < HYPER_DETERMINED_INDEX_MIN {
            scan(out);
            return;
        }
        if self.per_position.len() < candidates.len() {
            self.per_position.resize_with(candidates.len(), || (0, None));
        }
        let slot = &mut self.per_position[position];
        slot.0 = slot.0.saturating_add(1);
        if slot.0 < 2 && slot.1.is_none() {
            scan(out);
            return;
        }
        let index = slot.1.get_or_insert_with(|| {
            let mut index: HashMap<Pred, SmallVec<[u32; 2]>> = HashMap::with_capacity(list.len());
            for (entry, &(_, matched)) in list.iter().enumerate() {
                index.entry(matched).or_default().push(entry as u32);
            }
            index
        });
        if let Some(entries) = index.get(wanted) {
            out.extend_from_slice(entries);
        }
    }
}

// -------------------------------- ontology ---------------------------------

#[derive(Clone, Default)]
struct Ontology {
    clauses: Vec<OntologyClause>,
    facts: Vec<usize>, // indices of empty-body clauses (x-form only)
    /// Ground facts (empty-body clauses whose head mentions an individual),
    /// keyed by each individual they mention. Seeded fully into the ground
    /// context and on demand into a context that first derives an atom about
    /// that individual (docs/NOMINALS-CB.md); empty without nominal mode.
    ground_facts: HashMap<Term, Vec<usize>>,
    concept_clauses: HashMap<Iri, Vec<usize>>, // body Concept(iri,x)
    forward_role_clauses: HashMap<Iri, Vec<usize>>, // body Role(iri,x,_)
    backward_role_clauses: HashMap<Iri, Vec<usize>>, // body Role(iri,_,x)
    /// clauses with *any* body Concept(iri, _) (central or neighbour term)
    concept_body_any: HashMap<Iri, Vec<usize>>,
    /// clauses with *any* body Role(iri, _, _)
    role_body_any: HashMap<Iri, Vec<usize>>,
    /// The overwhelmingly common absorbed-existential shape
    /// `C(y) ∧ R(x,y) -> D(x)`, indexed by `(R,C)` instead of placing every
    /// such clause in R's broad Hyper posting. Values are sorted `(C,clause)`
    /// pairs, so a role side premise probes only concepts that are actually
    /// present at its target term. This is a compact two-column join index, not
    /// a reasoning shortcut: Hyper still applies the original clauses.
    role_target_concept_body: HashMap<Iri, Vec<(Iri, usize)>>,
}

impl Ontology {
    /// Append one normal-form clause and extend every immutable-looking lookup
    /// table used by Hyper and context initialisation.  `mark_nothing` enables
    /// the one-shot direct-bottom optimisation used while constructing a fresh
    /// engine.  Retained insertion leaves that optimisation unchanged: making
    /// an already ordered concept a static `nothing` symbol would change the
    /// cached maximal-literal masks, while replaying the new `C -> bottom`
    /// clause derives the same contradiction without changing the ordering.
    fn push_clause(&mut self, sig: &mut Sig, c: OntologyClause, mark_nothing: bool) -> usize {
        let idx = self.clauses.len();
        if c.body.is_empty() {
            // Ground facts (heads mentioning an individual) seed the ground
            // context fully and other contexts on demand.
            let mut inds: Vec<Term> = Vec::new();
            for l in &c.head {
                lit_inds(l, &mut inds);
            }
            if inds.is_empty() {
                self.facts.push(idx);
            } else {
                for o in inds {
                    self.ground_facts.entry(o).or_default().push(idx);
                }
            }
        } else {
            let guarded_role = if c.body.len() == 2 {
                let pair = match (c.body[0], c.body[1]) {
                    (
                        Pred::Concept { iri: concept, t: ct },
                        Pred::Role {
                            iri: role,
                            s,
                            t: rt,
                        },
                    )
                    | (
                        Pred::Role {
                            iri: role,
                            s,
                            t: rt,
                        },
                        Pred::Concept { iri: concept, t: ct },
                    ) if ct == rt && is_central(s) && is_neighbour(rt) => {
                        Some((role, concept))
                    }
                    _ => None,
                };
                pair
            } else {
                None
            };
            if mark_nothing && c.body.len() == 1 && c.head.is_empty() {
                if let Pred::Concept { iri, .. } = c.body[0] {
                    if (iri as usize) < sig.nothing.len() {
                        sig.nothing[iri as usize] = true;
                    }
                }
            }
            for b in &c.body {
                match *b {
                    Pred::Concept { iri, t } => {
                        self.concept_body_any.entry(iri).or_default().push(idx);
                        if is_central(t) {
                            sig.concept_succ_trigger[iri as usize] = true;
                            self.concept_clauses.entry(iri).or_default().push(idx);
                        }
                    }
                    Pred::Role { iri, s, t } => {
                        match guarded_role {
                            Some((guard_role, concept)) if iri == guard_role => {
                                self.role_target_concept_body
                                    .entry(iri)
                                    .or_default()
                                    .push((concept, idx));
                            }
                            _ => self.role_body_any.entry(iri).or_default().push(idx),
                        }
                        if is_central(s) {
                            sig.forward_role_succ_trigger[iri as usize] = true;
                            self.forward_role_clauses.entry(iri).or_default().push(idx);
                        }
                        if is_central(t) {
                            sig.backward_role_succ_trigger[iri as usize] = true;
                            self.backward_role_clauses.entry(iri).or_default().push(idx);
                        }
                    }
                }
            }
        }
        self.clauses.push(c);
        idx
    }

    /// Candidate lists are append-only by ontology-clause id.  A clause can
    /// mention the same predicate more than once, so canonicalise after a
    /// batch of appends just as fresh construction does.
    fn canonicalise_candidates(&mut self) {
        for v in self.concept_body_any.values_mut() {
            v.sort_unstable();
            v.dedup();
        }
        for v in self.role_body_any.values_mut() {
            v.sort_unstable();
            v.dedup();
        }
        for v in self.role_target_concept_body.values_mut() {
            v.sort_unstable();
            v.dedup();
        }
    }

    /// Candidate ontology clauses that may resolve with a context-clause head
    /// predicate `max` (i.e. have a body atom that can unify with `max`).
    /// Over-approximates by predicate iri; `can_unify` filters precisely.
    fn clauses_cand(&self, max: &Pred) -> &[usize] {
        match *max {
            Pred::Concept { iri, .. } => self
                .concept_body_any
                .get(&iri)
                .map(|v| v.as_slice())
                .unwrap_or(&[]),
            Pred::Role { iri, .. } => self
                .role_body_any
                .get(&iri)
                .map(|v| v.as_slice())
                .unwrap_or(&[]),
        }
    }
}

/// Statistics for the deterministic same-individual quotient applied before
/// the nominal ground context is built. Konclude performs the corresponding
/// operation by resolving each asserted nominal to its process node and then
/// merging the nodes, their labels, links, and distinctness data into one
/// representative. KM stores those data as ground clauses, so rewriting every
/// occurrence to the least representative is the clause-level form of the
/// same deterministic merge.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct GroundEqualityMergeStats {
    asserted_pairs: usize,
    merged_aliases: usize,
    clauses_before: usize,
    clauses_after: usize,
}

fn input_max_individual(clauses: &[OntologyClause]) -> i32 {
    let mut max_ind = 0;
    let mut see = |t: Term| {
        if is_individual(t) {
            max_ind = max_ind.max(ind_id(t));
        } else if is_comp(t) {
            max_ind = max_ind.max(ind_id(comp_parts(t).1));
        }
    };
    for clause in clauses {
        for pred in &clause.body {
            match *pred {
                Pred::Concept { t, .. } => see(t),
                Pred::Role { s, t, .. } => {
                    see(s);
                    see(t);
                }
            }
        }
        for literal in &clause.head {
            match *literal {
                Lit::P(Pred::Concept { t, .. }) => see(t),
                Lit::P(Pred::Role { s, t, .. }) => {
                    see(s);
                    see(t);
                }
                Lit::Eq { s, t } | Lit::Ineq { s, t } => {
                    see(s);
                    see(t);
                }
            }
        }
    }
    max_ind
}

fn ground_equality_find(parent: &mut [u32], id: u32) -> u32 {
    let mut root = id;
    while parent[root as usize] != root {
        root = parent[root as usize];
    }
    let mut current = id;
    while parent[current as usize] != root {
        let next = parent[current as usize];
        parent[current as usize] = root;
        current = next;
    }
    root
}

fn ground_equality_union_min(parent: &mut [u32], left: u32, right: u32) {
    let left_root = ground_equality_find(parent, left);
    let right_root = ground_equality_find(parent, right);
    if left_root != right_root {
        let (keep, merge) = if left_root < right_root {
            (left_root, right_root)
        } else {
            (right_root, left_root)
        };
        parent[merge as usize] = keep;
    }
}

/// Eagerly merge unconditional named-individual equalities.
///
/// Only unit ground facts `top -> o1 = o2` participate. A conditional or
/// disjunctive equality is deliberately ignored because treating it as an
/// asserted merge would be unsound. After computing the transitive closure,
/// every individual occurrence is rewritten to the least id in its class,
/// tautological equality clauses are removed, collapsed inequalities become
/// empty-head clashes, and duplicate clauses are coalesced. This is an exact
/// equality quotient, not an approximation: all labels and role links from an
/// alias are transferred to the same representative, just as in Konclude's
/// deterministic `getMergedIndividualNodes`/`mergeIndividualNodeInto` path.
fn merge_asserted_ground_equalities(
    clauses: Vec<OntologyClause>,
) -> (Vec<OntologyClause>, i32, GroundEqualityMergeStats) {
    let max_ind = input_max_individual(&clauses);
    let mut stats = GroundEqualityMergeStats {
        clauses_before: clauses.len(),
        clauses_after: clauses.len(),
        ..GroundEqualityMergeStats::default()
    };
    if max_ind == 0 {
        return (clauses, max_ind, stats);
    }

    let mut parent: Vec<u32> = (0..=max_ind as u32).collect();
    for clause in &clauses {
        if clause.body.is_empty() && clause.head.len() == 1 {
            if let Lit::Eq { s, t } = clause.head[0] {
                if is_individual(s) && is_individual(t) {
                    stats.asserted_pairs += 1;
                    ground_equality_union_min(&mut parent, ind_id(s) as u32, ind_id(t) as u32);
                }
            }
        }
    }
    for id in 1..=max_ind as u32 {
        let representative = ground_equality_find(&mut parent, id);
        parent[id as usize] = representative;
        stats.merged_aliases += usize::from(representative != id);
    }
    if stats.merged_aliases == 0 {
        return (clauses, max_ind, stats);
    }

    let canonical_term = |term: Term| {
        if is_individual(term) {
            ind_term(parent[ind_id(term) as usize] as i32)
        } else if is_comp(term) {
            let (function, individual) = comp_parts(term);
            let representative = ind_term(parent[ind_id(individual) as usize] as i32);
            comp_term(function, representative)
        } else {
            term
        }
    };
    let mut merged: Vec<OntologyClause> = Vec::with_capacity(clauses.len());
    let mut index: HashMap<u64, Vec<usize>> = HashMap::new();
    for clause in clauses {
        let body: Vec<Pred> = clause
            .body
            .iter()
            .map(|pred| pred.apply(&canonical_term))
            .collect();
        let mut head: Vec<Lit> = clause
            .head
            .iter()
            .map(|literal| literal.apply(&canonical_term))
            .collect();
        // A true equality makes the disjunctive head true, hence the whole
        // clause tautological. A false inequality contributes no disjunct.
        if head.iter().any(Lit::is_valid_equation) {
            continue;
        }
        head.retain(|literal| !literal.is_invalid_equation());
        let rewritten = OntologyClause::new(body, head);
        let hash = content_hash(&(&rewritten.body, &rewritten.head));
        let duplicate = index.get(&hash).is_some_and(|candidates| {
            candidates.iter().any(|&candidate| {
                merged[candidate].body == rewritten.body && merged[candidate].head == rewritten.head
            })
        });
        if duplicate {
            continue;
        }
        let id = merged.len();
        merged.push(rewritten);
        index.entry(hash).or_default().push(id);
    }
    stats.clauses_after = merged.len();
    (merged, max_ind, stats)
}

/// Detect named concepts that the normalised clause set proves equivalent to a
/// finite union of exact nominal proxies.  The frontend represents
/// `A ≡ {o1,…,on}` as an auxiliary `Q` with
///
/// * `A(x) → Q(x)` and `Q(x) → A(x)`,
/// * `Q(x) → N1(x) ∨ … ∨ Nn(x)` and every `Ni(x) → Q(x)`, and
/// * `Ni(x) → x ≈ oi` (plus the ground nominal fact).
///
/// We recognise the proof obligations from the clauses rather than trusting
/// auxiliary names.  This is the certificate used by the nominal-label reuse
/// path: if any direction is absent, the query stays on ordinary CB saturation.
fn detect_nominal_enumerations(sig: &Sig, clauses: &[OntologyClause]) -> HashMap<Iri, Vec<Term>> {
    let mut nominal_individual: HashMap<Iri, Term> = HashMap::new();
    let mut nominal_facts: HashSet<(Iri, Term)> = HashSet::new();
    let mut edges: HashSet<(Iri, Iri)> = HashSet::new();
    let mut forward: HashMap<Iri, Vec<Iri>> = HashMap::new();
    let mut reverse: HashMap<Iri, Vec<Iri>> = HashMap::new();

    for clause in clauses {
        if clause.body.is_empty() && clause.head.len() == 1 {
            if let Lit::P(Pred::Concept { iri, t }) = clause.head[0] {
                if is_individual(t) {
                    nominal_facts.insert((iri, t));
                }
            }
        }
    }
    for clause in clauses {
        if clause.body.len() != 1 || clause.head.len() != 1 {
            continue;
        }
        let Pred::Concept { iri: from, t: X } = clause.body[0] else {
            continue;
        };
        match clause.head[0] {
            Lit::P(Pred::Concept { iri: to, t: X }) => {
                if edges.insert((from, to)) {
                    forward.entry(from).or_default().push(to);
                    reverse.entry(to).or_default().push(from);
                }
            }
            Lit::Eq { s, t } => {
                let individual = if s == X && is_individual(t) {
                    Some(t)
                } else if t == X && is_individual(s) {
                    Some(s)
                } else {
                    None
                };
                if let Some(o) = individual.filter(|&o| nominal_facts.contains(&(from, o))) {
                    nominal_individual.insert(from, o);
                }
            }
            _ => {}
        }
    }

    let reachable = |start: Iri, graph: &HashMap<Iri, Vec<Iri>>| {
        let mut seen = HashSet::from([start]);
        let mut todo = vec![start];
        while let Some(node) = todo.pop() {
            if let Some(next) = graph.get(&node) {
                for &n in next {
                    if seen.insert(n) {
                        todo.push(n);
                    }
                }
            }
        }
        seen
    };

    let mut out: HashMap<Iri, Vec<Term>> = HashMap::new();
    for clause in clauses {
        if clause.body.len() != 1 || clause.head.is_empty() {
            continue;
        }
        let Pred::Concept { iri: q, t: X } = clause.body[0] else {
            continue;
        };
        let mut proxies = Vec::with_capacity(clause.head.len());
        let mut individuals = Vec::with_capacity(clause.head.len());
        let mut exact_nominal_union = true;
        for &literal in &clause.head {
            let Lit::P(Pred::Concept { iri: nominal, t: X }) = literal else {
                exact_nominal_union = false;
                break;
            };
            let Some(&individual) = nominal_individual.get(&nominal) else {
                exact_nominal_union = false;
                break;
            };
            proxies.push(nominal);
            individuals.push(individual);
        }
        // The reverse implications prove `N1 ∨ … ∨ Nn ⊑ Q`; without
        // them this is only an upper bound on Q and cannot certify either the
        // complete subsumer set or satisfiability.
        if !exact_nominal_union || !proxies.iter().all(|&n| edges.contains(&(n, q))) {
            continue;
        }
        individuals.sort_unstable();
        individuals.dedup();

        let q_forward = reachable(q, &forward);
        let q_reverse = reachable(q, &reverse);
        for iri in 0..sig.concept_names.len() as Iri {
            if sig.is_internal(iri) || sig.is_nothing_concept(iri) {
                continue;
            }
            if q_forward.contains(&iri) && q_reverse.contains(&iri) {
                out.entry(iri).or_insert_with(|| individuals.clone());
            }
        }
    }
    out
}

// ------------------------------- contexts ----------------------------------

#[derive(Clone)]
struct Context {
    id: usize,
    core: Vec<Pred>,
    root: bool,
    /// the query concept this root context classifies (if any)
    query: Option<Iri>,
    /// Worked-off clauses, as ids into the engine-level clause arena for this
    /// context's ordering domain (root / non-root).  The arena is content-
    /// interned and append-only, so identical clauses derived in thousands of
    /// contexts (notably the seeded shared closure) are stored once; ids are
    /// stable and ascend in work-off order.
    worked_off: Vec<u32>,
    /// Arena ids of the clauses currently in `worked_off` ∪ `todo` (the arena
    /// id IS the canonical content key, so this replaces the old full
    /// (body, head) copy used for duplicate detection).
    clause_keys: HashSet<u32>,
    /// Index from a head-predicate iri to the (ascending, de-duplicated)
    /// `worked_off` indices of clauses having a *maximal* head predicate with
    /// that iri.  Lets Hyper find unification candidates without scanning all
    /// of `worked_off`.  Concept and role iris live in separate namespaces, so
    /// they are indexed separately; `can_unify` still filters precisely.
    head_concept_index: HashMap<Iri, Posting>,
    head_role_index: HashMap<Iri, Posting>,
    /// Role postings refined by one fixed ground endpoint. In the nominal root,
    /// Hyper commonly joins `C(y)` with `R(x,y)`: after the side fact binds
    /// `y=o`, Sequoia's substitution-aware lookup visits only `R(_,o)` rather
    /// than every assertion of `R`. The other endpoint may remain a variable
    /// (`S(o,y)` is a crucial Nom premise), so indexing only fully ground roles
    /// is incomplete. These postings contain every maximal role whose indexed
    /// endpoint is an individual or grounded successor.
    ground_role_source_index: HashMap<(Iri, Term), Posting>,
    ground_role_target_index: HashMap<(Iri, Term), Posting>,
    /// Exact maximal-head predicate lookup used by Pred.  This mirrors
    /// Sequoia's `maxHeadPredicateIndex`: unlike Hyper, Pred does not unify a
    /// body atom, it matches the already-substituted predicate exactly.  The
    /// IRI indexes above remain the broader candidate indexes used by Hyper.
    max_head_pred_index: HashMap<Pred, Posting>,
    /// Clauses containing a term at a rewrite position in a maximal head
    /// literal.  This is Sequoia's `maxHeadLiteralTermIndex`, extended to
    /// nominal ground terms because KM's nominal Eq/Join rules can rewrite
    /// individuals as well as `f(x)` terms.
    max_head_term_index: HashMap<Term, Posting>,
    /// Every active clause (`worked_off` plus `todo`) indexed by each head
    /// literal. This is Sequoia's active context redundancy index: pending
    /// clauses participate in Elim without a linear scan of the pending queue.
    /// The rarest posting is verified with exact set inclusion, avoiding the
    /// exponential subset walk of a generic Rust trie on long nominal clauses.
    active_head_lit_index: HashMap<Lit, Posting>,
    /// Active clauses with an empty head. Such a clause can subsume a
    /// non-empty-head clause without sharing a literal, so it has a dedicated
    /// posting list.
    active_empty_head: Vec<u32>,
    todo: VecDeque<u32>,
    /// pred clauses pushed in from successor contexts (already back-substituted),
    /// as ids into the engine-level `pred_interned` table.  The same substituted
    /// clause can arrive more than once (e.g. from a successor's pre- and
    /// post-growth contexts under the central strategy); `neighbor_pred_seen`
    /// dedups arrivals, which only skips re-deriving already-derived clauses.
    neighbor_pred: Vec<u32>,
    neighbor_pred_seen: HashSet<u32>,
    /// Exact body-predicate posting lists over `neighbor_pred`, in arrival
    /// order.  Local Pred only needs clauses whose body contains the maximal
    /// function predicate currently being processed; indexing that membership
    /// avoids rescanning every received predecessor clause for every such
    /// predicate.
    neighbor_pred_body_index: HashMap<Pred, Vec<u32>>,
    /// successor edges: function term -> successor context id
    successors: HashMap<Term, usize>,
    /// Central strategy: per function symbol, the full (raw, un-substituted)
    /// set of succ-trigger predicates pushed so far.  The successor context for
    /// `f` is keyed by the σ-image of this set (its core); when the set grows,
    /// the edge re-targets a new context with the larger core.
    trigger_sets: HashMap<Term, std::collections::BTreeSet<Pred>>,
    /// Central strategy: the subset of `trigger_sets[f]` whose triggers were
    /// derived as unit facts (`⊤ → p`, no body, no disjunction) in this
    /// context.  ONLY these enter the successor's core: a disjunctively
    /// derived trigger is not known to hold, so asserting it in the core
    /// would make every consequence the successor pushes back conditional on
    /// the WHOLE core at once (an n-way simultaneous cut no resolution step
    /// can perform), losing the per-disjunct refutations completeness needs
    /// (the ≥n min-cardinality recognition stall on ore_ont_16461).
    /// Non-fact triggers still travel as Succ messages and become hypothesis
    /// clauses `p → p` at the target, so their consequences come back
    /// conditioned on `p` alone.
    fact_trigger_sets: HashMap<Term, std::collections::BTreeSet<Pred>>,
    /// predecessor edges: (predecessor ctx id, function term) -> pushed predicates
    predecessors: HashMap<(usize, Term), HashSet<Pred>>,
    pushed_succ: HashSet<Pred>,
    /// per predecessor edge, the `pred_pool` indices already pushed back, to
    /// avoid resending.  Pool indices are stable (the pool is append-only), so
    /// they identify the clause without copying it; a re-added identical clause
    /// gets a fresh index and is resent, which the receiver's
    /// `neighbor_pred_seen` dedups.
    pushed_pred: HashMap<(usize, Term), HashSet<u32>>,
    /// Semi-naive Pred propagation: append-only pool of worked-off clauses that
    /// are Pred-eligible (function-free, predicate-only head).  Entries are never
    /// removed (a clause back-subsumed out of `worked_off` is still
    /// context-entailed, so pushing it stays sound), which lets `pred_hwm` be a
    /// stable high-water mark despite `worked_off` reshuffling under back-subsume.
    /// Entries are arena ids (the arena is append-only, so the referenced
    /// clause outlives any back-subsumption).
    pred_pool: Vec<u32>,
    /// number of `pred_pool` entries already cross-checked against every edge at
    /// that edge's `edge_seen` pushed-length in a prior `propagate`.
    pred_hwm: usize,
    /// per predecessor edge, the `pushed`-set length at which all of
    /// `pred_pool[..pred_hwm]` were last checked against it.  An edge whose
    /// current pushed-set is longer is "dirty" and forces a re-check of the old
    /// pool against it (a previously-failed covered-check can only flip when the
    /// edge gains a pushed predicate).
    edge_seen: HashMap<(usize, Term), usize>,
    /// Semi-naive Succ propagation: append-only pool of worked-off clauses with a
    /// function-headed (succ-trigger candidate) maximal head predicate, and the
    /// high-water mark of entries already scanned for Succ triggers.
    /// Entries are arena ids.
    succ_pool: Vec<u32>,
    succ_hwm: usize,
    /// r-Succ (KM_RSUCC): append-only pool of worked-off clauses with a maximal
    /// head predicate that is a CENTRAL reachability fact (`__trans__`/`__chain__(x)`).
    /// These are forwarded to every successor as edge-conditioned neighbour facts
    /// (the predecessor vouching "my reach holds at your neighbour"), the missing
    /// step that lets a successor fire the transitivity clause across an inverse
    /// back-edge.  Entries are arena ids.  Empty unless `sig.rsucc`.
    rsucc_pool: Vec<u32>,
    /// Semi-naive r-Succ: the distinct CENTRAL reachability predicates extracted
    /// from `rsucc_pool` so far, in first-occurrence (pool) order, with
    /// `rsucc_hwm` the count of `rsucc_pool` entries already scanned into it.
    /// `rsucc_pool` is append-only and its reach extraction never consults
    /// `clause_keys`, so accumulating incrementally reproduces exactly the
    /// ordered-unique set a full rescan would build — the same delta discipline
    /// as `succ_hwm`/`pred_hwm`, avoiding the per-`propagate` full-pool rescan.
    /// `rsucc_reach_set` mirrors `rsucc_reach` for O(1) dedup on insertion.
    rsucc_reach: Vec<Pred>,
    rsucc_reach_set: HashSet<Pred>,
    rsucc_hwm: usize,
    /// per (successor function term, target ctx, central reach pred) already
    /// forwarded, to dedup the edge × reach-fact cross-product across `propagate`
    /// rounds.  The target id is part of the key so a re-targeted (grown-core)
    /// successor is re-sent the reach facts.
    pushed_rsucc: HashSet<(Term, usize, Pred)>,
    /// Semi-naive r-Succ cross-product: per successor edge `(f, target)` the
    /// number of `rsucc_reach` entries already offered to the `pushed_rsucc`
    /// gate for that edge.  `rsucc_reach` is append-only, so `reach[..hwm]` were
    /// all offered (hence already gate-checked) in prior rounds; scanning only
    /// `reach[hwm..]` per round skips work `pushed_rsucc.insert` would reject,
    /// avoiding the per-`propagate` full `successors × reach` rescan while
    /// emitting an identical `Msg::Succ` set and order (see `rsucc_cross_step`).
    rsucc_pair_reach_hwm: HashMap<(Term, usize), usize>,
    /// Semi-naive r-Succ cross-product driver gate.  `rsucc_offered` is the
    /// `rsucc_reach.len()` at the last time the `successors × reach` cross-step
    /// ran; `rsucc_edges_grew` records that a successor edge was added or
    /// re-targeted (a new `(f, target)` pair) since that run.  The cross-step can
    /// fire a *new* triple only when reach grew (`rsucc_reach.len() >
    /// rsucc_offered`) or an edge changed (`rsucc_edges_grew`); otherwise every
    /// current edge already has `hwm == rsucc_reach.len()` (advanced by the prior
    /// run) so the sweep is provably empty.  Skipping it then avoids the
    /// O(|successors|) hwm sweep and the transient `successors` Vec allocation on
    /// the (common) `propagate` rounds where the context was re-dirtied by
    /// unrelated predecessor / Pred churn.  `successors` is insert-only (never
    /// pruned), so a set flag can only over-approximate genuine growth — never
    /// miss it — keeping the emitted `Msg::Succ` set/order (hence the fixpoint)
    /// identical to the unconditional driver.
    rsucc_offered: usize,
    rsucc_edges_grew: bool,
    /// Individuals whose ground ontology facts have been seeded into this
    /// context (demand-driven; see `Ontology::ground_facts`).
    seeded_inds: HashSet<Term>,
    /// Join rule (arXiv:1805.01396 Table 3): worked-off clauses indexed by
    /// each *ground* body atom (the verbatim-copied `C_i` of Pred/r-Pred),
    /// so a later-derived provider for that atom can resolve it.  Empty
    /// without individuals — the rule is inert on the SRIQ fragment.
    ground_body_index: HashMap<Pred, Vec<u32>>,
    /// Join case 3: body-empty clauses with a maximal head literal `x ≈ o`,
    /// keyed by the individual `o` (the bridge premise `Γ' → Δ'' ∨ x ≈ o`).
    bridge_index: HashMap<Term, Vec<u32>>,
    /// r-Succ side condition (*): worked-off clauses whose head contains a
    /// merge-form literal (`x ≈ o`, `y ≈ o`, `x ≈ y`) — the candidates that
    /// can block an r-Succ push (deferring to equality reasoning when this
    /// context's element may itself be a nominal or merge with its
    /// predecessor).
    merge_clauses: Vec<u32>,
    /// `true` if a new worked-off clause or a new predecessor edge/pushed
    /// predicate has appeared since the last `propagate`.  When `false`,
    /// `propagate` has no new Succ/Pred message to emit (the `pushed_succ` /
    /// `pushed_pred` sets already cover everything seen), so the full
    /// `worked_off` scan can be skipped.  Soundness/output are unchanged: a
    /// skipped scan would only have re-derived already-sent messages.
    dirty: bool,
}

impl Context {
    fn new(id: usize, core: Vec<Pred>, root: bool, query: Option<Iri>) -> Context {
        Context {
            id,
            core,
            root,
            query,
            worked_off: Vec::new(),
            clause_keys: HashSet::new(),
            head_concept_index: HashMap::new(),
            head_role_index: HashMap::new(),
            ground_role_source_index: HashMap::new(),
            ground_role_target_index: HashMap::new(),
            max_head_pred_index: HashMap::new(),
            max_head_term_index: HashMap::new(),
            active_head_lit_index: HashMap::new(),
            active_empty_head: Vec::new(),
            todo: VecDeque::new(),
            neighbor_pred: Vec::new(),
            neighbor_pred_seen: HashSet::new(),
            neighbor_pred_body_index: HashMap::new(),
            successors: HashMap::new(),
            trigger_sets: HashMap::new(),
            fact_trigger_sets: HashMap::new(),
            predecessors: HashMap::new(),
            pushed_succ: HashSet::new(),
            pushed_pred: HashMap::new(),
            pred_pool: Vec::new(),
            pred_hwm: 0,
            edge_seen: HashMap::new(),
            succ_pool: Vec::new(),
            succ_hwm: 0,
            rsucc_pool: Vec::new(),
            rsucc_reach: Vec::new(),
            rsucc_reach_set: HashSet::new(),
            rsucc_hwm: 0,
            pushed_rsucc: HashSet::new(),
            rsucc_pair_reach_hwm: HashMap::new(),
            rsucc_offered: 0,
            rsucc_edges_grew: false,
            seeded_inds: HashSet::new(),
            ground_body_index: HashMap::new(),
            bridge_index: HashMap::new(),
            merge_clauses: Vec::new(),
            dirty: true,
        }
    }

    /// File the worked-off clause with arena id `cid` into every head index it
    /// belongs to, driven by its shared `Facet` list (see `Facet`): the key
    /// derivation is done once per interned clause rather than once per
    /// (context, clause) pair, and this walks a flat slice of `Copy` keys.
    ///
    /// Each key receives `cid` once, so a posting is still the ascending,
    /// duplicate-free id list `rebuild_head_index` would produce; appending in
    /// work-off order keeps each list in candidate order.
    fn index_clause(&mut self, facets: &FacetTable, cid: u32) {
        for &facet in facets.keys_of(cid) {
            match facet {
                Facet::HeadConcept(iri) => {
                    self.head_concept_index.entry(iri).or_default().push(cid)
                }
                Facet::HeadRole(iri) => self.head_role_index.entry(iri).or_default().push(cid),
                Facet::MaxPred(p) => self.max_head_pred_index.entry(p).or_default().push(cid),
                Facet::GroundRoleSource(iri, s) => {
                    let posting = self.ground_role_source_index.entry((iri, s)).or_default();
                    if posting.last() != Some(&cid) {
                        posting.push(cid);
                    }
                }
                Facet::GroundRoleTarget(iri, t) => {
                    let posting = self.ground_role_target_index.entry((iri, t)).or_default();
                    if posting.last() != Some(&cid) {
                        posting.push(cid);
                    }
                }
                Facet::RewriteTerm(term) => {
                    self.max_head_term_index.entry(term).or_default().push(cid)
                }
                Facet::GroundBody(p) => {
                    let posting = self.ground_body_index.entry(p).or_default();
                    if !posting.contains(&cid) {
                        posting.push(cid);
                    }
                }
                Facet::Bridge(o) => self.bridge_index.entry(o).or_default().push(cid),
                Facet::Merge => self.merge_clauses.push(cid),
            }
        }
    }

    /// Incrementally drop one `worked_off` clause from every head index.  This
    /// mirrors `index_clause` key-for-key — structurally so, since both walk the
    /// same shared `Facet` list — removing `cid` from each posting it was
    /// inserted under, so the resulting index state is identical to a full
    /// `rebuild_head_index` over `worked_off \ {cid}` (a posting is a set of
    /// clause ids; removing the id leaves the survivors in the same work-off
    /// order).  Used by back-subsumption instead of rebuilding the whole index
    /// whenever a worked-off clause is subsumed away.
    fn unindex_clause(&mut self, facets: &FacetTable, cid: u32) {
        for &facet in facets.keys_of(cid) {
            match facet {
                Facet::HeadConcept(iri) => posting_remove(&mut self.head_concept_index, iri, cid),
                Facet::HeadRole(iri) => posting_remove(&mut self.head_role_index, iri, cid),
                Facet::MaxPred(p) => posting_remove(&mut self.max_head_pred_index, p, cid),
                Facet::GroundRoleSource(iri, s) => {
                    posting_remove(&mut self.ground_role_source_index, (iri, s), cid)
                }
                Facet::GroundRoleTarget(iri, t) => {
                    posting_remove(&mut self.ground_role_target_index, (iri, t), cid)
                }
                Facet::RewriteTerm(term) => {
                    posting_remove(&mut self.max_head_term_index, term, cid)
                }
                Facet::GroundBody(p) => vec_posting_remove(&mut self.ground_body_index, p, cid),
                Facet::Bridge(o) => vec_posting_remove(&mut self.bridge_index, o, cid),
                Facet::Merge => self.merge_clauses.retain(|&x| x != cid),
            }
        }
    }

    /// Rebuild every `worked_off` index from scratch.  Back-subsumption now
    /// maintains the head index incrementally via `unindex_clause`; this full
    /// rebuild is retained as the reference oracle that the incremental path is
    /// differentially tested against (`back_subsume_incremental_unindex_matches_rebuild`).
    #[cfg(test)]
    fn rebuild_head_index(&mut self, facets: &FacetTable) {
        self.clear_head_indexes();
        let worked_off = self.worked_off.clone();
        for cid in worked_off {
            self.index_clause(facets, cid);
        }
    }

    #[cfg(test)]
    fn clear_head_indexes(&mut self) {
        self.head_concept_index.clear();
        self.head_role_index.clear();
        self.ground_role_source_index.clear();
        self.ground_role_target_index.clear();
        self.max_head_pred_index.clear();
        self.max_head_term_index.clear();
        self.ground_body_index.clear();
        self.bridge_index.clear();
        self.merge_clauses.clear();
    }

    /// Frozen pre-`Facet` reference for `index_clause`: re-derives the index
    /// keys from the arena clause on every call, exactly as the engine did
    /// before the key list was hoisted into the shared `FacetTable`.  Kept as
    /// the differential oracle for `facet_indexing_matches_reference_*`; the
    /// facet path must reproduce its index state key for key.  Never used off
    /// the test path.
    #[cfg(test)]
    fn index_clause_reference(&mut self, arena: &[ContextClause], cid: u32) {
        let c = &arena[cid as usize];
        let mut concept_iris: Vec<Iri> = Vec::new();
        let mut role_iris: Vec<Iri> = Vec::new();
        for (p, _) in c.max_head_predicates() {
            match p {
                Pred::Concept { iri, .. } => {
                    if !concept_iris.contains(&iri) {
                        concept_iris.push(iri);
                    }
                }
                Pred::Role { iri, .. } => {
                    if !role_iris.contains(&iri) {
                        role_iris.push(iri);
                    }
                }
            }
        }
        for iri in concept_iris {
            self.head_concept_index.entry(iri).or_default().push(cid);
        }
        for iri in role_iris {
            self.head_role_index.entry(iri).or_default().push(cid);
        }
        for (p, _) in c.max_head_predicates() {
            self.max_head_pred_index.entry(p).or_default().push(cid);
            if let Pred::Role { iri, s, t } = p {
                if is_individual(s) || is_comp(s) {
                    let source = self.ground_role_source_index.entry((iri, s)).or_default();
                    if source.last() != Some(&cid) {
                        source.push(cid);
                    }
                }
                if is_individual(t) || is_comp(t) {
                    let target = self.ground_role_target_index.entry((iri, t)).or_default();
                    if target.last() != Some(&cid) {
                        target.push(cid);
                    }
                }
            }
        }
        let mut rewrite_terms: SmallVec<[Term; 2]> = SmallVec::new();
        for l in c.max_head() {
            match l {
                Lit::P(Pred::Concept { t, .. }) => {
                    if !rewrite_terms.contains(&t) {
                        rewrite_terms.push(t);
                    }
                }
                Lit::P(Pred::Role { s, t, .. }) => {
                    if !rewrite_terms.contains(&s) {
                        rewrite_terms.push(s);
                    }
                    if !rewrite_terms.contains(&t) {
                        rewrite_terms.push(t);
                    }
                }
                Lit::Eq { s, .. } | Lit::Ineq { s, .. } => {
                    if !rewrite_terms.contains(&s) {
                        rewrite_terms.push(s);
                    }
                }
            }
        }
        for term in rewrite_terms {
            self.max_head_term_index.entry(term).or_default().push(cid);
        }
        for p in &c.body {
            if p.is_ground() {
                let e = self.ground_body_index.entry(*p).or_default();
                if !e.contains(&cid) {
                    e.push(cid);
                }
            }
        }
        if c.body.is_empty() {
            for l in c.max_head() {
                if let Lit::Eq { s, t } = l {
                    if is_individual(s) && t == X {
                        self.bridge_index.entry(s).or_default().push(cid);
                    }
                }
            }
        }
        if c.head.iter().any(is_merge_lit) {
            self.merge_clauses.push(cid);
        }
    }

    /// Frozen pre-`Facet` reference for `unindex_clause` (see
    /// `index_clause_reference`).
    #[cfg(test)]
    fn unindex_clause_reference(&mut self, arena: &[ContextClause], cid: u32) {
        let c = &arena[cid as usize];
        let mut concept_iris: Vec<Iri> = Vec::new();
        let mut role_iris: Vec<Iri> = Vec::new();
        for (p, _) in c.max_head_predicates() {
            match p {
                Pred::Concept { iri, .. } => {
                    if !concept_iris.contains(&iri) {
                        concept_iris.push(iri);
                    }
                }
                Pred::Role { iri, .. } => {
                    if !role_iris.contains(&iri) {
                        role_iris.push(iri);
                    }
                }
            }
        }
        for iri in concept_iris {
            posting_remove(&mut self.head_concept_index, iri, cid);
        }
        for iri in role_iris {
            posting_remove(&mut self.head_role_index, iri, cid);
        }
        for (p, _) in c.max_head_predicates() {
            posting_remove(&mut self.max_head_pred_index, p, cid);
            if let Pred::Role { iri, s, t } = p {
                if is_individual(s) || is_comp(s) {
                    posting_remove(&mut self.ground_role_source_index, (iri, s), cid);
                }
                if is_individual(t) || is_comp(t) {
                    posting_remove(&mut self.ground_role_target_index, (iri, t), cid);
                }
            }
        }
        let mut rewrite_terms: SmallVec<[Term; 2]> = SmallVec::new();
        for l in c.max_head() {
            match l {
                Lit::P(Pred::Concept { t, .. }) => {
                    if !rewrite_terms.contains(&t) {
                        rewrite_terms.push(t);
                    }
                }
                Lit::P(Pred::Role { s, t, .. }) => {
                    if !rewrite_terms.contains(&s) {
                        rewrite_terms.push(s);
                    }
                    if !rewrite_terms.contains(&t) {
                        rewrite_terms.push(t);
                    }
                }
                Lit::Eq { s, .. } | Lit::Ineq { s, .. } => {
                    if !rewrite_terms.contains(&s) {
                        rewrite_terms.push(s);
                    }
                }
            }
        }
        for term in rewrite_terms {
            posting_remove(&mut self.max_head_term_index, term, cid);
        }
        for p in &c.body {
            if p.is_ground() {
                vec_posting_remove(&mut self.ground_body_index, *p, cid);
            }
        }
        if c.body.is_empty() {
            for l in c.max_head() {
                if let Lit::Eq { s, t } = l {
                    if is_individual(s) && t == X {
                        vec_posting_remove(&mut self.bridge_index, s, cid);
                    }
                }
            }
        }
        if c.head.iter().any(is_merge_lit) {
            self.merge_clauses.retain(|&x| x != cid);
        }
    }

    /// Add a clause to Sequoia's active redundancy index. Exact duplicates are
    /// rejected before this function is called, so each posting contains `cid`
    /// once.
    fn index_active_clause(&mut self, arena: &[ContextClause], cid: u32) {
        let clause = &arena[cid as usize];
        if clause.head.is_empty() {
            self.active_empty_head.push(cid);
        } else {
            for &literal in &clause.head {
                self.active_head_lit_index
                    .entry(literal)
                    .or_default()
                    .push(cid);
            }
        }
    }

    /// Remove one clause from the active redundancy index.
    fn unindex_active_clause(&mut self, arena: &[ContextClause], cid: u32) {
        let clause = &arena[cid as usize];
        if clause.head.is_empty() {
            self.active_empty_head.retain(|&candidate| candidate != cid);
        } else {
            let mut empty = Vec::new();
            for &literal in &clause.head {
                if let Some(posting) = self.active_head_lit_index.get_mut(&literal) {
                    posting.retain(|candidate| *candidate != cid);
                    if posting.is_empty() {
                        empty.push(literal);
                    }
                }
            }
            for literal in empty {
                self.active_head_lit_index.remove(&literal);
            }
        }
    }

    /// Forward redundancy over the complete active set (`worked_off ∪ todo`).
    /// This has the same active semantics as Sequoia's context-clause
    /// redundancy index, including queued-clause subsumption.
    /// Forward subsumption.  `sigs` is the dense `ClauseSig` array parallel to
    /// `arena` (see `ClauseSig`): every candidate is screened against it before
    /// the clause itself is touched, which keeps a long posting-list scan inside
    /// one flat array instead of chasing each `ContextClause`'s two heap
    /// vectors.  The screen only rejects candidates that provably cannot
    /// subsume, so the answer is identical to scanning with `strengthens`
    /// alone.
    fn fwd_subsumed(
        &self,
        arena: &[ContextClause],
        sigs: &[ClauseSig],
        clause: &ContextClause,
        exclude: Option<u32>,
    ) -> bool {
        debug_assert_eq!(sigs.len(), arena.len(), "ClauseSig mirror out of sync");
        let want = ClauseSig::of(clause);
        for &ci in &self.active_empty_head {
            if Some(ci) == exclude {
                continue;
            }
            if !sigs[ci as usize].may_strengthen(&want) {
                continue;
            }
            if arena[ci as usize].strengthens(clause) {
                return true;
            }
        }
        for literal in &clause.head {
            if let Some(candidates) = self.active_head_lit_index.get(literal) {
                for &ci in candidates {
                    if Some(ci) == exclude {
                        continue;
                    }
                    if !sigs[ci as usize].may_strengthen(&want) {
                        continue;
                    }
                    if arena[ci as usize].strengthens(clause) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Backward subsumption: remove every existing clause that `clause`
    /// strengthens, from both `worked_off` and `todo`, dropping their keys. The
    /// rarest active head posting generates candidates; exact inclusion
    /// verification preserves the same removal set as Sequoia's superset walk.
    fn back_subsume(
        &mut self,
        arena: &[ContextClause],
        sigs: &[ClauseSig],
        facets: &FacetTable,
        clause: &ContextClause,
    ) {
        debug_assert_eq!(sigs.len(), arena.len(), "ClauseSig mirror out of sync");
        debug_assert_eq!(facets.len(), arena.len(), "FacetTable mirror out of sync");
        let nb = clause.body.len();
        let nh = clause.head.len();
        let have = ClauseSig::of(clause);
        let same = |candidate: &ContextClause| {
            candidate.body == clause.body && candidate.head == clause.head
        };
        let candidates: Vec<u32> = if clause.head.is_empty() {
            self.clause_keys.iter().copied().collect()
        } else {
            let mut rarest: Option<&Posting> = None;
            for literal in &clause.head {
                match self.active_head_lit_index.get(literal) {
                    None => {
                        return;
                    }
                    Some(posting) if rarest.map_or(true, |old| posting.len() < old.len()) => {
                        rarest = Some(posting);
                    }
                    Some(_) => {}
                }
            }
            rarest
                .map(|posting| posting.iter().copied().collect())
                .unwrap_or_default()
        };
        let removed: HashSet<u32> = candidates
            .into_iter()
            .filter(|&ci| {
                // Dense screen first (see `ClauseSig`): the length and Bloom
                // conditions are necessary for `clause.strengthens(candidate)`,
                // so anything they reject would have failed the exact check.
                if !have.may_strengthen(&sigs[ci as usize]) {
                    return false;
                }
                let candidate = &arena[ci as usize];
                debug_assert!(candidate.body.len() >= nb && candidate.head.len() >= nh);
                clause.strengthens(candidate) && !same(candidate)
            })
            .collect();
        if removed.is_empty() {
            return;
        }

        // Only worked-off clauses carry head-index postings (todo clauses are
        // indexed only in the active redundancy index, cleared below); collect
        // the removed worked-off ids so we can drop them from the head index
        // incrementally rather than rebuilding it from scratch.
        let removed_worked: Vec<u32> = self
            .worked_off
            .iter()
            .copied()
            .filter(|ci| removed.contains(ci))
            .collect();
        for &ci in &removed {
            self.unindex_active_clause(arena, ci);
            self.clause_keys.remove(&ci);
        }
        self.worked_off.retain(|ci| !removed.contains(ci));
        self.todo.retain(|ci| !removed.contains(ci));
        if !removed_worked.is_empty() {
            // Diagnostic: this call would previously have rebuilt the whole head
            // index, re-indexing every surviving worked-off clause.
            BACKSUB_UNINDEX_EVENTS.with(|c| c.set(c.get() + 1));
            BACKSUB_REINDEX_AVOIDED.with(|c| c.set(c.get() + self.worked_off.len() as u64));
        }
        for ci in removed_worked {
            self.unindex_clause(facets, ci);
        }
    }
}

/// A pred clause (substitution already applied): body and head over x / f(x),
/// plus — in nominal mode — ground atoms over individuals and the propagated
/// equality form `f(x) ≈ o` (image of a successor's `x ≈ o`, the Pr extension
/// of the ALCHOIQ calculus). Heads are full literals so those equalities
/// survive the crossing; without individuals only `Lit::P` heads ever enter
/// the pred pool, so this is representation-only for the SRIQ fragment.
#[derive(Clone, PartialEq, Eq, Hash)]
struct PredClause {
    body: Vec<Pred>,
    head: Vec<Lit>,
}

/// Sequoia `Rules.Pred` inserts each Cartesian-product conclusion through
/// `resultsBuffer.removeRedundant` before returning it to the context.  Keep
/// that exact strengthening antichain, but use the same exact-key trie as
/// Sequoia's active redundancy index instead of comparing every new result
/// with every buffered result.  The original `UnprocessedDeque` implementation
/// is linear; on nominal roots one Pred call can buffer thousands of mutually
/// related conclusions and make the pairwise scan quadratic.
///
/// This changes only the batch representation.  A buffered strengthening (or
/// equal clause) rejects the new result; otherwise the new strengthening
/// removes every weaker buffered result.  Therefore `into_vec` contains exactly
/// the same antichain and the context fixpoint is unchanged.
#[derive(Default)]
struct PredResultBuffer {
    clauses: Vec<Option<ContextClause>>,
    redundancy_trie: RedundancyTrie,
}

impl PredResultBuffer {
    fn push_nonredundant(&mut self, clause: ContextClause) {
        if self.redundancy_trie.contains_subset(&clause, None) {
            return;
        }
        for removed in self.redundancy_trie.remove_supersets(&clause) {
            self.clauses[removed as usize] = None;
        }
        let id = u32::try_from(self.clauses.len()).expect("Pred result buffer exhausted u32 ids");
        self.redundancy_trie.insert(&clause, id);
        self.clauses.push(Some(clause));
    }

    fn into_vec(self) -> Vec<ContextClause> {
        self.clauses.into_iter().flatten().collect()
    }
}

fn push_nonredundant_pred_result(out: &mut PredResultBuffer, clause: ContextClause) {
    out.push_nonredundant(clause);
}

/// Below this many selections, local Pred enumerates its premise product
/// directly instead of staging a per-premise antichain.  The staged join wins
/// only when the product is much larger than the antichain it collapses to;
/// for the one- and two-candidate premises that dominate ordinary ontologies
/// the buffer-per-premise overhead would be pure loss.
const SMALL_PRED_PRODUCT: u64 = 64;

/// Content hash for interning (collisions are resolved by exact comparison,
/// never trusted on their own).
fn content_hash<T: std::hash::Hash>(t: &T) -> u64 {
    use std::hash::Hasher;
    let mut h = std::collections::hash_map::DefaultHasher::new();
    t.hash(&mut h);
    h.finish()
}

// ------------------------------- messages ----------------------------------

#[derive(Clone)]
enum Msg {
    Succ {
        from: usize,
        f: Term,
        p: Pred, // already forward-substituted (over successor's x/y)
        target: usize,
    },
    /// A pushed-back clause, by reference into the sender's append-only
    /// `pred_pool` (both the pool entry and the sender's core are immutable
    /// once created, so resolving them at apply time reads exactly what a
    /// send-time snapshot would have carried).
    Pred {
        to: usize,
        from: usize,
        edge_label: Term,
        pool_idx: u32,
    },
}

// -------------------------------- engine -----------------------------------

/// Why a monotone ontology insertion cannot safely reuse the retained context
/// graph.  The caller must run the ordinary fresh exact engine instead; these
/// are proof boundaries, not best-effort fallbacks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RetainedInsertBoundary {
    /// A newly used body predicate would change the trigger-sensitive literal
    /// ordering of clauses already stored in the context arenas.
    ExistingTriggerOrdering,
    /// Fresh construction quotients unconditional named-individual equalities
    /// before saturation.  The retained graph has already been built over the
    /// unquotiented term ids and cannot be rewritten in place.
    AssertedGroundEquality,
    /// Fresh engines demand-seed named-individual facts when a context first
    /// mentions that individual. Contexts completed before the fact existed do
    /// not retain the complete historical mention set needed to reproduce that
    /// schedule exactly.
    GroundFactInsertion,
    /// Fresh construction promotes `C -> bottom` into static signature data
    /// before maximal-head masks and context clauses are built.
    DirectNothingPromotion,
    /// Nom introduced fresh individual ids in the range a later input
    /// individual would occupy.
    AdditionalNominalCollision,
}

/// Work retained across one exact insertion, used for truthful incremental
/// receipts and microbenchmarks.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct RetainedInsertStats {
    pub contexts_before: usize,
    pub context_clauses_before: usize,
    pub edges_before: usize,
    pub contexts_after: usize,
    pub context_clauses_after: usize,
    pub edges_after: usize,
}

/// The finalized, immutable ontology state of one classification: the clause
/// arena with its Hyper candidate indexes, the trigger-analysed signature, and
/// the nominal-enumeration certificates.  Building it reads the clause set and
/// mutates the signature (trigger bits, `nothing` promotion); once built,
/// nothing in saturation writes to it, so every parallel worker engine can
/// share one copy behind an `Arc` instead of holding a private clone (on a
/// million-clause ABox each clone is hundreds of MB, and the query-parallel
/// path builds one engine per worker thread).
///
/// Retained insertion is the one writer, and it goes through `Arc::make_mut`:
/// an engine that still shares its ontology copies first, so a shared prepared
/// ontology is never mutated under another worker.
#[derive(Clone)]
pub struct PreparedOntology {
    sig: Arc<Sig>,
    ont: Arc<Ontology>,
    nominal_enumerations: Arc<HashMap<Iri, Vec<Term>>>,
    /// Nom rule width `K` over the whole ontology (see `Engine::nom_k`).
    nom_k: usize,
    /// first fresh additional-nominal id (above every input individual)
    nom_first: i32,
    dropped_unsupported: usize,
}

impl PreparedOntology {
    /// The named query concepts of this ontology: every non-internal,
    /// non-`Nothing` concept name.  Reads only the finalized signature, so the
    /// query list no longer costs a throw-away engine construction.
    pub fn named_queries(&self) -> Vec<Iri> {
        (0..self.sig.concept_names.len() as Iri)
            .filter(|&i| !self.sig.is_internal(i) && !self.sig.is_nothing_concept(i))
            .collect()
    }
}

#[derive(Clone)]
pub struct Engine {
    pub sig: Arc<Sig>,
    ont: Arc<Ontology>,
    contexts: Vec<Context>,
    /// Root/split context dedup: content hash of the core -> candidate context
    /// ids (collisions resolved by exact `contexts[id].core` comparison, never
    /// trusted on their own). Keyed by hash rather than owning a `Vec<Pred>`
    /// key so each core is stored once (in `Context.core`) instead of a second
    /// full copy here -- the same content-interning discipline as `cc_intern_idx`
    /// and `pred_intern_idx`. Dedup semantics and returned ids are unchanged.
    core_index: HashMap<u64, Vec<usize>>,
    msgs: VecDeque<Msg>,
    /// The ground (nominal root) context `v_r`: the one context where Hyper
    /// may ground the central variable. Created lazily on the first r-Succ
    /// push or ground fact; None for ontologies without individuals.
    ground_ctx: Option<usize>,
    /// Named classes certified by `detect_nominal_enumerations` as exactly a
    /// finite union of input individuals. Konclude's nominal saturation reuses
    /// the completed ABox label when such a nominal is integrated; KM uses the
    /// exact multi-nominal analogue and intersects the completed ground labels
    /// instead of replaying the whole ABox through a query root.
    nominal_enumerations: Arc<HashMap<Iri, Vec<Term>>>,
    /// Complete named atomic subsumers for enumeration-certified queries already
    /// answered from the ground closure. Kept outside `contexts` so the
    /// expensive nominal query root is never created.
    nominal_shortcuts: HashMap<Iri, BTreeSet<Iri>>,
    /// Pay-as-you-go expansion: one successor context per function symbol `f`,
    /// instead of a single shared empty-core context for every anonymous
    /// successor (the trivial strategy).  Successors generated by distinct
    /// existential skolems no longer pile into one context, which is what blows
    /// up under disjunction.  Sound and complete: the trivial strategy only
    /// tolerated mixing successors because conditional clause bodies prevent a
    /// consequence about one successor from being pushed back along another's
    /// edge; partitioning by `f` pushes exactly the same per-edge consequences.
    successor_ctxs: HashMap<Term, usize>,
    /// Central expansion strategy (default; KM_NO_CENTRAL restores the per-`f`
    /// empty-core pay-as-you-go strategy): successor contexts are keyed by their core
    /// = the σ-image of the predecessor's pushed trigger set for `f`.  Trigger
    /// atoms become *core* atoms (`-> p` by the Core rule) instead of
    /// conditional hypotheses (`p -> p`), so consequences that the empty-core
    /// strategy derives as clauses with ever-growing hypothesis conjunctions in
    /// the body (`Q1(x) ∧ ... ∧ Qk(x) -> D(x)`, the measured blow-up on
    /// disjunctive ontologies) collapse to unit clauses.  Predecessors with
    /// identical trigger sets share one successor context.  Strategy choice is
    /// within the calculus's soundness/completeness freedom (same rules, same
    /// ordering; only WHICH context a Succ message targets changes — cf. the
    /// trivial and pay-as-you-go strategies above); the Pred rule's
    /// `neighbour_core` back-substitution already conditions returned clauses
    /// on the successor's core, which is exactly the pushed trigger set.
    /// Kept separate from `core_index`: root contexts use the root ordering,
    /// so a successor core that happens to equal a root core must NOT be
    /// deduplicated into the root context.
    /// Hash-interned like `core_index` (hash of the core -> candidate ids,
    /// exact-compared) so the successor core lives only in `Context.core`.
    central_index: HashMap<u64, Vec<usize>>,
    /// cached strategy flag: central (default) vs per-`f` pay-as-you-go (KM_NO_CENTRAL)
    central: bool,
    /// Portfolio candidate flags (default OFF/inert), cached from env at `new`:
    /// `core_cap` (KM_CORE_CAP=K) caps the successor core size — excess fact
    /// triggers ride back as `p→p` hypotheses (completeness-safe), bounding the
    /// core-growth cascade; `seed_from_subset` (KM_SEED_FROM_SUBSET) seeds a
    /// grown-core successor from its predecessor-in-the-chain instead of
    /// re-deriving the shared closure + chain; `todo_units_first`
    /// (KM_TODO_UNITS_FIRST) works off empty-body (fact) clauses first so
    /// subsumption prunes earlier (confluent); `early_unsat` (KM_EARLY_UNSAT)
    /// clears a context's todo once it derives ⊥ (the empty clause subsumes all,
    /// so the rest is redundant — sound).
    core_cap: usize,
    seed_from_subset: bool,
    todo_units_first: bool,
    early_unsat: bool,
    /// Hot-path env flags cached at `new` — reading them per call (saturate is
    /// invoked ~10^6 times on a mid ontology) turned `std::env::var` lookups
    /// into a measurable slice of wall time. `prof`/`trace_sat` gate the
    /// per-iteration profiling prints; `trigskip` is the redundant-trigger-skip
    /// default (KM_NO_TRIGSKIP to disable). Env cannot change during a run, so
    /// caching is behaviour-identical.
    prof: bool,
    trace_sat: bool,
    trigskip: bool,
    /// KM_PROF_TIME: accumulate per-rule wall time in the saturation loop
    /// (SUBSUME/HYPER/ADDCLAUSE/PREDLOCAL/EQRULE thread-locals), printed under
    /// KM_STATS. Off by default (zero cost bar a cached-bool branch).
    prof_time: bool,
    /// Context-independent closure: the worked-off clauses of an empty-core,
    /// non-root context saturated from the ontology facts + TBox alone (no Succ
    /// hypotheses, no incoming edges).  These consequences are entailed by the
    /// ontology and hold of *every* element, so they are valid in every
    /// successor context (all empty-core, non-root, same literal ordering).
    /// Computed once and seeded into each new successor context instead of
    /// re-deriving them per context — the measured cross-context duplication on
    /// disjunction/role-chain ontologies is 8-15x, almost all of it this shared
    /// TBox reasoning.  Sound + completeness-preserving (the seeded clauses are
    /// exactly those the context would re-derive), so the saturation fixpoint
    /// and output are unchanged; no Lean re-certification (a redundancy/sharing
    /// optimisation, not a calculus-rule change).
    /// (Arena ids in the non-root domain; seeding a context shares the arena
    /// entries instead of cloning the clauses.)
    shared_closure: Option<Vec<u32>>,
    /// Same idea as `shared_closure` but under the *root* literal ordering
    /// (`root=true`): the facts+TBox closure of an empty-core root context.
    /// Seeded into every query root context (core `{A(x)}`) so the shared TBox
    /// reasoning is computed once rather than per classified concept.  Root and
    /// non-root orderings differ (query concepts are mutually incomparable at a
    /// root), so the two closures are kept separate and never crossed.
    /// (Arena ids in the root domain.)
    shared_root_closure: Option<Vec<u32>>,
    equality: bool,
    /// Intern table for back-substituted pred clauses: one copy per distinct
    /// content, shared across all receiving contexts (`Context.neighbor_pred`
    /// stores ids).  The same clause shape recurs across thousands of contexts
    /// on role-chain ontologies, where the per-context copies dominated peak
    /// memory.  Append-only; ids are stable.
    pred_interned: Vec<PredClause>,
    /// content hash -> candidate ids (collisions resolved by exact comparison)
    pred_intern_idx: HashMap<u64, Vec<u32>>,
    /// Global content-interned clause arenas, one per ordering domain
    /// (`[non-root, root]` -- the same (body, head) has a different cached
    /// `max_head` under the root vs non-root literal ordering, so the domains
    /// are kept separate and never crossed).  Append-only; each distinct
    /// clause is stored once and contexts reference it by id, which collapses
    /// the per-context copies of the seeded shared closure and of clauses
    /// re-derived across contexts.
    cc_arena: [Vec<ContextClause>; 2],
    /// Dense subsumption pre-filter, one entry per `cc_arena` entry and always
    /// the same length (see `ClauseSig`).  Kept out of `ContextClause` on
    /// purpose: the subsumption scans read only this array, so keeping it flat
    /// is what makes a long posting-list walk cache-resident.
    cc_sig: [Vec<ClauseSig>; 2],
    /// Shared per-clause index keys and pool-eligibility bits, one entry per
    /// `cc_arena` entry and always the same length (see `Facet` / `FacetTable`).
    /// Filing a clause into a context's head indexes reads this instead of
    /// re-deriving the keys from the clause, so the derivation is paid once per
    /// distinct clause rather than once per (context, clause) slot.
    cc_facets: [FacetTable; 2],
    /// content hash -> candidate arena ids, per domain (exact-compare verified)
    cc_intern_idx: [HashMap<u64, Vec<u32>>; 2],
    pub dropped_unsupported: usize,
    /// A resource backstop dropped work before the monotone fixpoint. The
    /// derived clauses remain sound, but classification is not complete and
    /// must never be published as a successful answer.
    message_truncated: bool,
    /// Nom rule (arXiv:1805.01396 Table 3): `K`, where `K + 1` is the largest
    /// neighbour-variable index `i` (of `z_i`) over the whole ontology — the
    /// width of the additional-nominal disjunction `⋁_{i=1}^K y ≈ o'_{ρ·S^i}`.
    /// 0 when the ontology has at most one neighbour variable per clause (the
    /// Nom preconditions then cannot arise).
    nom_k: usize,
    /// Additional-nominal interner: (parent individual `o`, role `S`, edge
    /// orientation `S(o,y)` vs `S(y,o)`, index `1..=K`) → fresh individual id
    /// (the nominal label `ρ·S^i`).  Allocation order extends labels, so the
    /// id order satisfies the Def-3 label-monotonicity `o_ρ·σ > o_ρ`.
    /// Interior mutability: allocation happens inside the otherwise read-only
    /// Hyper resolvent build (single-threaded engine, never shared).
    nom_table: std::cell::RefCell<HashMap<(Term, Iri, bool, u16), Term>>,
    /// next fresh individual id (starts above every input individual)
    nom_next: std::cell::Cell<i32>,
    /// first additional-nominal id (= the initial `nom_next`): ids at or
    /// above this are Nom-introduced and exempt from the r-Pred
    /// announcement guard (no context can have announced them)
    nom_base: Term,
    /// Additional-nominal budget (`KM_NOM_BUDGET`, default 4096).  The Nom rule
    /// is the doubly-exponential source of the calculus; on exhaustion further
    /// Nom conclusions are dropped with an explicit warning (sound, possibly
    /// incomplete — never silent).
    nom_budget: usize,
    nom_truncated: std::cell::Cell<bool>,
    /// instrumentation counters (only read under KM_STATS)
    stat_propagate: u64,
    stat_pred_checks: u64,
    stat_succ_scans: u64,
    stat_saturate: u64,
    /// KM_MSGPROF diagnostic: Pred messages emitted per sender context, indexed
    /// by context id.  Empty (and never written) unless the variable is set, so
    /// the production path pays nothing.
    stat_pred_out_by_ctx: Vec<u64>,
    /// KM_MSGPROF diagnostic: arrivals that were exact duplicates of a payload
    /// this receiver already held, arrivals whose join found no provider, the
    /// conclusions the joins produced, and how many of those were genuinely new
    /// clauses in the receiver.  Together they separate "the broadcast is
    /// re-deriving what every receiver already has" from "each receiver draws a
    /// different conclusion".
    stat_pred_dup_arrival: u64,
    stat_pred_empty_join: u64,
    stat_pred_conclusions: u64,
    stat_pred_conclusions_new: u64,
    /// Direction B (`KM_SPLIT`) increment 2: per-context-core assumed disjunct
    /// facts. When a context with a core present here is (first) created, the
    /// listed concept facts `⊤ → d(x)` are seeded into it — this is how the
    /// splitting driver assumes a disjunct in a SUCCESSOR context, not only the
    /// query root. Cores are deterministic given the decisions, so the same
    /// context arises (and gets the same seed) across the fresh-engine-per-branch
    /// runs. Empty in the default (non-split) path.
    branch_decisions: HashMap<Vec<Pred>, Vec<Iri>>,
}

/// Direction B (`KM_SPLIT`): the consequences of one query context's closure,
/// read for the splitting driver. `units` are the forced `⊤ → B(x)` subsumers
/// in this branch; `disjunctions` are the residual `⊤ → l1(x) ∨ … ∨ lk(x)`
/// fact-disjunctions (all concept-on-x) that are the branch's split points.
/// `foreign` is set when a residual multi-head clause is NOT all-concept-on-x
/// (a disjunction over roles/equalities/successor terms): such a clause cannot
/// be split by the propositional-on-x driver, so the driver falls back to the
/// (complete) default engine for that query rather than risk incompleteness.
pub struct ClosureFacts {
    pub unsat: bool,
    pub foreign: bool,
    pub units: Vec<Iri>,
    /// Split points: `(context core, disjunct concept-iris on that context's
    /// central variable)`. Increment 2 splits disjunctions in ANY context (not
    /// just the query root), keyed by the context's core so the decision is
    /// reproducible across fresh-engine-per-branch runs.
    pub split_points: Vec<(Vec<Pred>, Vec<Iri>)>,
}

impl Engine {
    pub fn new(sig: Sig, ont_clauses: Vec<OntologyClause>, dropped: usize) -> Engine {
        Engine::from_prepared(&Engine::prepare(sig, ont_clauses, dropped))
    }

    /// Finalize the ontology once: index the clauses, complete the signature's
    /// trigger analysis, compute the Nom parameters and the nominal-enumeration
    /// certificates.  The result is immutable and shareable, so a query-parallel
    /// classification prepares it once and hands the same copy to every worker
    /// (`from_prepared`) instead of re-indexing and re-cloning the clause arena
    /// per worker.  Output-identical: `Engine::new` is exactly `prepare` followed
    /// by `from_prepared`, and preparation is a pure function of the input clause
    /// set.
    pub fn prepare(sig: Sig, ont_clauses: Vec<OntologyClause>, dropped: usize) -> PreparedOntology {
        let mut sig = sig;
        sig.rsucc = std::env::var_os("KM_RSUCC").is_some();
        let (ont_clauses, max_input_ind, ground_merge) =
            merge_asserted_ground_equalities(ont_clauses);
        if std::env::var_os("KM_PROF").is_some() && ground_merge.asserted_pairs != 0 {
            eprintln!(
                "KM_PROF deterministic-same-merge asserted_pairs={} merged_aliases={} clauses_before={} clauses_after={}",
                ground_merge.asserted_pairs,
                ground_merge.merged_aliases,
                ground_merge.clauses_before,
                ground_merge.clauses_after,
            );
        }
        let mut ont = Ontology::default();
        for c in ont_clauses {
            ont.push_clause(&mut sig, c, true);
        }
        // Sort+dedup the body-predicate candidate lists ONCE: the ontology is
        // immutable, so `clauses_cand` returns an already-canonical borrowed
        // slice instead of cloning+sorting+deduping on every Hyper call.
        // Output-identical (same candidate set, same order); just not rebuilt
        // per call.  (`concept_body_any` can list a clause twice when its body
        // mentions the same concept iri on two terms, e.g. `C(x) ∧ C(y)`.)
        ont.canonicalise_candidates();
        // Nom-rule parameters: K + 1 = the largest z_i index over the ontology,
        // and fresh additional nominals are allocated above every input
        // individual id (so the term/label order extends allocation order).
        let mut max_z: i32 = 0;
        // Fresh additional nominals must lie above every INPUT individual,
        // including aliases removed by the deterministic equality quotient.
        // Reusing a merged-away input id would not be fresh in OWL semantics.
        let mut max_ind: i32 = max_input_ind;
        {
            let mut see = |t: Term| {
                if is_neighbour(t) && t != Y {
                    max_z = max_z.max((Y - t) as i32);
                } else if is_individual(t) {
                    max_ind = max_ind.max(ind_id(t));
                } else if is_comp(t) {
                    max_ind = max_ind.max(ind_id(comp_parts(t).1));
                }
            };
            for c in &ont.clauses {
                for p in &c.body {
                    match *p {
                        Pred::Concept { t, .. } => see(t),
                        Pred::Role { s, t, .. } => {
                            see(s);
                            see(t);
                        }
                    }
                }
                for l in &c.head {
                    match *l {
                        Lit::P(Pred::Concept { t, .. }) => see(t),
                        Lit::P(Pred::Role { s, t, .. }) => {
                            see(s);
                            see(t);
                        }
                        Lit::Eq { s, t } | Lit::Ineq { s, t } => {
                            see(s);
                            see(t);
                        }
                    }
                }
            }
        }
        let nominal_enumerations = detect_nominal_enumerations(&sig, &ont.clauses);
        PreparedOntology {
            sig: Arc::new(sig),
            ont: Arc::new(ont),
            nominal_enumerations: Arc::new(nominal_enumerations),
            nom_k: (max_z - 1).max(0) as usize,
            nom_first: max_ind + 1,
            dropped_unsupported: dropped,
        }
    }

    /// A fresh engine over an already prepared ontology.  Only the per-engine
    /// mutable saturation state (contexts, arenas, message queue, Nom interner)
    /// is allocated; the clause arena, signature and nominal certificates are
    /// shared with every other engine built from the same `PreparedOntology`.
    pub fn from_prepared(prepared: &PreparedOntology) -> Engine {
        let nom_budget = std::env::var("KM_NOM_BUDGET")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(4096);
        Engine {
            sig: Arc::clone(&prepared.sig),
            ont: Arc::clone(&prepared.ont),
            contexts: Vec::new(),
            core_index: HashMap::new(),
            ground_ctx: None,
            nominal_enumerations: Arc::clone(&prepared.nominal_enumerations),
            nominal_shortcuts: HashMap::new(),
            msgs: VecDeque::new(),
            successor_ctxs: HashMap::new(),
            central_index: HashMap::new(),
            central: std::env::var_os("KM_NO_CENTRAL").is_none(),
            // Portfolio candidate flags (cached once; default OFF/inert).
            core_cap: std::env::var("KM_CORE_CAP")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(0),
            seed_from_subset: std::env::var_os("KM_SEED_FROM_SUBSET").is_some(),
            prof: std::env::var_os("KM_PROF").is_some(),
            trace_sat: std::env::var_os("KM_SAT").is_some(),
            trigskip: std::env::var_os("KM_NO_TRIGSKIP").is_none(),
            prof_time: std::env::var_os("KM_PROF_TIME").is_some(),
            // Default ON (sound: units-first is confluent scheduling, early-unsat
            // is a ⊥-subsumes-all short-circuit). Validated gold-clean + net
            // faster + recovers 10908 across the full ORE corpus (IBEX 47526798,
            // results/keep-improvements-20260615.txt). Opt out with KM_NO_*.
            todo_units_first: !std::env::var_os("KM_NO_TODO_UNITS_FIRST").is_some(),
            early_unsat: !std::env::var_os("KM_NO_EARLY_UNSAT").is_some(),
            shared_closure: None,
            shared_root_closure: None,
            equality: true,
            pred_interned: Vec::new(),
            pred_intern_idx: HashMap::new(),
            cc_arena: [Vec::new(), Vec::new()],
            cc_sig: [Vec::new(), Vec::new()],
            cc_facets: [FacetTable::new(), FacetTable::new()],
            cc_intern_idx: [HashMap::new(), HashMap::new()],
            dropped_unsupported: prepared.dropped_unsupported,
            message_truncated: false,
            nom_k: prepared.nom_k,
            nom_table: std::cell::RefCell::new(HashMap::new()),
            nom_next: std::cell::Cell::new(prepared.nom_first),
            nom_base: ind_term(prepared.nom_first),
            nom_budget,
            nom_truncated: std::cell::Cell::new(false),
            stat_propagate: 0,
            stat_pred_checks: 0,
            stat_succ_scans: 0,
            stat_saturate: 0,
            stat_pred_out_by_ctx: Vec::new(),
            stat_pred_dup_arrival: 0,
            stat_pred_empty_join: 0,
            stat_pred_conclusions: 0,
            stat_pred_conclusions_new: 0,
            branch_decisions: HashMap::new(),
        }
    }

    /// Check whether appending `additions` can preserve the existing context
    /// graph and its cached ordering/index invariants.  A rejected insertion is
    /// still supported exactly by the caller's fresh-engine fallback.
    pub(crate) fn retained_insert_boundary(
        &self,
        additions: &[OntologyClause],
    ) -> Option<RetainedInsertBoundary> {
        for clause in additions {
            // Fresh engines quotient precisely these asserted equalities before
            // building any context.  Replaying an equality conclusion cannot
            // retroactively change the term ids used as context/index keys.
            if clause.body.is_empty()
                && clause.head.len() == 1
                && matches!(clause.head[0], Lit::Eq { s, t } if is_individual(s) && is_individual(t))
            {
                return Some(RetainedInsertBoundary::AssertedGroundEquality);
            }
            if clause.body.is_empty() {
                let mut individuals = Vec::new();
                for literal in &clause.head {
                    lit_inds(literal, &mut individuals);
                }
                if !individuals.is_empty() {
                    return Some(RetainedInsertBoundary::GroundFactInsertion);
                }
            }
            if clause.body.len() == 1
                && clause.head.is_empty()
                && matches!(clause.body[0], Pred::Concept { .. })
            {
                return Some(RetainedInsertBoundary::DirectNothingPromotion);
            }
            // Su/Pr trigger membership participates in literal ordering.  New
            // symbols have no old arena occurrences, but changing a bit for an
            // existing symbol would invalidate every cached max-head mask that
            // mentions it.
            for body in &clause.body {
                match *body {
                    Pred::Concept { iri, t }
                        if is_central(t)
                            && (iri as usize) < self.sig.concept_succ_trigger.len()
                            && !self.sig.concept_succ_trigger[iri as usize] =>
                    {
                        return Some(RetainedInsertBoundary::ExistingTriggerOrdering);
                    }
                    Pred::Role { iri, s, t }
                        if (iri as usize) < self.sig.role_names.len()
                            && ((is_central(s)
                                && !self.sig.forward_role_succ_trigger[iri as usize])
                                || (is_central(t)
                                    && !self.sig.backward_role_succ_trigger[iri as usize])) =>
                    {
                        return Some(RetainedInsertBoundary::ExistingTriggerOrdering);
                    }
                    _ => {}
                }
            }
        }
        let max_added_individual = input_max_individual(additions);
        if max_added_individual >= ind_id(self.nom_base) && !self.nom_table.borrow().is_empty() {
            return Some(RetainedInsertBoundary::AdditionalNominalCollision);
        }
        None
    }

    fn retained_edge_count(&self) -> usize {
        self.contexts.iter().map(|ctx| ctx.successors.len()).sum()
    }

    fn retained_clause_count(&self) -> usize {
        self.contexts.iter().map(|ctx| ctx.worked_off.len()).sum()
    }

    pub(crate) fn retained_state_counts(&self) -> RetainedInsertStats {
        let contexts = self.contexts.len();
        let clauses = self.retained_clause_count();
        let edges = self.retained_edge_count();
        RetainedInsertStats {
            contexts_before: contexts,
            context_clauses_before: clauses,
            edges_before: edges,
            contexts_after: contexts,
            context_clauses_after: clauses,
            edges_after: edges,
        }
    }

    /// Append clauses to a completed engine and resume its monotone saturation
    /// from the retained context graph.  The caller must first pass
    /// `retained_insert_boundary`; this method changes only schedule and
    /// enumeration, not the calculus rules:
    ///
    /// * new ontology facts enter every existing context;
    /// * every active worked-off side clause is replayed through Hyper against
    ///   the extended ontology indexes;
    /// * newly derived clauses follow the ordinary todo, equality, Succ, Pred,
    ///   Join, and message-fixpoint paths;
    /// * future contexts use freshly computed shared closures.
    ///
    /// Since additions cannot invalidate an old consequence and KM's
    /// saturation is monotone/confluent, the resumed fixpoint equals a fresh
    /// run over the union.  No calculus rule changes, so Lean re-certification
    /// is not required.
    pub(crate) fn insert_ontology_clauses_retained(
        &mut self,
        mut next_sig: Sig,
        additions: Vec<OntologyClause>,
    ) -> RetainedInsertStats {
        debug_assert!(self.retained_insert_boundary(&additions).is_none());
        debug_assert_eq!(
            &next_sig.concept_names[..self.sig.concept_names.len()],
            self.sig.concept_names.as_slice()
        );
        debug_assert_eq!(
            &next_sig.role_names[..self.sig.role_names.len()],
            self.sig.role_names.as_slice()
        );

        let mut stats = self.retained_state_counts();
        // Builder signature vectors contain symbol identity but not ontology
        // trigger analysis. Preserve the old prefix, then let push_clause add
        // the delta bits for newly introduced symbols/clauses.
        for i in 0..self.sig.concept_names.len() {
            next_sig.concept_succ_trigger[i] |= self.sig.concept_succ_trigger[i];
            next_sig.nothing[i] |= self.sig.nothing[i];
        }
        for i in 0..self.sig.role_names.len() {
            next_sig.forward_role_succ_trigger[i] |= self.sig.forward_role_succ_trigger[i];
            next_sig.backward_role_succ_trigger[i] |= self.sig.backward_role_succ_trigger[i];
        }
        next_sig.rsucc = self.sig.rsucc;
        // A retained insertion is the one writer of the otherwise immutable
        // ontology state.  Replacing/`make_mut`-ing the shared handles leaves
        // any other holder (a co-existing engine that shares this prepared
        // ontology) on its own unchanged copy.
        self.sig = Arc::new(next_sig);

        let first_new = self.ont.clauses.len();
        let max_added_individual = input_max_individual(&additions);
        let mut max_z = self.nom_k as i32 + 1;
        let mut see_z = |term: Term| {
            if is_neighbour(term) && term != Y {
                max_z = max_z.max((Y - term) as i32);
            }
        };
        for clause in &additions {
            for pred in &clause.body {
                match *pred {
                    Pred::Concept { t, .. } => see_z(t),
                    Pred::Role { s, t, .. } => {
                        see_z(s);
                        see_z(t);
                    }
                }
            }
            for literal in &clause.head {
                match *literal {
                    Lit::P(Pred::Concept { t, .. }) => see_z(t),
                    Lit::P(Pred::Role { s, t, .. }) => {
                        see_z(s);
                        see_z(t);
                    }
                    Lit::Eq { s, t } | Lit::Ineq { s, t } => {
                        see_z(s);
                        see_z(t);
                    }
                }
            }
        }
        self.nom_k = self.nom_k.max((max_z - 1).max(0) as usize);
        if max_added_individual >= ind_id(self.nom_base) {
            debug_assert!(self.nom_table.borrow().is_empty());
            self.nom_base = ind_term(max_added_individual + 1);
            self.nom_next.set(max_added_individual + 1);
        }
        for clause in additions {
            // Do not promote direct-bottom clauses into Sig::nothing here: see
            // Ontology::push_clause. Hyper replay derives the exact same bottom
            // consequences without invalidating retained ordering caches.
            let sig = Arc::make_mut(&mut self.sig);
            Arc::make_mut(&mut self.ont).push_clause(sig, clause, false);
        }
        Arc::make_mut(&mut self.ont).canonicalise_candidates();

        // Any cached context-independent closure reflects the old ontology.
        // Existing contexts are replayed below; future contexts recompute the
        // closure lazily from the extended indexes.
        self.shared_closure = None;
        self.shared_root_closure = None;
        self.nominal_enumerations =
            Arc::new(detect_nominal_enumerations(&self.sig, &self.ont.clauses));
        self.nominal_shortcuts.clear();

        let old_contexts = self.contexts.len();
        let new_facts: Vec<usize> = (first_new..self.ont.clauses.len())
            .filter(|&index| self.ont.clauses[index].body.is_empty())
            .collect();
        for id in 0..old_contexts {
            // The preflight excludes named-individual facts, whose historical
            // demand-seeding schedule requires a rebuild. Every remaining
            // empty-body x/function fact belongs to every context, exactly as
            // in ordinary `add_facts` initialisation.
            for &fact in &new_facts {
                self.seed_fact(id, fact);
            }

            // The active old side clauses were already worked off before the
            // new ontology clauses existed. Replaying only their Hyper role is
            // sufficient: all local Eq/Factor/Join/Pred relationships among old
            // context clauses already reached a fixpoint, while every new
            // resolvent enters the ordinary full saturation loop below.
            let root = self.contexts[id].root;
            let sides = self.contexts[id].worked_off.clone();
            for cid in sides {
                if !self.contexts[id].clause_keys.contains(&cid) {
                    continue;
                }
                let side = self.cc_arena[root as usize][cid as usize].clone();
                let maxima: Vec<Pred> = side.max_head_predicates().map(|(p, _)| p).collect();
                for max in maxima {
                    for result in self.hyper(id, &side, max, root) {
                        self.add_clause(id, result);
                    }
                }
            }
            self.saturate(id);
            self.propagate(id);
        }

        stats.contexts_after = self.contexts.len();
        stats.context_clauses_after = self.retained_clause_count();
        stats.edges_after = self.retained_edge_count();
        stats
    }

    /// Install the Direction-B per-core assumed-disjunct decisions (see
    /// `branch_decisions`). Called by the splitting driver before a branch run.
    pub fn set_branch_decisions(&mut self, d: HashMap<Vec<Pred>, Vec<Iri>>) {
        self.branch_decisions = d;
    }

    /// Find the arena id of a clause with this exact (body, head) content in
    /// the given ordering domain, if it was ever interned, and return the
    /// content hash alongside it. The arena is content-unique, so at most one
    /// id matches. A caller that will intern on a miss can hand the hash back
    /// to `intern_cc_known_new` instead of recomputing it, so a genuinely new
    /// clause is hashed once rather than three times.
    fn cc_lookup(&self, root: bool, c: &ContextClause) -> (u64, Option<u32>) {
        let d = root as usize;
        let h = content_hash(&(&c.body, &c.head));
        let found = self.cc_intern_idx[d].get(&h).and_then(|ids| {
            ids.iter().copied().find(|&i| {
                let a = &self.cc_arena[d][i as usize];
                a.body == c.body && a.head == c.head
            })
        });
        (h, found)
    }

    /// Intern a context clause the caller has already confirmed is absent from
    /// the arena (via `cc_lookup`), reusing the content hash `h` that lookup
    /// computed. Skips the redundant find + re-hash that a naive intern does.
    fn intern_cc_known_new(&mut self, root: bool, c: ContextClause, h: u64) -> u32 {
        let d = root as usize;
        let id = self.cc_arena[d].len() as u32;
        // `cc_sig` and `cc_facets` are flat mirrors of `cc_arena` and must grow
        // with it in lockstep; every subsumption scan indexes `cc_sig` by arena
        // id, and every head-index filing indexes `cc_facets` by arena id.
        self.cc_sig[d].push(ClauseSig::of(&c));
        self.cc_facets[d].push_clause(&c, &self.sig);
        self.cc_arena[d].push(c);
        self.cc_intern_idx[d].entry(h).or_default().push(id);
        id
    }

    /// Rebuild the `cc_sig` / `cc_facets` mirrors of `cc_arena[d]` from scratch.
    /// Tests that install a hand-built arena wholesale (rather than going
    /// through `intern_cc_known_new`) call this to restore the lockstep the
    /// engine otherwise maintains on every intern.
    #[cfg(test)]
    fn rebuild_cc_mirrors(&mut self, d: usize) {
        self.cc_sig[d] = self.cc_arena[d].iter().map(ClauseSig::of).collect();
        let mut facets = FacetTable::new();
        for c in &self.cc_arena[d] {
            facets.push_clause(c, &self.sig);
        }
        self.cc_facets[d] = facets;
    }

    /// Intern a back-substituted pred clause, returning its stable id.
    fn intern_pred(&mut self, pc: PredClause) -> u32 {
        let h = content_hash(&pc);
        if let Some(ids) = self.pred_intern_idx.get(&h) {
            for &i in ids {
                if self.pred_interned[i as usize] == pc {
                    return i;
                }
            }
        }
        let id = self.pred_interned.len() as u32;
        self.pred_interned.push(pc);
        self.pred_intern_idx.entry(h).or_default().push(id);
        id
    }

    fn get_or_create_context(&mut self, core: Vec<Pred>, root: bool, query: Option<Iri>) -> usize {
        let h = content_hash(&core);
        if let Some(ids) = self.core_index.get(&h) {
            for &cand in ids {
                if self.contexts[cand].core == core {
                    return cand;
                }
            }
        }
        let id = self.contexts.len();
        let ctx = Context::new(id, core, root, query);
        self.contexts.push(ctx);
        self.core_index.entry(h).or_default().push(id);
        // Root contexts share the root-ordering facts+TBox closure: seed it and
        // add only the core rule (the facts live in the closure).  The empty-core
        // top context is itself the closure, so seeding it is a no-op-equivalent
        // (it adds no core clause and derives nothing further).
        if root && std::env::var_os("KM_NO_SHARE").is_none() {
            self.ensure_shared_root_closure();
            let closure = self.shared_root_closure.as_ref().unwrap().clone();
            for c in closure {
                self.seed_worked_off(id, c);
            }
            self.add_core(id);
        } else {
            self.init_context(id);
        }
        // Direction B increment 2: seed the assumed-disjunct facts for this
        // core, if the splitting driver decided one here.
        if !self.branch_decisions.is_empty() {
            if let Some(ds) = self.branch_decisions.get(&self.contexts[id].core).cloned() {
                let root = self.contexts[id].root;
                for d in ds {
                    let c = ContextClause::new(
                        vec![],
                        vec![Lit::P(Pred::Concept { iri: d, t: X })],
                        root,
                        &self.sig,
                    );
                    self.add_clause(id, c);
                }
            }
        }
        id
    }

    /// Compute the root-ordering facts+TBox closure once (see
    /// `shared_root_closure`).  A throwaway empty-core root context is saturated
    /// from facts+TBox alone and its worked-off snapshotted, then discarded.
    fn ensure_shared_root_closure(&mut self) {
        if self.shared_root_closure.is_some() {
            return;
        }
        let id = self.contexts.len();
        let ctx = Context::new(id, vec![], true, None);
        self.contexts.push(ctx);
        self.init_context(id);
        self.saturate(id);
        let closure = self.contexts[id].worked_off.clone();
        debug_assert_eq!(id, self.contexts.len() - 1);
        self.contexts.pop();
        self.shared_root_closure = Some(closure);
    }

    /// Core rule + facts for a freshly created context, then schedule saturation.
    fn init_context(&mut self, id: usize) {
        self.add_core(id);
        self.add_facts(id);
    }

    /// Core rule for context `id`: the empty clause if a core predicate is
    /// owl:Nothing, else one `-> p` clause per core predicate.
    fn add_core(&mut self, id: usize) {
        let root = self.contexts[id].root;
        let core = self.contexts[id].core.clone();
        if core.iter().any(|p| self.sig.is_nothing_pred(p)) {
            let c = ContextClause::new(vec![], vec![], root, &self.sig);
            self.add_clause(id, c);
        } else {
            for p in core {
                let c = ContextClause::new(vec![], vec![Lit::P(p)], root, &self.sig);
                self.add_clause(id, c);
            }
        }
    }

    /// Ontology facts (empty-body clauses) seeded into context `id`.  These are
    /// part of every context-independent closure, so a context seeded from a
    /// shared closure must NOT also call this (the facts are already present).
    fn add_facts(&mut self, id: usize) {
        let facts: Vec<usize> = self.ont.facts.clone();
        for fi in facts {
            self.seed_fact(id, fi);
        }
    }

    /// Seed one ontology fact (empty-body clause `fi`) into context `id`.
    fn seed_fact(&mut self, id: usize, fi: usize) {
        let root = self.contexts[id].root;
        let head = self.ont.clauses[fi].head.clone();
        // apply identity (facts have no neighbour vars); filter invalid eqs / nothing
        let head = self.filter_head(head);
        if let Some(head) = head {
            let c = ContextClause::new(vec![], head, root, &self.sig);
            self.add_clause(id, c);
        }
    }

    /// The ground (nominal root) context `v_r`, created on first use: empty
    /// core, fully pre-seeded with every ground ontology fact, and the only
    /// context where Hyper grounds the central variable.
    fn ground_context(&mut self) -> usize {
        if let Some(id) = self.ground_ctx {
            return id;
        }
        let id = self.contexts.len();
        let ctx = Context::new(id, vec![], false, None);
        self.contexts.push(ctx);
        self.ground_ctx = Some(id);
        let inds: Vec<Term> = self.ont.ground_facts.keys().copied().collect();
        self.contexts[id].seeded_inds.extend(inds);
        self.init_context(id);
        let mut fis: Vec<usize> = self.ont.ground_facts.values().flatten().copied().collect();
        fis.sort_unstable();
        fis.dedup();
        for fi in fis {
            self.seed_fact(id, fi);
        }
        self.saturate(id);
        id
    }

    /// Complete enumeration-certified class queries from the saturated ground
    /// context. For `A ≡ {o1,…,on}` and any atomic class B,
    /// The governing equivalence is `O ⊨ A ⊑ B` iff `O ⊨ B(oi)` for every
    /// listed individual `oi`.
    ///
    /// The forward direction instantiates the subsumption at every nominal;
    /// the reverse direction follows because every A-element equals one of the
    /// listed individuals. This is the exact finite-enumeration specialization
    /// of Konclude's nominal-label reuse. The ground context is first taken to
    /// its full message fixpoint; if any resource backstop fired, no shortcut is
    /// published and ordinary CB remains responsible for the query.
    fn complete_nominal_enumeration_queries(&mut self, queries: &[Iri]) {
        // KM_ROOT_ORDERED: the enumeration shortcut reads ⊤ → B(o) units off
        // the ground context, and its completeness was validated under the
        // default (incomparable) regime only. Under the ordered regime an
        // entailed unit can be trapped in a residual disjunction, so the
        // shortcut readout is not certified there — fall back to ordinary CB
        // classification (complete via the refutation residue readout).
        if root_ordered_mode() != 0 {
            return;
        }
        if std::env::var_os("KM_NO_NOMINAL_LABEL_CACHE").is_some()
            || !queries
                .iter()
                .any(|q| self.nominal_enumerations.contains_key(q))
        {
            return;
        }
        self.run_msg_fixpoint_min();
        if self.incomplete() {
            return;
        }
        let Some(gid) = self.ground_ctx else {
            return;
        };
        let ground = &self.contexts[gid];
        let arena = &self.cc_arena[ground.root as usize];
        if ground.worked_off.iter().any(|&ci| {
            let c = &arena[ci as usize];
            c.body.is_empty() && c.head.is_empty()
        }) {
            // The ontology is already inconsistent. `inconsistent()` reports
            // that globally, so no per-class shortcut is needed.
            return;
        }

        let mut direct_types: HashMap<Term, BTreeSet<Iri>> = HashMap::new();
        let mut equal: HashMap<Term, Vec<Term>> = HashMap::new();
        for &ci in &ground.worked_off {
            let clause = &arena[ci as usize];
            if !clause.body.is_empty() || clause.head.len() != 1 {
                continue;
            }
            match clause.head[0] {
                Lit::P(Pred::Concept { iri, t })
                    if is_individual(t)
                        && !self.sig.is_internal(iri)
                        && !self.sig.is_nothing_concept(iri) =>
                {
                    direct_types.entry(t).or_default().insert(iri);
                }
                Lit::Eq { s, t } if is_individual(s) && is_individual(t) => {
                    equal.entry(s).or_default().push(t);
                    equal.entry(t).or_default().push(s);
                }
                _ => {}
            }
        }

        let types_for = |individual: Term| {
            let mut types = BTreeSet::new();
            let mut seen = HashSet::from([individual]);
            let mut todo = vec![individual];
            while let Some(o) = todo.pop() {
                if let Some(found) = direct_types.get(&o) {
                    types.extend(found.iter().copied());
                }
                if let Some(same) = equal.get(&o) {
                    for &other in same {
                        if seen.insert(other) {
                            todo.push(other);
                        }
                    }
                }
            }
            types
        };

        let mut completed = 0usize;
        for &query in queries {
            let Some(individuals) = self.nominal_enumerations.get(&query) else {
                continue;
            };
            let mut common: Option<BTreeSet<Iri>> = None;
            for &individual in individuals {
                let types = types_for(individual);
                common = Some(match common {
                    None => types,
                    Some(current) => current.intersection(&types).copied().collect(),
                });
            }
            // A certified enumeration is non-empty. The detector never emits an
            // empty individual list, but retain the guard so a malformed future
            // normal form falls back instead of asserting a vacuous answer.
            if let Some(common) = common {
                self.nominal_shortcuts.insert(query, common);
                completed += 1;
            }
        }
        if self.prof && completed != 0 {
            eprintln!(
                "KM_PROF nominal-label-cache completed_queries={completed} ground_clauses={}",
                ground.worked_off.len()
            );
        }
    }

    /// Filter a head literal vector: apply the Ineq rule (drop `t != t`),
    /// drop valid equations `t == t` (makes clause a tautology -> None), and
    /// drop owl:Nothing predicates.  Returns None if the clause is tautological.
    fn filter_head(&self, head: Vec<Lit>) -> Option<Vec<Lit>> {
        let mut out = Vec::new();
        for l in head {
            if l.is_valid_equation() {
                return None; // s == s in head -> tautology
            }
            if l.is_invalid_equation() {
                continue; // Ineq rule: drop t != t
            }
            if let Lit::P(p) = l {
                if self.sig.is_nothing_pred(&p) {
                    continue;
                }
            }
            out.push(l);
        }
        Some(out)
    }

    /// Redundancy-aware clause addition (Elim): skip if subsumed; remove clauses
    /// it subsumes; enqueue to todo. Returns true if added.
    fn add_clause(&mut self, id: usize, clause: ContextClause) -> bool {
        if !self.prof_time {
            return self.add_clause_inner(id, clause);
        }
        let t = std::time::Instant::now();
        let r = self.add_clause_inner(id, clause);
        prof_add(&ADDCLAUSE_NS, t);
        r
    }

    fn add_clause_inner(&mut self, id: usize, clause: ContextClause) -> bool {
        if clause.is_head_tautology() {
            return false;
        }
        let root = self.contexts[id].root;
        let d = root as usize;
        // Exact-duplicate check: the arena id is the canonical content key.
        // Reuse the hash lookup computes so a new clause is hashed only once.
        let prof_time = self.prof_time;
        let __t = prof_time.then(std::time::Instant::now);
        let (clause_hash, existing) = self.cc_lookup(root, &clause);
        if let Some(t) = __t {
            prof_add(&ADD_LOOKUP_NS, t);
        }
        if let Some(cid) = existing {
            if self.contexts[id].clause_keys.contains(&cid) {
                return false;
            }
        }
        let nb = clause.body.len();
        let ctx = &self.contexts[id];
        // Forward subsumption: skip if some existing clause subsumes `clause`.
        let __t = prof_time.then(std::time::Instant::now);
        let fwd = ctx.fwd_subsumed(&self.cc_arena[d], &self.cc_sig[d], &clause, None);
        if let Some(t) = __t {
            prof_add(&ADD_FWDSUB_NS, t);
        }
        if fwd {
            return false;
        }
        // Back-subsumption: drop existing clauses that `clause` strengthens.
        {
            let __t = prof_time.then(std::time::Instant::now);
            let arena = &self.cc_arena[d];
            let sigs = &self.cc_sig[d];
            let facets = &self.cc_facets[d];
            let ctx = &mut self.contexts[id];
            ctx.back_subsume(arena, sigs, facets, &clause);
            if let Some(t) = __t {
                prof_add(&ADD_BACKSUB_NS, t);
            }
        }
        // Demand-driven ground-fact seeding (nominal mode): the first clause
        // mentioning an individual brings that individual's ground ontology
        // facts into this context (they are Hyper/Eq providers here). The
        // ground context is fully pre-seeded at creation.
        let mut new_inds: Vec<Term> = Vec::new();
        if !self.ont.ground_facts.is_empty() {
            let mut inds: Vec<Term> = Vec::new();
            for p in &clause.body {
                pred_inds(p, &mut inds);
            }
            for l in &clause.head {
                lit_inds(l, &mut inds);
            }
            let ctx = &mut self.contexts[id];
            for o in inds {
                if ctx.seeded_inds.insert(o) {
                    new_inds.push(o);
                }
            }
        }
        let __t = prof_time.then(std::time::Instant::now);
        let cid = match existing {
            Some(c) => c,
            None => self.intern_cc_known_new(root, clause, clause_hash),
        };
        let ctx = &mut self.contexts[id];
        ctx.clause_keys.insert(cid);
        ctx.index_active_clause(&self.cc_arena[d], cid);
        if let Some(t) = __t {
            prof_add(&ADD_INDEX_NS, t);
        }
        // KM_TODO_UNITS_FIRST: prioritise empty-body (fact) clauses so the strong
        // subsumers are worked off first and prune the rest earlier. Pure work-off
        // ordering — saturation is confluent, so the fixpoint/output is unchanged.
        if self.todo_units_first && nb == 0 {
            ctx.todo.push_front(cid);
        } else {
            ctx.todo.push_back(cid);
        }
        for o in new_inds {
            if let Some(fis) = self.ont.ground_facts.get(&o) {
                for fi in fis.clone() {
                    self.seed_fact(id, fi);
                }
            }
        }
        true
    }

    /// Saturate a single context (apply Hyper/Pred/Eq until todo is empty).
    fn saturate(&mut self, id: usize) {
        if !self.prof_time {
            return self.saturate_inner(id);
        }
        let t = std::time::Instant::now();
        self.saturate_inner(id);
        prof_add(&SATURATE_NS, t);
    }

    fn saturate_inner(&mut self, id: usize) {
        self.stat_saturate += 1;
        let trace_sat = self.trace_sat;
        let prof = self.prof;
        let (
            mut iters,
            mut subsumed,
            mut nhyper,
            mut npred,
            mut neqp,
            mut neqe,
            mut nfact,
            mut nadded,
        ) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
        let d = self.contexts[id].root as usize;
        loop {
            let cid = match self.contexts[id].todo.pop_front() {
                Some(c) => c,
                None => break,
            };
            // Transient working copy (the arena entry is shared across contexts
            // and rule code needs it while `self` is mutated).
            let clause = self.cc_arena[d][cid as usize].clone();
            if prof {
                iters += 1;
                if iters % 200_000 == 0 {
                    let ctx = &self.contexts[id];
                    eprintln!(
                        "KM_PROF ctx={} iters={} subsumed_at_workoff={} added={} todo={} wo={} | hyper_out={} pred_out={} eq_pred_out={} eq_eqn_out={} factor_out={} | backsub_unindex_events={} reindex_avoided={}",
                        id, iters, subsumed, nadded, ctx.todo.len(), ctx.worked_off.len(),
                        nhyper, npred, neqp, neqe, nfact,
                        BACKSUB_UNINDEX_EVENTS.with(|c| c.get()),
                        BACKSUB_REINDEX_AVOIDED.with(|c| c.get())
                    );
                    if self.prof_time {
                        let ms = |cell: &'static std::thread::LocalKey<std::cell::Cell<u64>>| {
                            cell.with(|value| value.get()) as f64 / 1e6
                        };
                        eprintln!(
                            "KM_PROF[time-ms] subsume={:.1} hyper={:.1} pred_local={:.1} add_clause={:.1}",
                            ms(&SUBSUME_NS),
                            ms(&HYPER_NS),
                            ms(&PREDLOCAL_NS),
                            ms(&ADDCLAUSE_NS),
                        );
                    }
                }
            }
            // Re-check forward subsumption at work-off time: a clause that was
            // not subsumed when enqueued may since have been subsumed by a
            // newly added strengthening.  Skipping it here -- before it fires
            // its rules -- prevents a
            // redundant clause from spawning a cascade of further redundant
            // consequences.  Sound (a subsumed clause is entailed by its
            // subsumer, so dropping it preserves completeness).
            {
                let ctx = &self.contexts[id];
                let __t_sub = self.prof_time.then(std::time::Instant::now);
                let is_sub =
                    ctx.fwd_subsumed(&self.cc_arena[d], &self.cc_sig[d], &clause, Some(cid));
                if let Some(t) = __t_sub {
                    prof_add(&SUBSUME_NS, t);
                }
                if is_sub {
                    let ctx = &mut self.contexts[id];
                    ctx.unindex_active_clause(&self.cc_arena[d], cid);
                    ctx.clause_keys.remove(&cid);
                    if prof {
                        subsumed += 1;
                    }
                    continue;
                }
            }
            let root = self.contexts[id].root;
            // Fire rules per maximal head literal.
            let max_head: Vec<Lit> = clause.max_head().collect();
            for max in &max_head {
                match max {
                    Lit::P(p) => {
                        // Hyper fires on every maximal head predicate; the
                        // candidate ontology clauses are those with a body atom
                        // (central or neighbour) that can unify with `p`.
                        let results = self.hyper(id, &clause, *p, root);
                        if prof {
                            nhyper += results.len() as u64;
                        }
                        for r in results {
                            if self.add_clause(id, r) && prof {
                                nadded += 1;
                            }
                        }
                        if is_function(p.max_term()) {
                            let results = self.pred_local(id, &clause, *p, root);
                            if prof {
                                npred += results.len() as u64;
                            }
                            for r in results {
                                if self.add_clause(id, r) && prof {
                                    nadded += 1;
                                }
                            }
                            if self.equality {
                                let __t = self.prof_time.then(std::time::Instant::now);
                                let results = self.eq_from_pred(id, &clause, *max, root);
                                if let Some(t) = __t {
                                    prof_add(&EQRULE_NS, t);
                                }
                                if prof {
                                    neqp += results.len() as u64;
                                }
                                for r in results {
                                    if self.add_clause(id, r) && prof {
                                        nadded += 1;
                                    }
                                }
                            }
                        } else if p.is_ground() {
                            // Join via the Pred pipeline (nominal calculus): a
                            // ground maximal head atom resolves the verbatim-
                            // copied ground body atoms (C_i) of neighbour pred
                            // clauses, which the function-term refire above
                            // never revisits.
                            let results = self.pred_local(id, &clause, *p, root);
                            if prof {
                                npred += results.len() as u64;
                            }
                            for r in results {
                                if self.add_clause(id, r) && prof {
                                    nadded += 1;
                                }
                            }
                            if self.equality {
                                let __t = self.prof_time.then(std::time::Instant::now);
                                let results = self.eq_from_pred(id, &clause, *max, root);
                                if let Some(t) = __t {
                                    prof_add(&EQRULE_NS, t);
                                }
                                if prof {
                                    neqp += results.len() as u64;
                                }
                                for r in results {
                                    if self.add_clause(id, r) && prof {
                                        nadded += 1;
                                    }
                                }
                            }
                        }
                    }
                    Lit::Eq { .. } if self.equality => {
                        // This equality is the paramodulation source: rewrite
                        // matching literals of worked-off clauses.
                        let __t = self.prof_time.then(std::time::Instant::now);
                        let results = self.eq_from_equation(id, &clause, *max, root);
                        if let Some(t) = __t {
                            prof_add(&EQRULE_NS, t);
                        }
                        if prof {
                            neqe += results.len() as u64;
                        }
                        for r in results {
                            if self.add_clause(id, r) && prof {
                                nadded += 1;
                            }
                        }
                    }
                    Lit::Ineq { .. } if self.equality => {
                        // This inequality is a paramodulation target: rewrite it
                        // with worked-off equalities (the reverse direction, so
                        // the equality/inequality clash is found regardless of
                        // derivation order).
                        let __t = self.prof_time.then(std::time::Instant::now);
                        let results = self.eq_from_pred(id, &clause, *max, root);
                        if let Some(t) = __t {
                            prof_add(&EQRULE_NS, t);
                        }
                        if prof {
                            neqp += results.len() as u64;
                        }
                        for r in results {
                            if self.add_clause(id, r) && prof {
                                nadded += 1;
                            }
                        }
                    }
                    _ => {}
                }
            }
            // Factor rule: applies to clauses with two head equalities sharing a side.
            if self.equality
                && clause
                    .head
                    .iter()
                    .filter(|l| matches!(l, Lit::Eq { .. }))
                    .count()
                    >= 2
            {
                let __t = self.prof_time.then(std::time::Instant::now);
                let results = self.factor(&clause, root);
                if let Some(t) = __t {
                    prof_add(&EQRULE_NS, t);
                }
                if prof {
                    nfact += results.len() as u64;
                }
                for r in results {
                    if self.add_clause(id, r) && prof {
                        nadded += 1;
                    }
                }
            }
            // Join rule (nominal calculus): in-context resolution on ground
            // atoms; no-op (empty indexes) without individuals.
            {
                let results = self.join(id, &clause, root);
                for r in results {
                    if self.add_clause(id, r) && prof {
                        nadded += 1;
                    }
                }
            }
            // Feed the semi-naive propagation pools (append-only).  Pred-eligible:
            // function-free head of predicates plus (nominal mode) the Pr
            // equality forms `x ≈ o` / `y ≈ o` / `o ≈ o'` (canonical
            // `Eq{o, ·}` — individuals sit above x and y in the term order);
            // other equalities stay local, as before.  Succ-eligible: some
            // maximal head predicate is on a function term (succ-trigger
            // candidate) or is an Su^r ground form (r-Succ candidate).
            // r-Succ: a maximal head CENTRAL reachability fact `__trans/__chain(x)`
            // is forwarded to successors as a neighbour fact (see `rsucc_pool`).
            // All three tests are pure functions of the interned clause (and of
            // `sig.rsucc` / `sig.is_reach`, both stable per clause), so they are
            // read off the shared `FacetTable` rather than re-derived for each
            // context that works this clause off.
            let ClauseFlags {
                sat_pred: pred_eligible,
                sat_succ: succ_eligible,
                sat_rsucc: rsucc_eligible,
                ..
            } = self.cc_facets[d].flags_of(cid);
            {
                let facets = &self.cc_facets[d];
                let ctx = &mut self.contexts[id];
                if pred_eligible {
                    ctx.pred_pool.push(cid);
                }
                if succ_eligible {
                    ctx.succ_pool.push(cid);
                }
                if rsucc_eligible {
                    ctx.rsucc_pool.push(cid);
                }
                ctx.worked_off.push(cid);
                ctx.index_clause(facets, cid);
                ctx.dirty = true;
            }
            // KM_EARLY_UNSAT: the empty clause (⊥) subsumes every other clause, so
            // once it is worked off the remaining todo is redundant. It is already
            // pred-eligible (empty head), so propagate still pushes the
            // contradiction back. Sound: dropping subsumed clauses preserves
            // completeness; the unsat verdict / pushback is retained.
            if self.early_unsat && clause.body.is_empty() && clause.head.is_empty() {
                self.contexts[id].todo.clear();
                break;
            }
            if trace_sat {
                let c = &self.contexts[id];
                let arena = &self.cc_arena[d];
                let wl = c.worked_off.len();
                if wl % 10000 == 0 {
                    let maxb = c
                        .worked_off
                        .iter()
                        .map(|&ci| arena[ci as usize].body.len())
                        .max()
                        .unwrap_or(0);
                    let maxh = c
                        .worked_off
                        .iter()
                        .map(|&ci| arena[ci as usize].head.len())
                        .max()
                        .unwrap_or(0);
                    let nctx = self.contexts.len();
                    eprintln!(
                        "KM_SAT ctx={} root={} core_len={} todo={} wo={} max_body={} max_head={} ncontexts={} hyper={}",
                        id, c.root, c.core.len(), c.todo.len(), wl,
                        maxb, maxh, nctx, HYPER_CALLS.with(|x| x.get())
                    );
                }
            }
        }
    }

    /// Hyper rule.  `side` is the just-popped clause; `max` one of its maximal
    /// head predicates.
    fn hyper(&self, id: usize, side: &ContextClause, max: Pred, root: bool) -> Vec<ContextClause> {
        if !self.prof_time {
            return self.hyper_inner(id, side, max, root);
        }
        let t = std::time::Instant::now();
        let r = self.hyper_inner(id, side, max, root);
        prof_add(&HYPER_NS, t);
        r
    }

    fn hyper_inner(
        &self,
        id: usize,
        side: &ContextClause,
        max: Pred,
        root: bool,
    ) -> Vec<ContextClause> {
        HYPER_CALLS.with(|c| c.set(c.get() + 1));
        let mut out = Vec::new();
        let ctx = &self.contexts[id];
        let arena = &self.cc_arena[root as usize];
        let role_candidates;
        let ontology_candidates: &[usize] = if let Pred::Role { iri, s, t } = max {
            role_candidates = {
                let mut candidates = self.ont.clauses_cand(&max).to_vec();
                // A guarded `C(y) ∧ R(x,y)` clause can unify with this side
                // only when the central source x has an admissible image. Its
                // second premise must be a maximal C(t) predicate already in
                // the context (plus the current side in the nominal ground
                // context, matching the existing S_v ∪ {C} semantics).
                if is_central(s) || is_individual(s) {
                    let mut concepts = Vec::new();
                    if let Some(posting) = ctx.max_head_term_index.get(&t) {
                        for &cid in posting {
                            for (predicate, _) in arena[cid as usize].max_head_predicates() {
                                if let Pred::Concept {
                                    iri: concept,
                                    t: concept_term,
                                } = predicate
                                {
                                    if concept_term == t {
                                        concepts.push(concept);
                                    }
                                }
                            }
                        }
                    }
                    if self.ground_ctx == Some(id) {
                        for (predicate, _) in side.max_head_predicates() {
                            if let Pred::Concept {
                                iri: concept,
                                t: concept_term,
                            } = predicate
                            {
                                if concept_term == t {
                                    concepts.push(concept);
                                }
                            }
                        }
                    }
                    concepts.sort_unstable();
                    concepts.dedup();
                    if let Some(guarded) = self.ont.role_target_concept_body.get(&iri) {
                        for concept in concepts {
                            let start = guarded.partition_point(|&(c, _)| c < concept);
                            let end = guarded.partition_point(|&(c, _)| c <= concept);
                            candidates.extend(guarded[start..end].iter().map(|&(_, oci)| oci));
                        }
                    }
                }
                candidates.sort_unstable();
                candidates.dedup();
                candidates
            };
            &role_candidates
        } else {
            self.ont.clauses_cand(&max)
        };
        // Read the narrowing state once per Hyper call, not per candidate
        // clause (a thread-local probe in the hottest loop of saturation).
        let narrow = hyper_narrow();
        for &oci in ontology_candidates {
            let oc = &self.ont.clauses[oci];
            let n = oc.body.len();
            // pick the first body position that can unify with `max` for the side condition
            let side_pos = match (0..n).find(|&i| can_unify(&oc.body[i], &max)) {
                Some(p) => p,
                None => continue,
            };
            // Pin the triggering maximal predicate as Sequoia's side
            // condition before looking up the other body atoms. Saturation
            // invokes Hyper once for every maximal predicate, so allowing all
            // of the side clause's other maxima here only re-enumerates the
            // same resolvents. The early binding also enables exact and
            // one-endpoint postings in the nominal ground context.
            let mut sigma = CentralSubst::new(self.ground_ctx == Some(id));
            if !unify(&mut sigma, &oc.body[side_pos], &max) {
                continue;
            }
            // candidate (matched max-head-predicate) lists per body position
            let mut candidates: Vec<Vec<(usize, Pred)>> = Vec::with_capacity(n);
            let mut ok = true;
            for i in 0..n {
                if i == side_pos {
                    candidates.push(vec![(usize::MAX, max)]);
                } else {
                    let mut v = Vec::new();
                    let wanted = oc.body[i].apply(&|term| sigma.apply(term));
                    let (cand, exact) = match (oc.body[i], wanted) {
                        (Pred::Concept { t, .. }, wanted) if hyper_term_determined(t, &sigma) => {
                            (ctx.max_head_pred_index.get(&wanted), true)
                        }
                        (
                            Pred::Role { s, t, .. },
                            wanted @ Pred::Role {
                                iri,
                                s: wanted_s,
                                t: wanted_t,
                            },
                        ) => {
                            let source_fixed = hyper_term_determined(s, &sigma);
                            let target_fixed = hyper_term_determined(t, &sigma);
                            if source_fixed && target_fixed {
                                (ctx.max_head_pred_index.get(&wanted), true)
                            } else if source_fixed && (is_individual(wanted_s) || is_comp(wanted_s))
                            {
                                (ctx.ground_role_source_index.get(&(iri, wanted_s)), false)
                            } else if target_fixed && (is_individual(wanted_t) || is_comp(wanted_t))
                            {
                                (ctx.ground_role_target_index.get(&(iri, wanted_t)), false)
                            } else {
                                (ctx.head_role_index.get(&iri), false)
                            }
                        }
                        (Pred::Concept { iri, .. }, _) => (ctx.head_concept_index.get(&iri), false),
                        (Pred::Role { iri, .. }, _) => (ctx.head_role_index.get(&iri), false),
                    };
                    if let Some(cand) = cand {
                        for &ci in cand {
                            if exact {
                                v.push((ci as usize, wanted));
                            } else {
                                for (p, _) in arena[ci as usize].max_head_predicates() {
                                    // Probe compatibility with the side binding
                                    // via the append-only trail rather than a
                                    // clone: `add` only appends, so rolling back
                                    // to `mark` leaves `sigma` in its exact
                                    // pre-probe (side-bound) state for the next
                                    // candidate.
                                    let mark = sigma.mark();
                                    if unify(&mut sigma, &oc.body[i], &p) {
                                        v.push((ci as usize, p));
                                    }
                                    sigma.rollback(mark);
                                }
                            }
                        }
                    }
                    // Ground context: the side clause is also a candidate at
                    // non-side positions (given-clause semantics, S_v ∪ {C}).
                    // Elsewhere this self-pairing is provably redundant — two
                    // distinct max heads yield a resolvent the side clause
                    // subsumes, the same head twice instantiates a head
                    // equality to a tautology — but in the ground context the
                    // same-head pair `S(o,y), S(o,y)` instantiates `z_i ≈ z_j`
                    // to `y ≈ y`, the Nom-rule trigger, which must fire.
                    if self.ground_ctx == Some(id) {
                        for (p, _) in side.max_head_predicates() {
                            let mark = sigma.mark();
                            if unify(&mut sigma, &oc.body[i], &p) {
                                v.push((usize::MAX, p));
                            }
                            sigma.rollback(mark);
                        }
                    }
                    if v.is_empty() {
                        ok = false;
                        break;
                    }
                    candidates.push(v);
                }
            }
            if !ok {
                continue;
            }
            let widths: SmallVec<[usize; 8]> = candidates.iter().map(Vec::len).collect();
            let product = widths
                .iter()
                .fold(1u128, |acc, &width| acc.saturating_mul(width as u128));
            // Exact semijoin reduction of the independently built postings (see
            // the module block above `reduce_hyper_candidates`).  Gated on the
            // raw product only as a cost heuristic: the narrowed lists are
            // subsequences of the raw ones and every dropped candidate is in no
            // unifiable combination, so running or skipping this changes
            // nothing about what the join emits.
            if narrow
                && n >= 2
                && product >= HYPER_REDUCE_MIN_PRODUCT
                && !reduce_hyper_candidates(oc, &mut candidates, &sigma)
            {
                continue;
            }
            if let Some(threshold) = hyper_product_trace_threshold() {
                if product >= threshold {
                    let narrowed_widths: SmallVec<[usize; 8]> =
                        candidates.iter().map(Vec::len).collect();
                    let narrowed_product = narrowed_widths
                        .iter()
                        .fold(1u128, |acc, &width| acc.saturating_mul(width as u128));
                    eprintln!(
                        "KM_HYPER_PRODUCT ctx={} oci={} max={:?} side=({},{}) \
                         widths={:?} product={} narrowed_widths={:?} narrowed_product={} \
                         body={:?} head={:?}",
                        id,
                        oci,
                        max,
                        side.body.len(),
                        side.head.len(),
                        widths,
                        product,
                        narrowed_widths,
                        narrowed_product,
                        oc.body,
                        oc.head,
                    );
                }
            }
            // Enumerate the unifiable combinations by a backtracking *join* rather
            // than the full cartesian product: extend the central substitution one
            // body position at a time, and at each position only descend into the
            // candidates whose match is consistent with the bindings already made
            // (shared neighbour variables, e.g. `y` in `R(x,y) ∧ C(y)`).  This
            // yields exactly the same set of resolvents as iterating the product
            // and filtering by `unify` -- the failed combinations were precisely
            // those skipped here -- but never materialises the doomed branches,
            // which on number restrictions (`R(x,y1) ∧ C(y1) ∧ R(x,y2) ∧ C(y2)`)
            // is the difference between `(#successors)^k` and the number of
            // genuinely unifiable tuples.  Positions are visited fewest-candidates
            // first so the most constraining atoms bind earliest.
            //
            // The order is keyed on the RAW widths, deliberately not on the
            // narrowed ones: with the position order fixed and every narrowed
            // list a subsequence of its raw list, the join descends through the
            // identical leaves in the identical sequence as the generic join,
            // so `out` is emitted element-for-element the same.  (Re-keying on
            // the narrowed widths would only permute a join whose branching is
            // already down to the genuine witnesses.)
            let mut order: Vec<usize> = (0..n).collect();
            order.sort_by_key(|&i| widths[i]);
            let mut chosen = vec![0usize; n];
            let mut determined = DeterminedIndex::new(narrow);
            // side-position variables are exempt from symmetric-group pruning
            let exempt: Vec<Term> = if oc.sym_groups.is_empty() {
                Vec::new()
            } else {
                match oc.body[side_pos] {
                    Pred::Concept { t, .. } => vec![t],
                    Pred::Role { s, t, .. } => vec![s, t],
                }
            };
            self.hyper_join(
                id,
                side,
                oc,
                &candidates,
                &order,
                0,
                &mut sigma,
                &exempt,
                &mut chosen,
                root,
                &mut determined,
                &mut out,
            );
        }
        out
    }

    /// Recursive backtracking enumeration helper for `hyper` (see its comment).
    /// `order[depth]` is the body position bound at this level; `chosen[pos]` is
    /// the index into `candidates[pos]` selected for the resolvent build.
    #[allow(clippy::too_many_arguments)]
    fn hyper_join(
        &self,
        id: usize,
        side: &ContextClause,
        oc: &OntologyClause,
        candidates: &[Vec<(usize, Pred)>],
        order: &[usize],
        depth: usize,
        sigma: &mut CentralSubst,
        exempt: &[Term],
        chosen: &mut Vec<usize>,
        root: bool,
        determined: &mut DeterminedIndex,
        out: &mut Vec<ContextClause>,
    ) {
        if depth == order.len() {
            if let Some(c) =
                self.build_hyper_resolvent(id, side, oc, sigma, candidates, chosen, root)
            {
                out.push(c);
            }
            return;
        }
        let pos = order[depth];
        // Fast path: the premises bound so far already determine every term of
        // this body atom, so `unify` can succeed only on the one instantiated
        // predicate and binds nothing new.  Look those candidates up instead of
        // rescanning (and re-unifying) the whole posting — the difference
        // between O(posting) and O(matches) per visit of this level, which on
        // the cardinality shape is paid once per partial filler assignment.
        //
        // Exactly the candidates the generic scan accepts, in the same order
        // (`DeterminedIndex::hits` keeps candidate-list order), and the shared
        // substitution is extended by the same single `unify` call — done once
        // here because every hit carries the identical predicate — so both the
        // resolvents and their sequence are unchanged.
        if determined.enabled {
            if let Some(wanted) = hyper_determined_instance(&oc.body[pos], sigma) {
                let mut hits: SmallVec<[u32; 4]> = SmallVec::new();
                determined.hits(pos, candidates, &wanted, &mut hits);
                if hits.is_empty() {
                    return;
                }
                let mark = sigma.mark();
                if unify(sigma, &oc.body[pos], &wanted)
                    && (oc.sym_groups.is_empty() || sym_groups_ok(oc, exempt, sigma))
                {
                    for &j in &hits {
                        chosen[pos] = j as usize;
                        self.hyper_join(
                            id,
                            side,
                            oc,
                            candidates,
                            order,
                            depth + 1,
                            sigma,
                            exempt,
                            chosen,
                            root,
                            determined,
                            out,
                        );
                    }
                }
                sigma.rollback(mark);
                return;
            }
        }
        for (j, &(_ci, p)) in candidates[pos].iter().enumerate() {
            // Extend the shared substitution in place and undo it on backtrack
            // via the append-only trail, instead of cloning `sigma` per
            // candidate.  `mark`/`rollback` restore the exact prior bindings, so
            // the resolvent built at every leaf — and their enumeration order —
            // is identical to the clone-per-candidate join.
            let mark = sigma.mark();
            if unify(sigma, &oc.body[pos], &p)
                && (oc.sym_groups.is_empty() || sym_groups_ok(oc, exempt, sigma))
            {
                chosen[pos] = j;
                self.hyper_join(
                    id,
                    side,
                    oc,
                    candidates,
                    order,
                    depth + 1,
                    sigma,
                    exempt,
                    chosen,
                    root,
                    determined,
                    out,
                );
            }
            sigma.rollback(mark);
        }
    }

    /// The additional nominal `o'_{ρ·S^k}` for parent individual `o` (label ρ),
    /// role `S`, edge orientation `fwd` (`S(o,y)` vs `S(y,o)`), and index `k`
    /// (Nom rule).  Interned: re-firing Nom with the same parameters reuses the
    /// same individual.  `None` when the budget (or the individual id range) is
    /// exhausted — reported once, never silent.
    fn nom_term(&self, o: Term, role: Iri, fwd: bool, k: u16) -> Option<Term> {
        let key = (o, role, fwd, k);
        if let Some(&t) = self.nom_table.borrow().get(&key) {
            return Some(t);
        }
        let next = self.nom_next.get();
        if self.nom_table.borrow().len() >= self.nom_budget || next >= (FTERM_BASE - X) as i32 {
            if !self.nom_truncated.replace(true) {
                eprintln!(
                    "WARNING: kobayashi-marust additional-nominal budget ({}) exhausted; \
                     further Nom conclusions dropped — classification may be incomplete.",
                    self.nom_budget
                );
            }
            return None;
        }
        self.nom_next.set(next + 1);
        let t = ind_term(next);
        self.nom_table.borrow_mut().insert(key, t);
        Some(t)
    }

    #[allow(clippy::too_many_arguments)]
    fn build_hyper_resolvent(
        &self,
        id: usize,
        side: &ContextClause,
        oc: &OntologyClause,
        sigma: &CentralSubst,
        candidates: &[Vec<(usize, Pred)>],
        idxs: &[usize],
        root: bool,
    ) -> Option<ContextClause> {
        // Nom rule (arXiv:1805.01396 Table 3): in the ground context with
        // σ(x) = o, head a-equalities instantiating to `y ≈ y` or `y ≈ f(o')`
        // constrain the *unnamed predecessors* of o (the premise clauses come
        // from different r-Succ senders).  Dropping `y ≈ y` as a tautology —
        // the pre-nominal behaviour — loses exactly that constraint; instead
        // the whole group is replaced by `⋁_{k=1}^K y ≈ o'_{ρ·S^k}` over fresh
        // additional nominals, where S is the role of a matched `S(o,y)` /
        // `S(y,o)` premise atom.  Only fires when nominals, inverse roles and
        // number restrictions interact; inert otherwise.
        let ground_o = if self.ground_ctx == Some(id) {
            sigma.get(X).filter(|t| is_individual(*t))
        } else {
            None
        };
        let subst = |t: Term| sigma.apply(t);
        // head: ontology head substituted, filtered
        let mut head: Vec<Lit> = Vec::new();
        let mut nom_pending = false;
        // Distinct `f(o')` right-hand terms among the replaced `y ≈ f(o')`
        // literals (K''): an anonymous predecessor may be pinned to any of
        // those values, and each needs its own additional nominal to cover
        // it.  The Table-3 statement uses K disjuncts and its soundness proof
        // K' = max(K, K''); the bound with a direct pigeonhole proof (any
        // n_y distinct candidates outside the pinned values violate the
        // counting clause, so |candidates| ≤ (n_y − 1) + K'' ≤ K + K'') is
        // the SUM, which is what the Lean certification proves — so the
        // engine emits K + K'' disjuncts (weaker conclusions are sound).
        let mut nom_rhs: Vec<Term> = Vec::new();
        for l in &oc.head {
            let ls = l.apply(&subst);
            if ground_o.is_some() {
                if let Lit::Eq { s, t } = ls {
                    if (s == Y && t == Y) || (is_comp(s) && t == Y) {
                        nom_pending = true;
                        if is_comp(s) && !nom_rhs.contains(&s) {
                            nom_rhs.push(s);
                        }
                        continue;
                    }
                }
            }
            if ls.is_valid_equation() {
                return None;
            }
            if ls.is_invalid_equation() {
                continue;
            }
            if let Lit::P(p) = ls {
                if self.sig.is_nothing_pred(&p) {
                    continue;
                }
            }
            head.push(ls);
        }
        if nom_pending {
            let o = ground_o.unwrap();
            let k_eff = self.nom_k + nom_rhs.len();
            // The matched premise atom S(o,y) / S(y,o) supplies the role label.
            let mut labelled = false;
            'outer: for i in 0..candidates.len() {
                let (_, matched) = candidates[i][idxs[i]];
                if let Pred::Role { iri, s, t } = matched {
                    let fwd = s == o && t == Y;
                    let bwd = t == o && s == Y;
                    if fwd || bwd {
                        for k in 1..=k_eff as u16 {
                            head.push(Lit::eq(Y, self.nom_term(o, iri, fwd, k)?));
                        }
                        labelled = true;
                        break 'outer;
                    }
                }
            }
            if !labelled {
                // No connecting role premise: the y-equality cannot be
                // expressed against additional nominals; the conclusion
                // degenerates to the pre-nominal tautology drop.
                return None;
            }
        }
        // plus each candidate clause's head minus the matched predicate
        let arena = &self.cc_arena[root as usize];
        // Direction B unit-propagation mode (`branch_ordered`): suppress a
        // resolvent that combines TWO OR MORE derived disjunctions (premise
        // clauses with a multi-literal head). That fact×fact resolution is the
        // multiplication that blows up the per-branch closure. With exhaustive
        // splitting the missing consequence is recovered by splitting one of the
        // disjunctive premises — it becomes a unit, then resolves normally — so
        // suppressing it keeps the closure tame without losing completeness on
        // the split-recovered fragment (validated by A/B vs the default engine).
        // The ontology rule head is NOT counted: a single rule application
        // introducing a fresh disjunction is bounded; only derived×derived blows
        // up. Inert when `branch_ordered` is false (the default/fallback engine).
        if branch_ordered() {
            let mut disj_premises = 0usize;
            for i in 0..candidates.len() {
                let (ci, _) = candidates[i][idxs[i]];
                let clause = if ci == usize::MAX { side } else { &arena[ci] };
                if clause.head.len() > 1 {
                    disj_premises += 1;
                    if disj_premises >= 2 {
                        return None;
                    }
                }
            }
        }
        let mut body: Vec<Pred> = Vec::new();
        for i in 0..candidates.len() {
            let (ci, matched) = candidates[i][idxs[i]];
            let clause = if ci == usize::MAX { side } else { &arena[ci] };
            for l in &clause.head {
                if *l != Lit::P(matched) {
                    head.push(*l);
                }
            }
            body.extend_from_slice(&clause.body);
        }
        Some(ContextClause::new(body, head, root, &self.sig))
    }

    /// Local Pred rule: resolve pred clauses (pushed from successors) whose body
    /// predicates are maximal in the head of clauses with the function term.
    /// Here `max` is a head predicate of `side` containing a function term; we
    /// resolve any neighbour pred clause whose body contains `max`.
    fn pred_local(
        &self,
        id: usize,
        side: &ContextClause,
        max: Pred,
        root: bool,
    ) -> Vec<ContextClause> {
        if !self.prof_time {
            return self.pred_local_inner(id, side, max, root);
        }
        let t = std::time::Instant::now();
        let r = self.pred_local_inner(id, side, max, root);
        prof_add(&PREDLOCAL_NS, t);
        r
    }

    fn pred_local_inner(
        &self,
        id: usize,
        side: &ContextClause,
        max: Pred,
        root: bool,
    ) -> Vec<ContextClause> {
        let mut out = PredResultBuffer::default();
        let ctx = &self.contexts[id];
        let arena = &self.cc_arena[root as usize];
        let relevant = match ctx.neighbor_pred_body_index.get(&max) {
            Some(relevant) => relevant.as_slice(),
            None => return out.into_vec(),
        };
        for &pid in relevant {
            let pc = &self.pred_interned[pid as usize];
            // For each nonground body predicate, candidate clauses with that
            // predicate maximal in head; `max` is provided by `side`. Ground
            // body atoms (nominal mode) are copied to the resolvent body.
            let mut ground: Vec<Pred> = Vec::new();
            let mut candidates: Vec<Vec<(usize, Pred)>> = Vec::with_capacity(pc.body.len());
            let mut ok = true;
            for &bp in &pc.body {
                // Sequoia Context.PredRule pins the occurrence equal to the
                // currently processed maximal predicate to `sideConditionToUse`.
                // Older providers for the same predicate fired when they were
                // worked off; a Pred clause arriving later is handled by
                // `pred_from_neighbor` against the complete worked-off index.
                // Including them here only repeats prior Cartesian products.
                if bp == max {
                    candidates.push(vec![(usize::MAX, bp)]);
                    continue;
                }
                let mut v = Vec::new();
                if let Some(cand) = ctx.max_head_pred_index.get(&bp) {
                    v.extend(cand.iter().map(|&ci| (ci as usize, bp)));
                }
                if v.is_empty() {
                    if bp.is_ground() {
                        ground.push(bp);
                        continue;
                    }
                    ok = false;
                    break;
                }
                candidates.push(v);
            }
            if !ok {
                continue;
            }
            trace_pred_product("local", id, Some(max), pc, &ground, &candidates);
            // Enumerate the product directly when it is small: staging an
            // antichain buffer per premise costs more than the handful of
            // selections it would filter, and the overwhelming majority of
            // local Pred joins are one- or two-candidate premises.
            //
            // Direction B (`KM_SPLIT`) always takes this path: it counts how
            // many premises of ONE product element carry a disjunctive head,
            // which is a property of the whole selection and not of any prefix
            // of it.  That mode is a gated diagnostic and never runs in the
            // default engine.
            let product = candidates.iter().fold(1u64, |acc, dimension| {
                acc.saturating_mul(dimension.len() as u64)
            });
            if branch_ordered() || product <= SMALL_PRED_PRODUCT {
                let n = candidates.len();
                let mut idxs = vec![0usize; n];
                loop {
                    if let Some(c) =
                        self.build_pred_resolvent(id, side, pc, &ground, &candidates, &idxs, root)
                    {
                        push_nonredundant_pred_result(&mut out, c);
                    }
                    let mut k = 0;
                    loop {
                        if k == n {
                            idxs[0] = usize::MAX;
                            break;
                        }
                        idxs[k] += 1;
                        if idxs[k] < candidates[k].len() {
                            break;
                        }
                        idxs[k] = 0;
                        k += 1;
                    }
                    if n == 0 || idxs[0] == usize::MAX {
                        break;
                    }
                }
                continue;
            }
            // Left-deep antichain join, identical in form and justification to
            // `pred_from_neighbor`: after each premise, drop the partial unions
            // that another partial already strengthens.  If partial P
            // strengthens Q then `P ∪ R` strengthens `Q ∪ R` for every choice R
            // from the remaining premises, so every pruned extension has a
            // stronger extension in the full product — the retained antichain,
            // and therefore the context fixpoint, is unchanged.
            //
            // The explicit product this replaces is what stalls the qualified
            // cardinality clauses of ontologies like ORE 1194, where one
            // `≤n R.C` premise set has several thousand-candidate dimensions:
            // the product was enumerated in full and every element was pushed
            // through the redundancy trie, even though the surviving antichain
            // after each dimension is small.
            //
            // A smaller dimension first normally minimizes the live antichain;
            // dimension order cannot affect the set union represented by a
            // complete selection from the product.
            candidates.sort_by_key(Vec::len);
            // `filter_head` is a per-literal filter with a single whole-head
            // veto (a `s ≈ s` tautology), so filtering each prefix agrees with
            // filtering the concatenation once at the end.
            let Some(head) = self.filter_head(pc.head.clone()) else {
                continue;
            };
            let mut partials = vec![ContextClause::new(ground, head, root, &self.sig)];
            for dimension in &candidates {
                let mut next = PredResultBuffer::default();
                for partial in &partials {
                    for &(ci, matched) in dimension {
                        // The pinned position for `max` is provided by the side
                        // clause, which has no arena id.
                        let provider = if ci == usize::MAX { side } else { &arena[ci] };
                        let mut body = partial.body.clone();
                        body.extend_from_slice(&provider.body);
                        let mut head = partial.head.clone();
                        for &literal in &provider.head {
                            if literal != Lit::P(matched) {
                                head.push(literal);
                            }
                        }
                        if let Some(head) = self.filter_head(head) {
                            push_nonredundant_pred_result(
                                &mut next,
                                ContextClause::new(body, head, root, &self.sig),
                            );
                        }
                    }
                }
                partials = next.into_vec();
                if partials.is_empty() {
                    break;
                }
            }
            // Merging each premise's antichain into the shared buffer keeps the
            // same result as pushing every product element: an element dropped
            // as redundant is strengthened by one that was kept, so the
            // antichain of the union is unchanged.
            for clause in partials {
                push_nonredundant_pred_result(&mut out, clause);
            }
        }
        out.into_vec()
    }

    /// Reference implementation of local Pred: enumerate the whole Cartesian
    /// product of premise providers and keep its strengthening antichain.  This
    /// is what `pred_local_inner` did before the left-deep join replaced it, and
    /// it is the oracle the join is tested against.
    #[cfg(test)]
    fn pred_local_full_product_reference(
        &self,
        id: usize,
        side: &ContextClause,
        max: Pred,
        root: bool,
    ) -> Vec<ContextClause> {
        let mut out = PredResultBuffer::default();
        let ctx = &self.contexts[id];
        let relevant = match ctx.neighbor_pred_body_index.get(&max) {
            Some(relevant) => relevant.as_slice(),
            None => return out.into_vec(),
        };
        for &pid in relevant {
            let pc = &self.pred_interned[pid as usize];
            let mut ground: Vec<Pred> = Vec::new();
            let mut candidates: Vec<Vec<(usize, Pred)>> = Vec::with_capacity(pc.body.len());
            let mut ok = true;
            for &bp in &pc.body {
                if bp == max {
                    candidates.push(vec![(usize::MAX, bp)]);
                    continue;
                }
                let mut v = Vec::new();
                if let Some(cand) = ctx.max_head_pred_index.get(&bp) {
                    v.extend(cand.iter().map(|&ci| (ci as usize, bp)));
                }
                if v.is_empty() {
                    if bp.is_ground() {
                        ground.push(bp);
                        continue;
                    }
                    ok = false;
                    break;
                }
                candidates.push(v);
            }
            if !ok {
                continue;
            }
            let n = candidates.len();
            let mut idxs = vec![0usize; n];
            loop {
                if let Some(c) =
                    self.build_pred_resolvent(id, side, pc, &ground, &candidates, &idxs, root)
                {
                    push_nonredundant_pred_result(&mut out, c);
                }
                let mut k = 0;
                loop {
                    if k == n {
                        idxs[0] = usize::MAX;
                        break;
                    }
                    idxs[k] += 1;
                    if idxs[k] < candidates[k].len() {
                        break;
                    }
                    idxs[k] = 0;
                    k += 1;
                }
                if n == 0 || idxs[0] == usize::MAX {
                    break;
                }
            }
        }
        out.into_vec()
    }

    fn build_pred_resolvent(
        &self,
        id: usize,
        side: &ContextClause,
        pc: &PredClause,
        ground: &[Pred],
        candidates: &[Vec<(usize, Pred)>],
        idxs: &[usize],
        root: bool,
    ) -> Option<ContextClause> {
        let _ = id;
        let arena = &self.cc_arena[root as usize];
        let mut head: Vec<Lit> = pc.head.clone();
        let mut body: Vec<Pred> = ground.to_vec();
        for i in 0..candidates.len() {
            let (ci, matched) = candidates[i][idxs[i]];
            let clause = if ci == usize::MAX { side } else { &arena[ci] };
            for l in &clause.head {
                if *l != Lit::P(matched) {
                    head.push(*l);
                }
            }
            body.extend_from_slice(&clause.body);
        }
        let head = self.filter_head(head)?;
        Some(ContextClause::new(body, head, root, &self.sig))
    }

    /// Join cases 1+2 conclusion: resolve the ground body atom `a` of
    /// `consumer` against `provider` (which has `a` maximal in its head):
    /// `Γ ∧ Γ' → Δ ∨ Δ' ∨ Δ''`.
    fn join_resolvent(
        &self,
        consumer: &ContextClause,
        a: Pred,
        provider: &ContextClause,
        root: bool,
    ) -> Option<ContextClause> {
        let body: Vec<Pred> = consumer
            .body
            .iter()
            .filter(|p| **p != a)
            .chain(provider.body.iter())
            .copied()
            .collect();
        let mut head: Vec<Lit> = consumer.head.clone();
        for l in &provider.head {
            if *l != Lit::P(a) {
                head.push(*l);
            }
        }
        let head = self.filter_head(head)?;
        let c = ContextClause::new(body, head, root, &self.sig);
        if c.is_head_tautology() {
            return None;
        }
        Some(c)
    }

    /// Join case 3 conclusion: discharge the ground body atom `a = A'{x↦o}` of
    /// `consumer` via the body-empty `provider` (`⊤ → Δ' ∨ A'`) and the
    /// body-empty `bridge` (`⊤ → Δ'' ∨ x ≈ o`): `Γ → Δ ∨ Δ' ∨ Δ''`.
    fn join_resolvent3(
        &self,
        consumer: &ContextClause,
        a: Pred,
        provider: &ContextClause,
        aprime: Pred,
        bridge: &ContextClause,
        o: Term,
        root: bool,
    ) -> Option<ContextClause> {
        let body: Vec<Pred> = consumer.body.iter().filter(|p| **p != a).copied().collect();
        let mut head: Vec<Lit> = consumer.head.clone();
        for l in &provider.head {
            if *l != Lit::P(aprime) {
                head.push(*l);
            }
        }
        let bl = Lit::Eq { s: o, t: X };
        for l in &bridge.head {
            if *l != bl {
                head.push(*l);
            }
        }
        let head = self.filter_head(head)?;
        let c = ContextClause::new(body, head, root, &self.sig);
        if c.is_head_tautology() {
            return None;
        }
        Some(c)
    }

    /// Join case 3 firings for one ground body atom `a` of `consumer`: each
    /// way of writing `a = A'{x↦o}` (with `A'` a plain x-form, no composite
    /// terms) is tried against the indexed bridges `⊤ → Δ'' ∨ x ≈ o` and the
    /// body-empty providers with `A'` maximal.
    fn join_case3_for(
        &self,
        ctx: &Context,
        arena: &[ContextClause],
        consumer: &ContextClause,
        a: Pred,
        root: bool,
        out: &mut Vec<ContextClause>,
    ) {
        let mut variants: Vec<(Pred, Term)> = Vec::new();
        match a {
            Pred::Concept { iri, t } if is_individual(t) => {
                variants.push((Pred::Concept { iri, t: X }, t));
            }
            Pred::Role { iri, s, t } if is_individual(s) && is_individual(t) => {
                variants.push((Pred::Role { iri, s: X, t }, s));
                variants.push((Pred::Role { iri, s, t: X }, t));
                if s == t {
                    variants.push((Pred::Role { iri, s: X, t: X }, s));
                }
            }
            _ => {}
        }
        for (aprime, o) in variants {
            let bridges = match ctx.bridge_index.get(&o) {
                Some(b) => b,
                None => continue,
            };
            let cands = match aprime {
                Pred::Concept { iri, .. } => ctx.head_concept_index.get(&iri),
                Pred::Role { iri, .. } => ctx.head_role_index.get(&iri),
            };
            let cands = match cands {
                Some(c) => c,
                None => continue,
            };
            for &pi in cands {
                let pcl = &arena[pi as usize];
                if !pcl.body.is_empty() {
                    continue; // Γ' = ⊤ required
                }
                if !pcl.max_head_predicates().any(|(p, _)| p == aprime) {
                    continue;
                }
                for &bi in bridges {
                    if bi == pi {
                        continue;
                    }
                    let bcl = &arena[bi as usize];
                    if let Some(r) = self.join_resolvent3(consumer, a, pcl, aprime, bcl, o, root) {
                        out.push(r);
                    }
                }
            }
        }
    }

    /// Join rule (arXiv:1805.01396 Table 3): in-context resolution on a ground
    /// atom.  Cases 1+2 resolve a clause `A ∧ Γ → Δ` (ground body atom `A`,
    /// arising from the verbatim-copied `C_i` of Pred/r-Pred) against a clause
    /// with `A` maximal in its head; case 3 discharges `A = A'{x↦o}` via a
    /// provider over `x` and an `x ≈ o` bridge.  Fired at work-off from every
    /// arrival order (consumer, provider, or bridge last).  Inert without
    /// individuals: all the indexes involved are then empty.
    fn join(&self, id: usize, side: &ContextClause, root: bool) -> Vec<ContextClause> {
        let mut out = Vec::new();
        let ctx = &self.contexts[id];
        if ctx.ground_body_index.is_empty() && ctx.bridge_index.is_empty() {
            return out;
        }
        let arena = &self.cc_arena[root as usize];
        // (a) `side` as provider: a maximal ground head atom resolves the
        // ground body atom of every indexed consumer.
        for (p, _) in side.max_head_predicates() {
            if p.is_ground() {
                if let Some(consumers) = ctx.ground_body_index.get(&p) {
                    for &ci in consumers {
                        if let Some(r) = self.join_resolvent(&arena[ci as usize], p, side, root) {
                            out.push(r);
                        }
                    }
                }
            }
        }
        // (b) `side` as consumer: each ground body atom resolves against
        // worked-off providers with that atom maximal, or via case 3.
        for &a in side.body.iter().filter(|p| p.is_ground()) {
            let cands = match a {
                Pred::Concept { iri, .. } => ctx.head_concept_index.get(&iri),
                Pred::Role { iri, .. } => ctx.head_role_index.get(&iri),
            };
            if let Some(cands) = cands {
                for &ci in cands {
                    let c = &arena[ci as usize];
                    if c.max_head_predicates().any(|(p, _)| p == a) {
                        if let Some(r) = self.join_resolvent(side, a, c, root) {
                            out.push(r);
                        }
                    }
                }
            }
            self.join_case3_for(ctx, arena, side, a, root, &mut out);
        }
        // (c) `side` as a late-arriving case-3 bridge or provider.
        if side.body.is_empty() {
            for l in side.max_head() {
                match l {
                    Lit::Eq { s, t } if is_individual(s) && t == X => {
                        // bridge arrival: complete triples over individual s
                        let o = s;
                        for (atom, consumers) in &ctx.ground_body_index {
                            let mut inds: Vec<Term> = Vec::new();
                            pred_inds(atom, &mut inds);
                            if !inds.contains(&o) {
                                continue;
                            }
                            for &ci in consumers {
                                let consumer = &arena[ci as usize];
                                // re-run case 3 for this consumer/atom against
                                // all bridges (now including `side`, which is
                                // not yet indexed): inline the variant loop
                                // with `side` as the bridge.
                                let mut variants: Vec<(Pred, Term)> = Vec::new();
                                match *atom {
                                    Pred::Concept { iri, t } if t == o => {
                                        variants.push((Pred::Concept { iri, t: X }, o));
                                    }
                                    Pred::Role { iri, s: rs, t: rt }
                                        if is_individual(rs) && is_individual(rt) =>
                                    {
                                        if rs == o {
                                            variants.push((Pred::Role { iri, s: X, t: rt }, o));
                                        }
                                        if rt == o {
                                            variants.push((Pred::Role { iri, s: rs, t: X }, o));
                                        }
                                        if rs == o && rt == o {
                                            variants.push((Pred::Role { iri, s: X, t: X }, o));
                                        }
                                    }
                                    _ => {}
                                }
                                for (aprime, _) in variants {
                                    let pcands = match aprime {
                                        Pred::Concept { iri, .. } => {
                                            ctx.head_concept_index.get(&iri)
                                        }
                                        Pred::Role { iri, .. } => ctx.head_role_index.get(&iri),
                                    };
                                    if let Some(pcands) = pcands {
                                        for &pi in pcands {
                                            let pcl = &arena[pi as usize];
                                            if !pcl.body.is_empty()
                                                || !pcl
                                                    .max_head_predicates()
                                                    .any(|(p, _)| p == aprime)
                                            {
                                                continue;
                                            }
                                            if let Some(r) = self.join_resolvent3(
                                                consumer, *atom, pcl, aprime, side, o, root,
                                            ) {
                                                out.push(r);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    Lit::P(p) if !p.is_ground() && p.is_function_free() => {
                        // provider arrival: for each indexed bridge individual
                        // o, `p{x↦o}` may be a consumer's ground body atom.
                        let mentions_x = match p {
                            Pred::Concept { t, .. } => t == X,
                            Pred::Role { s, t, .. } => s == X || t == X,
                        };
                        if !mentions_x {
                            continue;
                        }
                        let bridge_os: Vec<Term> = ctx.bridge_index.keys().copied().collect();
                        for o in bridge_os {
                            let a = p.apply(&|t| if t == X { o } else { t });
                            if !a.is_ground() {
                                continue;
                            }
                            let consumers = match ctx.ground_body_index.get(&a) {
                                Some(c) => c,
                                None => continue,
                            };
                            for &bi in &ctx.bridge_index[&o] {
                                let bcl = &arena[bi as usize];
                                for &ci in consumers {
                                    let consumer = &arena[ci as usize];
                                    if let Some(r) =
                                        self.join_resolvent3(consumer, a, side, p, bcl, o, root)
                                    {
                                        out.push(r);
                                    }
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        out
    }

    /// Factor rule (Table 2): from a clause whose head contains two equalities
    /// `s ≈ t` and `s ≈ t'` with the same maximal side `s`, derive the clause
    /// with `s ≈ t` replaced by `t ≉ t'`.  Sound: if `s = t` and `s ≠ t'` then
    /// `t ≠ t'`.  Needed for `≤ n` value-partition clashes.
    fn factor(&self, clause: &ContextClause, root: bool) -> Vec<ContextClause> {
        let mut out = Vec::new();
        let heads = &clause.head;
        for i in 0..heads.len() {
            let (s, t) = match heads[i] {
                Lit::Eq { s, t } => (s, t),
                _ => continue,
            };
            for j in 0..heads.len() {
                if i == j {
                    continue;
                }
                if let Lit::Eq { s: s2, t: t2 } = heads[j] {
                    if s2 == s && t2 != t {
                        // drop head[i] (= s≈t), keep head[j] (= s≈t'), add t≉t'
                        let mut newhead: Vec<Lit> = heads
                            .iter()
                            .enumerate()
                            .filter(|(k, _)| *k != i)
                            .map(|(_, l)| *l)
                            .collect();
                        newhead.push(Lit::ineq(t, t2));
                        if let Some(h) = self.filter_head(newhead) {
                            let c = ContextClause::new(clause.body.clone(), h, root, &self.sig);
                            if !c.is_head_tautology() {
                                out.push(c);
                            }
                        }
                    }
                }
            }
        }
        out
    }

    /// Eq rule where the max literal is a predicate containing a rewritable term,
    /// resolved against worked-off equality clauses.
    fn eq_from_pred(
        &self,
        id: usize,
        side: &ContextClause,
        max: Lit,
        root: bool,
    ) -> Vec<ContextClause> {
        let mut out = Vec::new();
        let ctx = &self.contexts[id];
        let arena = &self.cc_arena[root as usize];
        let mterm = max.max_term();
        let Some(candidates) = ctx.max_head_term_index.get(&mterm) else {
            return out;
        };
        for &ci in candidates {
            let c = &arena[ci as usize];
            for l in c.max_head() {
                if let Lit::Eq { s, t } = l {
                    if s == mterm && max.contains_at_rewrite_position(s) {
                        if let Some(res) = self.build_eq(side, max, c, s, t, l, root) {
                            out.push(res);
                        }
                    }
                }
            }
        }
        out
    }

    /// Eq rule where the max literal is itself an equality/inequality.
    fn eq_from_equation(
        &self,
        id: usize,
        side: &ContextClause,
        max: Lit,
        root: bool,
    ) -> Vec<ContextClause> {
        let mut out = Vec::new();
        let ctx = &self.contexts[id];
        let arena = &self.cc_arena[root as usize];
        let s = match max {
            Lit::Eq { s, .. } | Lit::Ineq { s, .. } => s,
            _ => return out,
        };
        let Some(candidates) = ctx.max_head_term_index.get(&s) else {
            return out;
        };
        for &ci in candidates {
            let c = &arena[ci as usize];
            for l in c.max_head() {
                if l.contains_at_rewrite_position(s) && l != max {
                    if let Lit::Eq { s: es, t: et } = max {
                        // side provides equality es==et, rewrite l
                        if let Some(res) = self.build_eq(c, l, side, es, et, max, root) {
                            out.push(res);
                        }
                    }
                }
            }
        }
        out
    }

    /// Build the Eq-rule conclusion rewriting `max` (in `clause`) using equality
    /// `s == t` (the max literal of `eq_clause`).
    #[allow(clippy::too_many_arguments)]
    fn build_eq(
        &self,
        clause: &ContextClause,
        max: Lit,
        eq_clause: &ContextClause,
        s: Term,
        t: Term,
        equality: Lit,
        root: bool,
    ) -> Option<ContextClause> {
        let mut head: Vec<Lit> = Vec::new();
        // rewrite max's s-occurrence to t
        match max {
            Lit::P(_) => {
                if let Some(r) = max.rewrite(s, t) {
                    head.push(r);
                }
            }
            Lit::Eq { s: ms, t: t2 } if ms == s => {
                if t == t2 {
                    return None; // redundant
                }
                if let Some(r) = max.rewrite(s, t) {
                    head.push(r);
                }
            }
            Lit::Ineq { s: ms, t: t2 } if ms == s => {
                if t != t2 {
                    if let Some(r) = max.rewrite(s, t) {
                        head.push(r);
                    }
                }
            }
            _ => return None,
        }
        for l in &clause.head {
            if *l != max {
                head.push(*l);
            }
        }
        for l in &eq_clause.head {
            if *l != equality {
                head.push(*l);
            }
        }
        let mut body = clause.body.clone();
        body.extend_from_slice(&eq_clause.body);
        let head = self.filter_head(head)?;
        let c = ContextClause::new(body, head, root, &self.sig);
        if c.is_head_tautology() {
            None
        } else {
            Some(c)
        }
    }

    // -------------------- inter-context propagation ------------------------

    /// The successor context for function symbol `f` (pay-as-you-go strategy).
    /// Each distinct `f` gets its own empty-core context, created lazily.  These
    /// are tracked in `successor_ctxs` rather than `core_index`, because every
    /// successor context shares the empty core and must not be deduplicated into
    /// one (that is precisely the trivial strategy this replaces).
    fn successor_for(&mut self, f: Term) -> usize {
        if let Some(&s) = self.successor_ctxs.get(&f) {
            return s;
        }
        // Disabled via KM_NO_SHARE for A/B measurement; default on.
        if std::env::var_os("KM_NO_SHARE").is_some() {
            let id = self.contexts.len();
            let ctx = Context::new(id, vec![], false, None);
            self.contexts.push(ctx);
            self.successor_ctxs.insert(f, id);
            self.init_context(id);
            return id;
        }
        self.ensure_shared_closure();
        let id = self.contexts.len();
        let ctx = Context::new(id, vec![], false, None);
        self.contexts.push(ctx);
        self.successor_ctxs.insert(f, id);
        // Seed the shared context-independent closure directly into worked-off
        // (already mutually saturated, so it fires no rules here).  This replaces
        // `init_context` for successor contexts: the ontology facts are part of
        // the closure, and the empty core contributes no core clauses.  The
        // hypothesis clause that arrives via the first Succ message (apply_succ)
        // then saturates against this seeded closure, deriving exactly the
        // context-specific consequences.
        let closure = self.shared_closure.as_ref().unwrap().clone();
        for c in closure {
            self.seed_worked_off(id, c);
        }
        id
    }

    /// Central strategy: the successor context whose core is exactly `core`
    /// (the σ-image of a pushed trigger set), created on first use.  Seeded
    /// with the shared non-root closure (facts+TBox consequences) plus the
    /// Core rule for its core atoms.
    fn central_successor_for_core(&mut self, core: Vec<Pred>, seed_from: Option<usize>) -> usize {
        let h = content_hash(&core);
        if let Some(ids) = self.central_index.get(&h) {
            for &cand in ids {
                if self.contexts[cand].core == core {
                    return cand;
                }
            }
        }
        let id = self.contexts.len();
        let ctx = Context::new(id, core, false, None);
        self.contexts.push(ctx);
        self.central_index.entry(h).or_default().push(id);
        if std::env::var_os("KM_NO_SHARE").is_some() {
            self.init_context(id);
        } else if let Some(src) = seed_from {
            // KM_SEED_FROM_SUBSET: the caller guarantees the source context's core
            // is a subset of this core, so every clause `src` has worked off was
            // derived from facts that also hold here — seed them directly instead
            // of re-deriving the shared closure + the chain prefix.  `src`'s
            // worked-off already includes the shared closure, so this subsumes the
            // usual seed.  Sound + fixpoint-preserving (only re-derivable clauses
            // are pre-seeded; the saturation then derives the remaining delta).
            let wo = self.contexts[src].worked_off.clone();
            for c in wo {
                self.seed_worked_off(id, c);
            }
            self.add_core(id);
        } else {
            self.ensure_shared_closure();
            let closure = self.shared_closure.as_ref().unwrap().clone();
            for c in closure {
                self.seed_worked_off(id, c);
            }
            self.add_core(id);
        }
        id
    }

    /// Compute the context-independent closure once: saturate a throwaway
    /// empty-core, non-root context from the ontology facts + TBox alone, then
    /// snapshot its worked-off clauses and discard the context.  No messages are
    /// generated (propagation is never run on it), so the snapshot is purely the
    /// facts/TBox consequences shared by every successor context.
    fn ensure_shared_closure(&mut self) {
        if self.shared_closure.is_some() {
            return;
        }
        let id = self.contexts.len();
        let ctx = Context::new(id, vec![], false, None);
        self.contexts.push(ctx);
        self.init_context(id); // seeds empty-body ontology facts (no core)
        self.saturate(id);
        let closure = self.contexts[id].worked_off.clone();
        // Discard the throwaway: nothing references `id` (no edges, not in
        // `successor_ctxs`/`core_index`, no query), so popping it keeps the
        // context vector and counts clean.
        debug_assert_eq!(id, self.contexts.len() - 1);
        self.contexts.pop();
        self.shared_closure = Some(closure);
    }

    /// Place an already-derived clause into context `id`'s worked-off set without
    /// firing any rules: mirrors the bookkeeping tail of `saturate` (clause-key
    /// set, semi-naive Pred/Succ pools, head indexes, dirty flag) so the seeded
    /// clause participates in later resolution and propagation exactly as if it
    /// had been worked off normally.
    fn seed_worked_off(&mut self, id: usize, cid: u32) {
        let d = self.contexts[id].root as usize;
        // Both eligibility tests are pure functions of the interned clause, so
        // they come off the shared `FacetTable`.  This is the hottest instance
        // of the per-slot re-derivation the table removes: every successor
        // context seeds the whole shared closure, so the closure's clauses were
        // re-analysed once per context.
        let ClauseFlags {
            seed_pred: pred_eligible,
            seed_succ: succ_eligible,
            ..
        } = self.cc_facets[d].flags_of(cid);
        let arena = &self.cc_arena[d];
        let facets = &self.cc_facets[d];
        let ctx = &mut self.contexts[id];
        if !ctx.clause_keys.insert(cid) {
            return;
        }
        ctx.index_active_clause(arena, cid);
        if pred_eligible {
            ctx.pred_pool.push(cid);
        }
        if succ_eligible {
            ctx.succ_pool.push(cid);
        }
        ctx.worked_off.push(cid);
        ctx.index_clause(facets, cid);
        ctx.dirty = true;
    }

    /// `true` if context `sid` has derived concept `iri` on its central
    /// variable as an unconditional fact (`⊤ → iri(x)`).  Used by the
    /// redundant-trigger skip to detect a push-back the successor already knows.
    fn ctx_derives_central(&self, sid: usize, iri: Iri) -> bool {
        let ctx = &self.contexts[sid];
        let arena = &self.cc_arena[ctx.root as usize];
        if let Some(idxs) = ctx.head_concept_index.get(&iri) {
            for &ci in idxs {
                let c = &arena[ci as usize];
                if c.body.is_empty()
                    && c.head.len() == 1
                    && matches!(c.head[0], Lit::P(Pred::Concept { iri: i, t }) if i == iri && is_central(t))
                {
                    return true;
                }
            }
        }
        false
    }

    /// After saturating context `id`, generate Succ and Pred messages.
    fn propagate(&mut self, id: usize) {
        if !self.prof_time {
            return self.propagate_inner(id);
        }
        let t = std::time::Instant::now();
        self.propagate_inner(id);
        prof_add(&PROPAGATE_NS, t);
    }

    fn propagate_inner(&mut self, id: usize) {
        if !self.contexts[id].dirty {
            return;
        }
        self.stat_propagate += 1;
        self.contexts[id].dirty = false;
        // ---- Succ ---- (semi-naive: scan only pool entries added since the last
        // propagate; succ triggers only arise from new worked-off clauses, and
        // `pushed_succ` still dedups within and across scans).
        let mut new_succ: Vec<(Pred, bool)> = Vec::new();
        // r-Succ (nominal calculus): ground max-head atoms about an
        // individual push their y-form to the ground context, edge labelled
        // by the individual.
        let mut ground_succ: Vec<(Pred, Term)> = Vec::new();
        let succ_start = self.contexts[id].succ_hwm;
        self.stat_succ_scans += (self.contexts[id].succ_pool.len() - succ_start) as u64;
        {
            let ctx = &self.contexts[id];
            let arena = &self.cc_arena[ctx.root as usize];
            for &ci in &ctx.succ_pool[succ_start..] {
                let c = &arena[ci as usize];
                // Core-eligibility: a trigger may enter the successor core only
                // if it is the SOLE succ-trigger over its function term in this
                // clause's head.  A core atom is discharged by cutting it from
                // its source clause (residue literals accumulate in the
                // resolvent), which works for any single trigger — body
                // conditions and other-term disjuncts ride along.  But two
                // triggers over the same f from ONE head (e.g. the
                // `… → A2(f)|A3(f)|Q` of a min-card case split) cannot both be
                // cut from the same clause, so conditioning a push-back on both
                // at once loses the per-disjunct refutations completeness
                // needs; such triggers stay hypotheses (`p → p` at the target).
                let mut multi: Vec<Term> = Vec::new();
                {
                    let mut seen: Vec<Term> = Vec::new();
                    for l in &c.head {
                        if let Lit::P(p) = l {
                            let t = p.max_term();
                            if is_function(t) && p.is_succ_trigger(&self.sig) {
                                if seen.contains(&t) {
                                    if !multi.contains(&t) {
                                        multi.push(t);
                                    }
                                } else {
                                    seen.push(t);
                                }
                            }
                        }
                    }
                }
                for (p, _) in c.max_head_predicates() {
                    if is_function(p.max_term())
                        && p.is_succ_trigger(&self.sig)
                        && !ctx.pushed_succ.contains(&p)
                    {
                        new_succ.push((p, !multi.contains(&p.max_term())));
                    } else if Some(id) != self.ground_ctx {
                        if let Some((yform, o)) = root_succ_form(&p) {
                            if !ctx.pushed_succ.contains(&yform)
                                && !rsucc_blocked(ctx, arena, c, &p)
                            {
                                ground_succ.push((yform, o));
                            }
                        }
                    }
                }
            }
        }
        if !ground_succ.is_empty() {
            let target = self.ground_context();
            for (p, o) in ground_succ {
                if self.contexts[id].pushed_succ.insert(p) {
                    self.msgs.push_back(Msg::Succ {
                        from: id,
                        f: o,
                        p,
                        target,
                    });
                }
            }
        }
        self.contexts[id].succ_hwm = self.contexts[id].succ_pool.len();
        if !self.central {
            // Legacy pay-as-you-go strategy: one empty-core successor per `f`.
            for (p, _) in new_succ {
                let f = p.max_term();
                let target = self.successor_for(f);
                // forward map: f -> x, x -> y
                let psigma = p.apply(&|v| forwards(f, v));
                self.contexts[id].pushed_succ.insert(p);
                if self.contexts[id].successors.insert(f, target) != Some(target) {
                    // New / re-targeted edge: the r-Succ cross-step must offer it
                    // the reach set (see `rsucc_edges_grew`).
                    self.contexts[id].rsucc_edges_grew = true;
                }
                self.msgs.push_back(Msg::Succ {
                    from: id,
                    f,
                    p: psigma,
                    target,
                });
            }
        } else {
            // Central strategy: group the new triggers by `f`, extend each
            // trigger set, and (re-)target the successor context whose core is
            // the σ-image of the full set.  A grown set yields a new target and
            // the WHOLE set is re-sent there (the new context needs every
            // pushed predicate for its edge bookkeeping and hypotheses); the
            // previous (smaller-core) context simply stops receiving — its
            // earlier back-pushed consequences remain sound because apply_pred
            // conditions them on that context's own core.
            let mut grew: Vec<Term> = Vec::new();
            let mut new_by_f: HashMap<Term, Vec<Pred>> = HashMap::new();
            {
                // Redundant-trigger skip (KM_NO_TRIGSKIP to disable): a concept
                // trigger `C(f)` whose successor context for `f` already derives
                // `C` on its own central is a redundant push-back — growing `f`'s
                // core to `{filler, C}` would just duplicate the `{filler}`
                // context (C is derivable from the filler), so it adds churn with
                // no new consequence.  Skipping it keeps the successor mapped to
                // its existing context (whose edge already delivers every
                // consequence) and stops the grown-core cascade that otherwise
                // overruns the message budget on transitive/role-chain onts.
                // Genuinely-new concepts (not yet derived by the successor) still
                // grow the core, so completeness is preserved.
                let trigskip = self.trigskip;
                let mut redundant: Vec<Pred> = Vec::new();
                if trigskip {
                    for (p, _) in &new_succ {
                        if let Pred::Concept { iri, t } = *p {
                            let f = t;
                            if let Some(&sid) = self.contexts[id].successors.get(&f) {
                                if self.ctx_derives_central(sid, iri) {
                                    redundant.push(*p);
                                }
                            }
                        }
                    }
                }
                let ctx = &mut self.contexts[id];
                for (p, is_fact) in new_succ {
                    // Always mark pushed so we never re-process this trigger.
                    ctx.pushed_succ.insert(p);
                    if redundant.contains(&p) {
                        continue; // redundant push-back: do not grow the core
                    }
                    let f = p.max_term();
                    ctx.trigger_sets.entry(f).or_default().insert(p);
                    if is_fact {
                        ctx.fact_trigger_sets.entry(f).or_default().insert(p);
                    }
                    new_by_f.entry(f).or_default().push(p);
                    if !grew.contains(&f) {
                        grew.push(f);
                    }
                }
            }
            for f in grew {
                let raw: Vec<Pred> = self.contexts[id].trigger_sets[&f].iter().copied().collect();
                // The successor core is the σ-image of the FACT triggers only;
                // disjunctively/conditionally derived triggers stay hypotheses
                // (see `fact_trigger_sets`).
                let mut core: Vec<Pred> = self.contexts[id]
                    .fact_trigger_sets
                    .get(&f)
                    .map(|s| s.iter().map(|p| p.apply(&|v| forwards(f, v))).collect())
                    .unwrap_or_default();
                core.sort();
                core.dedup();
                // KM_CORE_CAP: bound the successor core size. The excess fact
                // triggers stay in `raw` and arrive as `p→p` hypotheses at the
                // target (their consequences come back conditioned on `p` alone),
                // so completeness is preserved while the number of distinct cores
                // (hence the core-growth cascade) is bounded.
                if self.core_cap > 0 && core.len() > self.core_cap {
                    core.truncate(self.core_cap);
                }
                // KM_SEED_FROM_SUBSET: seed the new (grown-core) successor from the
                // previous target for this edge, but only when its core is a subset
                // of the new core (so every seeded clause is valid here). Saves
                // re-deriving the chain prefix.
                let seed_src = if self.seed_from_subset {
                    match self.contexts[id].successors.get(&f).copied() {
                        Some(old) if self.contexts[old].core.iter().all(|p| core.contains(p)) => {
                            Some(old)
                        }
                        _ => None,
                    }
                } else {
                    None
                };
                let target = self.central_successor_for_core(core, seed_src);
                let prev = self.contexts[id].successors.insert(f, target);
                if prev != Some(target) {
                    // New / re-targeted edge: the r-Succ cross-step must offer it
                    // the reach set (see `rsucc_edges_grew`).
                    self.contexts[id].rsucc_edges_grew = true;
                    // New target (first push or fact-core growth): send the full
                    // set so the new context's edge records every pushed
                    // predicate.
                    for p in &raw {
                        self.msgs.push_back(Msg::Succ {
                            from: id,
                            f,
                            p: p.apply(&|v| forwards(f, v)),
                            target,
                        });
                    }
                } else {
                    // Same target (hypothesis-only growth): send just the new
                    // triggers so the target gains their edge bookkeeping and
                    // hypothesis clauses.
                    for p in &new_by_f[&f] {
                        self.msgs.push_back(Msg::Succ {
                            from: id,
                            f,
                            p: p.apply(&|v| forwards(f, v)),
                            target,
                        });
                    }
                }
            }
        }
        // ---- r-Succ forward push (KM_RSUCC) ----
        // Forward this context's CENTRAL reachability facts (`__trans/__chain(x)`)
        // to every successor as edge-conditioned neighbour facts `reach(y)`.  This
        // is the missing step for transitive+inverse reconstruction: a successor
        // `h` needs its predecessor's `reach` visible as `reach(y)` to fire e.g.
        // `reach(y) ∧ hp(x,y) → reach(x)` across the inverse back-edge `hp(x,y)`
        // it already receives.  Pushed via the ordinary Succ message (so the
        // target gains the hypothesis `reach(y) → reach(y)` AND records `reach(y)`
        // in this edge's pushed set).  Soundness under the shared-successor central
        // strategy: the successor's conclusion is conditioned on `reach(y)` in its
        // body, and the Pred routing sends it back ONLY to predecessor edges whose
        // pushed set contains `reach(y)` — i.e. only to predecessors that actually
        // vouched for `reach`; a co-sharing predecessor that did not is unaffected.
        if self.sig.rsucc && !self.contexts[id].rsucc_pool.is_empty() {
            // Semi-naive: extend the persistent reach set from only the
            // `rsucc_pool` entries appended since the last scan (`rsucc_hwm`).
            // Because `rsucc_pool` is append-only and its reach extraction never
            // consults `clause_keys`, the accumulated `rsucc_reach` is exactly
            // the ordered-unique list the former full rescan produced, so the
            // reach × successor cross-product below (still gated by
            // `pushed_rsucc`) emits an identical set and order of Succ messages.
            {
                // Immutable pass: gather the reach predicates from only the new
                // pool tail (in pool order, duplicates tolerated by the fold).
                let new_reach = {
                    let ctx = &self.contexts[id];
                    let arena = &self.cc_arena[ctx.root as usize];
                    rsucc_reach_tail(arena, &ctx.rsucc_pool[ctx.rsucc_hwm..], &self.sig)
                };
                // Mutable pass: fold the tail into the persistent ordered-unique
                // accumulator (first occurrence wins, matching a full rescan).
                let ctx = &mut self.contexts[id];
                fold_reach_unique(&mut ctx.rsucc_reach, &mut ctx.rsucc_reach_set, new_reach);
                ctx.rsucc_hwm = ctx.rsucc_pool.len();
            }
            // Semi-naive cross-product DRIVER gate: run the `successors × reach`
            // sweep only on a genuine delta — reach grew, or a successor edge was
            // added/re-targeted since the last sweep.  When neither holds, every
            // current edge already has `hwm == rsucc_reach.len()` (the prior sweep
            // advanced it), so `rsucc_cross_step` would fire nothing; skipping it
            // drops only the O(|successors|) hwm scan + the `successors` Vec
            // allocation on the (common) rounds a context is re-dirtied by
            // unrelated predecessor / Pred churn.  Because `successors` is
            // insert-only, `rsucc_edges_grew` can only over-approximate growth, so
            // the guard never skips a round that would fire — the emitted
            // `Msg::Succ` set/order (hence the fixpoint) is identical to running
            // the sweep unconditionally.
            let reach_len = self.contexts[id].rsucc_reach.len();
            let run =
                self.contexts[id].rsucc_edges_grew || reach_len > self.contexts[id].rsucc_offered;
            if run {
                let successors: Vec<(Term, usize)> = self.contexts[id]
                    .successors
                    .iter()
                    .map(|(&f, &t)| (f, t))
                    .collect();
                // Semi-naive cross-product: for each successor edge scan only the
                // reach preds it has not yet been offered (`reach[hwm(edge)..]`),
                // still gated by `pushed_rsucc`.  `rsucc_reach` only grew in the
                // scan above (not in this loop) so its length is stable;
                // `rsucc_cross_step` reproduces the former full `successors ×
                // reach` rescan's fired triples and order exactly (see its
                // doc-comment).  Disjoint field borrows let it read `rsucc_reach`
                // while mutating the two maps.
                let fired = {
                    let ctx = &mut self.contexts[id];
                    rsucc_cross_step(
                        &successors,
                        &ctx.rsucc_reach,
                        &mut ctx.rsucc_pair_reach_hwm,
                        &mut ctx.pushed_rsucc,
                    )
                };
                // Every current edge is now offered `rsucc_reach[..reach_len]`;
                // record it so the next round can skip an unchanged sweep.
                self.contexts[id].rsucc_offered = reach_len;
                self.contexts[id].rsucc_edges_grew = false;
                for (f, target, p) in fired {
                    let psigma = p.apply(&|v| forwards(f, v)); // reach(x) -> reach(y)
                    self.msgs.push_back(Msg::Succ {
                        from: id,
                        f,
                        p: psigma,
                        target,
                    });
                }
            }
        }
        // ---- Pred ---- (semi-naive).  The Pred-eligible clauses live in
        // `pred_pool` (function-free, predicate-only head — built when a clause is
        // worked off, see `saturate`). The pool is an append-only derivation log,
        // but only entries still present in `clause_keys` may be pushed. This
        // mirrors Sequoia's `predClausesOnLastRound.removeRedundant`: an
        // intermediate clause back-subsumed before the end-of-round push is not
        // sent to predecessors. A `(clause, edge)`
        // covered-check `c.body ⊆ pushed[edge]` can only flip from fail to pass
        // when `pushed[edge]` gains a predicate, so we re-check a pair only when
        // the clause is new (index ≥ `pred_hwm`) or the edge's pushed-set grew
        // since `edge_seen`.  `pushed_pred` still dedups actual sends.  This
        // replaces the per-propagate full `worked_off × predecessors` rescan that
        // dominated runtime on existential-rich ontologies.
        let mut to_send: Vec<((usize, Term), u32)> = Vec::new();
        let mut pred_checks = 0u64;
        let ground_sender = Some(id) == self.ground_ctx;
        let new_edge_seen: Vec<((usize, Term), usize)>;
        {
            let ctx = &self.contexts[id];
            let arena = &self.cc_arena[ctx.root as usize];
            let hwm = ctx.pred_hwm;
            // edges with a freshness flag (pushed-set grew since last scan)
            let edges: Vec<(&(usize, Term), &HashSet<Pred>, bool)> = ctx
                .predecessors
                .iter()
                .map(|(e, pushed)| {
                    let seen = *ctx.edge_seen.get(e).unwrap_or(&0);
                    (e, pushed, pushed.len() > seen)
                })
                .collect();
            // Distinct source contexts and per-source freshness for the
            // ground-sender (r-Pred) path: a source is dirty when any of its
            // individual-labelled edges gained a pushed predicate.
            let mut sources: Vec<(usize, Term, bool)> = Vec::new();
            if ground_sender {
                for (e, _, dirty) in &edges {
                    match sources.iter_mut().find(|(u, _, _)| *u == e.0) {
                        Some(s) => {
                            s.2 |= *dirty;
                            if e.1 < s.1 {
                                s.1 = e.1; // smallest label as the stable representative
                            }
                        }
                        None => sources.push((e.0, e.1, *dirty)),
                    }
                }
            }
            for (i, &ci) in ctx.pred_pool.iter().enumerate() {
                // Back-subsumption removes the arena id from `clause_keys`.
                // Skipping it here is not an inference change: the retained
                // strengthening entails the dead clause and is itself eligible
                // for this round's Pred push.
                if !ctx.clause_keys.contains(&ci) {
                    continue;
                }
                let c = &arena[ci as usize];
                let new_clause = i >= hwm;
                // r-Pred (ground sender, x-free clauses): each body atom may be
                // discharged over a DIFFERENT individual-labelled edge of the
                // same source u (the paper's ⟨u, v_r, o_i⟩ per A_i), or — when
                // ground — copied verbatim (the C_i) provided u announced its
                // individuals.  Head individuals (e.g. Nom's fresh additional
                // nominals) need no edge: requiring one made every Nom
                // conclusion undeliverable.  Clauses mentioning x keep the
                // per-edge path below: their x is instantiated by the edge
                // label, so each edge yields a different conclusion.
                if ground_sender && !cc_mentions_x(c) {
                    for &(u, label, dirty_u) in &sources {
                        if !new_clause && !dirty_u {
                            continue;
                        }
                        pred_checks += 1;
                        // Every body atom must be DISCHARGED over u's edge
                        // labelled by that atom's individual (the paper's
                        // ⟨u, v_r, o_i⟩ per A_i, multi-edge per source), and
                        // every individual the clause mentions must be one u
                        // has announced (an edge per individual) — EXCEPT
                        // additional nominals (id ≥ nom_base), which no
                        // context can have announced: they are exactly what
                        // the Nom conclusions carry back.  Without the
                        // announcement guard, body-empty ground facts pass
                        // the discharge check vacuously and spray to every
                        // context with any root edge (livelock on ABox-heavy
                        // ontologies: ore_ont_10594, ~1900 individuals).
                        // Looser variants tried and rejected: verbatim C_i
                        // copies (announced-only) and no head filter — both
                        // unbounded on 10594.
                        let mut ok = true;
                        for b in &c.body {
                            let mut inds: Vec<Term> = Vec::new();
                            pred_inds(b, &mut inds);
                            let discharged = inds.iter().any(|o| {
                                ctx.predecessors
                                    .get(&(u, *o))
                                    .map_or(false, |s| s.contains(b))
                            });
                            if !discharged {
                                ok = false;
                                break;
                            }
                        }
                        if ok {
                            let mut inds: Vec<Term> = Vec::new();
                            for p in &c.body {
                                pred_inds(p, &mut inds);
                            }
                            for l in &c.head {
                                lit_inds(l, &mut inds);
                            }
                            ok = inds.iter().all(|o| {
                                *o >= self.nom_base || ctx.predecessors.contains_key(&(u, *o))
                            });
                        }
                        if ok {
                            let edge = (u, label);
                            let sent = ctx
                                .pushed_pred
                                .get(&edge)
                                .map_or(false, |s| s.contains(&(i as u32)));
                            if !sent {
                                to_send.push((edge, i as u32));
                            }
                        }
                    }
                    continue;
                }
                for (edge, pushed, dirty_edge) in &edges {
                    // (old clause, unchanged edge): already checked at this
                    // edge's pushed-length — skip.
                    if !new_clause && !*dirty_edge {
                        continue;
                    }
                    pred_checks += 1;
                    // Every body atom must be backed by this edge's pushed set
                    // (for the ground context these are the r-Succ hypotheses
                    // — the paper's "same u for every o_i" condition); and a
                    // ground-context clause only flows to a context that has
                    // announced every individual it mentions (an edge per
                    // individual), which keeps ground conclusions from being
                    // sprayed across unrelated contexts.
                    if c.body.iter().all(|b| pushed.contains(b))
                        && (!ground_sender || {
                            let mut inds: Vec<Term> = Vec::new();
                            for p in &c.body {
                                pred_inds(p, &mut inds);
                            }
                            for l in &c.head {
                                lit_inds(l, &mut inds);
                            }
                            inds.iter()
                                .all(|o| ctx.predecessors.contains_key(&(edge.0, *o)))
                        })
                    {
                        let sent = ctx
                            .pushed_pred
                            .get(*edge)
                            .map_or(false, |s| s.contains(&(i as u32)));
                        if !sent {
                            to_send.push((**edge, i as u32));
                        }
                    }
                }
            }
            new_edge_seen = ctx
                .predecessors
                .iter()
                .map(|(e, pushed)| (*e, pushed.len()))
                .collect();
        }
        self.stat_pred_checks += pred_checks;
        self.contexts[id].pred_hwm = self.contexts[id].pred_pool.len();
        for (e, len) in new_edge_seen {
            self.contexts[id].edge_seen.insert(e, len);
        }
        if !self.stat_pred_out_by_ctx.is_empty() && !to_send.is_empty() {
            if self.stat_pred_out_by_ctx.len() <= id {
                self.stat_pred_out_by_ctx.resize(id + 1, 0);
            }
            self.stat_pred_out_by_ctx[id] += to_send.len() as u64;
        }
        for (edge, pool_idx) in to_send {
            self.contexts[id]
                .pushed_pred
                .entry(edge)
                .or_default()
                .insert(pool_idx);
            self.msgs.push_back(Msg::Pred {
                to: edge.0,
                from: id,
                edge_label: edge.1,
                pool_idx,
            });
        }
    }

    /// Apply a Succ message: record the edge and add the hypothesis clause.
    /// Returns the target id; the caller saturates and propagates each touched
    /// target once after the whole message batch. Accumulating messages before
    /// saturation mirrors Sequoia's context work queue and avoids replaying an
    /// otherwise identical saturation tail once per incoming edge predicate.
    /// The fixpoint is unchanged: every added clause remains in `todo`, and the
    /// batch-end saturation processes their union before any propagation.
    fn apply_succ(&mut self, from: usize, f: Term, p: Pred, target: usize) -> usize {
        // record predecessor edge
        self.contexts[target]
            .predecessors
            .entry((from, f))
            .or_default()
            .insert(p);
        // a new edge / pushed predicate may let existing worked-off clauses be
        // pushed back to this predecessor, so the next propagate must re-scan.
        self.contexts[target].dirty = true;
        // Succ rule: add hypothesis clause p -> p. The batch driver saturates
        // the target unconditionally after all messages have been accumulated:
        // under the central strategy a FACT trigger's hypothesis is subsumed by
        // the core's `-> p` (add_clause returns false), while a disjunctively
        // derived trigger's hypothesis is genuinely new and saturates — its
        // consequences come back conditioned on `p` alone, which is what the
        // per-disjunct cuts need.  Either way the core clauses seeded at
        // context creation still sit in `todo` and must be worked off.
        let root = self.contexts[target].root;
        let c = ContextClause::new(vec![p], vec![Lit::P(p)], root, &self.sig);
        self.add_clause(target, c);
        target
    }

    /// Apply a Pred message: back-substitute and add the resulting pred clause /
    /// resolvents. Returns `to`; the caller saturates and propagates it once at
    /// the end of the message batch (see `apply_succ`).
    fn apply_pred(&mut self, to: usize, from: usize, edge_label: Term, pool_idx: u32) -> usize {
        if !self.prof_time {
            let pc = self.pred_payload(from, edge_label, pool_idx);
            return self.apply_pred_payload(to, pc);
        }
        let t = std::time::Instant::now();
        let pc = self.pred_payload(from, edge_label, pool_idx);
        prof_add(&PREDPAYLOAD_NS, t);
        let t = std::time::Instant::now();
        let r = self.apply_pred_payload(to, pc);
        prof_add(&PREDARRIVAL_NS, t);
        r
    }

    /// The sender-side half of a Pred message: back-substitute the sender's
    /// pool entry + core into the pred clause that crosses the edge. Reads only
    /// the (immutable) sender context `from` — `&self`, no mutation — so it is
    /// safe to call for every batched message up front, before any target is
    /// mutated. Isolating this read is what lets `apply_pred_payload` run in
    /// parallel across distinct targets without a sender/target aliasing race on
    /// the sender's append-only `pred_pool`.
    fn pred_payload(&self, from: usize, edge_label: Term, pool_idx: u32) -> PredClause {
        // Back-substitute: y -> x, x -> f(x).  The sender's pool entry and core
        // are immutable once created, so resolving them here reads exactly the
        // snapshot a send-time copy would have carried.
        let from_ctx = &self.contexts[from];
        let arena = &self.cc_arena[from_ctx.root as usize];
        let clause = &arena[from_ctx.pred_pool[pool_idx as usize] as usize];
        let f = edge_label;
        let subst = |v: Term| backwards(f, v);
        let mut body: Vec<Pred> = clause.body.iter().map(|p| p.apply(&subst)).collect();
        for p in &from_ctx.core {
            body.push(p.apply(&subst));
        }
        // Full literals: pool-eligible heads are predicates plus (nominal
        // mode) the individual equality forms; `x ≈ o` crosses as
        // `f(x) ≈ o`, which the receiver's Eq rule then rewrites.
        // Substitution plus the appended sender core can collapse predicates
        // that were distinct before crossing the edge.  PredClause denotes
        // conjunction/disjunction sets, exactly like ContextClause, so
        // normalize here before interning and before the receiver constructs a
        // Cartesian join.  Leaving duplicates in `body` enumerated the same
        // logical premise combination exponentially many times.
        body.sort();
        body.dedup();
        let mut head: Vec<Lit> = clause.head.iter().map(|l| l.apply(&subst)).collect();
        head.sort();
        head.dedup();
        PredClause { body, head }
    }

    /// The receiver-side half of a Pred message: intern the back-substituted
    /// clause, dedup against prior arrivals, and fire the Pred rule against
    /// `to`'s already-worked-off clauses. Newly added local clauses remain in
    /// `todo`; batch-end saturation both processes them and fires local Pred
    /// against every neighbor clause received in this batch. Mutates only
    /// context `to` (plus the shared arena / intern tables). Returns `to`.
    fn apply_pred_payload(&mut self, to: usize, pc: PredClause) -> usize {
        let pid = self.intern_pred(pc);
        let msgprof = !self.stat_pred_out_by_ctx.is_empty();
        // Duplicate arrival (same substituted clause already received, e.g. from
        // a successor's pre- and post-growth contexts): everything it could
        // contribute was already derived, so skip the re-derivation.
        if !self.contexts[to].neighbor_pred_seen.insert(pid) {
            if msgprof {
                self.stat_pred_dup_arrival += 1;
            }
            return to;
        }
        self.contexts[to].neighbor_pred.push(pid);
        for &predicate in &self.pred_interned[pid as usize].body {
            self.contexts[to]
                .neighbor_pred_body_index
                .entry(predicate)
                .or_default()
                .push(pid);
        }
        // Apply Pred rule against worked-off clauses of `to`.
        let root = self.contexts[to].root;
        let results = {
            let pc = &self.pred_interned[pid as usize];
            self.pred_from_neighbor(to, pc, root)
        };
        if msgprof {
            if results.is_empty() {
                self.stat_pred_empty_join += 1;
            }
            self.stat_pred_conclusions += results.len() as u64;
        }
        for r in results {
            let fresh = self.add_clause(to, r);
            if msgprof && fresh {
                self.stat_pred_conclusions_new += 1;
            }
        }
        to
    }

    /// Pred rule for a freshly received neighbor pred clause: resolve its
    /// body predicates against worked-off clauses of context `id`. Ground
    /// body atoms (nominal mode) resolve like the others when a provider
    /// exists and are otherwise copied verbatim to the resolvent body (the
    /// C_i of arXiv:1805.01396 Pred / r-Pred).
    ///
    /// Sequoia's `Rules.Pred` enumerates the full Cartesian product and retains
    /// only its strengthening antichain. We compute exactly that antichain as a
    /// left-deep join: after each premise, remove redundant partial unions before
    /// joining the next premise. If partial P strengthens Q, then P union R
    /// strengthens Q union R for every choice R from all remaining premises.
    /// Consequently every extension pruned here has a stronger extension in the
    /// final product. This changes join order and allocation only, not the Pred
    /// conclusions admitted to the context fixpoint.
    fn pred_from_neighbor(&self, id: usize, pc: &PredClause, root: bool) -> Vec<ContextClause> {
        let ctx = &self.contexts[id];
        let arena = &self.cc_arena[root as usize];
        let mut ground: Vec<Pred> = Vec::new();
        let mut candidates: Vec<Vec<(usize, Pred)>> = Vec::with_capacity(pc.body.len());
        for &bp in &pc.body {
            let mut v = Vec::new();
            if let Some(cand) = ctx.max_head_pred_index.get(&bp) {
                v.extend(cand.iter().map(|&ci| (ci as usize, bp)));
            }
            if v.is_empty() {
                if bp.is_ground() {
                    ground.push(bp);
                    continue;
                }
                return Vec::new(); // a body predicate has no provider: no resolvent
            }
            candidates.push(v);
        }
        trace_pred_product("arrival", id, None, pc, &ground, &candidates);
        // A smaller dimension first normally minimizes the live partial
        // antichain. Dimension order cannot affect the set union represented by
        // a complete selection from the Cartesian product.
        candidates.sort_by_key(Vec::len);

        let Some(head) = self.filter_head(pc.head.clone()) else {
            return Vec::new();
        };
        let mut partials = vec![ContextClause::new(ground, head, root, &self.sig)];
        for dimension in candidates {
            let mut next = PredResultBuffer::default();
            for partial in partials {
                for &(ci, matched) in &dimension {
                    let provider = &arena[ci];
                    let mut body = partial.body.clone();
                    body.extend_from_slice(&provider.body);
                    let mut head = partial.head.clone();
                    for &literal in &provider.head {
                        if literal != Lit::P(matched) {
                            head.push(literal);
                        }
                    }
                    if let Some(head) = self.filter_head(head) {
                        push_nonredundant_pred_result(
                            &mut next,
                            ContextClause::new(body, head, root, &self.sig),
                        );
                    }
                }
            }
            partials = next.into_vec();
            if partials.is_empty() {
                break;
            }
        }
        partials
    }

    // ------------------------------ driver ---------------------------------

    /// All named (non-internal, non-Nothing) concepts, i.e. the default query set.
    pub fn named_queries(&self) -> Vec<Iri> {
        (0..self.sig.concept_names.len() as Iri)
            .filter(|&i| !self.sig.is_internal(i) && !self.sig.is_nothing_concept(i))
            .collect()
    }

    pub fn run(&mut self) {
        let named = self.named_queries();
        self.run_for(&named);
    }

    /// Classify exactly the given query concepts (seed one root context each,
    /// then run the inter-context message fixpoint).  Each query's subsumptions
    /// are independent of which other queries are co-classified -- the shared
    /// successor context is only an optimisation -- so classifying a subset is
    /// sound and yields identical results for those concepts.  This is what lets
    /// classification be parallelised across disjoint concept chunks.
    /// KM_MSGPROF diagnostic: which contexts emit the Pred traffic.  Prints the
    /// `n` heaviest senders with the shape that explains the volume
    /// (`pool` x `preds` is the per-round upper bound on a sender's fan-out).
    /// Inert unless `KM_MSGPROF` armed `stat_pred_out_by_ctx`.
    fn report_pred_pressure(&self, n: usize) {
        if self.stat_pred_out_by_ctx.is_empty() {
            return;
        }
        let mut rank: Vec<(u64, usize)> = self
            .stat_pred_out_by_ctx
            .iter()
            .enumerate()
            .filter(|&(_, &v)| v > 0)
            .map(|(i, &v)| (v, i))
            .collect();
        rank.sort_unstable_by(|a, b| b.cmp(a));
        let total: u64 = rank.iter().map(|&(v, _)| v).sum();
        eprintln!(
            "KM_MSGPROF arrivals dup={} empty_join={} conclusions={} conclusions_new={} ({:.2}% new) | arena[succ]={} arena[root]={} pred_interned={} ctx_clause_slots={}",
            self.stat_pred_dup_arrival,
            self.stat_pred_empty_join,
            self.stat_pred_conclusions,
            self.stat_pred_conclusions_new,
            100.0 * self.stat_pred_conclusions_new as f64
                / self.stat_pred_conclusions.max(1) as f64,
            self.cc_arena[0].len(),
            self.cc_arena[1].len(),
            self.pred_interned.len(),
            self.contexts.iter().map(|c| c.clause_keys.len()).sum::<usize>(),
        );
        for &(sent, id) in rank.iter().take(n) {
            let c = &self.contexts[id];
            eprintln!(
                "KM_MSGPROF sender ctx={} root={} query={:?} pred_sent={} ({:.1}%) pool={} preds={} wo={} core={}",
                id,
                c.root,
                c.query,
                sent,
                100.0 * sent as f64 / total.max(1) as f64,
                c.pred_pool.len(),
                c.predecessors.len(),
                c.worked_off.len(),
                c.core.len(),
            );
        }
    }

    pub fn run_for(&mut self, queries: &[Iri]) {
        let prof = std::env::var("KM_PROF").is_ok();
        if std::env::var_os("KM_MSGPROF").is_some() && self.stat_pred_out_by_ctx.is_empty() {
            self.stat_pred_out_by_ctx = vec![0u64; self.contexts.len().max(1)];
        }
        // KM_CTXSPLIT: one-shot diagnostic for the shared-successor parallel
        // strategy. Splits wall time into root-seeding (per-query, parallelisable)
        // vs the inter-context message fixpoint (builds the query-independent
        // successor graph), and splits worked-off clauses into root vs successor
        // contexts. Tells whether sharing the successor graph across query-parallel
        // workers can recover the central-OOM cluster, or whether the bottleneck
        // is the (sequential) successor build itself.
        let ctxsplit = std::env::var("KM_CTXSPLIT").is_ok();
        let t_start = std::time::Instant::now();
        // Ground (nominal root) context: eager when the ontology has ground
        // facts — a contradiction among the individuals alone (detected only
        // here) is global inconsistency, independent of any query.
        if !self.ont.ground_facts.is_empty() {
            let gid = self.ground_context();
            self.propagate(gid);
        }
        self.complete_nominal_enumeration_queries(queries);
        // Root contexts: one per named (query) concept.
        for (qi, &iri) in queries.iter().enumerate() {
            if self.nominal_shortcuts.contains_key(&iri) {
                continue;
            }
            let core = vec![Pred::Concept { iri, t: X }];
            let id = self.get_or_create_context(core, true, Some(iri));
            self.saturate(id);
            self.propagate(id);
            if prof && (qi + 1) % 50 == 0 {
                eprintln!(
                    "KM_PROF seeding query {}/{} contexts={} msgs_pending={} saturate_calls={}",
                    qi + 1,
                    queries.len(),
                    self.contexts.len(),
                    self.msgs.len(),
                    self.stat_saturate
                );
            }
        }
        if prof {
            eprintln!(
                "KM_PROF seeded all {} queries; contexts={} msgs_pending={} saturate_calls={}",
                queries.len(),
                self.contexts.len(),
                self.msgs.len(),
                self.stat_saturate
            );
        }
        // Always seed the ⊤ (empty-core) context so a *global* inconsistency
        // (owl:Thing unsatisfiable) is detected regardless of which concepts are
        // named in the input (audit M2). It carries query=None, so `subsumptions`
        // skips it and it never contributes to the classification output.
        let top = self.get_or_create_context(vec![], true, None);
        self.saturate(top);
        self.propagate(top);
        let t_seed = t_start.elapsed();
        // Process inter-context messages to fixpoint, *batched*: drain the whole
        // pending set, apply every message as a clause/edge delta, record the
        // touched contexts, then saturate and propagate each touched context
        // exactly once. Applying a message never enqueues new messages (only
        // `propagate` does), so a batch is self-contained and the next batch is
        // the propagation output. Completing once per target and batch avoids
        // replaying saturation and re-scanning predecessor-edge and Succ/Pred
        // pools thousands of times on assertion-heavy or role-chain ontologies.
        // The fixpoint is unchanged: saturation is monotone and confluent, so
        // the derived clause set is independent of the completion schedule.
        let mut guard = 0usize;
        let (mut nsucc_msgs, mut npred_msgs) = (0u64, 0u64);
        let trace = std::env::var("KM_TRACE").is_ok();
        // Hard safety cap on the inter-context message fixpoint (backstop against
        // a runaway central-strategy core-growth cascade). Configurable via
        // KM_MSG_CAP; default 25M. Raising it trades time/memory for completeness
        // on heavy role-chain/transitive ontologies whose fixpoint is large but
        // finite -- e.g. ore_ont_9944 needs ~13.8M messages to converge (and
        // derives ~15k more subsumptions than the truncated 5M run); the per-run
        // time/memory limits remain the real guard for genuinely pathological
        // inputs, so honest convergence is preferred over silent truncation.
        let msg_cap: usize = std::env::var("KM_MSG_CAP")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(25_000_000);
        // Diagnostic opt-out retains the former one-saturation-per-message
        // schedule for byte/result A/B checks of batched completion.
        let batch_completion = std::env::var_os("KM_NO_BATCH_COMPLETION").is_none();
        let mut truncated = false;
        while !self.msgs.is_empty() {
            let batch: Vec<Msg> = self.msgs.drain(..).collect();
            let mut touched: Vec<usize> = Vec::new();
            let mut seen: HashSet<usize> = HashSet::new();
            for msg in batch {
                guard += 1;
                if guard > msg_cap {
                    // Hard safety cap on the inter-context message fixpoint.
                    // Hitting it means the run was truncated, so the
                    // classification may be INCOMPLETE -- never silently: warn on
                    // stderr (audit L1/L2). Sound (only consequences are
                    // dropped), but completeness is not guaranteed for this run.
                    eprintln!(
                        "WARNING: kobayashi-marust message fixpoint hit the {} cap; \
                         classification may be incomplete (truncated). {} pending messages dropped.",
                        msg_cap, self.msgs.len()
                    );
                    truncated = true;
                    self.message_truncated = true;
                    break;
                }
                if prof && guard % 20000 == 0 {
                    let gwo = self
                        .ground_ctx
                        .map(|g| self.contexts[g].worked_off.len())
                        .unwrap_or(0);
                    eprintln!(
                        "KM_PROF msgloop guard={} contexts={} msgs_pending={} saturate_calls={} succ={} pred={} ground_wo={}",
                        guard, self.contexts.len(), self.msgs.len(), self.stat_saturate,
                        nsucc_msgs, npred_msgs, gwo
                    );
                    self.report_pred_pressure(8);
                    if self.prof_time {
                        let ms = |cell: &'static std::thread::LocalKey<std::cell::Cell<u64>>| {
                            cell.with(|value| value.get()) as f64 / 1e6
                        };
                        eprintln!(
                            "KM_PROF[time-ms] msgloop pred_payload={:.1} pred_arrival={:.1} propagate={:.1} | add_clause={:.1} (lookup={:.1} fwdsub={:.1} backsub={:.1} index={:.1}) hyper={:.1} subsume={:.1} pred_local={:.1} eq={:.1} saturate={:.1}",
                            ms(&PREDPAYLOAD_NS),
                            ms(&PREDARRIVAL_NS),
                            ms(&PROPAGATE_NS),
                            ms(&ADDCLAUSE_NS),
                            ms(&ADD_LOOKUP_NS),
                            ms(&ADD_FWDSUB_NS),
                            ms(&ADD_BACKSUB_NS),
                            ms(&ADD_INDEX_NS),
                            ms(&HYPER_NS),
                            ms(&SUBSUME_NS),
                            ms(&PREDLOCAL_NS),
                            ms(&EQRULE_NS),
                            ms(&SATURATE_NS),
                        );
                    }
                }
                if trace && guard % 200_000 == 0 {
                    let (mut maxb, mut totwo) = (0usize, 0usize);
                    // Head-size histogram (h1/h2/h3/h4plus) + max head, to tell a
                    // disjunctive-blowup (many incomparable multi-head clauses) from
                    // a Horn one. `topwo` = largest single-context worked_off.
                    let (mut h1, mut h2, mut h3, mut h4p, mut maxh, mut topwo) =
                        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);
                    for c in &self.contexts {
                        let arena = &self.cc_arena[c.root as usize];
                        totwo += c.worked_off.len();
                        if c.worked_off.len() > topwo {
                            topwo = c.worked_off.len();
                        }
                        for &ci in &c.worked_off {
                            let cl = &arena[ci as usize];
                            if cl.body.len() > maxb {
                                maxb = cl.body.len();
                            }
                            if cl.head.len() > maxh {
                                maxh = cl.head.len();
                            }
                            match cl.head.len() {
                                0 | 1 => h1 += 1,
                                2 => h2 += 1,
                                3 => h3 += 1,
                                _ => h4p += 1,
                            }
                        }
                    }
                    eprintln!(
                        "KM_TRACE guard={} contexts={} msgs_pending={} worked_off_total={} \
                         max_body_len={} max_head_len={} top_ctx_wo={} head[<=1={} 2={} 3={} >=4={}]",
                        guard, self.contexts.len(), self.msgs.len(), totwo, maxb, maxh,
                        topwo, h1, h2, h3, h4p
                    );
                }
                let t = match msg {
                    Msg::Succ { from, f, p, target } => {
                        nsucc_msgs += 1;
                        self.apply_succ(from, f, p, target)
                    }
                    Msg::Pred {
                        to,
                        from,
                        edge_label,
                        pool_idx,
                    } => {
                        npred_msgs += 1;
                        self.apply_pred(to, from, edge_label, pool_idx)
                    }
                };
                if !batch_completion {
                    self.saturate(t);
                }
                if seen.insert(t) {
                    touched.push(t);
                }
            }
            if truncated {
                break;
            }
            // Message application above only accumulates edge data and local
            // clauses. Complete each touched context once for this round, then
            // propagate its combined delta. Saturation is monotone and local
            // Pred joins every newly worked-off clause with all neighbor clauses
            // accumulated in the batch, so this schedule reaches the same
            // fixpoint as saturating after every individual message.
            if batch_completion {
                for &id in &touched {
                    self.saturate(id);
                }
            }
            for id in touched {
                self.propagate(id);
            }
        }
        if ctxsplit {
            let t_total = t_start.elapsed();
            let t_fix = t_total.saturating_sub(t_seed);
            // Per-class context + worked-off + pred-pool split.
            let (mut qroot_n, mut other_root_n, mut succ_n) = (0usize, 0usize, 0usize);
            let (mut qroot_wo, mut other_root_wo, mut succ_wo) = (0usize, 0usize, 0usize);
            let (mut qroot_np, mut succ_np) = (0usize, 0usize);
            // largest successor contexts (the shared-build hot spots)
            let mut succ_sizes: Vec<usize> = Vec::new();
            let mut top_succ: usize = 0;
            for c in &self.contexts {
                let wo = c.worked_off.len();
                let np = c.neighbor_pred.len();
                if c.root && c.query.is_some() {
                    qroot_n += 1;
                    qroot_wo += wo;
                    qroot_np += np;
                } else if c.root {
                    other_root_n += 1;
                    other_root_wo += wo;
                } else {
                    succ_n += 1;
                    succ_wo += wo;
                    succ_np += np;
                    succ_sizes.push(wo);
                    if wo > top_succ {
                        top_succ = wo;
                    }
                }
            }
            succ_sizes.sort_unstable_by(|a, b| b.cmp(a));
            let top10_succ_wo: usize = succ_sizes.iter().take(10).sum();
            let total_wo = qroot_wo + other_root_wo + succ_wo;
            eprintln!(
                "KM_CTXSPLIT queries={} | t_seed_ms={} t_msgfix_ms={} t_total_ms={} \
                 (seed={:.0}% fix={:.0}%) | succ_msgs={} pred_msgs={} guard={}",
                queries.len(),
                t_seed.as_millis(),
                t_fix.as_millis(),
                t_total.as_millis(),
                100.0 * t_seed.as_secs_f64() / t_total.as_secs_f64().max(1e-9),
                100.0 * t_fix.as_secs_f64() / t_total.as_secs_f64().max(1e-9),
                nsucc_msgs,
                npred_msgs,
                guard
            );
            eprintln!(
                "KM_CTXSPLIT contexts: qroot={} other_root={} succ={} | \
                 worked_off: qroot={} ({:.0}%) other_root={} succ={} ({:.0}%) total={} | \
                 succ neighbor_pred={} qroot neighbor_pred={} | top_succ_wo={} top10_succ_wo={}",
                qroot_n,
                other_root_n,
                succ_n,
                qroot_wo,
                100.0 * qroot_wo as f64 / (total_wo.max(1)) as f64,
                other_root_wo,
                succ_wo,
                100.0 * succ_wo as f64 / (total_wo.max(1)) as f64,
                total_wo,
                succ_np,
                qroot_np,
                top_succ,
                top10_succ_wo
            );
        }
        if std::env::var("KM_DUMP_WO").is_ok() {
            let fmt_t = |t: Term| -> String {
                if t == X {
                    "x".to_string()
                } else if t == Y {
                    "y".to_string()
                } else if is_neighbour(t) {
                    format!("z{}", Y - t)
                } else {
                    format!("f{}(x)", t)
                }
            };
            let fmt_p = |p: &Pred| -> String {
                match *p {
                    Pred::Concept { iri, t } => {
                        format!("{}({})", self.sig.concept_names[iri as usize], fmt_t(t))
                    }
                    Pred::Role { iri, s, t } => format!(
                        "{}({},{})",
                        self.sig.role_names[iri as usize],
                        fmt_t(s),
                        fmt_t(t)
                    ),
                }
            };
            let fmt_l = |l: &Lit| -> String {
                match *l {
                    Lit::P(p) => fmt_p(&p),
                    Lit::Eq { s, t } => format!("{}={}", fmt_t(s), fmt_t(t)),
                    Lit::Ineq { s, t } => format!("{}!={}", fmt_t(s), fmt_t(t)),
                }
            };
            for ctx in &self.contexts {
                let core: Vec<String> = ctx.core.iter().map(&fmt_p).collect();
                eprintln!(
                    "== ctx {} root={} query={:?} core=[{}] wo={}",
                    ctx.id,
                    ctx.root,
                    ctx.query
                        .map(|i| self.sig.concept_names[i as usize].clone()),
                    core.join(", "),
                    ctx.worked_off.len()
                );
                let arena = &self.cc_arena[ctx.root as usize];
                for &ci in &ctx.worked_off {
                    let c = &arena[ci as usize];
                    let b: Vec<String> = c.body.iter().map(&fmt_p).collect();
                    let h: Vec<String> = c.head.iter().map(&fmt_l).collect();
                    eprintln!(
                        "   {} -> {}",
                        if b.is_empty() {
                            "T".to_string()
                        } else {
                            b.join(" & ")
                        },
                        if h.is_empty() {
                            "F".to_string()
                        } else {
                            h.join(" | ")
                        }
                    );
                }
            }
        }
        if let Ok(pat) = std::env::var("KM_TRACE_C") {
            // Substring-filtered context dump: only contexts whose core or
            // worked-off set mentions a concept/role name containing any of the
            // comma-separated needles.  Keeps output tractable on full ORE onts
            // when tracing one query's reachability propagation.
            let needles: Vec<String> = pat.split(',').map(|s| s.to_string()).collect();
            let fmt_t = |t: Term| -> String {
                if t == X {
                    "x".to_string()
                } else if t == Y {
                    "y".to_string()
                } else if is_neighbour(t) {
                    format!("z{}", Y - t)
                } else {
                    format!("f{}(x)", t)
                }
            };
            let nm_c = |iri: u32| self.sig.concept_names[iri as usize].clone();
            let nm_r = |iri: u32| self.sig.role_names[iri as usize].clone();
            let fmt_p = |p: &Pred| -> String {
                match *p {
                    Pred::Concept { iri, t } => format!("{}({})", nm_c(iri), fmt_t(t)),
                    Pred::Role { iri, s, t } => format!("{}({},{})", nm_r(iri), fmt_t(s), fmt_t(t)),
                }
            };
            let fmt_l = |l: &Lit| -> String {
                match *l {
                    Lit::P(p) => fmt_p(&p),
                    Lit::Eq { s, t } => format!("{}={}", fmt_t(s), fmt_t(t)),
                    Lit::Ineq { s, t } => format!("{}!={}", fmt_t(s), fmt_t(t)),
                }
            };
            let hit = |p: &Pred| -> bool {
                let n = match *p {
                    Pred::Concept { iri, .. } => nm_c(iri),
                    Pred::Role { iri, .. } => nm_r(iri),
                };
                needles.iter().any(|nd| n.contains(nd.as_str()))
            };
            for ctx in &self.contexts {
                let arena = &self.cc_arena[ctx.root as usize];
                let touch = ctx.core.iter().any(&hit)
                    || ctx.worked_off.iter().any(|&ci| {
                        let c = &arena[ci as usize];
                        c.body.iter().any(&hit)
                            || c.head.iter().any(|l| matches!(l, Lit::P(p) if hit(p)))
                    });
                if !touch {
                    continue;
                }
                let core: Vec<String> = ctx.core.iter().map(&fmt_p).collect();
                eprintln!(
                    "== ctx {} root={} query={:?} core=[{}] preds={} wo={}",
                    ctx.id,
                    ctx.root,
                    ctx.query.map(|i| nm_c(i)),
                    core.join(", "),
                    ctx.predecessors.len(),
                    ctx.worked_off.len()
                );
                let mut succs: Vec<String> = ctx
                    .successors
                    .iter()
                    .map(|(f, sid)| format!("f{}->{}", f, sid))
                    .collect();
                succs.sort();
                eprintln!("   SUCC: {}", succs.join(" "));
                let mut preds: Vec<String> = ctx
                    .predecessors
                    .keys()
                    .map(|(pid, f)| format!("{}@f{}", pid, f))
                    .collect();
                preds.sort();
                eprintln!("   PRED-OF: {}", preds.join(" "));
                for &ci in &ctx.worked_off {
                    let c = &arena[ci as usize];
                    // only print clauses mentioning a needle (keeps it focused)
                    let rel = c.body.iter().any(&hit)
                        || c.head.iter().any(|l| matches!(l, Lit::P(p) if hit(p)));
                    if !rel {
                        continue;
                    }
                    let b: Vec<String> = c.body.iter().map(&fmt_p).collect();
                    let h: Vec<String> = c.head.iter().map(&fmt_l).collect();
                    eprintln!(
                        "   {} -> {}",
                        if b.is_empty() {
                            "T".to_string()
                        } else {
                            b.join(" & ")
                        },
                        if h.is_empty() {
                            "F".to_string()
                        } else {
                            h.join(" | ")
                        }
                    );
                }
            }
        }
        if std::env::var("KM_STATS").is_ok() {
            let nroot = self.contexts.iter().filter(|c| c.root).count();
            let nsucc = self.contexts.iter().filter(|c| !c.root).count();
            let root_wo: usize = self
                .contexts
                .iter()
                .filter(|c| c.root)
                .map(|c| c.worked_off.len())
                .sum();
            let succ_wo: usize = self
                .contexts
                .iter()
                .filter(|c| !c.root)
                .map(|c| c.worked_off.len())
                .sum();
            let top_wo = self
                .contexts
                .iter()
                .find(|c| c.root && c.core.is_empty())
                .map(|c| c.worked_off.len())
                .unwrap_or(0);
            eprintln!(
                "KM_STATS contexts={} roots={} succs={} root_wo_total={} succ_wo_total={} top_wo={} avg_root_wo={:.0}",
                self.contexts.len(), nroot, nsucc, root_wo, succ_wo, top_wo,
                root_wo as f64 / nroot.max(1) as f64
            );
            eprintln!(
                "KM_STATS propagate={} pred_checks={} succ_scans={} hyper_calls={} saturate={}",
                self.stat_propagate,
                self.stat_pred_checks,
                self.stat_succ_scans,
                HYPER_CALLS.with(|c| c.get()),
                self.stat_saturate
            );
            if self.prof_time {
                let ms = |c: &'static std::thread::LocalKey<std::cell::Cell<u64>>| {
                    c.with(|x| x.get()) as f64 / 1e6
                };
                eprintln!(
                    "KM_STATS[time-ms] subsume={:.1} hyper={:.1} pred_local={:.1} add_clause={:.1} eq={:.1} propagate={:.1}",
                    ms(&SUBSUME_NS),
                    ms(&HYPER_NS),
                    ms(&PREDLOCAL_NS),
                    ms(&ADDCLAUSE_NS),
                    ms(&EQRULE_NS),
                    ms(&PROPAGATE_NS),
                );
            }
        }
        if std::env::var("KM_MEMSTATS").is_ok() {
            // Exact-ish accounting of where context memory sits (heap data via
            // capacity(); hash-table load factors not modelled, so map/set
            // figures are lower bounds). Diagnostics only -- no effect on
            // reasoning.
            use std::mem::size_of;
            let szp = size_of::<Pred>();
            let szl = size_of::<Lit>();
            let szcc = size_of::<ContextClause>();
            let cc_heap = |c: &ContextClause| {
                // max_head is now a u64 mask inside the struct (no heap).
                c.body.capacity() * szp + c.head.capacity() * szl
            };
            let mut cat: Vec<(&str, usize, usize)> = Vec::new(); // (name, count, bytes)
            let mut add = |name: &'static str, n: usize, b: usize| {
                if let Some(e) = cat.iter_mut().find(|e| e.0 == name) {
                    e.1 += n;
                    e.2 += b;
                } else {
                    cat.push((name, n, b));
                }
            };
            for ctx in &self.contexts {
                add("core", ctx.core.len(), ctx.core.capacity() * szp);
                add(
                    "worked_off(ids)",
                    ctx.worked_off.len(),
                    ctx.worked_off.capacity() * 4,
                );
                add(
                    "clause_keys(ids)",
                    ctx.clause_keys.len(),
                    ctx.clause_keys.len() * 12,
                );
                add(
                    "head_indexes",
                    ctx.head_concept_index.len()
                        + ctx.head_role_index.len()
                        + ctx.max_head_pred_index.len()
                        + ctx.max_head_term_index.len(),
                    ctx.head_concept_index
                        .values()
                        .map(|v| 24 + 4 + v.capacity() * 4)
                        .sum::<usize>()
                        + ctx
                            .head_role_index
                            .values()
                            .map(|v| 24 + 4 + v.capacity() * 4)
                            .sum::<usize>()
                        + ctx
                            .max_head_pred_index
                            .values()
                            .map(|v| 24 + szp + v.capacity() * 4)
                            .sum::<usize>()
                        + ctx
                            .max_head_term_index
                            .values()
                            .map(|v| 24 + std::mem::size_of::<Term>() + v.capacity() * 4)
                            .sum::<usize>(),
                );
                add(
                    "redundancy_postings",
                    ctx.active_empty_head.len()
                        + ctx
                            .active_head_lit_index
                            .values()
                            .map(|posting| posting.len())
                            .sum::<usize>(),
                    ctx.active_empty_head.capacity() * 4
                        + ctx
                            .active_head_lit_index
                            .values()
                            .map(|v| 24 + std::mem::size_of::<Lit>() + v.capacity() * 4)
                            .sum::<usize>(),
                );
                add("todo", ctx.todo.len(), ctx.todo.capacity() * 4);
                add(
                    "neighbor_pred(ids)",
                    ctx.neighbor_pred.len(),
                    ctx.neighbor_pred.capacity() * 4 + ctx.neighbor_pred_seen.len() * 12,
                );
                add(
                    "trigger_sets",
                    ctx.trigger_sets.values().map(|s| s.len()).sum::<usize>()
                        + ctx
                            .fact_trigger_sets
                            .values()
                            .map(|s| s.len())
                            .sum::<usize>(),
                    ctx.trigger_sets
                        .values()
                        .map(|s| 24 + s.len() * (szp + 8))
                        .sum::<usize>()
                        + ctx
                            .fact_trigger_sets
                            .values()
                            .map(|s| 24 + s.len() * (szp + 8))
                            .sum::<usize>(),
                );
                add(
                    "predecessor_edges(pushed)",
                    ctx.predecessors.values().map(|s| s.len()).sum(),
                    ctx.predecessors
                        .values()
                        .map(|s| 24 + s.len() * (szp + 8))
                        .sum(),
                );
                add(
                    "pushed_succ",
                    ctx.pushed_succ.len(),
                    ctx.pushed_succ.len() * (szp + 8),
                );
                add(
                    "pushed_pred(idx)",
                    ctx.pushed_pred.values().map(|s| s.len()).sum(),
                    ctx.pushed_pred.values().map(|s| 40 + s.len() * 12).sum(),
                );
                add(
                    "pred_pool(ids)",
                    ctx.pred_pool.len(),
                    ctx.pred_pool.capacity() * 4,
                );
                add(
                    "succ_pool(ids)",
                    ctx.succ_pool.len(),
                    ctx.succ_pool.capacity() * 4,
                );
                add(
                    "edges_misc",
                    ctx.successors.len() + ctx.edge_seen.len(),
                    ctx.successors.len() * 24 + ctx.edge_seen.len() * 32,
                );
            }
            add(
                "core_index(engine)",
                self.core_index.len(),
                self.core_index.len() * 40
                    + self
                        .core_index
                        .values()
                        .map(|v| v.capacity() * 8)
                        .sum::<usize>(),
            );
            add(
                "pred_interned(engine)",
                self.pred_interned.len(),
                self.pred_interned.capacity() * 48
                    + self
                        .pred_interned
                        .iter()
                        .map(|p| (p.body.capacity() + p.head.capacity()) * szp)
                        .sum::<usize>()
                    + self.pred_intern_idx.len() * 40
                    + self
                        .pred_intern_idx
                        .values()
                        .map(|v| v.capacity() * 4)
                        .sum::<usize>(),
            );
            add(
                "cc_arena(engine)",
                self.cc_arena[0].len() + self.cc_arena[1].len(),
                self.cc_arena
                    .iter()
                    .map(|a| a.capacity() * szcc + a.iter().map(&cc_heap).sum::<usize>())
                    .sum::<usize>()
                    + self
                        .cc_intern_idx
                        .iter()
                        .map(|m| m.len() * 40 + m.values().map(|v| v.capacity() * 4).sum::<usize>())
                        .sum::<usize>(),
            );
            // O(distinct clauses), not O(context slots): the point of the table
            // is that this line stays ≈33x below any per-slot category.
            add(
                "cc_facets(engine)",
                self.cc_facets[0].keys.len() + self.cc_facets[1].keys.len(),
                self.cc_facets
                    .iter()
                    .map(|f| {
                        f.keys.capacity() * std::mem::size_of::<Facet>()
                            + f.starts.capacity() * 4
                            + f.flags.capacity() * std::mem::size_of::<ClauseFlags>()
                    })
                    .sum::<usize>(),
            );
            cat.sort_by(|a, b| b.2.cmp(&a.2));
            let total: usize = cat.iter().map(|e| e.2).sum();
            eprintln!(
                "KM_MEMSTATS sizeof Pred={} Lit={} ContextClause={} | contexts={} | accounted={:.1} MB",
                szp, szl, szcc, self.contexts.len(), total as f64 / 1e6
            );
            for (name, n, b) in &cat {
                eprintln!(
                    "KM_MEMSTATS {:>9.1} MB {:>5.1}% n={:<12} {}",
                    *b as f64 / 1e6,
                    100.0 * *b as f64 / total.max(1) as f64,
                    n,
                    name
                );
            }
        }
        if std::env::var("SROIQ_DEBUG").is_ok() {
            for ctx in &self.contexts {
                let arena = &self.cc_arena[ctx.root as usize];
                eprintln!(
                    "ctx {} root={} core={:?} #wo={}",
                    ctx.id,
                    ctx.root,
                    ctx.core,
                    ctx.worked_off.len()
                );
                for &ci in &ctx.worked_off {
                    let c = &arena[ci as usize];
                    eprintln!("    {:?} -> {:?}", c.body, c.head);
                }
            }
        }
    }

    // ------------------------------ output ---------------------------------

    /// For each root context (core = {A(x)}), the entailed atomic subsumptions
    /// `A ⊑ B`: clauses `-> B(x)` (empty body, single head concept on x).
    pub fn subsumptions(&self) -> Vec<(String, Vec<String>)> {
        let mut out = Vec::new();
        for ctx in &self.contexts {
            if !ctx.root {
                continue;
            }
            let a = match ctx.query {
                Some(iri) => self.sig.concept_names[iri as usize].clone(),
                None => continue,
            };
            let arena = &self.cc_arena[ctx.root as usize];
            let mut supers: Vec<String> = Vec::new();
            let unsat = ctx.worked_off.iter().any(|&ci| {
                let c = &arena[ci as usize];
                c.body.is_empty() && c.head.is_empty()
            });
            if unsat {
                supers.push("owl:Nothing".to_string());
            }
            for &ci in &ctx.worked_off {
                let c = &arena[ci as usize];
                if c.body.is_empty() && c.head.len() == 1 {
                    if let Lit::P(Pred::Concept { iri, t }) = c.head[0] {
                        if is_central(t) {
                            let name = self.sig.concept_names[iri as usize].clone();
                            if name != a {
                                supers.push(name);
                            }
                        }
                    }
                }
            }
            supers.sort();
            supers.dedup();
            out.push((a, supers));
        }
        for (&query, supers) in &self.nominal_shortcuts {
            let a = self.sig.concept_names[query as usize].clone();
            let mut names: Vec<String> = supers
                .iter()
                .filter(|&&iri| iri != query)
                .map(|&iri| self.sig.concept_names[iri as usize].clone())
                .collect();
            names.sort();
            names.dedup();
            out.push((a, names));
        }
        // A direct `C(x) -> bottom` clause marks C as a nothing-concept and
        // removes it from the query set. Report such real named classes even
        // though they have no root context of their own.
        for iri in 0..self.sig.concept_names.len() as Iri {
            if self.sig.bottom == Some(iri) || self.sig.is_internal(iri) {
                continue;
            }
            if self.sig.is_nothing_concept(iri) {
                let a = self.sig.concept_names[iri as usize].clone();
                out.push((a, vec!["owl:Nothing".to_string()]));
            }
        }
        out.sort();
        out
    }

    pub fn inconsistent(&self) -> bool {
        // The ontology is inconsistent iff the ⊤ (empty-core) context derives the
        // empty clause: a generic element is forced into a contradiction, so there
        // is no model. Checking the ⊤ context (seeded in `run_for`) rather than a
        // concept literally named owl:Thing makes this independent of the input
        // vocabulary (the normaliser maps owl:Thing to an internal proxy, so the
        // old name-based check was effectively dead — audit M2).
        // The ground context derives the empty clause when the individuals
        // alone are contradictory (e.g. {o} ⊑ B, {o} ⊑ C, B ⊓ C ⊑ ⊥) — the
        // individuals exist in every model, so that too is global
        // inconsistency.
        let arena = &self.cc_arena[1];
        let top_bot = self.contexts.iter().any(|ctx| {
            ctx.root
                && ctx.core.is_empty()
                && ctx.worked_off.iter().any(|&ci| {
                    let c = &arena[ci as usize];
                    c.body.is_empty() && c.head.is_empty()
                })
        });
        if top_bot {
            return true;
        }
        if let Some(gid) = self.ground_ctx {
            let ctx = &self.contexts[gid];
            let arena = &self.cc_arena[ctx.root as usize];
            return ctx.worked_off.iter().any(|&ci| {
                let c = &arena[ci as usize];
                c.body.is_empty() && c.head.is_empty()
            });
        }
        false
    }

    pub fn num_contexts(&self) -> usize {
        self.contexts.len()
    }

    /// Whether a configured safety budget discarded inferences. Callers must
    /// decline this run instead of serializing its sound but partial closure.
    pub fn incomplete(&self) -> bool {
        self.message_truncated || self.nom_truncated.get()
    }

    /// Direction B (`KM_SPLIT`): run the ordered (tame) closure of query `Q`
    /// under the current `branch_decisions` (assumed disjunct facts per context
    /// core — installed via `set_branch_decisions` before the call), to fixpoint,
    /// and report the resulting `ClosureFacts`. Used by the splitting driver on a
    /// FRESH engine per branch (so the context graph is independent — branch
    /// isolation by construction). Soundness: each assumed disjunct is one
    /// disjunct of an entailed disjunction in its context, so the readout is one
    /// case of an exhaustive case analysis the driver intersects.
    pub fn classify_split_run(&mut self, query: Iri) -> ClosureFacts {
        if !self.ont.ground_facts.is_empty() {
            let gid = self.ground_context();
            self.propagate(gid);
        }
        let core = vec![Pred::Concept { iri: query, t: X }];
        let id = self.get_or_create_context(core, true, Some(query));
        self.saturate(id);
        self.propagate(id);
        // Seed ⊤ so a global inconsistency surfaces as this context's ⊥ too
        // (the shared root closure it was seeded from already carries the TBox).
        let top = self.get_or_create_context(vec![], true, None);
        self.saturate(top);
        self.propagate(top);
        self.run_msg_fixpoint_min();
        let mut facts = self.read_closure(id);
        // A bounded branch is not a model and cannot participate in the
        // exhaustive intersection. Force the splitting driver onto its
        // complete default-engine fallback instead.
        facts.foreign |= self.incomplete();
        facts
    }

    /// The set of "chain-unique" contexts: those reachable from a root context
    /// by a path of single successor edges. A context is chain-unique iff it has
    /// no predecessor edge (a root) or exactly ONE predecessor edge from a
    /// chain-unique context. Splitting a disjunction is sound ONLY in a
    /// chain-unique context: the central strategy MERGES contexts by core, so a
    /// context reached by two distinct successor edges (≥2 predecessor edges, or
    /// a predecessor that is itself non-unique) represents two successors that
    /// could independently pick different disjuncts; forcing them to agree (which
    /// a shared split does) would be unsound. In a chain-unique context the
    /// element is the unique successor along a functional chain from the query
    /// root, so a shared split is exactly a case analysis on that one element.
    fn chain_unique_contexts(&self) -> HashSet<usize> {
        let mut safe: HashSet<usize> = HashSet::new();
        loop {
            let mut changed = false;
            for (id, ctx) in self.contexts.iter().enumerate() {
                if safe.contains(&id) {
                    continue;
                }
                let ok = if ctx.predecessors.is_empty() {
                    true
                } else if ctx.predecessors.len() == 1 {
                    let (pid, _) = ctx.predecessors.keys().next().unwrap();
                    safe.contains(pid)
                } else {
                    false
                };
                if ok {
                    safe.insert(id);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        safe
    }

    /// Minimal inter-context message fixpoint (the `run_for` loop without the
    /// profiling/trace/dump instrumentation). On the `KM_MSG_CAP` backstop it
    /// drops the remaining messages (sound; the branch closure is then a sound
    /// under-approximation — the driver's `foreign` fallback covers correctness).
    fn run_msg_fixpoint_min(&mut self) {
        let msg_cap: usize = std::env::var("KM_MSG_CAP")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(25_000_000);
        let prof = std::env::var_os("KM_PROF").is_some();
        let batch_completion = std::env::var_os("KM_NO_BATCH_COMPLETION").is_none();
        let mut guard = 0usize;
        while !self.msgs.is_empty() {
            let batch: Vec<Msg> = self.msgs.drain(..).collect();
            let mut touched: Vec<usize> = Vec::new();
            let mut seen: HashSet<usize> = HashSet::new();
            for msg in batch {
                guard += 1;
                if prof && guard % 50000 == 0 {
                    eprintln!(
                        "KM_PROF split-fixpoint guard={} contexts={} msgs_pending={}",
                        guard,
                        self.contexts.len(),
                        self.msgs.len()
                    );
                }
                if guard > msg_cap {
                    self.message_truncated = true;
                    self.msgs.clear();
                    break;
                }
                let t = match msg {
                    Msg::Succ { from, f, p, target } => self.apply_succ(from, f, p, target),
                    Msg::Pred {
                        to,
                        from,
                        edge_label,
                        pool_idx,
                    } => self.apply_pred(to, from, edge_label, pool_idx),
                };
                if !batch_completion {
                    self.saturate(t);
                }
                if seen.insert(t) {
                    touched.push(t);
                }
            }
            if batch_completion {
                for &id in &touched {
                    self.saturate(id);
                }
            }
            for id in touched {
                self.propagate(id);
            }
        }
    }

    /// Read the closure into a `ClosureFacts` (Direction B increment 2). The
    /// query context `id` gives the readout: `⊤ → ⊥` → `unsat`; `⊤ → B(x)` → a
    /// unit subsumer. Split points are body-empty all-concept-on-central-var
    /// fact-disjunctions in ANY context, keyed by that context's core.
    ///
    /// SOUNDNESS + COMPLETENESS GUARDS (set `foreign` → driver falls back to the
    /// complete default engine):
    /// - a body-empty multi-head clause that is NOT all-concept-on-central-var (a
    ///   role/equality disjunction, or a disjunction on a successor/neighbour
    ///   term) — the propositional split cannot assume it as a fact;
    /// - a splittable disjunction in a context that is NOT chain-unique — sharing
    ///   the split across merged occurrences would be unsound (see
    ///   `chain_unique_contexts`).
    /// Body-NONEMPTY multi-head clauses (conditional disjunctions) are allowed:
    /// once their body atoms are derived as units (in some branch) Hyper resolves
    /// them into body-empty fact-disjunctions, which are then split; until then
    /// they are inert. So splitting every reachable fact-disjunction in
    /// chain-unique contexts is complete for the recovered fragment, and anything
    /// outside it falls back. Empirically validated by A/B vs the default engine.
    fn read_closure(&self, id: usize) -> ClosureFacts {
        let mut cf = ClosureFacts {
            unsat: false,
            foreign: false,
            units: Vec::new(),
            split_points: Vec::new(),
        };
        let safe = self.chain_unique_contexts();
        for (cid, ctx) in self.contexts.iter().enumerate() {
            let arena = &self.cc_arena[ctx.root as usize];
            for &ci in &ctx.worked_off {
                let c = &arena[ci as usize];
                if c.head.len() <= 1 {
                    continue;
                }
                // a disjunction (multi-head clause)
                let all_concept_central = c
                    .head
                    .iter()
                    .all(|l| matches!(l, Lit::P(Pred::Concept { t, .. }) if is_central(*t)));
                if !all_concept_central {
                    cf.foreign = true; // role/eq/non-central disjunction
                    return cf;
                }
                if c.body.is_empty() {
                    // a fact-disjunction: a split point, but only if this context
                    // is chain-unique (else a shared split would be unsound)
                    if !safe.contains(&cid) {
                        cf.foreign = true;
                        return cf;
                    }
                    let disjuncts: Vec<Iri> = c
                        .head
                        .iter()
                        .map(|l| match l {
                            Lit::P(Pred::Concept { iri, .. }) => *iri,
                            _ => unreachable!(),
                        })
                        .collect();
                    cf.split_points.push((ctx.core.clone(), disjuncts));
                }
                // body-nonempty concept-central multi-head: conditional
                // disjunction, allowed (converts to a fact-disjunction when its
                // body is derived, or stays inert).
            }
        }
        // Query-context readout: units and ⊥.
        let ctx = &self.contexts[id];
        let arena = &self.cc_arena[ctx.root as usize];
        for &ci in &ctx.worked_off {
            let c = &arena[ci as usize];
            if !c.body.is_empty() {
                continue;
            }
            if c.head.is_empty() {
                cf.unsat = true;
                continue;
            }
            if c.head.len() == 1 {
                if let Lit::P(Pred::Concept { iri, t }) = c.head[0] {
                    if is_central(t) {
                        cf.units.push(iri);
                    }
                }
            }
        }
        cf
    }

    /// `KM_ROOT_ORDERED` refutation residue readout (Direction A,
    /// docs/ROOT-ORDERED-RESOLUTION.md). Under the ordered regime an entailed
    /// named subsumer `B` of query `A` can be trapped non-maximal behind an
    /// unresolvable ordering-maximal disjunct, so the unit `⊤ → B(x)` never
    /// surfaces (the measured `KM_ORDERED_ALL` incompleteness). The unsat
    /// readout, by contrast, is order-robust, so recover the trapped subsumers
    /// by reduction to unsat: with the complement guard `B ⊓ NotB ⊑ ⊥` in the
    /// ontology (injected by the driver; `NotB` is fresh and occurs in no head,
    /// so the guard is inert outside refutation cores), `O ⊨ A ⊑ B` iff the
    /// context with core `{A(x), NotB(x)}` derives `⊥`.
    ///
    /// Candidate set: the named concepts occurring ORDERING-MAXIMAL in some
    /// worked-off head of `A`'s root context. Coverage argument: a refutation
    /// of `{A(x), NotB(x)}` must fire the complement guard at least once, and
    /// its first firing resolves a `NotB`-free clause with `B(x)` maximal in
    /// the head; every `NotB`-free derivation in the `{A, NotB}` context
    /// mirrors into the `{A}` context (`NotB` occurs in no ontology head, is
    /// never a Succ/Pred trigger, and so never leaves its own core), so such a
    /// clause also exists in `A`'s saturation. Hence every entailed subsumer is
    /// either a direct unit or a candidate here. (Proof obligations O1–O3 in
    /// docs/ROOT-ORDERED-RESOLUTION.md; the feature stays gated until they are
    /// certified.)
    ///
    /// Returns the recovered `(query, subsumer)` pairs. Sound: a returned pair
    /// is backed by a derived empty clause, i.e. `O + guards ⊨ A ⊓ NotB ⊑ ⊥`,
    /// and the guards are jointly conservative (interpret each `NotB` as the
    /// complement of `B`), so `O ⊨ A ⊑ B`.
    pub fn ordered_residue_repair(&mut self, not_of: &HashMap<Iri, Iri>) -> Vec<(Iri, Iri)> {
        let mut out = Vec::new();
        let roots: Vec<(usize, Iri)> = self
            .contexts
            .iter()
            .enumerate()
            .filter_map(|(i, c)| {
                if c.root {
                    c.query.map(|q| (i, q))
                } else {
                    None
                }
            })
            .collect();
        for (cid, q) in roots {
            let mut units: HashSet<Iri> = HashSet::new();
            let mut unsat = false;
            let mut cands: BTreeSet<Iri> = BTreeSet::new();
            {
                let ctx = &self.contexts[cid];
                let arena = &self.cc_arena[ctx.root as usize];
                for &ci in &ctx.worked_off {
                    let c = &arena[ci as usize];
                    if c.body.is_empty() && c.head.is_empty() {
                        unsat = true;
                        break;
                    }
                    if c.body.is_empty() && c.head.len() == 1 {
                        if let Lit::P(Pred::Concept { iri, t }) = c.head[0] {
                            if is_central(t) {
                                units.insert(iri);
                            }
                        }
                    }
                    for l in c.max_head() {
                        if let Lit::P(Pred::Concept { iri, t }) = l {
                            if is_central(t)
                                && !self.sig.is_internal(iri)
                                && !self.sig.is_nothing_concept(iri)
                            {
                                cands.insert(iri);
                            }
                        }
                    }
                }
            }
            if unsat {
                // ⊥ subsumes the readout (`subsumptions` reports owl:Nothing);
                // no refutation can add anything.
                continue;
            }
            for b in cands {
                if b == q || units.contains(&b) {
                    continue;
                }
                let Some(&nb) = not_of.get(&b) else { continue };
                let mut core = vec![
                    Pred::Concept { iri: q, t: X },
                    Pred::Concept { iri: nb, t: X },
                ];
                core.sort();
                core.dedup();
                let rid = self.get_or_create_context(core, true, None);
                self.saturate(rid);
                self.propagate(rid);
                self.run_msg_fixpoint_min();
                let ctx = &self.contexts[rid];
                let arena = &self.cc_arena[ctx.root as usize];
                let closed = ctx.worked_off.iter().any(|&ci| {
                    let c = &arena[ci as usize];
                    c.body.is_empty() && c.head.is_empty()
                });
                if closed {
                    out.push((q, b));
                }
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cx(iri: Iri, t: Term) -> Pred {
        Pred::Concept { iri, t }
    }
    fn rl(iri: Iri, s: Term, t: Term) -> Pred {
        Pred::Role { iri, s, t }
    }

    /// The dense `ClauseSig` mirror the engine keeps beside `cc_arena`; tests
    /// that build a standalone arena need the same parallel array.
    fn sigs_of(arena: &[ContextClause]) -> Vec<ClauseSig> {
        arena.iter().map(ClauseSig::of).collect()
    }

    /// The `FacetTable` mirror of a hand-built test arena, in arena order — the
    /// same lockstep `cc_facets` keeps with `cc_arena` in the engine.
    fn facets_of(arena: &[ContextClause], sig: &Sig) -> FacetTable {
        let mut table = FacetTable::new();
        for c in arena {
            table.push_clause(c, sig);
        }
        table
    }

    fn supers_of(e: &Engine, name: &str) -> Vec<String> {
        e.subsumptions()
            .into_iter()
            .find(|(n, _)| n == name)
            .map(|(_, v)| v)
            .unwrap_or_default()
    }

    /// Invariance guard for the inline-`SmallVec` `CentralSubst`: it must behave
    /// exactly like the previous `HashMap<Term, Term>` — same `add` accept/reject
    /// decisions, same `get`, same `apply` on every kind of term. `add`/`get` are
    /// mirrored against a reference `HashMap` oracle with the identical
    /// central/grounded special-casing, so any divergence in the substitution as
    /// a function (which is all Hyper's resolvents depend on) fails the test.
    #[test]
    fn central_subst_matches_hashmap_oracle() {
        use std::collections::HashMap;

        // Reference: what the old HashMap-backed `add` would store/decide.
        fn oracle_add(map: &mut HashMap<Term, Term>, allow_ground: bool, i: Term, o: Term) -> bool {
            if is_central(i) {
                if o == X || (allow_ground && is_individual(o)) {
                    return match map.get(&X) {
                        Some(&e) => e == o,
                        None => {
                            map.insert(X, o);
                            true
                        }
                    };
                }
                return false;
            }
            match map.get(&i) {
                Some(&existing) => existing == o,
                None => {
                    map.insert(i, o);
                    true
                }
            }
        }
        fn oracle_apply(map: &HashMap<Term, Term>, v: Term) -> Term {
            if v == X {
                return *map.get(&X).unwrap_or(&X);
            }
            if is_function(v) {
                if let Some(&b) = map.get(&X) {
                    if b != X {
                        return comp_term(v, b);
                    }
                }
                return v;
            }
            *map.get(&v).unwrap_or(&v)
        }

        // Probe terms across every category the substitution sees.
        let probes = [
            X,
            Y,
            zvar(1),
            zvar(2),
            zvar(5),
            ind_term(1),
            ind_term(2),
            fterm(1),
            fterm(2),
        ];

        for &allow_ground in &[false, true] {
            // Enough neighbour bindings to spill past the inline capacity (4),
            // exercising the heap path of the SmallVec too.
            let inserts: Vec<(Term, Term)> = vec![
                (X, if allow_ground { ind_term(1) } else { X }),
                (zvar(1), zvar(3)),
                (zvar(2), fterm(2)),
                (zvar(5), ind_term(2)),
                (zvar(1), zvar(4)), // conflicting re-bind: must be rejected by both
                (zvar(1), zvar(3)), // consistent re-bind: must be accepted by both
                (X, X),             // central re-bind (non-ground): may be rejected in ground mode
                (Y, ind_term(2)),
                (zvar(7), fterm(1)),
            ];

            let mut subst = CentralSubst::new(allow_ground);
            let mut oracle: HashMap<Term, Term> = HashMap::new();

            for (i, o) in inserts {
                let got = subst.add(i, o);
                let want = oracle_add(&mut oracle, allow_ground, i, o);
                assert_eq!(got, want, "add({i},{o}) allow_ground={allow_ground}");
                // After each step the two agree on every probe term.
                for &p in &probes {
                    assert_eq!(
                        subst.get(p),
                        oracle.get(&p).copied(),
                        "get({p}) allow_ground={allow_ground}"
                    );
                    assert_eq!(
                        subst.apply(p),
                        oracle_apply(&oracle, p),
                        "apply({p}) allow_ground={allow_ground}"
                    );
                }
            }

            // Clone is an independent map: mutating the clone leaves the
            // original untouched (Hyper relies on this per-candidate).
            let before: Vec<_> = probes.iter().map(|&p| subst.apply(p)).collect();
            let mut cloned = subst.clone();
            let _ = cloned.add(zvar(9), zvar(1));
            let after: Vec<_> = probes.iter().map(|&p| subst.apply(p)).collect();
            assert_eq!(
                before, after,
                "clone mutation leaked (allow_ground={allow_ground})"
            );
        }
    }

    /// A fresh (empty) substitution is the identity on every term, and an
    /// ungrounded central binding never accepts an individual image.
    #[test]
    fn central_subst_identity_and_ground_gate() {
        let mut subst = CentralSubst::new(false);
        for &t in &[X, Y, zvar(1), ind_term(1), fterm(1)] {
            assert_eq!(subst.apply(t), t);
            assert_eq!(subst.get(t), None);
        }
        // Non-ground context: x may only bind to x.
        assert!(!subst.add(X, ind_term(1)));
        assert!(subst.add(X, X));
        assert_eq!(subst.apply(X), X);
        assert_eq!(subst.apply(fterm(1)), fterm(1)); // b == X ⇒ no composite

        // Ground context: x binds to an individual, and f(x) ↦ f(o).
        let mut g = CentralSubst::new(true);
        let o = ind_term(3);
        assert!(g.add(X, o));
        assert_eq!(g.apply(X), o);
        assert_eq!(g.apply(fterm(1)), comp_term(fterm(1), o));
        // Re-binding x to a different individual is rejected.
        assert!(!g.add(X, ind_term(4)));
    }

    /// Trail invariant for the clone-free Hyper join: `mark()` + `rollback()`
    /// must be a faithful undo of any `add`/`unify` appended in between, i.e. a
    /// rolled-back substitution behaves identically to the clone taken at the
    /// mark on every probe term.  `build_hyper_resolvent` depends only on
    /// `sigma` as a function, so this is exactly the property that makes the
    /// in-place join derive the same resolvents the clone-per-candidate join did.
    #[test]
    fn central_subst_mark_rollback_restores_like_clone() {
        let probes = [
            X,
            Y,
            zvar(1),
            zvar(2),
            zvar(5),
            zvar(7),
            ind_term(1),
            ind_term(2),
            fterm(1),
            fterm(2),
        ];
        // A pool of (i, o) pairs; some conflict with the seed, some are fresh,
        // some are re-binds — covering the 0-, 1-, and reject-after-partial
        // append cases inside `unify`.
        let steps = [
            (zvar(2), fterm(2)),
            (zvar(5), ind_term(2)),
            (zvar(2), zvar(4)), // conflicts once zvar(2) is bound: rejected, no append
            (Y, ind_term(2)),
            (zvar(7), fterm(1)),
            (zvar(1), zvar(3)), // consistent re-bind of the seed: accepted, no append
        ];
        for &allow_ground in &[false, true] {
            let mut subst = CentralSubst::new(allow_ground);
            // Seed a "side condition" binding, as Hyper does before the join.
            let _ = subst.add(X, if allow_ground { ind_term(1) } else { X });
            let _ = subst.add(zvar(1), zvar(3));
            for &(i, o) in &steps {
                let snapshot = subst.clone();
                let mark = subst.mark();
                // Append-only mutation (single and role-like double add).
                let _ = subst.add(i, o);
                let _ = subst.add(o, i);
                subst.rollback(mark);
                assert_eq!(subst.mark(), snapshot.mark());
                for &p in &probes {
                    assert_eq!(
                        subst.apply(p),
                        snapshot.apply(p),
                        "apply({p}) after rollback (allow_ground={allow_ground})"
                    );
                    assert_eq!(subst.get(p), snapshot.get(p), "get({p}) after rollback");
                }
            }
        }
    }

    /// Differential test of the two Hyper backtracking strategies over
    /// `CentralSubst`: the pre-patch **clone-per-candidate** descent and the new
    /// **mark/rollback trail** descent.  Run over the same body atoms and the
    /// same ordered candidate lists, they must visit leaves in the identical
    /// order with the identical accumulated substitution — which is exactly what
    /// determines every resolvent `build_hyper_resolvent` emits.
    #[test]
    fn hyper_join_trail_matches_clone_join() {
        // Leaf record: the substitution as a function over a fixed probe set.
        fn leaf(sigma: &CentralSubst) -> Vec<Term> {
            [X, Y, zvar(1), zvar(2), zvar(3), ind_term(1), fterm(1)]
                .iter()
                .map(|&p| sigma.apply(p))
                .collect()
        }
        fn clone_join(
            bodies: &[Pred],
            cands: &[Vec<Pred>],
            depth: usize,
            sigma: &CentralSubst,
            out: &mut Vec<Vec<Term>>,
        ) {
            if depth == bodies.len() {
                out.push(leaf(sigma));
                return;
            }
            for &p in &cands[depth] {
                let mut s2 = sigma.clone();
                if unify(&mut s2, &bodies[depth], &p) {
                    clone_join(bodies, cands, depth + 1, &s2, out);
                }
            }
        }
        fn trail_join(
            bodies: &[Pred],
            cands: &[Vec<Pred>],
            depth: usize,
            sigma: &mut CentralSubst,
            out: &mut Vec<Vec<Term>>,
        ) {
            if depth == bodies.len() {
                out.push(leaf(sigma));
                return;
            }
            for &p in &cands[depth] {
                let mark = sigma.mark();
                if unify(sigma, &bodies[depth], &p) {
                    trail_join(bodies, cands, depth + 1, sigma, out);
                }
                sigma.rollback(mark);
            }
        }
        let con = |iri: Iri, t: Term| Pred::Concept { iri, t };
        let rol = |iri: Iri, s: Term, t: Term| Pred::Role { iri, s, t };
        // Body atoms sharing neighbour variables (y1=zvar(1), y2=zvar(2)) so that
        // cross-position consistency actually prunes branches, exercising the
        // partial-append/backtrack path of the trail.
        let bodies = vec![
            rol(10, X, zvar(1)),
            con(20, zvar(1)),
            rol(10, X, zvar(2)),
            con(21, zvar(2)),
        ];
        // Candidate heads per position; several unify, several clash on iri or on
        // an already-bound neighbour variable.
        let cands = vec![
            vec![
                rol(10, X, ind_term(1)),
                rol(10, X, ind_term(2)),
                rol(99, X, ind_term(3)),
            ],
            vec![
                con(20, ind_term(1)),
                con(20, ind_term(2)),
                con(20, ind_term(3)),
            ],
            vec![rol(10, X, ind_term(1)), rol(10, X, ind_term(2))],
            vec![con(21, ind_term(1)), con(21, ind_term(2))],
        ];
        for &allow_ground in &[false, true] {
            let mut a = Vec::new();
            clone_join(&bodies, &cands, 0, &CentralSubst::new(allow_ground), &mut a);
            let mut b = Vec::new();
            let mut sigma = CentralSubst::new(allow_ground);
            trail_join(&bodies, &cands, 0, &mut sigma, &mut b);
            assert_eq!(
                a, b,
                "trail/clone join diverged (allow_ground={allow_ground})"
            );
            // And the trail must leave the substitution empty again at the top.
            assert_eq!(sigma.mark(), 0, "trail leaked bindings at depth 0");
        }
    }

    // ---------------- Hyper join narrowing: differential harness -------------
    //
    // The narrowing (semijoin reduction + determined-position index) claims to
    // emit the generic join's resolvents, in the generic join's order.  These
    // tests hold it to that claim against a FROZEN copy of the pre-patch join.

    /// The pre-patch generic Hyper join, verbatim: scan every candidate at
    /// every level, `unify`, prune by symmetric groups, build at the leaves.
    /// Kept here as the differential oracle — it must never be "fixed" to
    /// track `hyper_join`, or the differential is worthless.
    #[allow(clippy::too_many_arguments)]
    fn generic_hyper_join(
        engine: &Engine,
        id: usize,
        side: &ContextClause,
        oc: &OntologyClause,
        candidates: &[Vec<(usize, Pred)>],
        order: &[usize],
        depth: usize,
        sigma: &mut CentralSubst,
        exempt: &[Term],
        chosen: &mut Vec<usize>,
        root: bool,
        out: &mut Vec<ContextClause>,
    ) {
        if depth == order.len() {
            if let Some(c) =
                engine.build_hyper_resolvent(id, side, oc, sigma, candidates, chosen, root)
            {
                out.push(c);
            }
            return;
        }
        let pos = order[depth];
        for (j, &(_ci, p)) in candidates[pos].iter().enumerate() {
            let mark = sigma.mark();
            if unify(sigma, &oc.body[pos], &p)
                && (oc.sym_groups.is_empty() || sym_groups_ok(oc, exempt, sigma))
            {
                chosen[pos] = j;
                generic_hyper_join(
                    engine,
                    id,
                    side,
                    oc,
                    candidates,
                    order,
                    depth + 1,
                    sigma,
                    exempt,
                    chosen,
                    root,
                    out,
                );
            }
            sigma.rollback(mark);
        }
    }

    /// Full content of a resolvent sequence: body, head AND the cached maximal
    /// -literal mask, in emission order.  Comparing this compares both what the
    /// join derived and the order it derived it in.
    fn resolvent_trace(clauses: &[ContextClause]) -> Vec<(Vec<Pred>, Vec<Lit>, u64)> {
        clauses
            .iter()
            .map(|c| (c.body.clone(), c.head.clone(), c.max_head_mask))
            .collect()
    }

    /// Run one join over the same hand-built candidate lists both ways,
    /// reproducing `hyper_inner`'s surroundings exactly (position order keyed
    /// on the raw widths, side-position variables exempt from symmetric-group
    /// pruning).  Returns `(generic, narrowed, narrowed widths)`.
    fn join_both_ways(
        engine: &Engine,
        side: &ContextClause,
        oc: &OntologyClause,
        side_pos: usize,
        raw: &[Vec<(usize, Pred)>],
        sigma0: &CentralSubst,
        root: bool,
    ) -> (Vec<ContextClause>, Vec<ContextClause>, Vec<usize>) {
        let n = oc.body.len();
        let widths: Vec<usize> = raw.iter().map(Vec::len).collect();
        let mut order: Vec<usize> = (0..n).collect();
        order.sort_by_key(|&i| widths[i]);
        let exempt: Vec<Term> = if oc.sym_groups.is_empty() {
            Vec::new()
        } else {
            match oc.body[side_pos] {
                Pred::Concept { t, .. } => vec![t],
                Pred::Role { s, t, .. } => vec![s, t],
            }
        };
        let mut generic = Vec::new();
        let mut sigma = sigma0.clone();
        let mut chosen = vec![0usize; n];
        generic_hyper_join(
            engine,
            0,
            side,
            oc,
            raw,
            &order,
            0,
            &mut sigma,
            &exempt,
            &mut chosen,
            root,
            &mut generic,
        );
        assert_eq!(sigma.mark(), sigma0.mark(), "generic join leaked bindings");

        let mut narrowed: Vec<Vec<(usize, Pred)>> = raw.to_vec();
        let mut narrow_out = Vec::new();
        if reduce_hyper_candidates(oc, &mut narrowed, sigma0) {
            let mut sigma = sigma0.clone();
            let mut chosen = vec![0usize; n];
            let mut determined = DeterminedIndex::new(true);
            engine.hyper_join(
                0,
                side,
                oc,
                &narrowed,
                &order,
                0,
                &mut sigma,
                &exempt,
                &mut chosen,
                root,
                &mut determined,
                &mut narrow_out,
            );
            assert_eq!(
                sigma.mark(),
                sigma0.mark(),
                "narrowed join leaked bindings"
            );
        }
        let narrowed_widths = narrowed.iter().map(Vec::len).collect();
        (generic, narrow_out, narrowed_widths)
    }

    /// Deterministic LCG — the property test must be reproducible, and the
    /// engine has no `rand` dependency.
    struct JoinRng(u64);
    impl JoinRng {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            self.0 >> 33
        }
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    /// A random candidate predicate of the same shape and iri as `body` — the
    /// only ones a head index can ever offer Hyper for that body position.
    fn random_match(rng: &mut JoinRng, body: &Pred, terms: &[Term]) -> Pred {
        match *body {
            Pred::Concept { iri, .. } => Pred::Concept {
                iri,
                t: terms[rng.below(terms.len())],
            },
            Pred::Role { iri, .. } => Pred::Role {
                iri,
                s: terms[rng.below(terms.len())],
                t: terms[rng.below(terms.len())],
            },
        }
    }

    /// Seed a non-root context with unit clauses `-> p` (the worked-off facts
    /// Hyper's candidate indexes are built from) and return `(engine, ctx id)`.
    fn engine_with_units(
        sig: Sig,
        ont: Vec<OntologyClause>,
        units: Vec<Pred>,
    ) -> (Engine, usize) {
        let mut e = Engine::new(sig, ont, 0);
        let id = e.contexts.len();
        let mut ctx = Context::new(id, vec![], false, None);
        for p in units {
            let clause = ContextClause::new(vec![], vec![Lit::P(p)], false, &e.sig);
            let cid = e.cc_arena[0].len() as u32;
            e.cc_facets[0].push_clause(&clause, &e.sig);
            e.cc_arena[0].push(clause);
            ctx.worked_off.push(cid);
            ctx.index_clause(&e.cc_facets[0], cid);
        }
        e.contexts.push(ctx);
        (e, id)
    }

    /// The ORE 1194 shape, end to end through `hyper`: a qualified at-most
    /// cardinality clause `G(x) ∧ ⋀ r(x,yi) ∧ C(yi) → ⋁ yi ≈ yj` fired against
    /// a context holding genuine `∃r.C` witnesses PLUS the two kinds of decoy
    /// that make the independently built postings wide — fillers with no
    /// r-edge, and r-edges whose target is not a filler.
    ///
    /// The narrowed join must return the generic join's resolvent sequence
    /// verbatim, and the resolvents must be exactly the 3-element subsets of
    /// the genuine witnesses.
    #[test]
    fn hyper_narrowing_matches_generic_join_on_qualified_at_most() {
        let mut sig = Sig::default();
        let g = sig.concept("G");
        let c = sig.concept("C");
        let decoy = sig.concept("Decoy");
        let r = sig.role("r");
        let (z1, z2, z3) = (zvar(1), zvar(2), zvar(3));
        let oc = OntologyClause::new(
            vec![
                cx(g, X),
                rl(r, X, z1),
                cx(c, z1),
                rl(r, X, z2),
                cx(c, z2),
                rl(r, X, z3),
                cx(c, z3),
            ],
            vec![Lit::eq(z1, z2), Lit::eq(z1, z3), Lit::eq(z2, z3)],
        );
        const WITNESSES: i32 = 5;
        const DECOYS: i32 = 6;
        let mut units = Vec::new();
        for i in 1..=WITNESSES {
            units.push(rl(r, X, fterm(i)));
            units.push(cx(c, fterm(i)));
        }
        for i in 1..=DECOYS {
            // filler with no edge, edge with no filler, and unrelated noise
            units.push(cx(c, fterm(WITNESSES + i)));
            units.push(rl(r, X, fterm(100 + i)));
            units.push(cx(decoy, fterm(WITNESSES + i)));
        }
        let (e, id) = engine_with_units(sig, vec![oc], units);
        let side = ContextClause::new(vec![], vec![Lit::P(cx(g, X))], false, &e.sig);

        set_hyper_narrow(false);
        let generic = e.hyper(id, &side, cx(g, X), false);
        set_hyper_narrow(true);
        let narrowed = e.hyper(id, &side, cx(g, X), false);
        assert_eq!(
            resolvent_trace(&generic),
            resolvent_trace(&narrowed),
            "narrowed Hyper join diverged from the generic join"
        );

        // Exactly the 3-subsets of the 5 genuine witnesses, each once (the
        // symmetric group keeps only the term-sorted assignment).
        let expected: Vec<Vec<Lit>> = {
            let mut out = Vec::new();
            for a in 1..=WITNESSES {
                for b in (a + 1)..=WITNESSES {
                    for d in (b + 1)..=WITNESSES {
                        let mut head = vec![
                            Lit::eq(fterm(a), fterm(b)),
                            Lit::eq(fterm(a), fterm(d)),
                            Lit::eq(fterm(b), fterm(d)),
                        ];
                        head.sort();
                        out.push(head);
                    }
                }
            }
            out.sort();
            out
        };
        let mut got: Vec<Vec<Lit>> = narrowed.iter().map(|res| res.head.clone()).collect();
        got.sort();
        assert!(
            narrowed.iter().all(|res| res.body.is_empty()),
            "unit premises must give body-free resolvents: {narrowed:?}"
        );
        assert_eq!(got, expected, "wrong witness combinations");
    }

    /// The reduction must actually narrow the cardinality shape: each filler
    /// position keeps only the terms that carry an r-edge, and each edge
    /// position only the edges whose target carries the filler concept.  Guards
    /// against a refactor that silently turns the pass into a no-op (which the
    /// differential tests alone would happily accept).
    #[test]
    fn reduce_hyper_candidates_keeps_exactly_the_witnesses() {
        let mut sig = Sig::default();
        let c = sig.concept("C");
        let r = sig.role("r");
        let (z1, z2) = (zvar(1), zvar(2));
        let oc = OntologyClause::new(
            vec![rl(r, X, z1), cx(c, z1), rl(r, X, z2), cx(c, z2)],
            vec![Lit::eq(z1, z2)],
        );
        // 2 witnesses, 3 filler-only terms, 4 edge-only targets.
        let fillers: Vec<Pred> = (1..=5).map(|i| cx(c, fterm(i))).collect();
        let edges: Vec<Pred> = (1..=2)
            .chain(6..=9)
            .map(|i| rl(r, X, fterm(i)))
            .collect();
        let mut candidates: Vec<Vec<(usize, Pred)>> = oc
            .body
            .iter()
            .map(|atom| match atom {
                Pred::Concept { .. } => fillers.iter().map(|&p| (usize::MAX, p)).collect(),
                Pred::Role { .. } => edges.iter().map(|&p| (usize::MAX, p)).collect(),
            })
            .collect();
        let mut sigma = CentralSubst::new(false);
        assert!(sigma.add(X, X));
        assert!(reduce_hyper_candidates(&oc, &mut candidates, &sigma));
        for (position, atom) in oc.body.iter().enumerate() {
            let kept: Vec<Pred> = candidates[position].iter().map(|&(_, p)| p).collect();
            match atom {
                Pred::Concept { .. } => assert_eq!(
                    kept,
                    vec![cx(c, fterm(1)), cx(c, fterm(2))],
                    "filler position kept a non-witness"
                ),
                Pred::Role { .. } => assert_eq!(
                    kept,
                    vec![rl(r, X, fterm(1)), rl(r, X, fterm(2))],
                    "edge position kept a non-witness"
                ),
            }
        }
    }

    /// An empty intersection means the clause has no resolvent for this side
    /// premise at all, which the reduction reports instead of letting the join
    /// walk the product.
    #[test]
    fn reduce_hyper_candidates_detects_the_empty_join() {
        let mut sig = Sig::default();
        let c = sig.concept("C");
        let r = sig.role("r");
        let z1 = zvar(1);
        let oc = OntologyClause::new(vec![rl(r, X, z1), cx(c, z1)], vec![Lit::P(cx(c, X))]);
        let mut candidates: Vec<Vec<(usize, Pred)>> = oc
            .body
            .iter()
            .map(|atom| match atom {
                // disjoint term sets: no filler sits at the end of an edge
                Pred::Concept { .. } => (1..=3).map(|i| (usize::MAX, cx(c, fterm(i)))).collect(),
                Pred::Role { .. } => (4..=6).map(|i| (usize::MAX, rl(r, X, fterm(i)))).collect(),
            })
            .collect();
        let mut sigma = CentralSubst::new(false);
        assert!(sigma.add(X, X));
        assert!(!reduce_hyper_candidates(&oc, &mut candidates, &sigma));
    }

    /// Property test: over randomly generated clause bodies, side conditions
    /// and candidate postings — including the grounded-central (nominal)
    /// substitution mode — the narrowed join must emit the frozen generic
    /// join's resolvent sequence exactly.  This is the general exactness claim;
    /// the cardinality test above is the shape that motivated it.
    #[test]
    fn hyper_narrowing_matches_generic_join_property() {
        let mut sig = Sig::default();
        for name in ["C0", "C1", "C2"] {
            sig.concept(name);
        }
        for name in ["r0", "r1"] {
            sig.role(name);
        }
        let e = Engine::new(sig, vec![], 0);
        // Candidate terms: the central variable, successors, and individuals
        // (the grounded-Hyper images).
        let terms = [
            X,
            fterm(1),
            fterm(2),
            fterm(3),
            ind_term(1),
            ind_term(2),
            comp_term(fterm(1), ind_term(1)),
        ];
        let vars = [X, zvar(1), zvar(2), zvar(3)];
        let mut rng = JoinRng(0x5eed_1194);
        let mut compared = 0usize;
        let mut raw_entries = 0usize;
        let mut narrowed_entries = 0usize;
        let mut long_postings = 0usize;
        for case in 0..400 {
            let allow_ground = rng.below(2) == 1;
            let mut body = Vec::new();
            for _ in 0..(2 + rng.below(4)) {
                if rng.below(3) == 0 {
                    body.push(cx(rng.below(3) as Iri, vars[rng.below(vars.len())]));
                } else {
                    body.push(rl(
                        rng.below(2) as Iri,
                        vars[rng.below(vars.len())],
                        vars[rng.below(vars.len())],
                    ));
                }
            }
            let oc = OntologyClause::new(
                body,
                vec![
                    Lit::eq(zvar(1), zvar(2)),
                    Lit::P(cx(2, X)),
                    Lit::P(cx(1, zvar(3))),
                ],
            );
            let n = oc.body.len();
            let side_pos = rng.below(n);
            let max = random_match(&mut rng, &oc.body[side_pos], &terms);
            let mut sigma = CentralSubst::new(allow_ground);
            if !unify(&mut sigma, &oc.body[side_pos], &max) {
                continue;
            }
            // Candidate lists exactly as `hyper_inner` builds them: everything
            // the head index offers that still unifies with the side binding.
            let mut raw: Vec<Vec<(usize, Pred)>> = Vec::with_capacity(n);
            let mut usable = true;
            for i in 0..n {
                if i == side_pos {
                    raw.push(vec![(usize::MAX, max)]);
                    continue;
                }
                let mut list = Vec::new();
                for _ in 0..(2 + rng.below(20)) {
                    let p = random_match(&mut rng, &oc.body[i], &terms);
                    let mark = sigma.mark();
                    if unify(&mut sigma, &oc.body[i], &p) {
                        list.push((usize::MAX, p));
                    }
                    sigma.rollback(mark);
                }
                if list.is_empty() {
                    usable = false;
                    break;
                }
                if list.len() >= HYPER_DETERMINED_INDEX_MIN {
                    long_postings += 1;
                }
                raw.push(list);
            }
            if !usable {
                continue;
            }
            let side = ContextClause::new(
                vec![cx(0, X)],
                vec![Lit::P(max), Lit::P(cx(1, X))],
                false,
                &e.sig,
            );
            let (generic, narrowed, widths) =
                join_both_ways(&e, &side, &oc, side_pos, &raw, &sigma, false);
            assert_eq!(
                resolvent_trace(&generic),
                resolvent_trace(&narrowed),
                "case {case}: narrowed join diverged\n body={:?}\n side_pos={side_pos} \
                 allow_ground={allow_ground}\n candidates={raw:?}",
                oc.body,
            );
            compared += 1;
            raw_entries += raw.iter().map(Vec::len).sum::<usize>();
            narrowed_entries += widths.iter().sum::<usize>();
        }
        assert!(compared >= 100, "property test degenerated: {compared} cases");
        assert!(
            narrowed_entries < raw_entries,
            "reduction never removed a candidate ({narrowed_entries} of {raw_entries})"
        );
        assert!(
            long_postings > 0,
            "no posting reached the hash-indexed determined-lookup threshold"
        );
    }

    /// Pipeline-level differential: a full saturation over a qualified at-most
    /// cardinality ontology must produce the identical classification with the
    /// narrowing on and off.
    #[test]
    fn hyper_narrowing_preserves_saturation_output() {
        let build = || {
            let mut sig = Sig::default();
            let a = sig.concept("A");
            let c = sig.concept("C");
            let d = sig.concept("D");
            let r = sig.role("r");
            let (z1, z2) = (zvar(1), zvar(2));
            let clauses = vec![
                // A ⊑ ∃r.C ⊓ ∃r.(C ⊓ D), over distinct skolems
                OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(r, X, fterm(1)))]),
                OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(c, fterm(1)))]),
                OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(r, X, fterm(2)))]),
                OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(c, fterm(2)))]),
                OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(d, fterm(2)))]),
                // A ⊑ ≤1 r.C
                OntologyClause::new(
                    vec![cx(a, X), rl(r, X, z1), cx(c, z1), rl(r, X, z2), cx(c, z2)],
                    vec![Lit::eq(z1, z2)],
                ),
                // a consumer of the merged filler
                OntologyClause::new(vec![rl(r, X, Y), cx(d, Y)], vec![Lit::P(cx(c, X))]),
            ];
            (sig, clauses, a)
        };
        let run = |narrow: bool| {
            let (sig, clauses, a) = build();
            set_hyper_narrow(narrow);
            let mut e = Engine::new(sig, clauses, 0);
            e.run_for(&[a]);
            let result = (e.subsumptions(), e.inconsistent());
            set_hyper_narrow(true);
            result
        };
        assert_eq!(
            run(false),
            run(true),
            "Hyper join narrowing changed the saturation output"
        );
    }

    /// Back-subsumption maintains the `worked_off` head index incrementally
    /// (`unindex_clause`) instead of rebuilding it from scratch.  This is a
    /// differential test against the full-rebuild oracle: after a strengthening
    /// clause subsumes two worked-off clauses away, the incrementally maintained
    /// index must equal the index a full `rebuild_head_index` produces over the
    /// survivors — same keys, same posting id-sequences, no empty postings.  A
    /// divergence in `unindex_clause`'s key set would change what Hyper/Pred see
    /// as candidates and so silently alter derivability.
    #[test]
    fn back_subsume_incremental_unindex_matches_rebuild() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b = sig.concept("B");
        let c = sig.concept("C");
        let d = sig.concept("D");
        let e = sig.concept("E");
        let f = sig.concept("F");
        let g = sig.concept("G");
        let cc = |body: Vec<Pred>, head: Vec<Lit>| ContextClause::new(body, head, true, &sig);
        // 0 and 2 are strengthened away by the A→B clause (id 3); 1 survives.
        let arena = vec![
            cc(vec![cx(a, X)], vec![Lit::P(cx(b, X)), Lit::P(cx(c, X))]), // 0: A → B ⊔ C
            cc(vec![cx(d, X)], vec![Lit::P(cx(e, X))]),                   // 1: D → E (survivor)
            cc(
                vec![cx(a, X), cx(f, X)],
                vec![Lit::P(cx(b, X)), Lit::P(cx(c, X)), Lit::P(cx(g, X))],
            ), // 2: A ⊓ F → B ⊔ C ⊔ G
            cc(vec![cx(a, X)], vec![Lit::P(cx(b, X))]),                   // 3: A → B (subsumer)
        ];
        let facets = facets_of(&arena, &sig);
        let mut ctx = Context::new(0, vec![], true, None);
        for cid in [0u32, 1, 2] {
            ctx.clause_keys.insert(cid);
            ctx.index_active_clause(&arena, cid);
            ctx.worked_off.push(cid);
            ctx.index_clause(&facets, cid);
        }
        ctx.back_subsume(&arena, &sigs_of(&arena), &facets, &arena[3]);
        assert_eq!(
            ctx.worked_off,
            vec![1u32],
            "clauses 0 and 2 must be back-subsumed away, exercising unindex_clause"
        );
        let snapshot = |ctx: &Context| {
            (
                ctx.head_concept_index.clone(),
                ctx.head_role_index.clone(),
                ctx.ground_role_source_index.clone(),
                ctx.ground_role_target_index.clone(),
                ctx.max_head_pred_index.clone(),
                ctx.max_head_term_index.clone(),
                ctx.ground_body_index.clone(),
                ctx.bridge_index.clone(),
                ctx.merge_clauses.clone(),
            )
        };
        let incremental = snapshot(&ctx);
        ctx.rebuild_head_index(&facets);
        let rebuilt = snapshot(&ctx);
        assert!(
            incremental == rebuilt,
            "incremental unindex_clause diverged from full rebuild_head_index"
        );
    }

    /// A role-carrying variant so `unindex_clause` is exercised on the role /
    /// ground-endpoint / body-index postings too, not only concept heads.  A
    /// clause with a maximal role head and a ground body atom is worked off, then
    /// strengthened away; the incremental index must again match the rebuild.
    #[test]
    fn back_subsume_incremental_unindex_matches_rebuild_roles() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b = sig.concept("B");
        let r = sig.role("R");
        let o = ind_term(1);
        let cc = |body: Vec<Pred>, head: Vec<Lit>| ContextClause::new(body, head, true, &sig);
        let arena = vec![
            // 0: A(x) → R(x,o) ⊔ B(x) — maximal role head with a ground endpoint.
            cc(
                vec![cx(a, X)],
                vec![Lit::P(rl(r, X, o)), Lit::P(cx(b, X))],
            ),
            // 1: A(x) → R(x,o) — strengthens 0.
            cc(vec![cx(a, X)], vec![Lit::P(rl(r, X, o))]),
            // 2: survivor.
            cc(vec![cx(b, X)], vec![Lit::P(cx(a, X))]),
        ];
        let facets = facets_of(&arena, &sig);
        let mut ctx = Context::new(0, vec![], true, None);
        for cid in [0u32, 2] {
            ctx.clause_keys.insert(cid);
            ctx.index_active_clause(&arena, cid);
            ctx.worked_off.push(cid);
            ctx.index_clause(&facets, cid);
        }
        ctx.back_subsume(&arena, &sigs_of(&arena), &facets, &arena[1]);
        assert_eq!(ctx.worked_off, vec![2u32], "clause 0 must be subsumed away");
        let snapshot = |ctx: &Context| {
            (
                ctx.head_concept_index.clone(),
                ctx.head_role_index.clone(),
                ctx.ground_role_source_index.clone(),
                ctx.ground_role_target_index.clone(),
                ctx.max_head_pred_index.clone(),
                ctx.max_head_term_index.clone(),
                ctx.ground_body_index.clone(),
                ctx.bridge_index.clone(),
                ctx.merge_clauses.clone(),
            )
        };
        let incremental = snapshot(&ctx);
        ctx.rebuild_head_index(&facets);
        let rebuilt = snapshot(&ctx);
        assert!(
            incremental == rebuilt,
            "incremental unindex_clause (roles) diverged from full rebuild_head_index"
        );
    }

    // ---------------- shared per-clause facets (structural sharing) ---------

    /// Signature for the facet population.  `rsucc` is on and a `__trans__`
    /// reachability concept is interned so the `sat_rsucc` flag is genuinely
    /// exercised rather than trivially false.
    fn facet_sig() -> Sig {
        let mut sig = Sig::default();
        sig.rsucc = true;
        // ids 0..: keep the interned names aligned with the iris the population
        // uses for the reach / ordinary concepts.
        assert_eq!(sig.concept("__trans__R__A"), 0);
        for i in 1..24 {
            sig.concept(&format!("C{i}"));
        }
        for i in 0..12 {
            sig.role(&format!("R{i}"));
        }
        sig
    }

    /// A deterministic clause population that reaches every `Facet` kind and
    /// every `ClauseFlags` bit: concept and role maximal heads, ground (`o`) and
    /// composite (`f(o)`) role endpoints on both positions, `≈` / `≉` heads
    /// (rewrite terms), the bridge form `o ≈ x` under an empty body, all three
    /// merge forms, ground body atoms, function-term heads (Succ), the
    /// reachability head (r-Succ), and iris repeated across maximal literals so
    /// the per-clause dedup is exercised rather than only the singleton case.
    ///
    /// The last clause has a 70-literal head, which trips
    /// `ContextClause::max_head_mask`'s "all maximal" fallback — the one place
    /// where the key set is not read off the mask.
    fn facet_population(sig: &Sig, root: bool, n: usize) -> Vec<ContextClause> {
        let o1 = ind_term(1);
        let o2 = ind_term(2);
        let f1 = fterm(1);
        let fo = comp_term(f1, o1);
        let preds = [
            cx(1, X),
            cx(2, X),
            cx(1, o1),
            rl(7, o1, o2),
            rl(7, X, Y),
            cx(3, Y),
            rl(8, X, o1),
            cx(4, f1),
        ];
        let lits = [
            Lit::P(cx(11, X)),
            Lit::P(cx(12, X)),
            // same iri as the previous literal on another term: exercises the
            // `head_concept_index` per-clause iri dedup.
            Lit::P(cx(11, Y)),
            Lit::P(rl(7, X, o1)),
            // same role iri, ground *source* rather than target.
            Lit::P(rl(7, o1, Y)),
            Lit::P(rl(9, X, fo)),
            Lit::P(cx(13, f1)),
            Lit::P(cx(0, X)),
            Lit::eq(o1, X),
            Lit::eq(o1, Y),
            Lit::eq(X, Y),
            Lit::ineq(o1, X),
        ];
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        // Singleton heads are unconditionally maximal, so these pin every facet
        // kind and pool bit into the population regardless of how the sampled
        // clauses happen to order.  The sampled bulk then supplies the
        // multi-literal, repeated-iri, and churn coverage.
        let pinned = [
            // reachability head (r-Succ pool)
            (vec![], vec![Lit::P(cx(0, X))]),
            // function-term head (Succ pool), and not seed-Pred-eligible
            (vec![], vec![Lit::P(cx(13, f1))]),
            // plain Pred-eligible clause
            (vec![cx(1, X)], vec![Lit::P(cx(11, X))]),
            // bridge premise `o ≈ x` under an empty body (also a merge form)
            (vec![], vec![Lit::eq(o1, X)]),
            // ground role *source* plus a ground body atom
            (vec![cx(1, o1)], vec![Lit::P(rl(7, o1, Y))]),
            // ground role *target*
            (vec![], vec![Lit::P(rl(7, X, o1))]),
            // composite `f(o)` endpoint
            (vec![rl(7, o1, o2)], vec![Lit::P(rl(9, X, fo))]),
            // merge form `x ≈ y` with a non-empty body (no bridge entry)
            (vec![cx(2, X)], vec![Lit::eq(X, Y)]),
        ];
        let mut out = Vec::with_capacity(n);
        for (body, head) in pinned {
            out.push(ContextClause::new(body, head, root, sig));
        }
        for i in 0..n.saturating_sub(out.len() + 1) {
            let (bm, hm) = (next(), next());
            // Every fourth clause is body-free, so the bridge form (which only
            // files under an empty body) is hit often instead of by luck.
            let body: Vec<Pred> = if i % 4 == 0 {
                Vec::new()
            } else {
                preds
                    .iter()
                    .enumerate()
                    .filter(|(k, _)| (bm >> (k * 3)) % 3 == 0)
                    .map(|(_, &p)| p)
                    .collect()
            };
            let head: Vec<Lit> = lits
                .iter()
                .enumerate()
                .filter(|(k, _)| (hm >> (k * 5)) % 3 == 0)
                .map(|(_, &l)| l)
                .collect();
            out.push(ContextClause::new(body, head, root, sig));
        }
        let wide: Vec<Lit> = (0..70u32).map(|i| Lit::P(cx(200 + i, X))).collect();
        out.push(ContextClause::new(vec![], wide, root, sig));
        out
    }

    type IndexSnapshot = (
        HashMap<Iri, Posting>,
        HashMap<Iri, Posting>,
        HashMap<(Iri, Term), Posting>,
        HashMap<(Iri, Term), Posting>,
        HashMap<Pred, Posting>,
        HashMap<Term, Posting>,
        HashMap<Pred, Vec<u32>>,
        HashMap<Term, Vec<u32>>,
        Vec<u32>,
    );

    /// Every structure `index_clause` / `unindex_clause` touch, so a divergence
    /// in any one key is caught rather than only in the concept head index.
    fn index_snapshot(ctx: &Context) -> IndexSnapshot {
        (
            ctx.head_concept_index.clone(),
            ctx.head_role_index.clone(),
            ctx.ground_role_source_index.clone(),
            ctx.ground_role_target_index.clone(),
            ctx.max_head_pred_index.clone(),
            ctx.max_head_term_index.clone(),
            ctx.ground_body_index.clone(),
            ctx.bridge_index.clone(),
            ctx.merge_clauses.clone(),
        )
    }

    /// Differential: filing a clause from its shared `Facet` list must leave the
    /// exact index state the frozen pre-facet derivation leaves — same keys,
    /// same posting id-sequences, no extra or missing key.  The head indexes are
    /// what Hyper, Pred, Eq, Join, and r-Succ read to pick candidates, so any
    /// divergence here silently changes what is derivable.
    #[test]
    fn facet_indexing_matches_reference_derivation() {
        for &root in &[false, true] {
            let sig = facet_sig();
            let arena = facet_population(&sig, root, 320);
            let facets = facets_of(&arena, &sig);
            let mut shared = Context::new(0, vec![], root, None);
            let mut reference = Context::new(0, vec![], root, None);
            for cid in 0..arena.len() as u32 {
                shared.worked_off.push(cid);
                shared.index_clause(&facets, cid);
                reference.worked_off.push(cid);
                reference.index_clause_reference(&arena, cid);
            }
            assert!(
                index_snapshot(&shared) == index_snapshot(&reference),
                "facet-driven index_clause diverged from the frozen derivation (root={root})"
            );
            // The population must actually reach every facet kind, or the
            // comparison above proves nothing about the untouched ones.
            assert!(!shared.head_concept_index.is_empty(), "no concept heads");
            assert!(!shared.head_role_index.is_empty(), "no role heads");
            assert!(
                !shared.ground_role_source_index.is_empty(),
                "no ground role sources"
            );
            assert!(
                !shared.ground_role_target_index.is_empty(),
                "no ground role targets"
            );
            assert!(!shared.max_head_pred_index.is_empty(), "no maximal preds");
            assert!(!shared.max_head_term_index.is_empty(), "no rewrite terms");
            assert!(!shared.ground_body_index.is_empty(), "no ground body atoms");
            assert!(!shared.bridge_index.is_empty(), "no bridge premises");
            assert!(!shared.merge_clauses.is_empty(), "no merge clauses");
        }
    }

    /// Differential over back-subsumption churn: removing a scattered ~40% of
    /// the population through the facet path must leave the same index state as
    /// the frozen derivation, and as a full rebuild over the survivors.  The
    /// rebuild leg is the stronger oracle: it also catches a key that was
    /// inserted but never removed (a stale posting entry pointing at a
    /// subsumed-away clause).
    #[test]
    fn facet_unindexing_matches_reference_and_rebuild() {
        for &root in &[false, true] {
            let sig = facet_sig();
            let arena = facet_population(&sig, root, 320);
            let facets = facets_of(&arena, &sig);
            let mut shared = Context::new(0, vec![], root, None);
            let mut reference = Context::new(0, vec![], root, None);
            for cid in 0..arena.len() as u32 {
                shared.worked_off.push(cid);
                shared.index_clause(&facets, cid);
                reference.worked_off.push(cid);
                reference.index_clause_reference(&arena, cid);
            }
            let dropped: Vec<u32> = (0..arena.len() as u32)
                .filter(|cid| (cid * 7 + 3) % 5 < 2)
                .collect();
            assert!(dropped.len() > 100, "churn too small to be a real test");
            for &cid in &dropped {
                shared.unindex_clause(&facets, cid);
                reference.unindex_clause_reference(&arena, cid);
            }
            shared.worked_off.retain(|cid| !dropped.contains(cid));
            reference.worked_off.retain(|cid| !dropped.contains(cid));
            assert!(
                index_snapshot(&shared) == index_snapshot(&reference),
                "facet-driven unindex_clause diverged from the frozen derivation (root={root})"
            );
            let mut rebuilt = shared.clone();
            rebuilt.rebuild_head_index(&facets);
            assert!(
                index_snapshot(&shared) == index_snapshot(&rebuilt),
                "incremental facet unindex diverged from a full rebuild (root={root})"
            );
        }
    }

    /// The insert/remove key sets are the same list walked twice, so filing then
    /// unfiling the whole population must leave no residue at all — not even an
    /// empty posting under a surviving key.
    #[test]
    fn facet_index_then_unindex_leaves_no_residue() {
        for &root in &[false, true] {
            let sig = facet_sig();
            let arena = facet_population(&sig, root, 200);
            let facets = facets_of(&arena, &sig);
            let mut ctx = Context::new(0, vec![], root, None);
            for cid in 0..arena.len() as u32 {
                ctx.index_clause(&facets, cid);
            }
            for cid in 0..arena.len() as u32 {
                ctx.unindex_clause(&facets, cid);
            }
            let empty = Context::new(0, vec![], root, None);
            assert!(
                index_snapshot(&ctx) == index_snapshot(&empty),
                "facet unindex left residue in the head indexes (root={root})"
            );
        }
    }

    /// The cached pool-eligibility bits must equal the predicates they replaced
    /// in `saturate` and `seed_worked_off`, verbatim.  A wrong bit does not
    /// corrupt an index — it silently drops (or invents) a Pred / Succ / r-Succ
    /// message, which changes the inter-context fixpoint.
    #[test]
    fn clause_flags_match_the_predicates_they_replaced() {
        for &root in &[false, true] {
            let sig = facet_sig();
            let arena = facet_population(&sig, root, 320);
            let facets = facets_of(&arena, &sig);
            let (mut seen_pred, mut seen_succ, mut seen_rsucc) = (0usize, 0usize, 0usize);
            for (i, c) in arena.iter().enumerate() {
                let flags = facets.flags_of(i as u32);
                assert_eq!(
                    flags.seed_pred,
                    c.head
                        .iter()
                        .all(|l| l.is_function_free() && matches!(l, Lit::P(_))),
                    "seed_pred mismatch on clause {i}"
                );
                assert_eq!(
                    flags.seed_succ,
                    c.max_head_predicates()
                        .any(|(p, _)| is_function(p.max_term())),
                    "seed_succ mismatch on clause {i}"
                );
                assert_eq!(
                    flags.sat_pred,
                    c.head.iter().all(|l| {
                        l.is_function_free()
                            && match l {
                                Lit::P(_) => true,
                                Lit::Eq { s, t } => {
                                    is_individual(*s) && (*t == X || *t == Y || is_individual(*t))
                                }
                                Lit::Ineq { .. } => false,
                            }
                    }),
                    "sat_pred mismatch on clause {i}"
                );
                assert_eq!(
                    flags.sat_succ,
                    c.max_head_predicates()
                        .any(|(p, _)| is_function(p.max_term()) || root_succ_form(&p).is_some()),
                    "sat_succ mismatch on clause {i}"
                );
                assert_eq!(
                    flags.sat_rsucc,
                    sig.rsucc
                        && c.max_head_predicates().any(|(p, _)| match p {
                            Pred::Concept { iri, t } => is_central(t) && sig.is_reach(iri),
                            _ => false,
                        }),
                    "sat_rsucc mismatch on clause {i}"
                );
                seen_pred += usize::from(flags.sat_pred);
                seen_succ += usize::from(flags.sat_succ);
                seen_rsucc += usize::from(flags.sat_rsucc);
            }
            assert!(
                seen_pred > 0 && seen_succ > 0 && seen_rsucc > 0,
                "population must exercise all three pools (root={root}): \
                 pred={seen_pred} succ={seen_succ} rsucc={seen_rsucc}"
            );
        }
    }

    /// End-to-end mirror invariant: after a real classification the facet table
    /// must still be exactly parallel to the clause arena in both ordering
    /// domains, and every entry must equal a fresh derivation from its clause.
    /// This is what makes the `facets.keys_of(cid)` lookups in `index_clause` /
    /// `unindex_clause` safe — a table that drifted out of lockstep would file
    /// clauses under another clause's keys.  The derived subsumptions are
    /// asserted alongside, so a drift that happened to keep the table's shape
    /// still fails.
    #[test]
    fn cc_facets_mirrors_cc_arena_end_to_end() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b = sig.concept("B");
        let c = sig.concept("C");
        let d = sig.concept("D");
        let g1 = sig.concept("G1");
        let g2 = sig.concept("G2");
        let r = sig.role("R");
        let f1 = fterm(1);
        let clauses = vec![
            // A ⊑ ∃R.B, so the successor context and the non-root domain are used.
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(r, X, f1))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(b, f1))]),
            // B ⊑ C, derived inside the successor and pushed back by Pred.
            OntologyClause::new(vec![cx(b, X)], vec![Lit::P(cx(c, X))]),
            // ∃R.C ⊑ D, the Hyper firing that consumes the pushed-back clause.
            OntologyClause::new(
                vec![rl(r, X, zvar(1)), cx(c, zvar(1))],
                vec![Lit::P(cx(d, X))],
            ),
            // A ⊑ G1 ⊔ G2 with G2 ⊑ G1 strengthens to A ⊑ G1 in the root
            // context, so the run really drives back-subsumption (and hence
            // `unindex_clause`) rather than only insertion.
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(g1, X)), Lit::P(cx(g2, X))]),
            OntologyClause::new(vec![cx(g2, X)], vec![Lit::P(cx(g1, X))]),
        ];
        let mut e = Engine::new(sig, clauses, 0);
        e.run_for(&[a]);
        assert!(!e.inconsistent());
        let sups = supers_of(&e, "A");
        assert!(
            sups.contains(&"D".to_string()),
            "expected A ⊑ D across the Succ/Pred edge, got {sups:?}"
        );
        assert!(
            sups.contains(&"G1".to_string()),
            "expected A ⊑ G1 from the strengthened disjunction, got {sups:?}"
        );
        let mut checked = 0usize;
        for domain in 0..2 {
            assert_eq!(
                e.cc_facets[domain].len(),
                e.cc_arena[domain].len(),
                "FacetTable is not parallel to cc_arena[{domain}]"
            );
            for (i, clause) in e.cc_arena[domain].iter().enumerate() {
                let mut expect = Vec::new();
                facet_keys(clause, &mut expect);
                assert_eq!(
                    e.cc_facets[domain].keys_of(i as u32),
                    expect.as_slice(),
                    "facet keys drifted for cc_arena[{domain}][{i}]"
                );
                assert_eq!(
                    e.cc_facets[domain].flags_of(i as u32),
                    clause_flags(clause, &e.sig),
                    "clause flags drifted for cc_arena[{domain}][{i}]"
                );
                checked += 1;
            }
        }
        assert!(checked > 0, "the run interned no clauses");
    }

    /// End-to-end: a live disjunction strengthened to a unit by resolution
    /// (`A ⊑ B ⊔ C`, `C ⊑ B` ⟹ `A ⊑ B`) drives real back-subsumption of a
    /// worked-off clause through the incremental `unindex_clause` path.  The
    /// derived subsumption must be unchanged.
    #[test]
    fn disjunct_strengthening_backsubsumes_and_derives() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b = sig.concept("B");
        let c = sig.concept("C");
        let clauses = vec![
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(b, X)), Lit::P(cx(c, X))]),
            OntologyClause::new(vec![cx(c, X)], vec![Lit::P(cx(b, X))]),
        ];
        let mut e = Engine::new(sig, clauses, 0);
        e.run_for(&[a]);
        let sups = supers_of(&e, "A");
        assert!(sups.contains(&"B".to_string()), "expected A ⊑ B, got {sups:?}");
        assert!(!e.inconsistent());
    }

    /// arXiv:1805.01396 Example 3 — the O+I+Q interaction that needs the Nom
    /// rule (additional nominals): A ⊑ ∃R.B1 ⊓ ∃R.B2, every B1/B2 element has
    /// an incoming S-edge from o, S is functional, ∃R.(B1⊓B2) ⊑ C.  Both
    /// anonymous R-successors of an A-element are S-successors of o, hence
    /// merged by functionality into one element (the additional nominal),
    /// which is then B1 ⊓ B2, so A ⊑ C.
    #[test]
    fn nom_rule_oiq_example3() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b1 = sig.concept("B1");
        let b2 = sig.concept("B2");
        let c = sig.concept("C");
        let rr = sig.role("R");
        let ss = sig.role("S");
        let o = ind_term(1);
        let f = fterm(1);
        let g = fterm(2);
        let clauses = vec![
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(rr, X, f))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(b1, f))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(rr, X, g))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(b2, g))]),
            OntologyClause::new(vec![cx(b1, X)], vec![Lit::P(rl(ss, o, X))]),
            OntologyClause::new(vec![cx(b2, X)], vec![Lit::P(rl(ss, o, X))]),
            // functionality of S: S(x,z1) ∧ S(x,z2) → z1 ≈ z2
            OntologyClause::new(
                vec![rl(ss, X, zvar(1)), rl(ss, X, zvar(2))],
                vec![Lit::eq(zvar(1), zvar(2))],
            ),
            // ∃R.(B1 ⊓ B2) ⊑ C
            OntologyClause::new(
                vec![rl(rr, zvar(1), X), cx(b1, X), cx(b2, X)],
                vec![Lit::P(cx(c, zvar(1)))],
            ),
        ];
        let mut e = Engine::new(sig, clauses, 0);
        e.run_for(&[a]);
        let sups = supers_of(&e, "A");
        assert!(
            sups.contains(&"C".to_string()),
            "expected A ⊑ C via the Nom rule, got {:?}",
            sups
        );
        assert!(!e.inconsistent());
    }

    /// Interning the context core by content hash (`core_index` / `central_index`
    /// keyed by `content_hash(core)` -> candidate ids, exact-compared) must
    /// preserve the exact dedup semantics of the old `HashMap<Vec<Pred>, usize>`:
    /// an identical core reuses its context (never creating a duplicate), a
    /// distinct core gets a distinct id, and the core lives only in
    /// `Context.core` (the single interning source of truth). Root and central
    /// successor cores stay in separate index domains, so an equal core in each
    /// must resolve to two different contexts. This is the memory-reduction
    /// invariant: the duplicate `Vec<Pred>` key is gone, dedup is unchanged.
    #[test]
    fn context_core_interning_dedup() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b = sig.concept("B");
        let mut e = Engine::new(sig, vec![], 0);

        let core_a = vec![cx(a, X)];
        let core_b = vec![cx(b, X)];

        // Same core -> same id, and no duplicate context is created.
        let id_a = e.get_or_create_context(core_a.clone(), true, Some(a));
        let n_after_first = e.contexts.len();
        let id_a2 = e.get_or_create_context(core_a.clone(), true, Some(a));
        assert_eq!(id_a, id_a2, "identical core must reuse the same context");
        assert_eq!(
            e.contexts.len(),
            n_after_first,
            "re-requesting an existing core must not create a context"
        );
        // The core is stored once, in Context.core.
        assert_eq!(e.contexts[id_a].core, core_a);

        // Distinct core -> distinct id.
        let id_b = e.get_or_create_context(core_b.clone(), true, Some(b));
        assert_ne!(id_a, id_b, "distinct cores must get distinct contexts");
        assert_eq!(e.contexts[id_b].core, core_b);

        // Root and central successor domains are kept separate: an equal core in
        // each must NOT be deduplicated together (root vs non-root ordering).
        let cid_a = e.central_successor_for_core(core_a.clone(), None);
        assert_ne!(
            id_a, cid_a,
            "a central core equal to a root core must be its own context"
        );
        assert_eq!(e.contexts[cid_a].core, core_a);
        // The central index dedups identical cores just like the root index.
        let cid_a2 = e.central_successor_for_core(core_a.clone(), None);
        assert_eq!(cid_a, cid_a2, "central index must dedup identical cores");
    }

    /// Negative control for Nom: without the functionality clause the two
    /// successors need not merge, so A ⊑ C must NOT be derived.
    #[test]
    fn nom_rule_no_counting_no_merge() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b1 = sig.concept("B1");
        let b2 = sig.concept("B2");
        let c = sig.concept("C");
        let rr = sig.role("R");
        let ss = sig.role("S");
        let o = ind_term(1);
        let f = fterm(1);
        let g = fterm(2);
        let clauses = vec![
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(rr, X, f))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(b1, f))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(rr, X, g))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(b2, g))]),
            OntologyClause::new(vec![cx(b1, X)], vec![Lit::P(rl(ss, o, X))]),
            OntologyClause::new(vec![cx(b2, X)], vec![Lit::P(rl(ss, o, X))]),
            OntologyClause::new(
                vec![rl(rr, zvar(1), X), cx(b1, X), cx(b2, X)],
                vec![Lit::P(cx(c, zvar(1)))],
            ),
        ];
        let mut e = Engine::new(sig, clauses, 0);
        e.run_for(&[a]);
        let sups = supers_of(&e, "A");
        assert!(
            !sups.contains(&"C".to_string()),
            "A ⊑ C must not be derived without functionality, got {:?}",
            sups
        );
        assert!(!e.inconsistent());
    }

    /// Filler-merge through a nominal (the Phase-1 witness, engine-level):
    /// A ⊑ ∃r.({o}⊓B), A ⊑ ∃r.({o}⊓C), B⊓C ⊑ E, ∃r.E ⊑ G entails A ⊑ G.
    /// Clausified with individuals as constants (DL8 for the {o} conjuncts:
    /// the filler definers imply x ≈ o).
    #[test]
    fn nominal_filler_merge() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b = sig.concept("B");
        let c = sig.concept("C");
        let ee = sig.concept("E");
        let g = sig.concept("G");
        let d1 = sig.concept("__d1");
        let d2 = sig.concept("__d2");
        let r = sig.role("r");
        let o = ind_term(1);
        let f1 = fterm(1);
        let f2 = fterm(2);
        let clauses = vec![
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(r, X, f1))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(d1, f1))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(r, X, f2))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(d2, f2))]),
            // definers: __d1 ⊑ {o} ⊓ B, __d2 ⊑ {o} ⊓ C
            OntologyClause::new(vec![cx(d1, X)], vec![Lit::eq(X, o)]),
            OntologyClause::new(vec![cx(d1, X)], vec![Lit::P(cx(b, X))]),
            OntologyClause::new(vec![cx(d2, X)], vec![Lit::eq(X, o)]),
            OntologyClause::new(vec![cx(d2, X)], vec![Lit::P(cx(c, X))]),
            OntologyClause::new(vec![cx(b, X), cx(c, X)], vec![Lit::P(cx(ee, X))]),
            OntologyClause::new(
                vec![rl(r, X, zvar(1)), cx(ee, zvar(1))],
                vec![Lit::P(cx(g, X))],
            ),
        ];
        let mut e = Engine::new(sig, clauses, 0);
        e.run_for(&[a]);
        let sups = supers_of(&e, "A");
        assert!(
            sups.contains(&"G".to_string()),
            "expected A ⊑ G via nominal filler merge, got {:?}",
            sups
        );
        assert!(!e.inconsistent());
    }

    #[test]
    fn guarded_role_hyper_index_preserves_absorbed_existential() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let c = sig.concept("C");
        let d = sig.concept("D");
        let r = sig.role("r");
        let f = fterm(1);
        let clauses = vec![
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(c, f))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(r, X, f))]),
            OntologyClause::new(
                vec![cx(c, zvar(1)), rl(r, X, zvar(1))],
                vec![Lit::P(cx(d, X))],
            ),
        ];
        let prepared = Engine::prepare(sig, clauses, 0);
        assert!(prepared.ont.clauses_cand(&rl(r, X, f)).is_empty());
        assert_eq!(
            prepared.ont.role_target_concept_body.get(&r),
            Some(&vec![(c, 2)])
        );

        let mut engine = Engine::from_prepared(&prepared);
        engine.run_for(&[a]);
        let supers = supers_of(&engine, "A");
        assert!(
            supers.contains(&"D".to_string()),
            "guarded role lookup lost A ⊑ D: {supers:?}"
        );
    }

    /// ABox + nominal unsat: C(o) asserted, B ⊑ {o}, B ⊓ owl-disjoint with C
    /// via B(x) ∧ C(x) → ⊥, and A ⊑ ∃r.B forces the successor to BE o, which
    /// is both B and C — A is unsatisfiable.
    #[test]
    fn nominal_ground_clash() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b = sig.concept("B");
        let c = sig.concept("C");
        let r = sig.role("r");
        let o = ind_term(1);
        let f = fterm(1);
        let clauses = vec![
            OntologyClause::new(vec![], vec![Lit::P(cx(c, o))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(r, X, f))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(b, f))]),
            OntologyClause::new(vec![cx(b, X)], vec![Lit::eq(X, o)]),
            OntologyClause::new(vec![cx(b, X), cx(c, X)], vec![]),
        ];
        let mut e = Engine::new(sig, clauses, 0);
        e.run_for(&[a]);
        let sups = supers_of(&e, "A");
        assert!(
            sups.contains(&"owl:Nothing".to_string()),
            "expected A unsatisfiable (successor is o, which is C and B), got {:?}",
            sups
        );
    }

    #[test]
    fn asserted_ground_equality_merge_transfers_labels_and_links() {
        let a = ind_term(1);
        let alias = ind_term(2);
        let other = ind_term(3);
        let concept = cx(7, alias);
        let canonical_concept = cx(7, a);
        let role = rl(11, alias, other);
        let canonical_role = rl(11, a, other);
        let clauses = vec![
            OntologyClause::new(vec![], vec![Lit::eq(alias, a)]),
            OntologyClause::new(vec![], vec![Lit::P(concept)]),
            OntologyClause::new(vec![], vec![Lit::P(canonical_concept)]),
            OntologyClause::new(vec![], vec![Lit::P(role)]),
            OntologyClause::new(vec![cx(8, X)], vec![Lit::eq(X, alias)]),
        ];

        let (merged, max_ind, stats) = merge_asserted_ground_equalities(clauses);
        assert_eq!(max_ind, 3, "fresh nominal allocation retains input ids");
        assert_eq!(stats.asserted_pairs, 1);
        assert_eq!(stats.merged_aliases, 1);
        assert!(merged.iter().any(|clause| {
            clause.body.is_empty() && clause.head == vec![Lit::P(canonical_concept)]
        }));
        assert_eq!(
            merged
                .iter()
                .filter(|clause| clause.body.is_empty()
                    && clause.head == vec![Lit::P(canonical_concept)])
                .count(),
            1,
            "representative labels form a set"
        );
        assert!(merged.iter().any(|clause| {
            clause.body.is_empty() && clause.head == vec![Lit::P(canonical_role)]
        }));
        assert!(merged
            .iter()
            .any(|clause| { clause.body == vec![cx(8, X)] && clause.head == vec![Lit::eq(X, a)] }));
        assert!(!merged.iter().any(|clause| {
            clause.head == vec![Lit::eq(alias, a)]
                || clause.head == vec![Lit::P(concept)]
                || clause.head == vec![Lit::P(role)]
        }));
    }

    #[test]
    fn asserted_same_and_different_individuals_collapse_to_clash() {
        let a = ind_term(1);
        let alias = ind_term(2);
        let clauses = vec![
            OntologyClause::new(vec![], vec![Lit::eq(alias, a)]),
            OntologyClause::new(vec![], vec![Lit::ineq(alias, a)]),
        ];
        let (merged, _, stats) = merge_asserted_ground_equalities(clauses);
        assert_eq!(stats.merged_aliases, 1);
        assert_eq!(merged.len(), 1);
        assert!(merged[0].body.is_empty() && merged[0].head.is_empty());
    }

    #[test]
    fn disjunctive_ground_equality_is_not_an_asserted_merge() {
        let a = ind_term(1);
        let b = ind_term(2);
        let clauses = vec![OntologyClause::new(
            vec![],
            vec![Lit::eq(b, a), Lit::P(cx(7, X))],
        )];
        let (merged, _, stats) = merge_asserted_ground_equalities(clauses);
        assert_eq!(stats.asserted_pairs, 0);
        assert_eq!(stats.merged_aliases, 0);
        assert_eq!(merged[0].head, vec![Lit::P(cx(7, X)), Lit::eq(b, a)]);
    }

    #[test]
    fn ground_hyper_uses_bound_role_endpoints_without_order_dependence() {
        fn run(facts_reversed: bool) {
            let mut sig = Sig::default();
            let c = sig.concept("C");
            let d = sig.concept("D");
            let e = sig.concept("E");
            let r = sig.role("R");
            let left = ind_term(1);
            let right = ind_term(2);
            let mut facts = vec![
                OntologyClause::new(vec![], vec![Lit::P(cx(c, right))]),
                OntologyClause::new(vec![], vec![Lit::P(rl(r, left, right))]),
                OntologyClause::new(vec![], vec![Lit::P(rl(r, right, left))]),
                // Mixed fixed/variable roles are the nominal-calculus shape
                // used by functionality and r-Succ (`S(o,y)`). They must be
                // present in the corresponding one-endpoint posting too.
                OntologyClause::new(vec![], vec![Lit::P(rl(r, left, Y))]),
                OntologyClause::new(vec![], vec![Lit::P(rl(r, Y, right))]),
            ];
            if facts_reversed {
                facts.reverse();
            }
            let mut clauses = vec![
                // Binding C(y) first selects only R(_, right) by target.
                OntologyClause::new(
                    vec![cx(c, zvar(1)), rl(r, X, zvar(1))],
                    vec![Lit::P(cx(d, X))],
                ),
                // The inverse orientation selects only R(right, _) by source.
                OntologyClause::new(
                    vec![cx(c, zvar(1)), rl(r, zvar(1), X)],
                    vec![Lit::P(cx(e, X))],
                ),
            ];
            clauses.extend(facts);
            let mut engine = Engine::new(sig, clauses, 0);
            engine.run_for(&[]);
            let ground_id = engine.ground_ctx.expect("ground context");
            let context = &engine.contexts[ground_id];
            let arena = &engine.cc_arena[context.root as usize];
            let has = |predicate: Pred| {
                context.worked_off.iter().any(|&cid| {
                    let clause = &arena[cid as usize];
                    clause.body.is_empty() && clause.head == vec![Lit::P(predicate)]
                })
            };
            assert!(has(cx(d, left)));
            assert!(has(cx(e, left)));
            assert!(context.ground_role_target_index.contains_key(&(r, right)));
            assert!(context.ground_role_source_index.contains_key(&(r, right)));
            assert!(context
                .ground_role_source_index
                .get(&(r, left))
                .is_some_and(|posting| posting.len() >= 2));
            assert!(context
                .ground_role_target_index
                .get(&(r, right))
                .is_some_and(|posting| posting.len() >= 2));
        }

        run(false);
        run(true);
    }

    #[test]
    fn resource_backstops_mark_the_engine_incomplete() {
        let mut e = Engine::new(Sig::default(), Vec::new(), 0);
        assert!(!e.incomplete());
        e.message_truncated = true;
        assert!(e.incomplete());
        e.message_truncated = false;
        e.nom_truncated.set(true);
        assert!(e.incomplete());
    }

    #[test]
    fn exact_max_head_pred_index_separates_terms() {
        let sig = Sig::default();
        let p1 = cx(7, fterm(1));
        let p2 = cx(7, fterm(2));
        let arena = vec![
            ContextClause::new(vec![], vec![Lit::P(p1)], false, &sig),
            ContextClause::new(vec![], vec![Lit::P(p2)], false, &sig),
        ];
        let facets = facets_of(&arena, &sig);
        let mut ctx = Context::new(0, vec![], false, None);
        for cid in 0..arena.len() as u32 {
            ctx.worked_off.push(cid);
            ctx.index_clause(&facets, cid);
        }

        assert_eq!(ctx.head_concept_index.get(&7).unwrap().as_slice(), &[0, 1]);
        assert_eq!(ctx.max_head_pred_index.get(&p1).unwrap().as_slice(), &[0]);
        assert_eq!(ctx.max_head_pred_index.get(&p2).unwrap().as_slice(), &[1]);
    }

    #[test]
    fn max_head_term_index_matches_sequoia_eq_lookup() {
        let sig = Sig::default();
        let f1 = fterm(1);
        let f2 = fterm(2);
        let f3 = fterm(3);
        let o = ind_term(1);
        let arena = vec![
            ContextClause::new(vec![], vec![Lit::P(cx(1, f1))], false, &sig),
            ContextClause::new(
                vec![],
                vec![Lit::P(Pred::Role {
                    iri: 1,
                    s: X,
                    t: f2,
                })],
                false,
                &sig,
            ),
            ContextClause::new(vec![], vec![Lit::eq(f3, o)], false, &sig),
        ];
        let facets = facets_of(&arena, &sig);
        let mut ctx = Context::new(0, vec![], false, None);
        for cid in 0..arena.len() as u32 {
            ctx.worked_off.push(cid);
            ctx.index_clause(&facets, cid);
        }

        assert_eq!(ctx.max_head_term_index[&f1].as_slice(), &[0]);
        assert_eq!(ctx.max_head_term_index[&f2].as_slice(), &[1]);
        assert_eq!(ctx.max_head_term_index[&X].as_slice(), &[1]);
        assert_eq!(ctx.max_head_term_index[&f3].as_slice(), &[2]);
        assert!(!ctx.max_head_term_index.contains_key(&o));
    }

    #[test]
    fn sequoia_active_redundancy_index_matches_linear_subsumption() {
        let sig = Sig::default();
        let o = ind_term(1);
        let p1 = cx(1, o);
        let p2 = cx(2, o);
        let h1 = Lit::P(cx(3, o));
        let h2 = Lit::P(cx(4, o));
        let mut arena = vec![
            ContextClause::new(vec![], vec![h1], false, &sig),
            ContextClause::new(vec![p1], vec![h2], false, &sig),
            ContextClause::new(vec![p2], vec![], false, &sig),
        ];
        // Inflate a shared head to exercise a case that made the former
        // posting-list scan expensive.
        for i in 0..32 {
            arena.push(ContextClause::new(
                vec![cx(100 + i, o)],
                vec![h1],
                false,
                &sig,
            ));
        }
        let facets = facets_of(&arena, &sig);
        let mut ctx = Context::new(0, vec![], false, None);
        for cid in 0..arena.len() as u32 {
            ctx.clause_keys.insert(cid);
            ctx.index_active_clause(&arena, cid);
            if cid % 2 == 0 {
                ctx.worked_off.push(cid);
                ctx.index_clause(&facets, cid);
            } else {
                ctx.todo.push_back(cid);
            }
        }

        let bodies = vec![vec![], vec![p1], vec![p2], vec![p1, p2], vec![cx(131, o)]];
        let heads = vec![vec![], vec![h1], vec![h2], vec![h1, h2]];
        for body in bodies {
            for head in &heads {
                let incoming = ContextClause::new(body.clone(), head.clone(), false, &sig);
                let expected = ctx
                    .clause_keys
                    .iter()
                    .any(|&cid| arena[cid as usize].test_strengthening(&incoming) == -1);
                let actual = ctx.fwd_subsumed(&arena, &sigs_of(&arena), &incoming, None);
                assert_eq!(
                    actual, expected,
                    "indexed and linear forward subsumption differ for {:?}",
                    incoming
                );
            }
        }
    }

    /// Deterministic pseudo-random clause population used by the `ClauseSig`
    /// screen tests below.  A small predicate/literal alphabet with a lot of
    /// reuse is what makes subsumption pairs actually occur; a wide alphabet
    /// would make almost every pair trivially incomparable and the test
    /// vacuous.
    fn screen_population(sig: &Sig, root: bool, n: usize) -> Vec<ContextClause> {
        let o = ind_term(1);
        let preds = [
            cx(1, X),
            cx(2, X),
            cx(3, X),
            cx(1, o),
            rl(7, X, o),
            rl(7, X, Y),
            rl(8, X, Y),
            cx(4, Y),
        ];
        let lits = [
            Lit::P(cx(11, X)),
            Lit::P(cx(12, X)),
            Lit::P(cx(13, X)),
            Lit::P(rl(7, X, o)),
            Lit::P(rl(9, X, Y)),
            Lit::eq(X, o),
            Lit::ineq(X, o),
            Lit::eq(Y, o),
        ];
        let mut state = 0x2545_f491_4f6c_dd1du64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            // Subset-heavy sampling: pick each alphabet element independently
            // with probability ~1/3, so bodies/heads of very different sizes
            // and genuine subset pairs both occur often.
            let (bm, hm) = (next(), next());
            let body: Vec<Pred> = preds
                .iter()
                .enumerate()
                .filter(|(i, _)| (bm >> (i * 3)) % 3 == 0)
                .map(|(_, &p)| p)
                .collect();
            let head: Vec<Lit> = lits
                .iter()
                .enumerate()
                .filter(|(i, _)| (hm >> (i * 3)) % 3 == 0)
                .map(|(_, &l)| l)
                .collect();
            out.push(ContextClause::new(body, head, root, sig));
        }
        out
    }

    /// Safety contract of the dense subsumption screen: it may only ever reject
    /// a candidate that genuinely does not subsume.  A single false negative
    /// would silently drop a redundancy elimination — forward subsumption would
    /// admit a clause it should have skipped, back subsumption would keep a
    /// clause it should have removed — so this is the property that makes the
    /// screen fixpoint-preserving rather than merely fast.
    #[test]
    fn clause_sig_screen_never_rejects_a_genuine_subsumer() {
        let sig = Sig::default();
        for &root in &[false, true] {
            let pop = screen_population(&sig, root, 400);
            let sigs = sigs_of(&pop);
            let mut witnessed = 0usize;
            for (i, a) in pop.iter().enumerate() {
                for (j, b) in pop.iter().enumerate() {
                    if a.strengthens(b) {
                        witnessed += 1;
                        assert!(
                            sigs[i].may_strengthen(&sigs[j]),
                            "screen rejected a real subsumer: {a:?} strengthens {b:?}"
                        );
                    }
                }
            }
            // Guard against a vacuous pass: the population must actually contain
            // subsumption pairs beyond the reflexive ones.
            assert!(
                witnessed > pop.len(),
                "population produced no non-reflexive subsumption pairs ({witnessed})"
            );
        }
    }

    /// The screen must also be selective enough to be worth its keep: on a
    /// population where most pairs are incomparable it has to reject the large
    /// majority of candidates without consulting the clause.
    #[test]
    fn clause_sig_screen_rejects_most_non_subsumers() {
        let sig = Sig::default();
        let pop = screen_population(&sig, false, 200);
        let sigs = sigs_of(&pop);
        let (mut pairs, mut passed, mut real) = (0usize, 0usize, 0usize);
        for (i, a) in pop.iter().enumerate() {
            for (j, b) in pop.iter().enumerate() {
                pairs += 1;
                if sigs[i].may_strengthen(&sigs[j]) {
                    passed += 1;
                }
                if a.strengthens(b) {
                    real += 1;
                }
            }
        }
        assert!(
            passed * 2 < pairs,
            "screen let through {passed}/{pairs} pairs ({real} real) — no filtering value"
        );
    }

    /// Forward subsumption with the screen must return exactly what an
    /// unscreened linear scan over the active clause set returns, for every
    /// incoming clause drawn from the same alphabet.  This is the end-to-end
    /// equivalence the screen has to preserve at the call site, indexes
    /// included.
    #[test]
    fn screened_fwd_subsumed_matches_unscreened_linear_scan() {
        let sig = Sig::default();
        let arena = screen_population(&sig, false, 240);
        let sigs = sigs_of(&arena);
        let facets = facets_of(&arena, &sig);
        let mut ctx = Context::new(0, vec![], false, None);
        for cid in 0..arena.len() as u32 {
            if ctx.clause_keys.insert(cid) {
                ctx.index_active_clause(&arena, cid);
                if cid % 3 == 0 {
                    ctx.worked_off.push(cid);
                    ctx.index_clause(&facets, cid);
                } else {
                    ctx.todo.push_back(cid);
                }
            }
        }
        let probes = screen_population(&sig, false, 240);
        let mut hits = 0usize;
        for (k, incoming) in probes.iter().enumerate() {
            // Exercise the `exclude` path too (the work-off re-check passes the
            // clause's own arena id).
            let exclude = if k % 4 == 0 {
                arena
                    .iter()
                    .position(|c| c.body == incoming.body && c.head == incoming.head)
                    .map(|i| i as u32)
            } else {
                None
            };
            let expected = ctx
                .clause_keys
                .iter()
                .any(|&cid| Some(cid) != exclude && arena[cid as usize].strengthens(incoming));
            let actual = ctx.fwd_subsumed(&arena, &sigs, incoming, exclude);
            assert_eq!(
                actual, expected,
                "screened and unscreened forward subsumption differ for {incoming:?}"
            );
            hits += expected as usize;
        }
        assert!(hits > 0, "no probe was subsumed — the test proves nothing");
        assert!(hits < probes.len(), "every probe was subsumed — degenerate");
    }

    /// Back subsumption with the screen must remove exactly the clause set an
    /// unscreened scan removes.  Removing too few leaves redundant clauses
    /// alive (slower but sound); removing too many would drop a clause that is
    /// NOT entailed by the survivor, which is a completeness bug — so the
    /// removal sets are compared for equality, not inclusion.
    #[test]
    fn screened_back_subsume_removes_the_same_clauses() {
        let sig = Sig::default();
        let arena = screen_population(&sig, false, 200);
        let sigs = sigs_of(&arena);
        let facets = facets_of(&arena, &sig);
        let strengtheners = screen_population(&sig, false, 60);
        let mut checked = 0usize;
        for clause in &strengtheners {
            let mut ctx = Context::new(0, vec![], false, None);
            for cid in 0..arena.len() as u32 {
                if ctx.clause_keys.insert(cid) {
                    ctx.index_active_clause(&arena, cid);
                    ctx.worked_off.push(cid);
                    ctx.index_clause(&facets, cid);
                }
            }
            let before: HashSet<u32> = ctx.clause_keys.clone();
            let expected: HashSet<u32> = before
                .iter()
                .copied()
                .filter(|&cid| {
                    let candidate = &arena[cid as usize];
                    clause.strengthens(candidate)
                        && !(candidate.body == clause.body && candidate.head == clause.head)
                })
                .collect();
            ctx.back_subsume(&arena, &sigs, &facets, clause);
            let removed: HashSet<u32> = before.difference(&ctx.clause_keys).copied().collect();
            assert_eq!(
                removed, expected,
                "screened back subsumption removed a different set for {clause:?}"
            );
            checked += removed.len();
        }
        assert!(checked > 0, "no clause was ever back-subsumed — vacuous");
    }

    /// The dense signature array must stay in lockstep with the clause arena:
    /// every arena id indexes a `ClauseSig` describing exactly that clause.
    /// The subsumption scans index `cc_sig` by arena id with no bounds fallback,
    /// so a drift here would mis-screen (or panic) rather than fail loudly.
    #[test]
    fn clause_sig_array_mirrors_the_clause_arena() {
        let clauses = vec![
            OntologyClause::new(vec![cx(1, X)], vec![Lit::P(cx(2, X))]),
            OntologyClause::new(vec![cx(2, X)], vec![Lit::P(cx(3, X)), Lit::P(cx(4, X))]),
            OntologyClause::new(vec![cx(3, X), cx(4, X)], vec![]),
            OntologyClause::new(vec![cx(1, X)], vec![Lit::P(rl(5, X, fterm(1)))]),
            OntologyClause::new(vec![cx(1, X)], vec![Lit::P(cx(2, fterm(1)))]),
        ];
        let mut sig = Sig::default();
        for name in ["A", "B", "C", "D", "E", "F"] {
            sig.concept(name);
        }
        let mut e = Engine::new(sig, clauses, 0);
        e.run();
        for d in 0..2usize {
            assert_eq!(
                e.cc_sig[d].len(),
                e.cc_arena[d].len(),
                "cc_sig/cc_arena length drift in domain {d}"
            );
            for (i, c) in e.cc_arena[d].iter().enumerate() {
                assert_eq!(
                    e.cc_sig[d][i],
                    ClauseSig::of(c),
                    "cc_sig[{d}][{i}] does not describe its arena clause"
                );
            }
        }
        assert!(
            e.cc_arena[0].len() + e.cc_arena[1].len() > 5,
            "run derived too little to exercise the arena"
        );
    }

    #[test]
    fn sequoia_redundancy_trie_removes_exact_supersets() {
        let sig = Sig::default();
        let a = cx(1, X);
        let b = cx(2, X);
        let c = Lit::P(cx(3, X));
        let d = Lit::P(cx(4, X));
        let strong = ContextClause::new(vec![a], vec![c], false, &sig);
        let equal = ContextClause::new(vec![a], vec![c], false, &sig);
        let weak_body = ContextClause::new(vec![a, b], vec![c], false, &sig);
        let weak_head = ContextClause::new(vec![a], vec![c, d], false, &sig);
        let incomparable = ContextClause::new(vec![b], vec![d], false, &sig);
        let clauses = [equal, weak_body, weak_head, incomparable];
        let mut trie = RedundancyTrie::default();
        for (cid, clause) in clauses.iter().enumerate() {
            trie.insert(clause, cid as u32);
        }

        assert!(trie.contains_subset(&strong, None));
        assert!(!trie.contains_subset(&strong, Some(0)));
        let mut removed = trie.remove_supersets(&strong);
        removed.sort_unstable();
        assert_eq!(removed, vec![0, 1, 2]);
        assert!(!trie.contains_subset(&strong, None));
        assert!(trie.contains_subset(&clauses[3], None));
    }

    #[test]
    fn local_pred_pins_triggering_clause_like_sequoia() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b = sig.concept("B");
        let c = sig.concept("C");
        let max = cx(a, fterm(1));
        let other = cx(b, X);
        let guard = cx(c, X);
        let mut e = Engine::new(sig, vec![], 0);
        e.contexts.push(Context::new(0, vec![], false, None));
        e.cc_arena[0] = vec![
            ContextClause::new(vec![], vec![Lit::P(max)], false, &e.sig),
            ContextClause::new(vec![], vec![Lit::P(other)], false, &e.sig),
        ];
        e.rebuild_cc_mirrors(0);
        for cid in 0..e.cc_arena[0].len() as u32 {
            e.contexts[0].worked_off.push(cid);
            e.contexts[0].index_clause(&e.cc_facets[0], cid);
        }
        e.pred_interned.push(PredClause {
            body: vec![max, other],
            head: vec![],
        });
        e.contexts[0].neighbor_pred.push(0);
        e.contexts[0]
            .neighbor_pred_body_index
            .entry(max)
            .or_default()
            .push(0);

        let side = ContextClause::new(vec![guard], vec![Lit::P(max)], false, &e.sig);
        let local = e.pred_local_inner(0, &side, max, false);
        assert_eq!(local.len(), 1);
        assert_eq!(local[0].body, vec![guard]);

        // The complementary event remains complete: if the Pred clause arrives
        // after both providers, it joins against the full worked-off index.
        let late = e.pred_from_neighbor(0, &e.pred_interned[0], false);
        assert_eq!(late.len(), 1);
        assert!(late[0].body.is_empty());
    }

    #[test]
    fn incremental_pred_join_matches_sequoia_cartesian_antichain() {
        let mut sig = Sig::default();
        let p1 = cx(sig.concept("P1"), X);
        let p2 = cx(sig.concept("P2"), X);
        let p3 = cx(sig.concept("P3"), X);
        let a = cx(sig.concept("A"), X);
        let b = cx(sig.concept("B"), X);
        let h = Lit::P(cx(sig.concept("H"), X));
        let mut e = Engine::new(sig, vec![], 0);
        e.contexts.push(Context::new(0, vec![], false, None));
        // Each premise has two incomparable providers. The raw product has
        // eight selections, but its final strengthening antichain has only the
        // two unit bodies {A} and {B}; every mixed body is redundant.
        e.cc_arena[0] = vec![
            ContextClause::new(vec![a], vec![Lit::P(p1)], false, &e.sig),
            ContextClause::new(vec![b], vec![Lit::P(p1)], false, &e.sig),
            ContextClause::new(vec![a], vec![Lit::P(p2)], false, &e.sig),
            ContextClause::new(vec![b], vec![Lit::P(p2)], false, &e.sig),
            ContextClause::new(vec![a], vec![Lit::P(p3)], false, &e.sig),
            ContextClause::new(vec![b], vec![Lit::P(p3)], false, &e.sig),
        ];
        e.rebuild_cc_mirrors(0);
        for cid in 0..e.cc_arena[0].len() as u32 {
            e.contexts[0].worked_off.push(cid);
            e.contexts[0].index_clause(&e.cc_facets[0], cid);
        }
        let pred = PredClause {
            body: vec![p1, p2, p3],
            head: vec![h],
        };

        let incremental = e.pred_from_neighbor(0, &pred, false);
        let mut cartesian = PredResultBuffer::default();
        for first in [0usize, 1] {
            for second in [2usize, 3] {
                for third in [4usize, 5] {
                    let mut body = Vec::new();
                    body.extend_from_slice(&e.cc_arena[0][first].body);
                    body.extend_from_slice(&e.cc_arena[0][second].body);
                    body.extend_from_slice(&e.cc_arena[0][third].body);
                    push_nonredundant_pred_result(
                        &mut cartesian,
                        ContextClause::new(body, vec![h], false, &e.sig),
                    );
                }
            }
        }
        let canonical = |clauses: Vec<ContextClause>| {
            clauses
                .into_iter()
                .map(|clause| (clause.body, clause.head))
                .collect::<BTreeSet<_>>()
        };
        assert_eq!(canonical(incremental), canonical(cartesian.into_vec()));
    }

    /// The left-deep antichain join in `pred_local_inner` must retain exactly
    /// the antichain the full Cartesian product enumeration retained.  Anything
    /// missing is a completeness bug (a Pred conclusion never reaches the
    /// context); anything extra is redundant work the antichain was supposed to
    /// remove.  The scenarios below are randomised over premise counts,
    /// provider bodies and disjunctive heads, and include the shape that stalls
    /// on ORE 1194: several premises each with many incomparable providers.
    #[test]
    fn local_pred_left_deep_join_matches_full_product_antichain() {
        let canonical = |clauses: Vec<ContextClause>| {
            clauses
                .into_iter()
                .map(|clause| (clause.body, clause.head))
                .collect::<BTreeSet<_>>()
        };
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut compared = 0usize;
        let mut nonempty = 0usize;
        for scenario in 0..40usize {
            let mut sig = Sig::default();
            let premises: Vec<Pred> = (0..3 + scenario % 3)
                .map(|i| cx(sig.concept(&format!("P{i}")), X))
                .collect();
            let guards: Vec<Pred> = (0..4)
                .map(|i| cx(sig.concept(&format!("G{i}")), X))
                .collect();
            let extra: Vec<Lit> = (0..3)
                .map(|i| Lit::P(cx(sig.concept(&format!("H{i}")), X)))
                .collect();
            let trigger = cx(sig.concept("T"), fterm(1));
            let mut e = Engine::new(sig, vec![], 0);
            e.contexts.push(Context::new(0, vec![], false, None));

            // Providers: for each premise, a handful of clauses with that
            // premise maximal in the head, with pseudo-random bodies and
            // sometimes an extra head disjunct.
            let mut arena: Vec<ContextClause> = Vec::new();
            for premise in &premises {
                let providers = 2 + (next() % 4) as usize;
                for _ in 0..providers {
                    let mask = next();
                    let body: Vec<Pred> = guards
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| (mask >> (i * 5)) % 3 == 0)
                        .map(|(_, &p)| p)
                        .collect();
                    let mut head = vec![Lit::P(*premise)];
                    if mask % 7 == 0 {
                        head.push(extra[(mask % 3) as usize]);
                    }
                    arena.push(ContextClause::new(body, head, false, &e.sig));
                }
            }
            e.cc_arena[0] = arena;
            e.rebuild_cc_mirrors(0);
            for cid in 0..e.cc_arena[0].len() as u32 {
                e.contexts[0].worked_off.push(cid);
                e.contexts[0].index_clause(&e.cc_facets[0], cid);
            }

            // A neighbour Pred clause whose body is the pinned trigger plus
            // every premise, i.e. a multi-dimension local Pred join.
            let mut body = vec![trigger];
            body.extend(premises.iter().copied());
            body.sort();
            body.dedup();
            let head = if scenario % 2 == 0 {
                vec![extra[0]]
            } else {
                vec![extra[0], extra[1]]
            };
            e.pred_interned.push(PredClause { body, head });
            e.contexts[0].neighbor_pred.push(0);
            e.contexts[0]
                .neighbor_pred_body_index
                .entry(trigger)
                .or_default()
                .push(0);

            let side = ContextClause::new(
                vec![guards[scenario % guards.len()]],
                vec![Lit::P(trigger)],
                false,
                &e.sig,
            );
            let joined = e.pred_local_inner(0, &side, trigger, false);
            let reference = e.pred_local_full_product_reference(0, &side, trigger, false);
            assert_eq!(
                canonical(joined),
                canonical(reference),
                "left-deep join and full product disagree in scenario {scenario}"
            );
            compared += 1;
            nonempty += usize::from(!e.pred_local_inner(0, &side, trigger, false).is_empty());
        }
        assert_eq!(compared, 40);
        assert!(
            nonempty > 30,
            "only {nonempty}/40 scenarios produced conclusions — test is near-vacuous"
        );
    }

    /// The same equivalence on the exact shape that stalls: one premise with
    /// many incomparable providers, so the full product is large while its
    /// antichain is small.  This is the case where the two implementations do
    /// wildly different amounts of work and must still agree.
    #[test]
    fn local_pred_join_matches_product_on_a_wide_premise_set() {
        let mut sig = Sig::default();
        let premises: Vec<Pred> = (0..3)
            .map(|i| cx(sig.concept(&format!("P{i}")), X))
            .collect();
        let guards: Vec<Pred> = (0..12)
            .map(|i| cx(sig.concept(&format!("G{i}")), X))
            .collect();
        let h = Lit::P(cx(sig.concept("H"), X));
        let trigger = cx(sig.concept("T"), fterm(1));
        let mut e = Engine::new(sig, vec![], 0);
        e.contexts.push(Context::new(0, vec![], false, None));
        // 12 pairwise-incomparable providers per premise: the full product has
        // 12^3 = 1728 elements but its antichain is the 12 singleton bodies
        // (picking the same guard in all three premises); every mixed body is
        // strengthened by one of those.  That gap is exactly what the left-deep
        // join skips and the product enumeration pays for.
        let mut arena = Vec::new();
        for premise in &premises {
            for guard in &guards {
                arena.push(ContextClause::new(
                    vec![*guard],
                    vec![Lit::P(*premise)],
                    false,
                    &e.sig,
                ));
            }
        }
        e.cc_arena[0] = arena;
        e.rebuild_cc_mirrors(0);
        for cid in 0..e.cc_arena[0].len() as u32 {
            e.contexts[0].worked_off.push(cid);
            e.contexts[0].index_clause(&e.cc_facets[0], cid);
        }
        let mut body = vec![trigger];
        body.extend(premises.iter().copied());
        body.sort();
        e.pred_interned.push(PredClause {
            body,
            head: vec![h],
        });
        e.contexts[0].neighbor_pred.push(0);
        e.contexts[0]
            .neighbor_pred_body_index
            .entry(trigger)
            .or_default()
            .push(0);
        let side = ContextClause::new(vec![], vec![Lit::P(trigger)], false, &e.sig);

        let canonical = |clauses: Vec<ContextClause>| {
            clauses
                .into_iter()
                .map(|clause| (clause.body, clause.head))
                .collect::<BTreeSet<_>>()
        };
        let joined = canonical(e.pred_local_inner(0, &side, trigger, false));
        let reference = canonical(e.pred_local_full_product_reference(0, &side, trigger, false));
        assert_eq!(joined, reference);
        assert_eq!(
            joined.len(),
            guards.len(),
            "the 1728-element product must collapse to one union per guard"
        );
        for (body, _) in &joined {
            assert_eq!(body.len(), 1, "a mixed-guard body survived the antichain");
        }
    }

    #[test]
    fn pred_payload_normalizes_substitution_collisions() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b = sig.concept("B");
        let o = ind_term(1);
        let edge = comp_term(fterm(1), o);
        let mut e = Engine::new(sig, vec![], 0);
        e.contexts
            .push(Context::new(0, vec![cx(a, X)], false, None));
        e.cc_arena[0].push(ContextClause::new(
            vec![cx(a, X)],
            vec![Lit::P(cx(b, Y)), Lit::P(cx(b, o))],
            false,
            &e.sig,
        ));
        e.rebuild_cc_mirrors(0);
        e.contexts[0].pred_pool.push(0);

        let payload = e.pred_payload(0, edge, 0);
        assert_eq!(payload.body, vec![cx(a, edge)]);
        assert_eq!(payload.head, vec![Lit::P(cx(b, o))]);
    }

    #[test]
    fn pred_result_buffer_keeps_a_strengthening_antichain() {
        let sig = Sig::default();
        let a = Lit::P(cx(1, X));
        let b = cx(2, X);
        let c = Lit::P(cx(3, X));
        let weak = ContextClause::new(vec![b], vec![a, c], false, &sig);
        let strong = ContextClause::new(vec![], vec![a], false, &sig);
        let incomparable = ContextClause::new(vec![], vec![c], false, &sig);
        let mut out = PredResultBuffer::default();

        push_nonredundant_pred_result(&mut out, weak.clone());
        push_nonredundant_pred_result(&mut out, strong.clone());
        let live: Vec<&ContextClause> = out.clauses.iter().flatten().collect();
        assert_eq!(
            live.len(),
            1,
            "the stronger result must remove the weak one"
        );
        assert_eq!(live[0].body, strong.body);
        assert_eq!(live[0].head, strong.head);

        push_nonredundant_pred_result(&mut out, weak);
        assert_eq!(
            out.clauses.iter().flatten().count(),
            1,
            "a buffered strengthening must reject the weak result"
        );
        push_nonredundant_pred_result(&mut out, incomparable);
        assert_eq!(
            out.clauses.iter().flatten().count(),
            2,
            "incomparable conclusions must both survive"
        );
    }

    #[test]
    fn nominal_enumeration_reuses_complete_ground_labels() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b = sig.concept("B");
        let c = sig.concept("C");
        let q = sig.concept("Q_0");
        let n1 = sig.concept("__nom__o1");
        let n2 = sig.concept("__nom__o2");
        let o1 = ind_term(1);
        let o2 = ind_term(2);
        let clauses = vec![
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(q, X))]),
            OntologyClause::new(vec![cx(q, X)], vec![Lit::P(cx(a, X))]),
            OntologyClause::new(vec![cx(q, X)], vec![Lit::P(cx(n1, X)), Lit::P(cx(n2, X))]),
            OntologyClause::new(vec![cx(n1, X)], vec![Lit::P(cx(q, X))]),
            OntologyClause::new(vec![cx(n2, X)], vec![Lit::P(cx(q, X))]),
            OntologyClause::new(vec![cx(n1, X)], vec![Lit::eq(X, o1)]),
            OntologyClause::new(vec![cx(n2, X)], vec![Lit::eq(X, o2)]),
            OntologyClause::new(vec![], vec![Lit::P(cx(n1, o1))]),
            OntologyClause::new(vec![], vec![Lit::P(cx(n2, o2))]),
            OntologyClause::new(vec![], vec![Lit::P(cx(b, o1))]),
            OntologyClause::new(vec![], vec![Lit::P(cx(b, o2))]),
            OntologyClause::new(vec![], vec![Lit::P(cx(c, o1))]),
        ];

        let detected = detect_nominal_enumerations(&sig, &clauses);
        assert_eq!(detected.get(&a), Some(&vec![o1, o2]));

        let mut engine = Engine::new(sig, clauses, 0);
        engine.run_for(&[a]);
        assert!(engine.nominal_shortcuts.contains_key(&a));
        assert!(
            !engine.contexts.iter().any(|ctx| ctx.query == Some(a)),
            "the certified enumeration must not create the expensive query root"
        );
        let row = engine
            .subsumptions()
            .into_iter()
            .find(|(name, _)| name == "A")
            .expect("A classification");
        assert_eq!(row.1, vec!["B".to_string()]);
    }

    #[test]
    fn nominal_enumeration_requires_the_reverse_union_proof() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let q = sig.concept("Q_0");
        let n1 = sig.concept("__nom__o1");
        let n2 = sig.concept("__nom__o2");
        let o1 = ind_term(1);
        let o2 = ind_term(2);
        let clauses = vec![
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(q, X))]),
            OntologyClause::new(vec![cx(q, X)], vec![Lit::P(cx(a, X))]),
            OntologyClause::new(vec![cx(q, X)], vec![Lit::P(cx(n1, X)), Lit::P(cx(n2, X))]),
            OntologyClause::new(vec![cx(n1, X)], vec![Lit::P(cx(q, X))]),
            // Deliberately omit n2(x) -> q(x).
            OntologyClause::new(vec![cx(n1, X)], vec![Lit::eq(X, o1)]),
            OntologyClause::new(vec![cx(n2, X)], vec![Lit::eq(X, o2)]),
            OntologyClause::new(vec![], vec![Lit::P(cx(n1, o1))]),
            OntologyClause::new(vec![], vec![Lit::P(cx(n2, o2))]),
        ];
        assert!(!detect_nominal_enumerations(&sig, &clauses).contains_key(&a));
    }

    #[test]
    fn back_subsumption_deactivates_pending_pred_push() {
        let sig = Sig::default();
        let a = Lit::P(cx(1, X));
        let b = cx(2, X);
        let c = Lit::P(cx(3, X));
        let weak = ContextClause::new(vec![b], vec![a, c], false, &sig);
        let strong = ContextClause::new(vec![], vec![a], false, &sig);
        let arena = vec![weak.clone(), weak, strong.clone()];
        let mut ctx = Context::new(0, vec![], false, None);
        ctx.todo.push_back(0);
        ctx.worked_off.push(1);
        ctx.clause_keys.insert(0);
        ctx.clause_keys.insert(1);
        ctx.pred_pool.push(1);
        let facets = facets_of(&arena, &sig);
        ctx.index_clause(&facets, 1);
        ctx.index_active_clause(&arena, 0);
        ctx.index_active_clause(&arena, 1);

        ctx.back_subsume(&arena, &sigs_of(&arena), &facets, &strong);
        assert!(!ctx.clause_keys.contains(&0));
        assert!(!ctx.clause_keys.contains(&1));
        assert!(ctx.todo.is_empty());
        assert!(ctx.worked_off.is_empty());
        assert!(
            ctx.pred_pool
                .iter()
                .all(|cid| !ctx.clause_keys.contains(cid)),
            "a back-subsumed intermediate must not cross the Pred boundary"
        );
    }
}

#[cfg(test)]
mod rsucc_rolechain_tests {
    //! Invariance tests for the semi-naive (delta) r-Succ reach forwarding.
    //!
    //! The optimization replaced a per-`propagate` FULL rescan of `rsucc_pool`
    //! (rebuilding the ordered-unique reach-predicate list every round) with an
    //! incremental fold into a persistent accumulator gated by an `rsucc_hwm`
    //! high-water mark.  Everything downstream (the successor × reach
    //! cross-product, the `pushed_rsucc` dedup, the `Msg::Succ` construction) is
    //! byte-for-byte unchanged, so if the accumulated reach list equals what the
    //! full rescan produced, the emitted message set/order — hence the whole
    //! saturation fixpoint — is identical.  `rsucc_reach_delta_equals_full_rescan`
    //! certifies exactly that equality (the crux); the witness tests confirm the
    //! four role-chain families still classify correctly and identically with
    //! r-Succ on vs off (answer invariance).
    use super::*;

    fn cx(iri: Iri, t: Term) -> Pred {
        Pred::Concept { iri, t }
    }
    fn rl(iri: Iri, s: Term, t: Term) -> Pred {
        Pred::Role { iri, s, t }
    }

    // ---- Test 1 (crux): delta reach extraction == full rescan, every split. ----
    #[test]
    fn rsucc_reach_delta_equals_full_rescan() {
        let mut sig = Sig::default();
        let t1 = sig.concept("__trans__R__A"); // reach
        let t2 = sig.concept("__trans__R__B"); // reach
        let ch = sig.concept("__chain__S__A"); // reach
        let plain = sig.concept("PlainC"); // NOT reach
        assert!(sig.is_reach(t1) && sig.is_reach(ch) && !sig.is_reach(plain));
        let f = fterm(1);
        // Single-literal heads are always maximal, so `max_head_predicates`
        // returns exactly the head predicate — isolating the reach filter.
        let mk = |p: Pred| ContextClause::new(vec![], vec![Lit::P(p)], false, &sig);
        let arena: Vec<ContextClause> = vec![
            mk(cx(t1, X)),    // 0: reach t1
            mk(cx(plain, X)), // 1: filtered (not a reach concept)
            mk(cx(t2, X)),    // 2: reach t2
            mk(cx(t1, X)),    // 3: duplicate t1
            mk(cx(ch, X)),    // 4: reach ch
            mk(cx(t2, X)),    // 5: duplicate t2
            mk(cx(t1, f)),    // 6: filtered (reach concept but non-central term)
        ];
        let pool: Vec<u32> = (0..arena.len() as u32).collect();

        // Full rescan reference — what the pre-optimization code recomputed
        // every propagate.
        let full = {
            let mut acc = Vec::new();
            let mut set = HashSet::new();
            fold_reach_unique(&mut acc, &mut set, rsucc_reach_tail(&arena, &pool, &sig));
            acc
        };
        assert_eq!(
            full,
            vec![cx(t1, X), cx(t2, X), cx(ch, X)],
            "full rescan must be the ordered-unique central reach preds"
        );

        // For EVERY 2-way split point the incremental fold reproduces `full`
        // (append-only pool ⇒ scanning [..k] then [k..] equals scanning all).
        for k in 0..=pool.len() {
            let mut acc = Vec::new();
            let mut set = HashSet::new();
            fold_reach_unique(
                &mut acc,
                &mut set,
                rsucc_reach_tail(&arena, &pool[..k], &sig),
            );
            fold_reach_unique(
                &mut acc,
                &mut set,
                rsucc_reach_tail(&arena, &pool[k..], &sig),
            );
            assert_eq!(acc, full, "delta split at {k} diverged from full rescan");
        }

        // Per-entry arrival (the real propagate cadence: pool grows one worked-off
        // clause at a time across rounds).
        let mut acc = Vec::new();
        let mut set = HashSet::new();
        for i in 0..pool.len() {
            fold_reach_unique(
                &mut acc,
                &mut set,
                rsucc_reach_tail(&arena, &pool[i..i + 1], &sig),
            );
        }
        assert_eq!(
            acc, full,
            "per-entry incremental arrival diverged from full rescan"
        );
    }

    /// Run `clauses` (querying `query`) with r-Succ forced on or off, returning
    /// `query`'s named supers.  `sig.rsucc` is set AFTER `Engine::new` so the
    /// result is independent of the ambient `KM_RSUCC` env var (no test races).
    fn supers_rsucc(
        clauses: Vec<OntologyClause>,
        sig: Sig,
        query_id: Iri,
        rsucc: bool,
    ) -> Vec<String> {
        let name = sig.concept_names[query_id as usize].clone();
        let mut e = Engine::new(sig, clauses, 0);
        Arc::make_mut(&mut e.sig).rsucc = rsucc;
        e.run_for(&[query_id]);
        let mut s = e
            .subsumptions()
            .into_iter()
            .find(|(n, _)| *n == name)
            .map(|(_, v)| v)
            .unwrap_or_default();
        s.sort();
        s
    }

    // ---- Test 2: transitive witness. ∃R.C ⊑ D over transitive R, two R-hops. --
    #[test]
    fn transitive_witness_answer_invariant() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b = sig.concept("B");
        let c = sig.concept("C");
        let d = sig.concept("D");
        let p = sig.concept("__trans__R__C"); // reach concept
        let r = sig.role("R");
        let (f1, f2) = (fterm(1), fterm(2));
        let clauses = vec![
            // A ⊑ ∃R.B ; B ⊑ ∃R.C
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(r, X, f1))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(b, f1))]),
            OntologyClause::new(vec![cx(b, X)], vec![Lit::P(rl(r, X, f2))]),
            OntologyClause::new(vec![cx(b, X)], vec![Lit::P(cx(c, f2))]),
            // transitivity recognition of the consumer ∃R.C ⊑ D:
            OntologyClause::new(vec![rl(r, X, Y), cx(c, Y)], vec![Lit::P(cx(p, X))]),
            OntologyClause::new(vec![rl(r, X, Y), cx(p, Y)], vec![Lit::P(cx(p, X))]),
            OntologyClause::new(vec![cx(p, X)], vec![Lit::P(cx(d, X))]),
        ];
        let off = supers_rsucc(clauses.clone(), sig_clone(&sig), a, false);
        let on = supers_rsucc(clauses, sig, a, true);
        assert!(
            off.contains(&"D".to_string()),
            "transitive A ⊑ D (off): {off:?}"
        );
        assert_eq!(on, off, "r-Succ changed the transitive answer");
    }

    // ---- Test 3: chain witness. R∘S ⊑ T, consumer ∃T.C ⊑ D. ----
    #[test]
    fn chain_witness_answer_invariant() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b = sig.concept("B");
        let c = sig.concept("C");
        let d = sig.concept("D");
        let q = sig.concept("__chain__S__C"); // reach concept
        let r = sig.role("R");
        let s = sig.role("S");
        let (f1, f2) = (fterm(1), fterm(2));
        let clauses = vec![
            // A ⊑ ∃R.B ; B ⊑ ∃S.C
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(r, X, f1))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(b, f1))]),
            OntologyClause::new(vec![cx(b, X)], vec![Lit::P(rl(s, X, f2))]),
            OntologyClause::new(vec![cx(b, X)], vec![Lit::P(cx(c, f2))]),
            // chain recognition of R∘S⊑T with consumer ∃T.C ⊑ D:
            //   S(x,y) ∧ C(y) → __chain__S__C(x) ; R(x,y) ∧ __chain__S__C(y) → D(x)
            OntologyClause::new(vec![rl(s, X, Y), cx(c, Y)], vec![Lit::P(cx(q, X))]),
            OntologyClause::new(vec![rl(r, X, Y), cx(q, Y)], vec![Lit::P(cx(d, X))]),
        ];
        let off = supers_rsucc(clauses.clone(), sig_clone(&sig), a, false);
        let on = supers_rsucc(clauses, sig, a, true);
        assert!(off.contains(&"D".to_string()), "chain A ⊑ D (off): {off:?}");
        assert_eq!(on, off, "r-Succ changed the chain answer");
    }

    // ---- Test 4: inverse witness. Transitive R with an inverse pair (R, Ri);
    //      the delta scan runs over an ontology carrying inverse back-edges. ----
    #[test]
    fn inverse_witness_answer_invariant() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b = sig.concept("B");
        let c = sig.concept("C");
        let d = sig.concept("D");
        let p = sig.concept("__trans__R__C"); // reach concept
        let r = sig.role("R");
        let ri = sig.role("Ri");
        let (f1, f2) = (fterm(1), fterm(2));
        let clauses = vec![
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(r, X, f1))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(b, f1))]),
            OntologyClause::new(vec![cx(b, X)], vec![Lit::P(rl(r, X, f2))]),
            OntologyClause::new(vec![cx(b, X)], vec![Lit::P(cx(c, f2))]),
            // inverse bridges R⁻ = Ri
            OntologyClause::new(vec![rl(r, X, Y)], vec![Lit::P(rl(ri, Y, X))]),
            OntologyClause::new(vec![rl(ri, X, Y)], vec![Lit::P(rl(r, Y, X))]),
            // transitivity recognition of ∃R.C ⊑ D
            OntologyClause::new(vec![rl(r, X, Y), cx(c, Y)], vec![Lit::P(cx(p, X))]),
            OntologyClause::new(vec![rl(r, X, Y), cx(p, Y)], vec![Lit::P(cx(p, X))]),
            OntologyClause::new(vec![cx(p, X)], vec![Lit::P(cx(d, X))]),
        ];
        let off = supers_rsucc(clauses.clone(), sig_clone(&sig), a, false);
        let on = supers_rsucc(clauses, sig, a, true);
        assert!(
            off.contains(&"D".to_string()),
            "inverse+transitive A ⊑ D (off): {off:?}"
        );
        assert_eq!(on, off, "r-Succ changed the inverse+transitive answer");
    }

    // ---- Test 5: domain/range witness. domain(R)=D ⇒ A ⊑ D; range(S)=⊥ under an
    //      existential ⇒ the subject is unsatisfiable. ----
    #[test]
    fn domain_range_witness_answer_invariant() {
        // domain: A ⊑ ∃R.B, domain(R)=D  ⟹  A ⊑ D
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b = sig.concept("B");
        let d = sig.concept("D");
        let r = sig.role("R");
        let f1 = fterm(1);
        let dom = vec![
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(r, X, f1))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(b, f1))]),
            OntologyClause::new(vec![rl(r, X, Y)], vec![Lit::P(cx(d, X))]), // domain(R)=D
        ];
        let off = supers_rsucc(dom.clone(), sig_clone(&sig), a, false);
        let on = supers_rsucc(dom, sig, a, true);
        assert!(
            off.contains(&"D".to_string()),
            "domain A ⊑ D (off): {off:?}"
        );
        assert_eq!(on, off, "r-Succ changed the domain answer");

        // range: A2 ⊑ ∃S.⊤, range(S)=E, E ⊑ ⊥  ⟹  A2 unsatisfiable (⊑ owl:Nothing)
        let mut sig2 = Sig::default();
        let a2 = sig2.concept("A2");
        let e = sig2.concept("E");
        let s = sig2.role("S");
        let g = fterm(1);
        let rng = vec![
            OntologyClause::new(vec![cx(a2, X)], vec![Lit::P(rl(s, X, g))]),
            OntologyClause::new(vec![rl(s, X, Y)], vec![Lit::P(cx(e, Y))]), // range(S)=E
            OntologyClause::new(vec![cx(e, X)], vec![]),                    // E ⊑ ⊥
        ];
        let name = sig2.concept_names[a2 as usize].clone();
        // A2 is unsatisfiable (its S-successor is E ⊑ ⊥); `subsumptions` surfaces
        // the ⊥ subject. We only need the answer to be identical with r-Succ on/off.
        let mut e_off = Engine::new(sig2.clone(), rng.clone(), 0);
        Arc::make_mut(&mut e_off.sig).rsucc = false;
        e_off.run_for(&[a2]);
        let mut e_on = Engine::new(sig2, rng, 0);
        Arc::make_mut(&mut e_on.sig).rsucc = true;
        e_on.run_for(&[a2]);
        let supers_off = e_off
            .subsumptions()
            .into_iter()
            .find(|(n, _)| *n == name)
            .map(|(_, v)| v)
            .unwrap_or_default();
        let supers_on = e_on
            .subsumptions()
            .into_iter()
            .find(|(n, _)| *n == name)
            .map(|(_, v)| v)
            .unwrap_or_default();
        assert_eq!(
            supers_on, supers_off,
            "r-Succ changed the range/unsat answer"
        );
    }

    fn sig_clone(sig: &Sig) -> Sig {
        sig.clone()
    }

    // ---- Test 6 (crux of the follow-up optimization): the semi-naive
    //      successor × reach cross-product (`rsucc_cross_step`, per-edge hwm)
    //      reproduces the former full per-round `successors × reach` rescan
    //      exactly — same fired triples, same order, same final `pushed` set —
    //      across a schedule that grows the reach list AND grows / re-targets /
    //      drops-and-restores successor edges (the cases a naive global reach
    //      high-water mark would get wrong).  Everything downstream of the fired
    //      list (the `Msg::Succ` build) is unchanged, so equal fired sequences
    //      ⇒ identical emitted messages ⇒ identical fixpoint. ----
    #[test]
    fn rsucc_cross_delta_equals_full_rescan() {
        let mut sig = Sig::default();
        let r0 = cx(sig.concept("__trans__R__A"), X);
        let r1 = cx(sig.concept("__trans__R__B"), X);
        let r2 = cx(sig.concept("__chain__S__A"), X);
        // Successor edges (function term, target ctx id).
        let (fa, fb, fc) = (fterm(1), fterm(2), fterm(3));
        let (ta, tb, tb2, tc) = (10usize, 20, 21, 30);

        // A schedule of propagate rounds: (current successor edges, reach list).
        // reach is append-only; successor edges grow, re-target (fb: tb -> tb2),
        // drop (fa absent in round 3) and restore (fa back in round 5).
        let rounds: Vec<(Vec<(Term, usize)>, Vec<Pred>)> = vec![
            (vec![(fa, ta)], vec![r0]),                    // 1: one edge, one reach
            (vec![(fa, ta), (fb, tb)], vec![r0, r1]),      // 2: +edge, +reach
            (vec![(fb, tb)], vec![r0, r1, r2]),            // 3: fa absent, +reach
            (vec![(fb, tb2), (fc, tc)], vec![r0, r1, r2]), // 4: fb re-targeted, +edge
            (vec![(fa, ta), (fb, tb2)], vec![r0, r1, r2]), // 5: fa restored (must get r1,r2)
            (vec![(fa, ta), (fb, tb2)], vec![r0, r1, r2]), // 6: steady state (no new work)
        ];

        // Reference: the pre-optimization inline loop — every round rescans the
        // FULL current `successors × reach`, gated by a persistent `pushed`.
        fn full_round(
            successors: &[(Term, usize)],
            reach: &[Pred],
            pushed: &mut HashSet<(Term, usize, Pred)>,
        ) -> Vec<(Term, usize, Pred)> {
            let mut fired = Vec::new();
            for &(f, target) in successors {
                for &p in reach {
                    if pushed.insert((f, target, p)) {
                        fired.push((f, target, p));
                    }
                }
            }
            fired
        }

        let mut full_pushed: HashSet<(Term, usize, Pred)> = HashSet::new();
        let mut full_fired: Vec<(Term, usize, Pred)> = Vec::new();
        let mut delta_pushed: HashSet<(Term, usize, Pred)> = HashSet::new();
        let mut delta_hwm: HashMap<(Term, usize), usize> = HashMap::new();
        let mut delta_fired: Vec<(Term, usize, Pred)> = Vec::new();
        for (succ, reach) in &rounds {
            full_fired.extend(full_round(succ, reach, &mut full_pushed));
            delta_fired.extend(rsucc_cross_step(
                succ,
                reach,
                &mut delta_hwm,
                &mut delta_pushed,
            ));
        }

        // Per-round and cumulative equality of the fired sequence (order + set).
        assert_eq!(
            delta_fired, full_fired,
            "semi-naive cross-product fired a different (triple, order) sequence than the full rescan"
        );
        // The dedup set the two paths accumulate must also coincide.
        assert_eq!(
            delta_pushed, full_pushed,
            "semi-naive cross-product built a different pushed_rsucc set than the full rescan"
        );
        // Restored edge fa must have received the reach preds (r1, r2) that were
        // appended while it was absent — the exact case a global reach hwm drops.
        assert!(
            full_fired.contains(&(fa, ta, r1)) && full_fired.contains(&(fa, ta, r2)),
            "restored edge should receive reach preds appended while it was absent"
        );
    }

    // A per-round schedule for the driver-gate tests: `inserts` are the
    // successor edges `propagate` records this round (mirroring the engine's
    // per-round `successors.insert` calls, including re-targets), and
    // `new_reach` are the reach preds appended to the accumulator this round.
    // A round with both empty is a pure churn round (the context was re-dirtied
    // by unrelated predecessor / Pred work) — exactly what the gate must skip.
    type GateRound = (Vec<(Term, usize)>, Vec<Pred>);

    /// Replay `schedule` with the DRIVER GATE (run the cross-step only when reach
    /// grew or an edge changed) and, independently, UNCONDITIONALLY (run every
    /// round). Returns `(gated_fired, gated_pushed, uncond_fired, uncond_pushed,
    /// gated_runs, total_rounds)`. `successors` is modelled insert-only + retarget
    /// (never pruned), exactly as the engine maintains it, so this certifies the
    /// gate on the real state evolution.
    fn replay_driver_gate(
        schedule: &[GateRound],
    ) -> (
        Vec<(Term, usize, Pred)>,
        HashSet<(Term, usize, Pred)>,
        Vec<(Term, usize, Pred)>,
        HashSet<(Term, usize, Pred)>,
        usize,
        usize,
    ) {
        // Shared successor-map evolution (both paths see identical edges).
        let mut succ_map: HashMap<Term, usize> = HashMap::new();
        // Gated path state.
        let mut g_reach: Vec<Pred> = Vec::new();
        let mut g_seen: HashSet<Pred> = HashSet::new();
        let mut g_hwm: HashMap<(Term, usize), usize> = HashMap::new();
        let mut g_pushed: HashSet<(Term, usize, Pred)> = HashSet::new();
        let mut g_fired: Vec<(Term, usize, Pred)> = Vec::new();
        let mut edges_grew = false;
        let mut offered: usize = 0;
        let mut gated_runs = 0usize;
        // Unconditional (reference) path state.
        let mut u_reach: Vec<Pred> = Vec::new();
        let mut u_seen: HashSet<Pred> = HashSet::new();
        let mut u_hwm: HashMap<(Term, usize), usize> = HashMap::new();
        let mut u_pushed: HashSet<(Term, usize, Pred)> = HashSet::new();
        let mut u_fired: Vec<(Term, usize, Pred)> = Vec::new();

        for (inserts, new_reach) in schedule {
            // Apply this round's successor inserts (identically to both paths);
            // an insert whose mapping changes flags the gate (engine: the
            // `insert(f,target) != Some(target)` check at the two Succ sites).
            for &(f, t) in inserts {
                if succ_map.insert(f, t) != Some(t) {
                    edges_grew = true;
                }
            }
            // Grow the append-only reach accumulator (fold-unique, first wins) —
            // identical growth for both paths.
            fold_reach_unique(&mut g_reach, &mut g_seen, new_reach.clone());
            fold_reach_unique(&mut u_reach, &mut u_seen, new_reach.clone());
            let successors: Vec<(Term, usize)> = succ_map.iter().map(|(&f, &t)| (f, t)).collect();

            // Reference: cross-step every round.
            u_fired.extend(rsucc_cross_step(
                &successors,
                &u_reach,
                &mut u_hwm,
                &mut u_pushed,
            ));

            // Gated: cross-step only on a genuine delta.
            let reach_len = g_reach.len();
            if edges_grew || reach_len > offered {
                g_fired.extend(rsucc_cross_step(
                    &successors,
                    &g_reach,
                    &mut g_hwm,
                    &mut g_pushed,
                ));
                offered = reach_len;
                edges_grew = false;
                gated_runs += 1;
            }
        }
        (
            g_fired,
            g_pushed,
            u_fired,
            u_pushed,
            gated_runs,
            schedule.len(),
        )
    }

    // ---- Test 7 (crux of THIS optimization): the driver GATE (run the
    //      `successors × reach` cross-step only on a genuine reach/edge delta)
    //      produces the identical cumulative fired sequence and `pushed_rsucc`
    //      set as running the cross-step unconditionally every round — while
    //      actually skipping the pure-churn rounds.  Since `successors` is
    //      insert-only, the gate can only over-approximate growth, so on a
    //      skipped round the unconditional path also fires nothing; equal fired
    //      sequences ⇒ identical `Msg::Succ` emission ⇒ identical fixpoint. ----
    #[test]
    fn rsucc_driver_gate_equals_unconditional() {
        let mut sig = Sig::default();
        let r0 = cx(sig.concept("__trans__R__A"), X);
        let r1 = cx(sig.concept("__trans__R__B"), X);
        let r2 = cx(sig.concept("__chain__S__A"), X);
        let (fa, fb, fc) = (fterm(1), fterm(2), fterm(3));
        let (ta, tb, tb2, tc) = (10usize, 20, 21, 30);

        // Interleaves every delta shape with pure-churn rounds the gate must skip:
        let schedule: Vec<GateRound> = vec![
            (vec![(fa, ta)], vec![r0]),   // edge + reach  -> run
            (vec![], vec![]),             // churn         -> SKIP
            (vec![], vec![r1]),           // reach only    -> run
            (vec![], vec![]),             // churn         -> SKIP
            (vec![(fb, tb)], vec![]),     // edge only     -> run
            (vec![], vec![]),             // churn         -> SKIP
            (vec![(fb, tb2)], vec![]),    // re-target fb  -> run (new (fb,tb2) pair)
            (vec![(fc, tc)], vec![r2]),   // edge + reach  -> run
            (vec![(fa, ta)], vec![]),     // re-insert unchanged edge -> no delta -> SKIP
            (vec![], vec![]),             // churn         -> SKIP
        ];

        let (g_fired, g_pushed, u_fired, u_pushed, gated_runs, rounds) =
            replay_driver_gate(&schedule);

        assert_eq!(
            g_fired, u_fired,
            "driver gate fired a different (triple, order) sequence than the unconditional driver"
        );
        assert_eq!(
            g_pushed, u_pushed,
            "driver gate built a different pushed_rsucc set than the unconditional driver"
        );
        // The gate must genuinely skip: 5 delta rounds run, 5 churn/no-op skip.
        assert_eq!(
            gated_runs, 5,
            "gate should run only the 5 genuine-delta rounds"
        );
        assert_eq!(rounds, 10);
        // A re-inserted unchanged edge (round 9) is NOT a delta and must be skipped.
        // (Covered by gated_runs == 5, but noted here for intent.)
    }

    // ---- Test 8 (microbenchmark, #[ignore]): quantify the sweep the gate
    //      avoids.  With many successor edges and mostly-churn propagate rounds
    //      (the steady state on transitive / role-chain contexts), the
    //      unconditional driver rebuilds the `successors` Vec and sweeps every
    //      edge's hwm each round; the gate collapses that to O(1) per churn
    //      round.  Prints the invocation counts and wall times.  Run with:
    //        cargo test --release -- --ignored --nocapture rsucc_driver_gate_micro
    #[test]
    #[ignore]
    fn rsucc_driver_gate_microbench() {
        let mut sig = Sig::default();
        let reach_preds: Vec<Pred> = (0..8)
            .map(|i| cx(sig.concept(&format!("__trans__R__C{i}")), X))
            .collect();
        let n_edges = 4_000usize; // successor edges on the context
        let churn_per_reach = 200usize; // churn rounds between reach-growth events
        // Build a schedule: seed all edges in round 0, then alternate a single
        // reach-growth round with a long run of pure-churn rounds.
        let mut schedule: Vec<GateRound> = Vec::new();
        let all_edges: Vec<(Term, usize)> =
            (0..n_edges).map(|i| (fterm(i as i32 + 1), i)).collect();
        schedule.push((all_edges, vec![reach_preds[0]]));
        for rp in reach_preds.iter().skip(1) {
            for _ in 0..churn_per_reach {
                schedule.push((vec![], vec![])); // pure churn: gate skips
            }
            schedule.push((vec![], vec![*rp])); // reach grows: gate runs
        }

        let t0 = std::time::Instant::now();
        let (g_fired, g_pushed, u_fired, u_pushed, gated_runs, rounds) =
            replay_driver_gate(&schedule);
        let dt = t0.elapsed();

        assert_eq!(g_fired, u_fired, "microbench: gate diverged from unconditional");
        assert_eq!(g_pushed, u_pushed, "microbench: gate pushed set diverged");
        // Both paths ran inside `replay_driver_gate`; report the sweep counts.
        // Unconditional cross-step runs = every round; gated runs = delta rounds.
        let uncond_sweeps = rounds;
        let saved = uncond_sweeps - gated_runs;
        eprintln!(
            "rsucc_driver_gate_microbench: edges={n_edges} rounds={rounds} \
             uncond_cross_step_runs={uncond_sweeps} gated_cross_step_runs={gated_runs} \
             skipped={saved} ({:.1}% of rounds) \
             uncond_edge_sweeps={} gated_edge_sweeps={} \
             replay(both paths)={:?}",
            100.0 * saved as f64 / uncond_sweeps as f64,
            uncond_sweeps * n_edges,
            gated_runs * n_edges,
            dt,
        );
        assert!(saved > 0, "gate should skip the churn rounds");
    }
}
