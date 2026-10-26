---
name: project_km_heap_profile
description: "KM tableau heap profile (dhat) — peak=Graph::clone 92%, churn=match_rec HashMap-Subst 80%; harness in engine/prof/, dhat-heap Cargo feature"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3e94cd1a-f3b7-4c1c-a08d-39c076fa2104
---

Session 2026-06-08 (kobayashi-marust). Heap-profiled the tableau before the
trail-based-backtracking rewrite (the user asked: profile first, then
backtracking). Builds on [[project_km_hybrid_tableau]] [[project_km_nominals_routing]]
[[project_km_reasoner_perf]].

## Tooling
No system profilers on lc-dell (no valgrind/heaptrack/perf). Used `dhat-rs`
behind a `dhat-heap` Cargo feature (optional dep + `#[global_allocator]` +
`Profiler::new_heap()` in both `main.rs` and `bin/tableau_cli.rs`, all
`#[cfg(feature="dhat-heap")]` so the normal build is byte-identical). Build:
`CARGO_TARGET_DIR=target-dhat RUSTFLAGS="-C debuginfo=1" cargo build --release
--features dhat-heap --bins` (debuginfo needed because release has lto=true which
strips symbols). Harness committed to `engine/prof/` (gen_disjunction_stress.py,
ofn_to_tin.py, ofn_to_clauses.py, parse_dhat.py, README.md). Stress = A⊑∃r.A
chain + K live disjunctions C_i⊔D_i per node + C0⊓C1/D0⊓D1 clash traps (forces
backtracking). K=12 P=8 runs ~5s.

## Findings (tableau, K=12 P=8)
- **Peak live 268 MB: ~92% is `Graph::clone`.** Confirms hypothesis — the
  per-branch whole-graph `g.clone()` (tableau.rs lines 448/468/515/526/533) is the
  memory peak. -> trail-based backtracking (change-log + undo) is the right fix.
- **Total churn 3.85 GB / 18.5M allocations: ~80% is `Tableau::match_rec`** (NOT
  clone — clone is only ~10% of churn). This is a SECOND hotspot I had not
  flagged. Root cause: `type Subst = HashMap<Var,Node>` (tableau.rs:238) for maps
  holding only 1-3 vars, + `match_body` eagerly materialising `Vec<Subst>` with
  `out.push(subst.clone())` per solution (14M tiny ~84B allocs + 936k ~2KB
  HashMap allocs). Fix: small-inline Subst (Vec<(Var,Node)> or dense
  Vec<Node>-by-local-var) + visitor callback instead of collecting. Independent of
  backtracking; targets churn/runtime rather than peak.

## CB engine
Profiled on local ontologies only (kinship 18KB: 778KB peak; disjunction 3KB:
172KB peak) — too small to be representative. Allocation is spread flat across
saturate/propagate/run_for/get_or_create_context (+ fixed rayon/crossbeam
threadpool ~70KB startup), no single dominator — consistent with CB memory being
SIZE-bound (per [[project_km_nominals_routing]]). Real CB memory profiling needs
the ORE corpus on unimatrix01 (~/bench), not done yet.

## Trail-based backtracking DONE (2026-06-08, hotspot #1)
Replaced per-branch `g.clone()` in `expand` with a trail: `expand(&mut Graph)->bool`
mutates one graph in place; each branch alternative `checkpoint()`s, applies its
edit, recurses, `rollback_to(cp)` on failure. Undo records: Concept/Edge/Exobl/
NewNode + Merge(Box<MergeUndo>) (boxed so common records aren't sized by the merge
variant's 4 vecs). present_lits/present_roles NOT rolled back (monotone
over-approx, sound — only gate `matchable`). Merge undo is the hard part: records a
fresh-bit per moved concept/exobl/edge so undo removes exactly what the merge
created (handles dedup collisions); restores pred + repr[gone]=gone. node 0 always
lowest-id survivor so classify's g.concepts[0] read stays valid.
RESULT: peak 268MB->0.98MB (**274x**) on K=12/P=8, identical verdicts, 16/16 oracle
fixtures MATCH HermiT, 22+16 rust tests pass. Wall-clock ~neutral (+5%, noise) and
churn ~unchanged (3.85->3.56GB) — both expected: CPU is match_rec-bound, clone was
a MEMORY cost not CPU. Next task (user agreed: backtracking first, then this):
match_rec Subst fix (small-inline Subst + visitor) for the churn/runtime.

## match_rec / Subst fix DONE (2026-06-08, hotspot #2)
Replaced `type Subst = HashMap<Var,Node>` with an inline
`SmallVec<[(Var,Node);4]>` newtype (added `smallvec` dep): clauses have 1-4 vars
so `clone` is allocation-free for the common case (the 14M tiny per-solution
HashMap allocs were the churn). Also turned `match_rec` into an early-exit visitor
(`match_visit(cl,g,&mut dyn FnMut(&Subst)->bool)`, returns false=stop); `match_body`
collects via it, `find_disjunctive` stops at first usable match.
RESULT: allocations 18.5M->1.77M (**10.5x**), wall-clock K=12/P=8 5.37->2.30s
(**2.3x**), K=14/P=10 16.7->10.3s; peak unchanged (~0.89MB); verdicts identical,
16/16 oracle MATCH, 22+16 tests pass. KEY: malloc/free CALL COUNT (not byte
volume) is the CPU cost — total bytes stayed ~flat but 10x fewer calls = 2.3x
faster. Residual churn = `horn_saturate` materialising each clause's solution set
before mutating g (can't apply-during-visit: Role-body clause iterates g.edges
while head mutates it). Combined w/ backtracking: tableau is peak-300x, allocs-10x,
~2.3x-faster vs clone+HashMap baseline, same answers.

## Edge adjacency index DONE (2026-06-08)
Added `Graph::out_edges: Vec<Vec<(R,Node)>>` mirroring `edges`, maintained via
`raw_edge_insert`/`raw_edge_remove` (all edge writes route through them: add_edge,
merge, undo_merge, rollback Edge; new_node pushes empty, NewNode rollback pops).
`edges` HashSet kept for O(1) contains. Replaced O(E)/O(N) read scans with
out_edges[s]: match_rec Role (source-bound branch), ∃-satisfied checks
(saturate/first_unsat_exists/number-path/head_atom_present Exists), edge_label.
match_rec Role keeps a full-`edges` fallback when source var unbound. RESULT: win
grows with size — K=14/P=10 10.3->7.2s (30%), K=16/P=12 (TIMEOUT@60s on clone
baseline) now ~18s. 22+16 tests pass, 16/16 oracle MATCH. Committed+pushed.
User wants all 3 next: edge index (DONE), then backjumping+sat-caching, then
deepen CB->tableau hybrid. See [[feedback_commit_push]].

## Incremental (semi-naive) saturation DONE (2026-06-08)
Measured first (KM_TAB_STATS env counter): the ∀+⊔ stress is SATURATION-bound not
backtrack-bound (~1170 expands, only ~90 backtracks) — each expand re-derived the
whole Horn closure though it only adds one disjunct on an already-saturated
parent. ALSO measured: a DISTANT-CLASH disjunction instance backtracks
exponentially (33k tries, 99% backtrack) — that's where BACKJUMPING helps (next).
User chose "both, incremental first". Implemented worklist-driven Horn closure for
the non-careful path only: Tableau gains lit_index/role_index/node_triggered
(built in new()); expand_inc/saturate_inc/horn_inc drive from a VecDeque<NewFact>,
firing only clauses a new fact triggers + binding the trigger var (no full rescan).
Reuses match_rec via match_visit_from (seeded Subst); collects PendHead and applies
AFTER the match (g held immutably during match = the same mutate-during-iterate
hazard). ∃/blocking stays batch. Careful path (merge/inv/number/nominal) unchanged
(batch saturate). Root clash checked explicitly in find_model.
RESULT: K=12/8 2.05->0.32s, K=14/10 7.2->0.93s (~8x on edge-idx, **~18x vs original
clone baseline**), K=16/12 18.5->2.5s. Verdicts identical, 22+16 tests, 16/16
oracle MATCH. Committed+pushed. NEXT: backjumping (conflict-set dep-directed
backtracking) for the distant-clash exponential regime. KM_TAB_STATS kept (env-gated).

## Dependency-directed backjumping DONE (2026-06-08)
Conflict-set backjumping on the non-careful incremental path. Each fact carries a
DepSet (sorted SmallVec<u32> of disjunction decision levels): Horn head = union of
body deps; disjunct@level L adds {L}; ∃ successor inherits obligation dep; clash
conflict = union of clashing facts' deps. Stored Graph::cdep/edep/xdep, rolled back
with facts. expand_inc returns Outcome::Sat|Conflict(DepSet) + takes dl; when a
disjunct's conflict doesn't contain the current level → backjump (skip siblings +
irrelevant intervening decisions). Single-level-per-fact is UNSOUND (must track
full SETS) — verified by analysis. RESULT: distant-clash instance 33,053 tries/
32,797 backtracks → 309/53 (exponential→linear); ∀+⊔ stress UNCHANGED (0.32/0.92/
2.5s — dep sets stay tiny since structural facts have empty deps). SOUNDNESS:
22+16 tests, 16/16 oracle, **160/160 random disjunctive ontologies MATCH HermiT**
(differential gen_rand.py). Careful path keeps chronological. All 3 user-requested
items now: edge-index ✓, incremental-saturation ✓, backjumping ✓. REMAINING from
the original 3-item ask: deepen CB→tableau hybrid (told-subsumers). NOTE: ORE corpus
mostly live=0, so backjumping is insurance for pathological disjunctive cases.

## Told-subsumer classify pruning DONE (2026-06-08) — 3rd item complete
Internal CB-style hybrid using the backjumping dep machinery: in classify, a root
subsumer B of A with EMPTY dep was derived deterministically -> holds in all models
-> A⊑B definite, recorded with NO consistent(&[A,¬B]) confirmation test (each test
= full model build). Only nonempty-dep (choice-dependent) candidates confirmed.
Careful path (no deps) confirms all, as before. RESULT: 50-concept Horn chain +
disjunctions = 1225 subsumptions, 0 confirm tests. Verdicts unchanged: 22+16 tests,
16/16 oracle, 160/160 random MATCH. No router plumbing, no CB-explosion risk (vs
the external "run CB first" approach which risks the 47GB blowup on live disjunction).
ALL THREE original items now DONE: edge-index, incremental-sat, backjumping, +told-
subsumer (the CB->tableau hybrid). KM_TAB_STATS now also prints classify
definite/confirm counts.

## tableau.rs is NOT Lean-certified
The Lean cert covers the CB ContextCalculus only; the tableau is validated
empirically vs HermiT. So changing match_rec/backtracking representation needs an
oracle re-run (oracle/validate_ht.py), not a Lean re-cert. [[feedback_writing_style]]
note about "machine-checked" de-emphasis is separate.
