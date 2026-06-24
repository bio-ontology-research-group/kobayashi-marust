# SHIQ-completion sound shared-saturation — design

Goal: make the QoSat shared pass (`saturate_global`) SOUND for SHIQ (∀, ≤/≥
cardinality, ⊔ disjunction, inverse) while keeping its single-pass speed, so the 9
throughput-family onts (10908/14817/10621/7499/7914/3215/9663/9724/15672) classify
sound+complete+fast. No shortcuts: build the real completion graph.

## The core problem (measured)

QoSat seeds one shared node per named concept and saturates once (fast: 7914 in
55 s / 512 MB). It is UNSOUND for ∀ because successor fillers are shared by
`(filler-concept, role)` (`ensure_filler`): a `∀R.C` write from source A lands on a
filler also reached by source A′, so A′ inherits C spuriously (`qo_insufficient`,
`apply_head` critical-ALL). On 7914 this is ~49k spurious subsumptions
(190539 vs gold 141517); 9724 = 34012/37251 polluted nodes.

The complete `Ht::classify` IS sound (non-shared successors + blocking + ≤-merge +
branching) but too slow: it rebuilds a per-concept model for each of N concepts and
there is no shared deterministic backbone to amortise (empty-seed model = 1 node),
and a few disjunction concepts are individually explosive.

## Design: content-addressed (label-keyed) successors + blocking + merge + convergent ⊔

The fix is to make successor SHARING SOUND by keying a successor on the full set of
concepts forced onto it, not on `(filler-concept, role)`:

1. **Non-shared-by-default successors with content-addressed dedup.**
   - `∃R.C` at node x creates an R-successor whose *seed* is C plus every `∀R.D`
     currently on x plus R's range. Two successors are the SAME node iff their
     forced-concept set is identical; otherwise distinct. This removes
     cross-source ∀ pollution (different ∀-context ⇒ different node) while still
     sharing identical successors (speed).
   - Because ∀-writes can arrive AFTER a successor is created, maintain the keying
     incrementally: when a new `∀R.D` reaches x, push D to all current R-successors
     of x AND re-key (split a shared successor if predecessors now diverge). This is
     the lazy-unfolding/partition-refinement step.

2. **Blocking for termination.** Port the Ht blocking test (pairwise/anywhere as
   Konclude uses) into the QoSat expansion: a successor is blocked (its
   ∃-obligations not expanded) when an ancestor witnesses its label per the block
   condition. Reuse Ht's incremental subset-blocking (`INCRBLOCK2`).

3. **Cardinality.** `≤n R.C`: when a node has >n R-successors that carry C, MERGE
   (port Ht's merge: union labels + redirect edges, with the choose-rule deciding
   C/¬C per successor). `≥n R.C`: generate n distinct successors. Replace the
   current `Eq`-head deferral (`card_defer`) with the real merge.

4. **Convergent disjunction.** Keep the existing QoSat parked-disjunction + branch
   DFS but adopt Ht's search discipline (NEGTRIED + ORD + dependency-directed
   backjumping) so the open core converges instead of blowing up. Reuse the Ht
   conflict/dependency machinery.

5. **Reading subsumers.** After the sound completion, a query concept A's subsumers
   = the concepts certain at A's root over all completions. Deterministic part is
   read directly; for roots with branching, a subsumer must hold in every
   completion (the existing all-completion intersection / per-candidate verify, now
   sound because the model is sound).

## Reuse map (to fill from the KM-machinery agent)

- Ht blocking fn: <file:line>
- Ht ≤-merge fn + choose-rule: <file:line>
- Ht disjunction DFS + backjump + dependency: <file:line>
- Ht clash detection: <file:line>
- QoSat ∀-pollution site: `apply_head` critical-ALL (~hypertableau.rs:3845)
- QoSat cardinality deferral: `apply_head` Eq case (~hypertableau.rs:3918)
- QoSat successor creation: `ensure_filler` (~hypertableau.rs:2823)

## Konclude reference (traced)

All in `Source/Reasoner/Kernel/Algorithm/` of the local Konclude clone.

**Saturation-then-tableau split (THE architecture).**
`CCalculationTableauApproximationSaturationTaskHandleAlgorithm` runs a NON-branching
saturation applying ALL deterministic rules (AND, ∀, ≥n successor-gen, ≤n merge
EXCEPT the choose-rule, nominal, implication) to fixpoint; results are cached and
reused for equivalent subproblems (`mConfSatExpCachedSuccAbsorp` /
`mConfSatExpCachedDisjAbsorp`). Only the residue (disjunction + choose-rule) goes to
the branching `CCalculationTableauCompletionTaskHandleAlgorithm`. → KM mapping: this
is QoSat's `saturate_global` (deterministic) + `qo_branch_dfs` (tableau), but
QoSat's saturation is ∀-unsound (shared fillers) and its branch search lacks
convergence.

**≤n merge (the ≤-rule)** — `CCalculationTableauCompletionTaskHandleAlgorithm.cpp`:
- `applyATMOSTRule()` (14859): card = param-1; card<0 ⇒ clash; card==1 ⇒ functional.
- `initializeMergingIndividualNodes()` (15818): collect R-successors carrying C
  using a DISTINCT hash to maximise the distinct candidate set.
- `mergeMergingIndividualNodes[Pairwise]()` (15095/15042): pick mergeable pairs
  (`isIndividualNodesMergeable`, label-compatible = no C/¬C conflict); when distinct
  count ≥ card, FORCE merge `getMergedIndividualNodes()` (15443) = union labels +
  redirect edges; track `CMERGEDependencyNode`.
- choose-rule `qualifyMergingIndividualNodes()` (15675): unqualified successor ⇒ 2
  branches (C / ¬C), `CQUALIFYDependencyNode`.
- `applyATLEASTRule()` (16066) → `createDistinctSuccessorIndividuals()` (16140):
  make `card` distinct successors, each seeded with filler C.

**Disjunction (or-rule) + convergence** — same file:
- `planORProcessing()` (16489): DISJUNCTION DELAYING — count operands not yet
  pos/neg-contained; if ≤1 unsatisfied, execute now; else install a
  `CConceptRoleBranchingTrigger` and DELAY (branch only when live-disjunct count is
  minimal). This is the key width-reducer KM lacks (its `qo_unit_scan` is a partial
  version).
- `executeORBranching()` (16737): semantic branching — one task per unsatisfied
  disjunct, earlier disjuncts negated in later branches (like KM's NEGTRIED).
- Dependency-directed backtracking `backtrackFromTrackingLine[Step]()` (6963/6976):
  3 phases — (1) undo deterministic consequences of older individual levels, (2)
  flip earliest non-det decision at the current branch level, (3) try next level;
  NOGOOD-cache unsatisfiable combinations to prune future branches. This is the
  convergence mechanism; KM's conflict learning is measured ineffective, so this is
  a real port (not a flag flip).

**Completion-graph node + ∃-successor + blocking** (Agent 1) —
`CCalculationTableauCompletionTaskHandleAlgorithm.cpp` + `CIndividualProcessNode`:
- Node = unique id + concept-label set + role-successor hash + ANCESTOR link.
- `createSuccessorIndividual()` (21631): each ∃ makes a FRESH isolated node
  (`createNewIndividual` 21641) linked to parent — successors are NEVER shared.
- `applyALLRule()` (16297): ∀r.C propagates FORWARD over the node's GENUINE r-edges
  only (`getRoleSuccessorLinkIterator`, 16346), each successor gets an INDEPENDENT
  copy (`addConceptToIndividual`, 16375) — no shared fillers, no backward prop. This
  is precisely why Konclude's ∀ is sound and QoSat's (shared fillers) is not.
- Default blocking = OPTIMIZED SUBSET (B1∧B2), `detectIndividualNodeBlockedStatus()`
  (18987) → `isLabelConceptOptimizedBlocking()` (18484): B1 = `w.label ⊆ blocker.label`
  (18494); B2 = for the parent link w→v (role r), every operand C of every `∀r.C` in
  `blocker.label` must be present in `v` (18500-18560). Dynamic, ancestor-based
  (iterate ancestors, 19195). This is exactly KM's `block_mode=3` (pairwise) intent.
- `tryEstablishSaturationCaching()` (21670): precomputed saturation results predict
  blocking early and prune — the cross-completion work-sharing that keeps it fast.

## Decision: Path 2 (sound shared saturation), not Path 1 (per-concept delegation)

Agent 3 mapped a clean Path-1 seam (delegate AFFECTED concepts to a SHIQ-configured
`Ht::consistent`). But measured + analysed: `block_mode=3` (REQUIRED for sound
inverse/number) is NOT covered by the incremental-blocking speedup (`incr2` only
fires for `block_mode==1`, hypertableau.rs:4953), so a correctly-configured
per-concept `Ht::consistent` is SLOWER than the (already-timing-out) default-config
complete HT. With affected sets of 7171 (7914) / 20321 (9724), per-concept
delegation cannot meet 150 s. Also the n≥2 qualified ≤-merge is unimplemented even
in `Ht` (`apply_head`:1025 → `unsupported`). So Path 1 is out; build Path 2.

Path 2 makes the ONE shared `saturate_global` pass sound, so the work is shared
across all concepts (not redone per concept). Pieces, each gated `KM_HT_QO_SHIQ`:
- **P2.1 non-shared successors + ancestor subset blocking.** Replace `ensure_filler`'s
  shared `(fil,cls)` node with a per-source successor (`new_node` owned by the
  creating node, parent link recorded), and add B1∧B2 ancestor blocking to the
  expansion so it terminates. Eliminates ∀ pollution (Konclude's mechanism). Reuse
  KM's `compute_blocked` mode-3 logic adapted to the QoSat node model.
- **P2.2 cardinality.** ≥n → n distinct successors; ≤n → port the distinct-set merge
  + choose-rule (Konclude 15095/15675), replacing the `Eq` deferral; this also fills
  the n≥2 gap that `Ht` itself lacks.
- **P2.3 convergent disjunction.** Port `planORProcessing` delaying + 3-phase
  dependency-directed backtracking + nogood caching into `qo_branch_dfs`.
- **P2.4 cross-completion saturation caching** (`tryEstablishSaturationCaching`) for
  speed — share deterministic sub-results across concept roots.

Reading subsumers stays as in the current card-split: clean concepts emit their
(now-sound) labels directly; concepts touching the open disjunction core get the
all-completion confirm — now sound because the model is sound.

## Build/validate plan (incremental, on ws/IBEX — never the laptop)

Gated behind `KM_HT_QO_SHIQ` so the established paths are untouched until validated.
1. Non-shared content-addressed successors + ∀ soundness; validate on a tiny
   synthetic `∀`-pollution ontology (A⊑∀R.C, A′⊑∃R.⊤, ¬(A′⊑∃R.C)) + check
   `qo_insufficient` no longer fires.
2. Add blocking; validate termination on a cyclic `∃` ontology.
3. Add ≤-merge + choose-rule; validate on a cardinality ontology.
4. Add convergent ⊔; validate on 5303-style disjunctions.
5. Run the 9 family onts vs gold (`/ibex/.../gold`), 150 s cap, iterate.
6. Full 587-corpus regression (no soundness/coverage regression) before default-on.
7. Lean re-cert LAST (per the user's standing rule), once the rule set is final.
