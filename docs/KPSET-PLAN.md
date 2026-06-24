# 2b — Konclude-style sound inverse saturation (KPSet G1/G2/G3) for the QO gate

Status: design (not implemented). This is the lever that takes the QO sound+complete
path on inverse onts from "under budget" (2a, ~tens of seconds) to **Konclude speed**
(~10s on 7581). It is a core-saturation extension, not a routing tweak.

## Why it is needed (measured, 2026-06-23, ore_ont_7581 on ws)

The QO fast path classifies via a forward-only global saturation in ~10s (gold-exact,
matches Konclude's saturation core). The *certified-complete* path adds a verify
funnel (forward L + structural suspects + per-concept inverse de-conflation +
complete-tableau verify of the tight candidates). 2a parallelised that funnel under
the 240s budget. But every certified path is bounded by one fact:

**KM's inverse-aware saturation is fundamentally expensive.**
- Forward-only global pass: ~10s.
- Inverse-augmented global pass: **111s** — it builds a 6.5M-fact model.
- Per-concept inverse: cheap on average (~1.7ms) but pollutes; the candidates it
  yields are the HARD pairs (~1-2s each to verify).

Root cause: KM's EL-style completion reads a shared filler's **runtime label** across
edges (the NF4 backward-link rule `∃r.D ⊑ E`). That is sound for forward EL (the
filler's label is its concept's global closure). But an inverse-bridge clause
`r1(x,y) → r2(y,x)` adds a back-edge `filler → r2 → predecessor`; the NF4 rule then
reads the *predecessor-specific* label across it, and because the filler is **shared**
across all predecessors that have `∃r1.filler`, the read conflates them — the 6.5M
spurious facts. Forward-only sidesteps this by dropping the inverse edges, which is
why it is the only fast saturation.

This is exactly the invariant Konclude maintains and KM violates.

## Konclude's mechanism (verified vs /tmp/Konclude source; see docs/KONCLUDE-STUDY.md)

ONE non-branching approximation saturation over the TBox, shared nodes, kept sound by:
- **G1** subsumers of a concept are read from its OWN self-node, never a shared
  successor (`CPrecomputedSaturationSubsumerExtractor`).
- **G2** from a successor, propagate only STATUS flags (sat / clash / insufficient),
  never concept labels — so a shared filler cannot conflate its predecessors.
- **G3** a ∀-forward / ≤n-merge / open-⊔ write that a node cannot soundly absorb marks
  it INSUFFICIENT (`isCriticalALLConceptDescriptorInsufficient` →
  `setInsufficientNodeOccured`). KPSet carries a 3-valued certain/possible/absent set.

Only INSUFFICIENT concepts reach the complete tableau (≈0 for 7581). The inverse
contributes through the tableau's **tree** expansion (bounded by blocking) for that
residue, never through dense back-edge label propagation in the saturation — so the
saturation stays forward-only-fast.

## STATUS 2026-06-23: Phase A (containment check) IMPLEMENTED + measured

`KM_HT_QO_KPSET` (gated, default off; 129 cargo tests incl. two new KPSet tests).
The port of Konclude's `isCriticalALLConceptDescriptorInsufficient`
(CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp:3451): KM now
KEEPS the inverse-bridge clauses (creates the back-edges, recorded in
`inv_edges`), but every concept-head write whose firing matched an inverse
back-edge becomes a **containment check** instead of a write (`kp_check_head` /
`kp_write`), re-evaluated at the saturation fixpoint (`kp_finalize`, Konclude's
post-pass `checkCriticalIndividuals`). A miss raises `kp_insufficient`; nothing is
written across a reversed edge, so the cross-concept shared-filler conflation
cannot form.

**Measured on ore_ont_7581 (ws):** the inverse-AWARE KPSet pass no longer blows
up — it runs at forward-only cost (whole `km classify` 37s / 1.0 GB, vs the old
inverse-augmented 111s / 6.5M-fact pollution). SOUNDNESS confirmed: it never
over-derives (unit tests + it falls back to the gold-exact forward-only result,
565317 = gold, 0 unsound / 0 incomplete).

**But it does NOT yet certify 7581.** `kp_miss = 929558` over `inv_edges =
898356`: KM's cb_to_ht encodes each inverse role as a materialised reversed edge
(`r1(x,y) → r2(y,x)`), and the 129k NF4 existential-subsumption clauses
(`∃r2.D ⊑ E`) then fire across those back-edges at the SHARED filler nodes,
producing ~930k predecessor-dependent consequences that are not forward-present
(all spurious, since NOINV = gold). The containment check correctly refuses to
write them (sound) — but the single global `kp_insufficient` bool is too coarse:
one missed check at any shared filler defers the WHOLE classification. So KPSet
defers and the pipeline falls back to forward-only (gold-exact, fast).

Konclude reaches insufficient ≈ 0 here because it does NOT materialise reversed
edges that trigger forward existential-subsumption at shared fillers; its inverse
is a backward-∀ annotation over forward links, and the residual possible-subsumers
are pruned by the **KPSet 3-valued possible set + pseudo-model merge**
(`isPseudoModelSubsumerPossible`, study doc P2) BEFORE any tableau test — not by a
global flag. So the remaining work to certify 7581 fast is:
  1. **Per-node insufficiency** (`HashSet<Node>`, not a global bool) so CLEAN
     query concepts certify while only genuinely-affected ones defer; and
  2. **Per-concept possible-subsumer tracking + pseudo-model-merge refutation**
     (study doc P2) to prune the ~930k spurious possible-subsumers cheaply, so the
     tableau residue is the few genuinely load-bearing pairs (≈ 0 for 7581).
Both are Konclude ports, not new research.

**Per-node granularity MEASURED INSUFFICIENT (2026-06-23).** Added per-node
insufficiency (`kp_insuff_nodes`) + a probe: a query concept is unaffected iff its
self-node does not forward-reach any insufficient node (NF4 propagates
filler→predecessor, so reverse-reach over `in_edges` marks every affected
ancestor). Result on 7581: **0 / 72989 concepts CLEAN** (`insuff_nodes = 36495`,
half the model; every query concept reaches one). So per-node + subtree-reachability
recovers nothing — the conservatism is total. This rules out item (1) as a
standalone lever and confirms item (2), the **pseudo-model-merge refutation of
per-concept possible-subsumers**, is the actual remaining port. Konclude refutes
`A ⊑ B` by a linear sorted-map merge (a deterministic concept of B's model absent
in A's ⇒ not subsumed; a role-cardinality-interval clash ⇒ not subsumed) — it does
NOT use subtree reachability, precisely because reachability is this conservative.
The ~930k possibles become possible-subsumers that the merge prunes cheaply; for
7581 (forward = gold) every one is refuted ⇒ residue 0 ⇒ certified fast.

## STATUS 2026-06-23 (P2): pseudo-model merge CERTIFIES 7581 under budget

`KM_HT_QO_PMMERGE` (gated, default off; 130 tests). Port of the concept part of
`isPseudoModelSubsumerPossible` (KPSet classifier cpp:1626): each tight inverse-only
candidate `(A,B)` from the verify funnel is refuted by building ONE model of `A`
(`model_root_pos` = `consistent(&[A])`) and dropping `A ⊑ B` when `B` is absent from
that model's root — sound (`B` false in a real model of `A`). **7581: all 177
candidates refuted → 0 survivors → 0 `consistent(A ⊓ ¬B)` tests; gold-exact (565317 =
gold, 0/0); 129s / 2.5 GB, UNDER the 240s budget** (2a was 244s over). The hard
inverse-pair tableau blowups are never reached. Remaining toward Konclude ~10s: the
pre-filter spends ~90s building 63 full `consistent(A)` models. **Building the
pseudo-model from the (forward) saturation instead is UNSOUND in general** — the
forward label under-approximates inverse-entailed subsumers, so "B absent from the
forward model ⇒ A⋢B" would refute real subsumptions on load-bearing-inverse onts.
A sound saturation pseudo-model needs the complete deterministic subsumer set
(forward + inverse), which is exactly the classification being computed. Konclude
itself builds pseudo-models from per-concept SAT completions (not the raw
saturation: `getAssociatedSaturationCacheEntry`, classifier cpp:1530) — KM already
mirrors that. Konclude's speed there comes from a FAST sat test that reuses a cached
⊤-saturation; KM's equivalent (`KM_HT_SATCACHE`) is sound only for ALC(H)
no-inverse, so it cannot fast-path 7581's per-concept models. The result-identical
incremental blocking/obligation speedups (`set_fast_tableau`, baked into the
model-builder workers) shave only ~7s — the cost is intrinsic model size, not
blocking. So the real levers to ~10s are EITHER a sound inverse-aware fast-sat
cache (a further port) OR a cb_to_ht inverse encoding that does not materialise
reversed edges (so the forward saturation becomes inverse-complete and the
pseudo-model becomes free). Both are larger structural changes; the certified
122-126s under-budget result stands meanwhile. NB this uses the 2a verify funnel
(`KM_HT_QO_PC`+`KM_HT_QO_VERIFY`+`KM_HT_QO_PMMERGE`), NOT the KPSet global gate
(which defers on 7581, see below).

## STATUS 2026-06-23 (levers 1 & 2 for ~10s): both quick forms REFUTED empirically

Goal was to close 126s → Konclude ~10s. The 90-104s is building 63 real per-concept
`consistent(A)` models; per-A timing shows a few are intrinsically slow (45-64s) —
large DETERMINISTIC (7581 is Horn) inverse expansions, bound by per-model cost.

- **Lever 2 — inverse re-encoding (`KM_HT_QO_INVCOMPOSE`, `compose_inverse`).**
  IMPLEMENTED + benchmarked. Resolves each bidirectional inverse bridge into its
  single-role consumers as forward clauses and drops the bridges (sound: composed
  clauses are resolvents; real ∃-edges untouched; 130 tests pass). 7581's inverse
  is part_of/has_part — BIDIRECTIONALLY load-bearing (both create ∃-edges), and all
  ~110k inverse-role consumers are single-role NF4, so composition applies cleanly.
  **RESULT: net-NEGATIVE — the gate saturation DIVERGES** (edge_work 3M→5M climbing,
  22M+ drain steps, no convergence). Reason: the reversed-edge NF4 (`∃r.D⊑E`,
  head-on-source) is handled by the `prop` backward-link store (computed once per
  (filler,role), broadcast — O(consequences)); the composed forward-∀ clause
  (head-on-target) cannot use `prop` and re-fires per edge → blowup. **So avoiding
  reversed edges is STRICTLY SLOWER here: the reversed-edge + `prop` encoding is the
  efficient one, and the shared-filler write (the source of insufficiency) is
  intrinsic to the inverse semantics regardless of encoding.** Kept gated (default
  off) as a documented negative result; may help onts whose inverse consumers are
  not `prop`-optimisable.
- **Lever 1 — faster per-concept models.** Threading does NOT help: `KM_HT_PAR=48`
  ≈ `PAR=16` (103s vs 104s; RSS 2.5→6.7 GB) — not thread-bound, bound by per-model
  cost under allocator/memory contention. Proven that the candidates REQUIRE the
  exact tableau model (the inverse-augmented saturation over-approximates, so a
  candidate `B` is IN it and cannot be refuted by absence; forward under-approximates
  and cannot confirm — the gap is exactly the candidate set). Also tried `KM_HT_QO_PMCOMPOSE` (build the per-concept tableaux over the
  inverse-composed, reversed-edge-free clause set, so `consistent(A)` could use cheap
  subset blocking instead of inverse pairwise blocking): only MARGINAL (slowest
  models 63→53s, 64→56s; total 100s vs 104s, ~3%). So the slow models are NOT
  inverse-blocking-bound either — it is raw deterministic expansion volume per model.
  So the only real lever
  is Konclude's **satisfiable-expander cache made sound under inverse** (reuse
  satisfiable filler subtrees across the 63 model builds). KM's `KM_HT_SATCACHE` /
  `KM_HT_SATFOLD` are the no-inverse versions; the inverse-sound port (a node's sat
  can depend on inverse-predecessor context, so the cache key must capture it) is the
  substantial remaining work. The certified 126s under-budget result stands.

## DEFINITIVE TRACE of Konclude on 7581 (2026-06-23, deployed binary, stats logging)

Ran the deployed Konclude (`Binaries/Konclude classification -v`) on ore_ont_7581:
```
parsed 1432ms; preprocessing 3097ms; precomputing(saturation) 3448ms;
"has been sufficiently saturated, extracting data for classification";
class classification 903ms; total 9657ms.
```
The "Used N satisfiable tests / pseudo-model merged / calculated subsumption tests"
line did NOT print. So Konclude does **ZERO tableau tests and ZERO pseudo-model
merges on 7581** — it classifies entirely from the saturation. The selector is
`CConfigDependedSubsumptionClassifierFactory::isClassificationBySaturationCalculation
Sufficient`: if `!getProcessingDataBox()->isInsufficientNodeOccured()` (and no
problematic EQ candidates), use `COptimizedClassExtractedSaturationSubsumptionClassifier`
— extract subsumers straight off the saturation. **Konclude's saturation marks ZERO
insufficient nodes on 7581.**

Mechanism (`applyALLRule`, cpp:6143): a `∀role.C` does (a) BACKWARD propagation —
write C's operands to the predecessors recorded on `role`'s backward-prop links
(`addConceptFilteredToIndividual`, non-critical); (b) if it propagates "into the
creation direction", queue a per-creation-role ALL-concept EXTENSION on the
successor and mark it CRITICAL (deferred to `isCriticalALLConceptDescriptor
Insufficient`, which sets insufficient only if a successor lacks the operands).
Konclude WRITES operands (to extensions / backward to predecessors) and reaches a
clean fixpoint; 7581 trips no criticality.

## Why KM cannot cheaply replicate "sufficient" (MEASURED 2026-06-23)

KM's KPSet check-and-defers on every inverse-edge write → 36495 insufficient nodes /
930k misses. Two sound, gated replication attempts FAILED to make the saturation
sufficient:
- `KM_HT_QO_KPGUARD` (criticality only for body-guard operands — an operand that
  guards no clause body is inert, so a miss on it is not a completeness threat):
  sound, but **the 7581 inverse operands ARE body-guards** (they are subsumer
  concepts that occur in bodies), so it does not reduce insufficiency.
- `KM_HT_QO_SAT` (separate role-keyed `(concept, role)` successor nodes, Konclude-
  style, so inverse writes never hit a concept self-node): added ~43k nodes / 1.2M
  inverse edges, kp_miss=1.24M, still insufficient. Worse, actually PROPAGATING the
  operands (writing, then letting forward NF4 fire) re-introduces shared-filler
  pollution **across predecessors** — a `(concept, role)` filler is still shared by
  all predecessors with that ∃, so a forward NF4 reading an inverse operand at it
  writes a predecessor-specific consequence to the wrong predecessors.

Root cause of the gap: Konclude's per-creation-role ALL-concept *extension* is a
SEPARATE structure consulted for consistency/criticality, with subsumers read from
self-nodes (G1) and genuine inverse subsumers added by the BACKWARD propagation to
predecessors — the three pieces together keep the shared-successor model sound across
multiple predecessors. KM's reversed-edge + `prop` model has none of that
separation. Faithfully porting it is a substantial re-architecture of QoSat's node
model (shared successors + per-role extension + backward-prop links + narrow
criticality), not a flag. Both attempts are committed gated (default off, sound via
the forward-only fallback, gold-exact). The certified **126s pseudo-model-merge
result remains the working sound+complete-under-budget path.**

## STATUS 2026-06-23 (re-architecture step 1): `fprop` + `fcheck` — sound inverse certification, 36495→1581 insufficient

Committing to the saturation re-architecture, the first landed piece (gated, default
off, 131 tests). Two new mechanisms in `QoSat`:

- **`fprop` (KM_HT_QO_FPROP)** — the forward-broadcast mirror of `prop`. `prop`
  optimises head-on-SOURCE Horn NF4 (`R(s,t) ⊓ D(t) → E(s)`, backward links);
  `fprop` optimises head-on-TARGET (`R(s,t) ⊓ D(s) → E(t)`), which is EXACTLY the
  shape `compose_inverse` emits. This **fixes the `KM_HT_QO_INVCOMPOSE` divergence**:
  bare INVCOMPOSE re-fired the composed clauses per edge (edge_work climbing
  3M→5M, never converging); with `fprop` the composed pass CONVERGES at
  forward-only cost (7581: edge_work drains to 0, nodes stable at 72990, 151s).
- **`fcheck` (KM_HT_QO_FCHECK)** — the captured composed clauses run in
  CONTAINMENT-CHECK mode (Konclude G1/G3) instead of writing. MEASURED: writing
  the composed head `E` to the shared successor over-derives grossly (the forward
  MIRROR of the reversed-edge conflation — 7581 blows to 1.34 GB raw). So under
  `fcheck` the broadcast records a deferred obligation (`kp_check1`) verified at
  fixpoint; a miss marks the node insufficient. When no obligation misses, the
  sound forward closure is certified COMPLETE and returned directly (no funnel).

**MEASURED on ore_ont_7581 (ws), INVCOMPOSE + FCHECK:**
- SOUND + gold-exact: km = 565317 = gold, **0 unsound / 0 incomplete**.
- Lowest memory of any path: **1.0 GB** (vs 2.5 GB for the certified pseudo-model
  merge, 3.7 GB for fprop write-mode).
- Insufficiency cut from KPSet's 36495 nodes to **1581 nodes / 31202 missed
  obligations** — the composed-forward + source-guard check is far tighter than
  the reversed-edge check.
- But still `kp_insufficient` ⇒ `global_fwd` DEFERS to the verify funnel (which
  delivers the gold-exact result in ~133 s). It does NOT certify on the global
  pass yet.

**Why the 1581 still block, and why routing them is DEAD.** The missed
obligations are genuine inverse-entailed facts at SHARED ∃-filler nodes (a
`has_part` filler `u` is shared across all wholes `v` with `v has_part u`; an
obligation `E(u)` from one whole `v1 ∈ D` is checked against the shared `u`, which
other non-`D` wholes also reach). They do NOT change the named subsumption set
(forward already = gold) — they are false alarms FOR CLASSIFICATION. The decisive
filter probe (bidirectional reachability closure of the 1581 insufficient nodes):
**0 / 72989 query concepts CLEAN** — the dense part_of/has_part graph links every
named concept to an insufficient filler. So routing only the genuinely-affected
concepts to the funnel (the cheap option) recovers nothing, exactly as the KPSet
per-node probe found. The only path to certification-on-the-global-pass is to
stop the filler insufficiency from mattering at all — Konclude's G1/G2: a filler
label is NEVER read as a named subsumer (G1) and only STATUS, never concept
labels, propagates from a filler to its predecessors (G2). KM violates G2 via
`prop` (it reads a filler's label and propagates a CONCEPT to predecessors). The
remaining re-architecture is therefore to make the inverse-affected filler
propagation status-only — separate per-creation-role successor nodes whose
concept labels are consulted only for criticality, never broadcast as named
subsumers. That is the multi-day core change below; this increment lands the
sound, lower-memory certification mechanism and the measurement that pins the
remaining work precisely.

## STATUS 2026-06-23 (re-arch step 2): G1 criticality in fcheck — every encoding-level lever now REFUTED

Added the `kp_write` G1 criticality refinement to `fprop_emit` (a missed
obligation at a separate ∃-filler under `sat_mode` is non-critical unless the
missed concept is a body guard) and tested the full stack
**INVCOMPOSE + FCHECK + SAT + KPGUARD** on 7581:
- still gold-exact (565317 = gold, 0/0), still 1.0 GB;
- **insufficiency UNCHANGED: kp_miss = 31202 / 1599 nodes.** The criticality
  filter removed nothing because the composed heads `E'` are THEMSELVES body
  guards (`kp_guard` contains them), so every obligation is critical, and the
  reachability closure is total (0/72989).

This refutes the last encoding-level lever. The chain of dead ends is now
complete: writing inverse consequences to shared successors is unsound
(over-derives); checking them (fcheck) is sound but flags 1581 filler-level
obligations that don't change the answer; per-node routing recovers nothing
(total reachability); guard/self-node criticality recovers nothing (the heads
are guards); separate fillers (sat_mode) don't change it. **Every one of these
works at the level of KM's NF4 + `prop` clause encoding with HEAD-containment
checks.** Konclude reaches 0 insufficient on 7581 with a structurally different
test: `isCriticalALLConceptDescriptorInsufficient` checks, for each ∀-restriction
PRESENT at a node, whether that ∀'s OPERANDS are present at the node's REAL
successors (cpp:3514) — an operand-at-successor check on genuine ∀-restrictions
over separate per-creation-role successor nodes, not a head-containment check on
NF4 implications over shared fillers. On 7581 the forward closure already forces
every such operand at every successor, so nothing is critical.

**Conclusion of the encoding-level work:** matching Konclude's ~10s on 7581 is
not reachable by augmenting KM's NF4+`prop`/reversed-edge encoding (every lever
tried is sound but non-certifying). It requires reimplementing Konclude's
approximation-saturation CALCULUS in `QoSat`: ∀-restriction concepts as
first-class operators with operand-at-successor criticality, separate
per-creation-role successor nodes, and G1/G2 (self-node subsumers + status-only
propagation). That is the multi-day core rewrite in the plan below — a new
calculus path, not a flag on the existing one. The sound, lower-memory `fcheck`
certification mechanism and this exhaustive refutation are committed; the
certified 126 s pseudo-model-merge path and the gold-exact `fcheck`+funnel path
(133 s, 1.0 GB) both stand as working sound+complete-under-budget results.

## STATUS 2026-06-23 (BREAKTHROUGH): hybrid certifies 7581 sound+complete in 31s

The encoding-level refutation above was missing one combination. The 1.34 GB
write-mode over-derivation came from writing the composed inverse head to a
SHARED filler. Under **`sat_mode`** (separate per-(concept,role) filler nodes,
Konclude G1) the composed writes land on filler nodes that are NEVER read as a
named subsumer — so writing them is SOUND. The full sound+complete fast path is:

**INVCOMPOSE + FPROP + SAT + KPSET** (`KM_HT_QO_INVCOMPOSE` + `KM_HT_QO_FPROP` +
`KM_HT_QO_SAT` + `KM_HT_QO_KPSET`, via the kpset gate):
1. **INVCOMPOSE** resolves every *composable* inverse pair into forward clauses
   and drops their bridges (110k of 7581's ~110k single-role consumers).
2. **FPROP** broadcasts the composed head-on-target clauses at `prop` speed
   (fixes the divergence).
3. **SAT** puts the composed writes on separate filler nodes, so named self-node
   subsumer sets stay inverse-clean (G1) — the writes become SOUND (no
   shared-filler conflation; the 1.34 GB collapses to the gold closure).
4. **KPSET** containment-checks any *residual* (non-composable / one-directional)
   inverse bridges that INVCOMPOSE could not eliminate; a miss raises
   `kp_insufficient` and defers to the funnel.

Certified sound+complete iff `kp_miss = 0` (no residual contribution lost) and no
`qo_insufficient` / parked disjunction.

**MEASURED on ore_ont_7581 (ws):** `QOKP certified sound+complete (kp_miss=0,
inv_edges=0)`, **31.3 s / 1.0 GB**, km = 565317 = gold, **0 unsound / 0
incomplete**. (7581's 2 residual bridges are vacuous — they create 0 reversed
edges — so kpset's check passes and the global pass certifies.) This is **4x
faster than the 126 s pseudo-model-merge path** and within ~3x of Konclude's
~10 s, at the lowest memory of any path.

**Soundness (principled, not coincidental).** `sat_mode` guarantees a named
concept `A`'s self-node is never an ∃-filler, so it picks up `E` only from
clauses anchored AT it (forward EL via `prop` over its own `∃`-successors) — never
from a composed inverse write (those land on fillers and propagate back only
sound forward consequences). The composed clauses are resolvents (sound by
construction). The residual bridges are the only uncomposed inverse contribution,
and kpset never lets one through silently — `kp_miss = 0` is a sound completeness
certificate for them. A **residual-bridge guard** (`count_inverse_bridges`) was
added so the bare write-mode path (FPROP+SAT without KPSET) DEFERS when any bridge
survived composition, rather than silently dropping it (that is exactly what made
the unguarded 30 s run gold-exact-by-luck; the guard makes it sound).

REMAINING toward Konclude ~10 s: the 31 s is the single global saturation over the
composed clause set (566k clauses, 116k nodes incl. ~43k separate fillers). The
gap is constant-factor (saturation throughput + the extra filler nodes), not a
missing mechanism. Next: validate no corpus regression (unimatrix sweep), then
fold composition of the residual multi-role consumers (so kpset is not even
needed) and trim `sat_mode`'s filler overhead.

## STATUS 2026-06-24: CORPUS VALIDATION (unimatrix job 7322) — 0 regressions, 7581 recovered

Full ORE-2015 sweep comparing the HYBRID (INVCOMPOSE+FPROP+SAT+KPSET) against
PRIOR-2a (the funnel alone), both forced-QO (CB disabled, `KM_ENGINE=/bin/false`)
with `KM_HT_QO_VERIFY`, 200 s cap, each ont scored vs Konclude gold AND vs the
other config. 582/592 onts (10 slow-tail both-timeouts unscored):

- **0 REGRESSIONS** — the hybrid is NEVER worse than prior-2a on any ont
  (no new unsound, no new incomplete, no lost answer that prior-2a had besides the
  3 perf cases below).
- **7581 RECOVERED**: hybrid = 565317 = gold (0 unsound / 0 incomplete) in
  **32.7 s**; prior-2a **TIMES OUT** at the cap. This is the only ont where the
  hybrid wins on the answer, and it is the target ont.
- **All 14 gold-gap onts are `agree = true`** (hybrid output byte-identical to
  prior-2a): 10908, 11315, 11745, 14312, 1618, 5404, 5566, 6999, 8982, … Every
  unsound/incomplete-vs-gold case is a PRE-EXISTING QO-path limitation (unsat
  under-detection e.g. 5404 RELAPPROXC138; partial-answer e.g. 8982 −207408;
  the known 6999 datatype gap), identical in both configs and unaffected by this
  change. In production these route to CB (which is sound/complete on them).
- **Cost — 3 perf cases** (11395, 3905, 3377): the hybrid TIMES OUT at the 200 s
  cap where prior-2a finishes in ~104–121 s. These are large CB-territory onts
  (3377 has 4.49M subsumptions); INVCOMPOSE adds composed clauses and SAT adds
  ~filler nodes, and that overhead crosses the cap. CONCLUSION: the hybrid is a
  sound, fast SPECIALIST for the Horn-inverse certify fragment (7581) — it must be
  ROUTED to that fragment (or raced only there), NOT blanket-enabled, because the
  composition+filler overhead hurts large non-certifying onts.

A real bug was found and fixed by this sweep: INVCOMPOSE swapped `self.clauses`
without rebuilding the tableau trigger indexes, so the per-concept verify tableau
panicked (`fire_anchor_concept` out-of-range `pos`) on ore_ont_10127 — fixed by
`rebuild_triggers` (commit 98077ba); 10127 now gold-exact.

NET: the hybrid certify path is validated sound+complete (0 regressions corpus-wide,
recovers 7581 4-6x faster than any prior path). Default-on requires a ROUTER that
sends only Horn-inverse certify candidates to it. Routing + composing the residual
multi-role consumers (drop the kpset dependency) + trimming sat_mode filler overhead
are the remaining steps.

## Implementation plan for KM (`engine/src/hypertableau.rs`, `QoSat`)

**Phase A — certain/possible label split + status-only reads (G1/G2).**
Give each node label a two-part split: `certain` (facts independent of which
predecessor reached the node — its concept's told + global Horn closure) and
`possible` (facts written via ∀/range/inverse from a *specific* predecessor). The
NF4-backward / ∀ rules read only `certain`. A derivation that would require a
`possible` fact at a successor marks the *reading* node INSUFFICIENT for that operand
instead of deriving it as certain. Inverse back-edge writes land in `possible`, never
`certain`, so they never propagate to other predecessors of a shared filler — the
6.5M conflation cannot form, and the saturation stays ~forward-only speed.

**Phase B — insufficient → complete-tableau residue (G3).**
Reuse the existing `qo_insufficient` plumbing and the per-concept complete-tableau
verify already wired behind `KM_HT_QO_VERIFY`: route only the concepts that Phase A
marked insufficient to `consistent(A ⊓ ¬B)`. The difference from 2a: the residue is
the *genuinely* insufficient concepts (small — 0 for 7581's inert inverse), not the
72,989 structural suspects, so the per-concept inverse de-conflation pass disappears
entirely.

**Phase C — KPSet 3-valued refinement (optional).**
Full possible-set tracking (certain / possible / absent) per node for a tighter
residue, matching Konclude's KPSet. Only needed if Phase A's binary split leaves too
large an insufficient set on some ont.

## Soundness + completeness

G1+G2+G3 are Konclude's certified saturation invariants. Reading only `certain` labels
never over-derives (sound); everything not soundly decided in the saturation is marked
insufficient and decided by the complete tableau (complete). Result = sound+complete,
identical truth to the current funnel, computed without the 6.5M pollution. The
forward-only gate is the special case "no possible facts, no insufficiency", so its
gold-exact behaviour is preserved by construction.

## Expected payoff

- 7581: ~10–15s (insufficient ≈ 0; saturation ≈ forward-only), matching Konclude.
- Generalises soundly to the SHIQ-without-live-disjunction class (the CB-timeout
  giants), not just inverse-inert onts.

## Risk / effort

Multi-day. It rewrites the core NF4 / ∀ propagation in `QoSat` to track
certain/possible and emit insufficiency rather than pollute. Validation: the
forward-only gate must stay gold-exact (it is the certain-only case); 7581 must reach
~Konclude speed with insufficient ≈ 0; full QO-routed corpus regression
(unsound/incomplete must not move). Re-derive the soundness argument against
docs/KONCLUDE-STUDY.md before any default-on.
