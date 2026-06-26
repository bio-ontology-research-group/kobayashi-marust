# Lever C — faithful Konclude G2/G3 saturation port (throughput giants)

> ## ⇒ VALIDATED RESULTS (2026-06-26, session 9) — both Konclude mechanisms ported + measured
>
> Both throughput-giant mechanisms are now PORTED, SOUND (159 cargo tests, 0
> regressions), opt-in (env, no routing change), and measured on the giant TINs.
> They are COMPLEMENTARY: each closes one of the two forward-pass insufficiency
> channels (`forall_insuff` and `card_insuff`), and the giants split by which
> channel dominates.
>
> | giant | dominant channel | port #2 (SPLIT) | cardmerge (≤-rule) | forward affected set |
> |-------|------------------|-----------------|--------------------|----------------------|
> | **9663** | ∀ (325k) + card (35k) | forall_insuff 325,315→0 (114k redirects) | card_insuff 34,596→**0** (11,339 merges) | **2,451 → ~92** (bounded 92k nodes, 546 MB) |
> | 7914 | cardinality (75k) | inert (forall_insuff=0) | NODE BLOWUP (>1.3 GB, no QOGF) | — |
> | 9724 | cardinality (98M) | inert | NODE BLOWUP (→cap 599k, unsupported bail) | — |
>
> **Win: 9663.** SPLIT + CARDMERGE together collapse 9663's forward-pass affected
> (deferred) set from ~2,451 to ~92 of 23k concepts — both insufficiency channels
> closed, node count bounded. The vast majority of concepts now certify from the
> sound forward pass; only ~92 go to the residue verify. (Port #2 alone already
> took 9663 from 2,451→59 on the ∀ channel; cardmerge then closes the residual
> cardinality channel, +~33 merge-clash deferrals → 92.)
>
> **Remaining to FULLY solve 9663:** the ~92-node residue verify (`KM_HT_QO_VERIFY`
> funnel / TR dfs) is slow and times out at 175 s — a SEPARATE bottleneck from the
> two ports (which did their structural job). Speeding that small residue verify
> is the next lever for 9663.
>
> **cardmerge blows up on high-cardinality giants (7914, 9724).** The privatize
> (`copyDependingIndividualNode`) makes a copy per (shared filler, constrained
> predecessor); under pervasive functional roles that is ~per-edge, exploding the
> node count (9724 → 599k cap-bail; 7914 → >1.3 GB). It is SAFE (gated; bails
> `unsupported` at the node cap → defers → CB), never unsound — but inert there.
> The fix is a CHEAPER merge: content-share merged nodes by their fil-set (like
> port #2's operand-set keying) instead of one copy per predecessor, and/or a
> node-budget fallback to `card_defer` once copies exceed a fraction of the cap so
> the CLEAN bulk still certifies. That is the next cardmerge increment.
>
> Commits: `aae23ed` SPLIT, `530064b` self-equality short-circuit, `0ae502a`
> CARDMERGE. Diagnostic: `QOGF split-diag: redirects= forall_insuff= card_insuff=
> cardmerges=`. TINs cached on ws: `/tmp/{9663,9724,7914,7581}.tin`.

> ## ⇒ CORRECTED DIAGNOSIS (2026-06-26, session 9) — READ FIRST
>
> **Port #2 (∀ copy-on-conflict split fillers) is BUILT, sound, unit-tested, and
> committed (`KM_HT_QO_SPLIT`, commits `aae23ed` + `530064b`) — but it is INERT
> on 9724, because the prior "9724 = ∀-into-shared-filler over-defer" framing
> below is WRONG.** Decisive diagnostic (ws, ore_ont_9724 TIN, KM_HT_TRACE
> split-diag): on 9724 the forward pass has **redirects=0, forall_insuff=0,
> card_insuff=98,380,184**. 9724's deferral is **100% cardinality Eq-heads**,
> ZERO ∀-critical writes. So the giant lever is the **cardinality Eq-head MERGE**,
> not port #2.
>
> **What port #2 IS good for:** the sound, monotone, bounded copy-on-conflict for
> a genuine forward `∀r.C`-into-shared-filler conflict (redirect the source's
> r-edge onto a node keyed by `(base-fil, role, source ∀-operand set)`; base
> fillers stay unpolluted). Tests `split_certifies_shared_filler_conflict` +
> `split_forall_operand_still_propagates`. It will help a ∀/inverse-dominated
> giant — but we have not yet found which (the other giant TINs are not on ws;
> relay 7914/9663/7499/14817 from unimatrix to validate). Keep it opt-in (env),
> NOT wired into the route, until a giant shows payoff + a corpus sweep.
>
> **Sound refinement landed (`530064b`):** the `KM_HT_QO_CARD` Eq-head deferral
> ignored `s`/`t` and deferred on EVERY firing including `Eq(n,n)` self-equalities
> (both successors are the same shared node). Added the self-equality
> short-circuit (`sn==tn ⇒ satisfied, no defer`). Sound; tests
> `card_self_equality_not_insufficient` + `card_distinct_merge_still_defers`. On
> 9724 it only trims 98.4M→97.5M (clean 2816→2823), so **the 97M residue are REAL
> distinct-successor merges** — 9724 genuinely needs the merge performed.
>
> **THE NEXT LEVER (cardinality Eq-head merge) and why it is NOT a copy-on-merge:**
> a forced `Eq(sn,tn)` (distinct filler nodes, under `sat_mode`) must fuse the two
> successors. Port #2's copy-on-conflict keys a node by a MONOTONE operand SET, so
> it is complete. A merged cardinality node's content is the UNION of two EVOLVING
> labels (sn and tn keep gaining concepts after the merge), so a content-keyed
> copy-on-merge is INCOMPLETE. The faithful port is a proper **union-find node
> merge** (Konclude ≤-rule / `mergeIndividualNode`): redirect all in/out edges of
> the victim onto the survivor, union labels (clash ⇒ source unsat), resolve every
> node reference through `merged_into`, re-fire to fixpoint. Crux + risks:
> (1) MUST be under `sat_mode` (merge filler nodes, NEVER concept self-nodes —
> merging self-nodes conflates classification, unsound); (2) the shared filler is
> reached by predecessors WITHOUT the ≤n, so the merge must be per-source
> (copy-on-conflict again) or it pollutes them; (3) cascades + termination +
> interaction with port #2 split and inverse. The forward-only certify already
> yields ~99.8% of subsumptions soundly (`clean_subs`), so the real goal is a
> TIGHT merge-affected set (mark a concept affected only when a merge actually
> CLASHES or adds a subsumer), not raw coverage. This is multi-session,
> soundness-critical, Lean-re-cert work — do it test-first from Konclude
> `mergeIndividualNode`, validate on the giant TINs only.
>
> KM anchors: `apply_head` Eq branch (the merge site, hypertableau.rs ~4612),
> `DBG_CARD_INSUFF` / `DBG_SPLIT` / `DBG_FORALL_INSUFF` split-diag trace,
> `qo_classify_global_fwd` card-split (the affected-set reverse-reach).
> Konclude anchors: the ≤-rule + `mergeIndividualNode` + choose-rule.

> ## ⇒ PRIOR FRAMING (status 2026-06-26, session 8) — SUPERSEDED for 9724, see above
>
> **Goal still open:** classify the throughput giants (9724, 7914, 9663, 14817,
> 7499; SRIQ/SHIF, inverse + cardinality) in ~Konclude time. None classify yet.
>
> **The single remaining lever (everything converges here): PORT #2** — a
> sound+complete KPSet saturation that does NOT over-defer the inverse-∀, i.e. the
> per-creation-role ALL-concept extension with **copy-on-conflict** successors. Full
> spec + the Konclude source anchors are in the "Port #2 spec" + "Konclude ROUTING
> trace" sections below. It is the residual-decision engine inside Konclude's routing.
>
> **Why it's the lever (proven this session, ws, ore_ont_9724):** Konclude's routing
> = global saturation → read known subsumers off deterministic labels → pseudo-model
> merge prune → residual `C⊓¬D` test on survivors, decided by FAST SOUND SATURATION.
> KM already IMPLEMENTS this routing (`qo_classify_global_fwd` + `KM_HT_QO_VERIFY` +
> `KM_HT_QO_PMMERGE`, gold-exact on 7581). KM's gap is the residual decision: it uses
> the COMPLETE TABLEAU (`consistent(A⊓¬B)`) which BLOWS UP (7581 244s; 9724 timeout).
> Konclude decides it in KPSet saturation. Measured on 9724 with `card_defer`: forward
> saturation already gives **clean_subs=456239 / gold 457090 (99.8%)** soundly; the
> only blocker is **66.6M filler-targeted, body-guard inverse misses** that defer
> 20321/23136 concepts. RULED OUT (kp_miss byte-identical 66,661,218 each): KPWRITE
> (misses are filler-targeted, not self-node), KPGUARD (misses are guard concepts),
> INVCOMPOSE-off, shiq mode (times out 200s/4.4GB), the verify funnel (residual
> tableau blows up). ⇒ no shortcut; port #2 is required.
>
> **Port #2 first increment (test-first, ws):** make the guard test
> `qo_shared_filler_conflict_ground_truth` (hypertableau.rs, already committed) flip
> from "defers" to "certifies A,B both consistent" by: writing inverse-∀ operands into
> a per-(filler, source-context) extension, firing guard rules from it, detecting a
> per-filler clash, and SPLITTING the shared filler (copy-on-conflict) for the
> conflicting predecessor instead of unsoundly clashing all sharing predecessors. The
> hard sub-problem: KM's shared `sat_filler` keys by `(concept,role)`; splitting
> cleanly needs per-entry provenance (which predecessor imposed each label entry) —
> Konclude's `copyDependingIndividualNode`. Bound copies by ∀-operand-set, not by
> predecessor, to avoid the ×concepts OOM that plain non-shared `shiq` mode hits.
>
> **Committed this session (payg-strategy, 152 tests pass, tree clean):**
> `9b343b9` KPWRITE (sound backward-∀ self-node write, Konclude applyALLRule) +
> `KM_NO_INVCOMPOSE` switch · `a7b8fc6` wired `KM_HT_QO_CARD` into the qo_candidate
> route (cardinality giants now complete the forward pass; **needs a corpus sweep to
> confirm 0 regressions before relying on it**) · `979e536` the copy-on-conflict
> soundness guard test · `cd66966`/`0d79ef1`/`ee84ca2` the diagnosis + port-#2 spec +
> routing trace (this doc).
>
> **Validated experiment recipes (ws, group-safe):** dump TIN: `KM_DUMP_TIN=/tmp/x.tin
> km classify <ont>` (kill after TIN written; CB then times out). Verify-funnel direct:
> `km tableau < tin` under `KM_HT=1 KM_HT_FORCE=1 KM_HT_QO=1 KM_HT_QO_PC=1
> KM_HT_QO_SAT=1 KM_HT_QO_FPROP=1 KM_HT_QO_CARD=1 KM_HT_QO_VERIFY=1 KM_HT_QO_PMMERGE=1
> KM_HT_NUMBER=1 KM_NO_INVCOMPOSE=1` (the orchestrator forces CERTIFY_ONLY, so test the
> funnel via the direct worker, NOT via `km classify`). ore_ont_9724.owl is on ws at
> `~/minimize/`; 7581 and the other giants are NOT on ws (use unimatrix corpus
> `~/ore2015/pool_sample/files/`). Build ws: `rsync -a engine/src/ ws:...; ssh ws 'cd
> ~/km-frontend/kobayashi-marust/engine && nice cargo build --release'`.
>
> **Also pending:** 7581+16444 regressed to timeout in sweep 7419. INVESTIGATED
> 2026-06-26 (ws, TIN funnel trace): the regression is NOT cheap routing. With
> SHOQ disabled (`KM_NO_HT_SHOQ`) 7581 STILL times out (130s, 0 subs), so SHOQ is
> not stealing the route. The QO certify funnel itself now defers with the exact
> reason `QOGF defer: INVCOMPOSE write-mode but 4 residual inverse bridges
> (composition not total) — cannot certify` (same defer under `KM_NO_INVCOMPOSE`).
> So 7581 is the SAME class as 9724: the inverse-composition certify is incomplete
> — 4 cb_to_ht inverse bridges the INVCOMPOSE write-mode cannot make total, so the
> sound gate correctly refuses to certify. The fix is the faithful Konclude inverse
> handling (port #2's per-creation-role extension + backward-∀ over genuine
> predecessor edges), NOT a routing toggle. 9724 reconfirmed same session: card-split
> clean=2816 / affected=20320 of 23136 ⇒ defers ⇒ times out. Both converge on port #2.
> CONFIRMED no-shortcut (2026-06-26): applied the 7581-winning recipe to 9724
> (INVCOMPOSE+INVCHAIN+INVONEWAY+CARD+GFCERT). Composition SUCCEEDS (871 bridges,
> 395 composed, 125519->140494 clauses, NOT node-capped) but QOGF still defers
> (insufficient=true, kp_miss=0, insuff_nodes=32603, card-split clean=2815/affected
> =20321). 9724's blocker is the cardinality Eq-heads + ∀-into-shared-filler
> critical-ALL, NOT the inverse bridges — so the 7581 fix does not transfer; only
> port #2 removes it.
> TINs cached on ws: /tmp/7581.tin (52MB), /tmp/9724.tin (14MB). Disjunction family
> (1603/541/9540/12653): Konclude uses pseudo-model/expander cache + small per-test
> completion graphs (separate from port #2).
>
> **HARD RULES:** build on ws / sweep via Slurm+unimatrix, NEVER IBEX login nodes
> ([[feedback_ibex_login_no_compute]]); group-safe km + clean orphans by PID
> ([[feedback_ws_no_orphans]]); port from Konclude source, don't invent
> ([[feedback_port_from_konclude]]); Lean re-cert at the very END. Memory:
> [[project_km_shiq_build]] session 8.

Status: source-grounded plan (2026-06-25). PORT from Konclude, do not invent
([[feedback_port_from_konclude]]). This REPLACES an earlier draft that invented a
"successor-subtree cache" — Konclude does NOT do that; the real mechanism is below.

## What Konclude actually does (read from source, file:line)

`Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`:

- **Shared non-branching saturation**, one node per (concept, polarity); `∃R.C`
  reuses the shared C-node (this IS Konclude's amortization / "cache" — there is no
  separate subtree cache).
- **∀-rule = CHECK, never pollute** (`isCriticalALLConceptDescriptorInsufficient`,
  :3451). For a `∀R.C` descriptor on node `n`, walk `n`'s R-successors; for each
  successor read its `ReapplyConceptSaturationLabelSet` and test
  `succConSet->containsConcept(operand, neg)` for every operand of C (:3514-3518). It
  does NOT add C to the successor. If an operand is absent ⇒ `return true` (critical).
- **Critical ⇒ INSUFFICIENT + propagate by STATUS FLAG, not label** (:881-884):
  `updateDirectAddingIndividualStatusFlags(n, INDSATFLAGINSUFFICIENT)` +
  `INDSATFLAGPROPAGATIONINCOMPLETE` + `setInsufficientNodeOccured`. Insufficiency
  rides up the predecessor chain via `updateIndirectAddingIndividualStatusFlags(n,
  succ->getIndirectStatusFlags())` (:1657/1803/1939/2018) — G2: a node inherits its
  successor's STATUS flags, never its concept set.
- **3-state outcome**: CLEAN (completed, no clash, not insufficient) ⇒ read subsumers
  off the node; CLASHED ⇒ unsat; INSUFFICIENT ⇒ residue → complete tableau.
- Cache key for the per-concept result is **(concept, negation)** (KONCLUDE-SATURATION-
  CACHE-SPEC.md), reused at every occurrence. Session 6g: that key is INERT in KM
  (KM's shared pass already shares C-nodes; each (concept,neg) saturates once/run).

## What KM already has (do NOT re-invent)

- Shared pass: `saturate_global` (`hypertableau.rs:3366`), one node per concept via
  `concept_node_of` — = Konclude's shared saturation.
- The G2/G3 CHECK: `KM_HT_QO_KPSET` — `kp_check_head` containment-checks a head write
  instead of writing it; misses set `kp_insufficient`; `kp_finalize` =
  `checkCriticalIndividuals`. This IS `isCriticalALLConceptDescriptorInsufficient`.
- Criticality at the ∀-write: `apply_head` t!=X branch (`:4310-4346`) already marks
  `qo_insufficient` + records `kp_insuff_nodes` when a write is not "clean".
- Per-node CLEAN split + reverse-reachability affected-set (`card_defer`).

## The REAL gap (why KM over-defers, and the faithful fix)

KM's kpset/criticality is present but **too coarse on inverse-heavy giants**: every
inverse-bridge back-edge write is a "miss" (7581: kp_miss≈930k; 9724: 66M), so
`qo_insufficient` trips globally and the per-node reverse-reach marks ~every concept
insufficient (7581: 0/72989 clean) ⇒ whole classification deferred ⇒ falls to the slow
per-concept path. The faithful port is NOT a new cache; it is making the G2/G3
propagation **precise** so CLEAN concepts survive:

1. **Status-flag (not label) propagation, edge-direction-correct.** Port Konclude's
   `updateIndirectAddingIndividualStatusFlags`: insufficiency propagates ONLY along the
   genuine forward predecessor chain of the node that is actually critical, not via the
   conflated reversed inverse back-edges. KM's reverse-reach currently follows inverse
   back-edges too ⇒ over-marks. Restrict propagation to Konclude's predecessor links.
2. **Per-creation-role ALL-concept extension** (`getRoleSuccessorALLConceptExtensionData`,
   :960; `CSaturationLinkedSuccessorIndividualALLConceptsExtensionData`): the ∀-operands
   live in a SEPARATE per-(successor,creation-role) structure used only for the
   criticality check + consistency, NOT in the shared subsumer label. KM writes them
   into the label (pollution) or defers; port the separate extension so the shared
   subsumer label stays clean and only criticality consults the operands.
3. **Backward propagation to predecessors** (`addConceptFilteredToIndividual` on the
   ancestor, :1235): the sound named-subsumer inverse contribution goes BACKWARD to the
   predecessor (non-critical), distinct from the forward operand check. KM conflates
   these via reversed-edge label reads.

Together these keep the shared single pass sound for ∀ + inverse WITHOUT ×concepts
memory and WITHOUT global deferral — Konclude's actual lever. This is the substantial
multi-session engine work (matches the shiq_build "orders of magnitude" finding).

## EMPIRICAL ground truth (2026-06-26, ws, ore_ont_9724, KM_HT_TRACE)

Measured the actual blockers on 9724 (SHIF, 23136 named, 14115 ∃-heads, 674 eq
heads, 0 disjunctions). Overturns the "66M kp_miss = inverse over-defer" framing:

- The default qo_candidate path (INVCOMPOSE on, no card_defer) bails the pass
  **`unsupported=true` at the FIRST functional/≤n `Eq`-head** (`apply_head:4474`),
  with `kp_miss=0`, `inv_edges=1`. So inverse is NOT the first wall — CARDINALITY is.
- With **`KM_HT_QO_CARD`** (card_defer): `unsupported=false`, the forward pass
  completes and already yields **clean_subs=456239 of gold 457090 (99.8%)** as a
  SOUND lower bound (clean concepts complete; affected concepts emit their sound
  forward subsumers). Only ~851 subsumptions need the inverse/cardinality
  completion. BUT `kp_miss=66,661,218` (`inv_edges=2.5M`) ⇒ 20321/23136 concepts
  "affected" ⇒ the gate still DEFERS.
- **KPWRITE does NOT fire on these 66M misses** (kp_miss byte-identical with/without
  it): the misses are **FILLER-targeted** (`is_filler`), where writing+reading as a
  named subsumer is the conflation kpwrite correctly refuses. So the self-node
  backward write (committed, sound, tested) is real but inert on 9724.
- INVCOMPOSE on vs off (`KM_NO_INVCOMPOSE`): kp_miss 66.7M vs 65.9M, clean unchanged
  — INVCOMPOSE is not the lever either.

CONCLUSION: 9724 needs (1) `card_defer` (already exists, just not in the
qo_candidate env) PLUS (2) **port #2 — the per-creation-role ALL-concept
extension** so the 66M filler-inverse containment checks are made against the
correct per-(successor,creation-role) operand store and PASS (eliminating the
spurious affected-set), instead of being checked against the conflated shared
filler label and missing. That collapses the affected set so the card-split
certifies or leaves a tiny residue. Port #2 is the next implementation.

## Konclude ROUTING trace (2026-06-26, two source agents + ws experiments)

Per user directive "follow where Konclude routes these onts." Konclude's classify
routing (file:line in agent reports): (1) ONE global saturation pass → per-concept
pseudo-models (small trees ≤30 nodes, depth ≤3); (2) if globally clean read the WHOLE
hierarchy off deterministic labels, NO tableau; (3) else keep pseudo-models, read
KNOWN subsumers off deterministic-branch labels, PRUNE candidate subsumptions via
pseudo-model merge (`isPseudoModelSubsumerPossible`, COptimizedKPSetClassSubsumption
ClassifierThread.cpp:1626 — C⊑D needs every DETERMINISTIC concept/role-succ of C
present in D, else refuted, sound), and run the residual `C⊓¬D`-unsat test ONLY on
surviving insufficient candidates, propagating each verdict through the ancestor/
descendant subtree (`prunePossibleSubsumptions`:2204) so #tests ≪ #pairs.

KM ALREADY IMPLEMENTS this routing: `qo_classify_global_fwd` (global pass) +
`KM_HT_QO_VERIFY` (structural suspects → per-suspect inverse saturation → tight
candidates → residual test) + `KM_HT_QO_PMMERGE` (the pseudo-model refutation
pre-filter). Validated gold-exact on 7581. THE GAP: (a) the production qo_candidate
route uses KPSET+CERTIFY_ONLY which DEFERS to CB instead of running the funnel;
(b) more fundamentally, KM's residual test is `consistent(A⊓¬B)` via the COMPLETE
TABLEAU, which BLOWS UP (7581: 244s, just over timeout; 9724: traced — QOGF
card-split 2816 clean/20320 affected, then the per-candidate complete-tableau
verification times out). Konclude decides the residual in FAST SOUND SATURATION
(KPSet G1/G2/G3), NOT a tableau. So "the same routing" requires the same RESIDUAL
DECISION ENGINE = port #2 below (a sound+complete KPSet that does not over-defer the
inverse-∀). Every lever tried (kpwrite, kpguard, invcompose, shiq, card_defer, the
verify funnel) converges here. Port #2 IS the routing's residual engine.

## Port #2 spec — per-creation-role ALL-concept extension (read from source 2026-06-26)

Konclude data flow (CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp):
- `applyALLRule` (:6143): a `∀R.C` on node n (a) writes operands BACKWARD to genuine
  R-predecessors via backPropHash (`addConceptFilteredToIndividual`, :6167 = KPWRITE,
  done); (b) if R propagates into the creation direction, calls
  `addALLConceptExtensionProcessingRole` (:6196) + marks n CRITICAL + queues a
  CCT_FORALL critical descriptor.
- `addSuccessorExtensionsALLConcept` (:2520): puts the ∀-operands into a SEPARATE
  `allConSuccExtData->addExtensionConcept(op,neg)` store — NOT the subsumer label.
- `processSuccessorALLConceptsExtensions` (:2659) → `updateSuccessorRoleALLConceptsExtensions`
  applies the stored operands to n's R-successors AND propagates to "dependent
  individuals" via `addProcessExtensionToDependentIndividuals` (:2718) following
  `getCopyDependingIndividualNodeLinker` — the COPY-ON-MERGE links.
- `isCriticalALLConceptDescriptorInsufficient` (:3451): the operand-containment check.

THE HARD PART (why this is not a small change): QoSat's `sat_filler` shares one
filler per `(filler-concept, role)` across ALL `∃R.D` holders (bounded memory). Writing
the per-predecessor ∀-operands into that SHARED filler accumulates the UNION of
constraints from incompatible predecessors → a SPURIOUS clash on the filler →
unsoundly marks every sharing predecessor unsat (this is the "7581 6.5M pollution"
the pure-check kpset exists to avoid). Konclude resolves it with
`copyDependingIndividualNode`: successors are SHARED UNTIL a conflicting constraint
arrives, then COPIED (split) so each predecessor keeps its own consistent successor.
That is the non-shared/copy-on-conflict successor infrastructure (the KM_HT_QO_SHIQ
`qo_parent` per-source successors are the non-shared extreme — sound but ×concepts
memory / OOM on 7914 per shiq_build). Port #2 = the MIDDLE ground Konclude uses:
share by content, copy only on a real per-predecessor ∀-conflict.

KM realization plan: (1) keep the shared `sat_filler`; (2) attach a per-(filler,role)
extension set for inverse-∀ operands instead of deferring them as kp checks; (3)
fire forward GUARD rules from the extension (completeness) but detect a per-filler
clash; (4) on a clash that is NOT forced by the filler's own concept (i.e. it came
from a predecessor-specific ∀), SPLIT the filler (copy-depending) for the conflicting
predecessor rather than killing the shared node. Synthetic test FIRST: two predecessors
∃R.D, one adds `∀R⁻.C`, the other `∀R⁻.¬C` — the shared filler must NOT clash both
predecessors (the copy-on-conflict regression test). Build on ws, Lean re-cert at END.

## Build plan (incremental, ws synthetic-test-first, Lean re-cert at END)

1. Regression test locking the CLEAN/INSUFFICIENT verdicts KPSET already produces on a
   tiny ∀+∃+inverse KB (the safety net).
2. Port #1: restrict insufficiency propagation to forward predecessor links (not
   inverse back-edges) — measure 7581/9724 clean% rises from ~0.
3. Port #2: the per-creation-role ALL-concept extension (operands out of the subsumer
   label) — eliminates the remaining pollution-driven misses.
4. Measure on 7914/9724 isolated (`km tableau` on a dumped TIN, group-safe). Target:
   global pass certifies most concepts; small residue to the verify funnel.
5. Full corpus sweep (rare, unimatrix) + Lean re-cert of the affected QoSat rules.

Konclude anchors: isCriticalALL :3451, status-flag propagation :1657/1803/1939/2018,
INDSATFLAGINSUFFICIENT :881-884, per-creation-role ext :960, backward write :1235.
KM anchors: kp_check_head / kp_finalize, qo_insufficient `apply_head:4331`,
kp_insuff_nodes reverse-reach, saturate_global :3366.

## Session 2026-06-26 results: cardmerge bounded, residue-complete built, giants still blocked

Landed (committed): **content-shared cardmerge** (Konclude ≤-rule). A forced
cardinality Eq unions the two fillers' seeds and redirects both anchor edges to
`seed_filler(r, sorted-seed)` — one node per distinct merged content. This replaced
the union-find privatize that blew node count up (9724 599k, 7914 >1.3 GB). Result
(KM_HT_QO_CARDMERGE, 170s, KM_HT_TRACE): node count bounded everywhere
(7914 21583, 9724 46822, 9663 81084), no panic, 159 tests.

Per-giant gate diagnosis (`QOGF split-diag` / `eq-defer-why`):
- **7914**: `card_insuff=0` — ALL 7785 cardinality Eqs merge; the cardinality is
  fully handled. Residue obstacles are 146 ≤-rule branch points + 68 parked ⊔.
- **9663**: split-dominated (114350 ∀ redirects), `card_insuff=0`, 22 insuff nodes,
  but **105 parked ⊔** — the live-disjunction family.
- **9724**: `card_insuff=106M` with `eq-defer-why nonfiller=73.6M norole=32.5M` — its
  Eqs are nominal/ABox-shaped, NOT the ∃-filler-pair form content-shared cardmerge
  handles. Needs a different (nominal/individual) merge mechanism.

Built (gated `KM_HT_QO_RESIDUE_COMPLETE`, NOT yet a win): **residue-restricted
complete verify**. On a card-split deferral, emit the clean bulk (concepts whose
root reverse-reaches no insufficiency / parked ⊔ — sound + complete) and run the
full tableau ONLY on the affected residue. Per residue concept: one real model
`consistent(a)`, take its positive query concepts as a sound+complete candidate
superset, confirm each with `consistent(a ⊓ ¬b)`. Pending-disjunction anchors are
seeded into the affected set; closure is in_edges-only (reverse reach — a root is
polluted only by an insufficiency in its own forward model). All confined to the
flag; default card-split path byte-identical.

WHY IT DOES NOT YET CRACK THE GIANTS (two independent walls):
1. **Residues are not small.** in_edges-only affected counts: 7914 **7204** / 17680,
   9724 20313 / 23136, 9663 **48315** / 58192. The insufficiencies + parked ⊔ are
   ancestrally pervasive (most concepts reverse-reach one), so the residue is 40-83%
   of the KB, not a tiny core.
2. **The full-tableau `consistent()` model build itself explodes on cardinality.**
   On 7914 each residue model build is ~18 s and growing (`TR dfs depth=0` =
   deterministic ≥n-successor forest that never blocks) — 8 builds in 145 s. The
   ≤-merge (KM_HT_QMERGE) in the full Ht tableau does NOT fold these the way QoSat's
   content-shared cardmerge does.

NEXT (the real remaining work, in priority order):
- **Port content-shared cardinality folding into the full Ht tableau `consistent()`**
  (mirror `seed_filler` in the `Ext` ≥/≤ machinery) so residue model builds
  terminate. This is the unblocker for 7914 (residue-complete would then finish 7204
  bounded builds). Bigger change; Ext-level, test-first.
- **9724**: nominal/ABox-shaped Eq merge (`mergeIndividualNode` for individuals),
  outside the ∃-filler-pair form.
- **9663**: live-disjunction family — search convergence, the known-hard problem
  (see project_km_disjunction_split); residue restriction cannot help when 83% of
  concepts reverse-reach a parked ⊔.
