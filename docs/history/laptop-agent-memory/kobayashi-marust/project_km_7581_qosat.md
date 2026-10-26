---
name: project_km_7581_qosat
description: 2026-06-23 7581 SOLVED sound+complete via forward-only per-concept QoSat (drop inverse-bridge back-edge reads); 106 spurious were inverse pollution, NOT range/canon
metadata: 
  node_type: memory
  type: project
  originSessionId: 17d1eba9-eaa6-4268-97ae-40756c219352
---

2026-06-23. User: "Implement the Konclude-style Ht for 7581 — make it sound AND
complete; look at Konclude code to cheat, then fix our Ht." DONE.

## RE-ARCH ATTEMPT (2026-06-23, commit bf75bc4, payg-strategy): fprop+fcheck SOUND but NON-CERTIFYING; encoding-level levers EXHAUSTED
User: "commit to what is necessary to get the time down to Konklude level: QoSat
saturation re-architecture." Built two QoSat mechanisms (gated, 131 tests):
- **fprop (KM_HT_QO_FPROP)**: forward-broadcast mirror of `prop` (head-on-TARGET
  Horn NF4, the shape compose_inverse emits). **FIXES the INVCOMPOSE divergence**
  (composed clauses re-fired per edge → edge_work 3M→5M never converging; fprop
  converges at forward cost). Threaded as new_opts 3rd param (race-free tests).
- **fcheck (KM_HT_QO_FCHECK)**: composed clauses run CONTAINMENT-CHECK not write.
  Write-mode = UNSOUND (1.34GB over-derive; forward mirror of reversed-edge
  conflation). fcheck = SOUND gold-exact (565317=gold 0/0), **1.0GB (lowest of
  any path)**, insufficiency cut 36495(KPSET)→1581 nodes/31202 obligations.
MEASURED 7581 INVCOMPOSE+FCHECK[+SAT+KPGUARD]: still DEFERS (kp_insufficient),
funnel delivers gold in ~133s. Why it can't certify on the global pass:
- the 1581 misses are GENUINE inverse facts at SHARED ∃-fillers (has_part filler
  shared across wholes) that DON'T change the named subsumption set (forward=gold).
- per-node bidirectional reachability filter: **0/72989 concepts clean** (dense
  part_of/has_part graph) → routing residue to funnel DEAD (same as KPSET).
- guard/self-node criticality (KPGUARD) + separate fillers (SAT) recover NOTHING:
  the composed heads E' are THEMSELVES body-guards → critical regardless.
**Every encoding-level lever refuted.** All work at KM's NF4+prop/reversed-edge
encoding with HEAD-containment checks. Konclude gets 0-insufficient via a
DIFFERENT test: isCriticalALL (cpp:3514) checks ∀-restriction OPERANDS at REAL
successors over SEPARATE per-creation-role successors — not head-containment on
NF4 over shared fillers. VERDICT (SUPERSEDED below): seemed to need a new calculus path.

## BREAKTHROUGH (2026-06-23, payg-strategy): hybrid certifies 7581 in 31s SOUND
The missing combination: the 1.34GB write-mode over-derive was SHARED-filler
pollution; under **sat_mode (separate per-(concept,role) fillers = Konclude G1)**
the composed writes land on fillers NEVER read as named subsumers → SOUND.
**Sound+complete fast path = INVCOMPOSE + FPROP + SAT + KPSET** (all 4 flags, via
the kpset gate):
- INVCOMPOSE composes the ~110k composable inverse consumers to forward clauses,
  drops their bridges; FPROP broadcasts them at prop speed; SAT writes them to
  separate fillers (sound, G1); KPSET containment-checks the residual
  non-composable bridges (certify iff kp_miss=0).
- MEASURED 7581: `QOKP certified sound+complete kp_miss=0 inv_edges=0`,
  **31.3s / 1.0GB, km=565317=gold, 0/0**. 4x faster than the 126s pseudo-model
  path, within ~3x of Konclude ~10s, lowest memory.
- 7581's 2 residual bridges are VACUOUS (0 reversed edges) so kpset passes.
- Added a residual-bridge GUARD (count_inverse_bridges): bare write-mode
  (FPROP+SAT, no KPSET) DEFERS when any bridge survived composition — else it'd
  drop it and be gold-exact only by luck (the unguarded 30s run). Guard makes it
  sound; KPSET is the principled way to clear the residual.
- Soundness principled: sat_mode ⇒ named self-node never a filler ⇒ gets E only
  via forward EL (prop over own ∃-succ), never a composed inverse write.
Commits bf75bc4 (fprop+fcheck) + bf86f0a (G1 crit/refutation) + this. All gated.
Full chain in docs/KPSET-PLAN.md.

## CORPUS VALIDATION DONE (2026-06-24, unimatrix job 7322, commit 98077ba)
Sweep: HYBRID (INVCOMPOSE+FPROP+SAT+KPSET) vs PRIOR-2a funnel, both forced-QO
(KM_ENGINE=/bin/false)+VERIFY, 200s cap, vs Konclude gold + vs each other. 582/592:
- **0 REGRESSIONS** — hybrid NEVER worse than prior-2a on any ont.
- **7581 RECOVERED**: hyb=565317=gold 0/0 in 32.7s; prior-2a TIMES OUT (only
  answer-win, the target ont).
- **All 14 gold-gap onts agree=true** (10908/11315/11745/14312/1618/5404/5566/
  6999/8982/...) = PRE-EXISTING QO limitations identical in both configs (unsat
  under-detection e.g. 5404 RELAPPROXC138; partial-answer 8982 -207408; 6999
  datatype). CB-handled in production. NOT my change.
- COST: 3 large CB-territory onts (11395/3905/3377, 3377=4.49M subs) TIMEOUT at
  200s cap where prior finished ~110s — INVCOMPOSE composed-clauses + SAT filler
  overhead. => ROUTE the hybrid to the Horn-inverse certify fragment, do NOT
  blanket-enable.
- BUG FOUND+FIXED by the sweep: INVCOMPOSE swapped self.clauses without rebuilding
  Ht tableau triggers -> per-concept verify panicked (fire_anchor_concept
  out-of-range pos) on 10127. Fixed: rebuild_triggers (98077ba). 10127 gold-exact.
VERDICT: certify path validated sound+complete corpus-wide. Default-on needs a
ROUTER (Horn-inverse certify candidates only). km-hybrid binary deployed at
unimatrix ~/bench/km/km-hybrid; sweep harness ~/bench/ore_harness/qo_runone.py +
qo_sweep.sbatch; results res_qosweep_*.jsonl.

## ROUTER WIRED (2026-06-24, commit ca71836): KM_HT_QO_ROUTER, one flag, validated
Sound certify-OR-DEFER race arm. Pieces: (1) quasi_order_classify certify-only mode
(KM_HT_QO_CERTIFY_ONLY) — structural pre-gate defers if count_inverse_bridges==0,
and defers (NO funnel) if kpset doesn't certify; (2) tableau.rs run_json: certify-
only deferral returns NO answer (no branching/legacy fallback) so CB decides;
(3) race.rs spawn_ht: has_inverse_bridge(clauses) detects the BRIDGE encoding
(cb_to_ht tin.inverse=FALSE for 7581! bridges not the pairwise flag — KEY GOTCHA),
routes only faithful+nominal-free+inverse-bridge onts to the hybrid+certify-only
arm, non-inverse HT-routable (5303) keep normal branching path; (4) mod.rs: race
mode (first valid wins) under router so fast certify beats CB timeout.
VALIDATED (real pipeline, only KM_HT_QO_ROUTER=1): 7581 RECOVERED 565317=gold 0/0
89.6s (hybrid wins race; standalone certify 31s, rest is CB racing cores); 5404
km=1291=gold 0/0 (DEFERS->CB, fixes the forced-QO +7/-1 pre-existing gap); 10127
512=gold 0/0. Router-mode corpus sweep found a CERTIFY COMPLETENESS GAP (see below).

## CERTIFY GAP + FALLBACK FIX (2026-06-24, commit e164958)
Router sweep 7352 (race mode) exposed: **the kpset certify is NOT a complete
oracle**. ore_ont_15098: certify kp_miss=0 (claims complete) but yields 939 subs,
truth 951 — MISSES 12 inverse-entailed subs of Q_* definers via for/is_supported_by
inverse pairs. So kp_miss=0 does NOT guarantee completeness; composed-forward+kpset
can silently miss inverse subs. 7581 certifies complete, 15098 doesn't — distinguishing
condition NOT yet characterised. Was MASKED in sweep 7322 (fallback mode, CB's 951
always preferred over certify's 939); race mode let the faster incomplete certify win.
FIX: router runs the certify arm in FALLBACK mode (mod.rs ht_mode=cfg.ht_mode, NOT
forced race) — CB preferred when it finishes, certify taken only when CB errors/exceeds
KM_HT_BUDGET_S. Validated: 15098 km=951=gold 0/0 (CB wins, 0.9s); 7581 km=565317=gold
0/0 (CB times out->certify, 90s @budget=60). Router SOUND regardless of the gap (only
relies on certify where CB gives NO answer). Default budget 225s. Sweep 7369 (fallback,
budget=150) running. REMAINING: make kp_miss=0 a true completeness oracle (or
characterise the safe fragment) before the certify can be a primary/non-fallback answer.

## 2b PHASE A DONE + MEASURED (2026-06-23, commits d1c1863 + 1aa338e, payg-strategy)
User insisted 2b is a PORT not research ("the code is in Konclude, implement the
missing pieces"). Re-cloned Konclude source to ws:/tmp/Konclude-src. KEY mechanism
(CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp:3451
`isCriticalALLConceptDescriptorInsufficient`): Konclude NEVER writes a ∀/backward
operand onto a shared successor — it CHECKS containment (succConSet->containsConcept
for every operand); if absent → mark node INSUFFICIENT, never write. That + it does
NOT materialise reversed inverse edges (inverse = backward-∀ annotation over forward
links) is why insufficient≈0 on 7581.
- IMPLEMENTED in QoSat behind **KM_HT_QO_KPSET** (gated, default OFF, 0 baseline
  risk, 129 tests incl 2 new): keep inverse-bridge clauses, record their back-edges
  in `inv_edges`; any concept-head write anchored on an inverse back-edge →
  CONTAINMENT CHECK (`kp_check_head`/`kp_write`), deferred to fixpoint
  (`kp_finalize` = Konclude `checkCriticalIndividuals`). Miss → `kp_insufficient`.
  `qo_classify_kpset` tried first in quasi_order_classify; Some=certified
  sound+complete, None=fall through.
- **7581 RESULT: SOUND + NO BLOWUP but does NOT yet certify.** Inverse-aware KPSet
  pass runs at forward cost (37s/1.0GB whole classify, vs old 111s/6.5M-fact
  pollution) — containment discipline killed the blowup. Gold-exact via forward-only
  fallback (565317=gold, 0/0). BUT kp_miss=929558 over inv_edges=898356: KM's
  cb_to_ht encodes inverse as MATERIALISED reversed edges, so 129k `∃r2.D⊑E` fire
  across back-edges at SHARED fillers → ~930k predecessor-dependent spurious
  consequences (all spurious since NOINV=gold). Global kp_insufficient bool too
  coarse → defers whole classification.
- **Per-node granularity MEASURED USELESS**: added kp_insuff_nodes + reverse-reach
  probe (concept affected iff self-node forward-reaches an insufficient node). 7581:
  **0/72989 CLEAN** (insuff_nodes=36495, every concept reaches one). Subtree
  reachability is totally conservative.
- **REMAINING PORT = study P2 pseudo-model merge** (`isPseudoModelSubsumerPossible`,
  COptimizedKPSetClassSubsumptionClassifierThread): track per-concept POSSIBLE
  subsumers (the kp-misses), refute each A⊑B by LINEAR sorted-map merge (a
  deterministic concept of B's model absent in A's ⇒ not subsumed; role-cardinality
  clash ⇒ not subsumed) — NOT subtree reachability. For 7581 (forward=gold) every
  possible refutes → residue 0 → certified fast. This is the next step. See
  docs/KPSET-PLAN.md (STATUS section) + docs/KONCLUDE-STUDY.md P2.
- Run harness on ws: /tmp/kpset_7581.sh (KM_ENGINE=/bin/false to disable CB — the
  KM_ENGINE_BIN harness bug; KM_HT_QO_KPSET=1 KM_HT_QO_PC=1 KM_HT_TRACE=1).

## DEFINITIVE RESULT (validated end-to-end, ws, ore_canon vs konclude gold)
- **Forward-only per-concept QoSat gate: 7581 = gold EXACTLY. km_subs=565317,
  gold=565317, UNSOUND=0, INCOMPLETE=0, consistent=true.** exit 0, ~283s wall
  (frontend-dominated; saturation alone ~109s), 10GB RSS. Was: 106 unsound (gate)
  or timeout (CB). The 106 are GONE; zero real subsumptions lost.
- SPEED CAVEAT: 283s on ws is over the 240s production budget *on ws*; saturation
  is ~109s, the rest is frontend parse of the 37MB OWL. NOT yet confirmed on the
  benchmark host (unimatrix/IBEX). This is a speed concern, not correctness.

## 2b P2 DONE — 7581 CERTIFIED SOUND+COMPLETE UNDER BUDGET (2026-06-23, commit 9045d95)
**KM_HT_QO_PMMERGE**: port of concept-part of Konclude isPseudoModelSubsumerPossible
(COptimizedKPSetClassSubsumptionClassifierThread.cpp:1626). For each tight inverse-only
candidate (A,B) from the 2a verify funnel: instead of blowing-up consistent(A⊓¬B),
build ONE model of A (`model_root_pos`=consistent(&[A]), much easier) and REFUTE A⊑B
iff B absent from that model's root label — SOUND (B false in a real inverse-aware
model of A ⇒ A⋢B). Survivors→full tableau; refuted→dropped no-test.
**7581 (ws): 565317=gold, 0 unsound/0 incomplete, 129s/2.5GB — UNDER 240s budget**
(2a was 244s OVER). All 177 candidates REFUTED → 0 survivors → 0 consistent(A⊓¬B)
tests (the hard inverse blowups never reached; verify stage 0.37s). FIRST time KM
certifies 7581 completeness within budget instead of trusting forward-only.
- Soundness key: after consistent(&[A])=Some(true), self.ext.concepts[0] (root) is
  A's model assignment; absent positive concept = false there = genuine countermodel.
  130 tests (new pmmerge_model_root_refutes_nonsubsumer).
- BOTTLENECK toward Konclude ~10s: pmmerge spends ~90s building 63 full consistent(A)
  models. **Building the pseudo-model from the SATURATION is UNSOUND** (commit 4cc0102):
  forward label UNDER-approximates inverse-entailed subsumers, so "B absent => A⋢B"
  would refute REAL subsumptions on load-bearing-inverse onts. A sound saturation
  pseudo-model needs the complete deterministic subsumer set = the classification
  itself (circular). Konclude builds pseudo-models from per-concept SAT COMPLETIONS too
  (getAssociatedSaturationCacheEntry, classifier cpp:1530), NOT raw saturation — KM
  already mirrors that; Konclude's speed = a FAST sat test reusing a cached ⊤-saturation,
  and KM_HT_SATCACHE is sound only for ALC(H) NO-inverse so it can't fast-path 7581.
  set_fast_tableau() (force incr2+incroblig, result-identical) baked into the model
  workers shaves only ~7s -> intrinsic model size is the cost. REAL levers to ~10s:
  (a) sound inverse-aware fast-sat cache (port), or (b) cb_to_ht inverse encoding WITHOUT
  materialised reversed edges (so forward saturation becomes inverse-complete + the
  pseudo-model is free). Both are larger structural changes. Run: /tmp/kpset_pm.sh on ws
  (KM_HT_QO_PC+VERIFY+PMMERGE+PAR=16; speedups now baked in, no extra flags needed).

## LEVERS 1&2 toward ~10s — BOTH QUICK FORMS REFUTED (2026-06-23, commits eaff662+30c7f04)
7581 inverse = part_of/has_part (BFO_50/51) + 52/53, BIDIRECTIONALLY load-bearing
(both create ∃-edges; ~110k single-role NF4 consumers). 90-104s = building 63 real
consistent(A) models; a FEW intrinsically slow (45-64s, large DETERMINISTIC inverse
expansions, rootlen ~250).
- LEVER 2 (compose_inverse, KM_HT_QO_INVCOMPOSE): resolve bidirectional bridges into
  single-role consumers as forward clauses, drop bridges (SOUND resolvents, 130 tests).
  NET-NEGATIVE: gate saturation DIVERGES (edge_work 3M→5M, 22M+ steps). Root: reversed-
  edge NF4 (∃r.D⊑E head-on-SOURCE) is prop-optimised (compute-once per (filler,role)+
  broadcast); composed forward-∀ (head-on-TARGET) can't use prop → re-fires per edge.
  Reversed-edge+prop is the EFFICIENT encoding; shared-filler write is intrinsic to
  inverse regardless of encoding. Gated off.
- LEVER 1 threading: KM_HT_PAR=48 ≈ 16 (103 vs 104s, RSS 2.5→6.7GB) NOT thread-bound
  (allocator/mem contention). KM_HT_QO_PMCOMPOSE (composed clauses for model-builders
  only, gate keeps originals): MARGINAL (63→53s/64→56s, ~3%). Slow models = raw
  deterministic EXPANSION VOLUME, not inverse-blocking, not threads.
- PROVEN: candidates REQUIRE the exact tableau (inverse-augmented saturation over-
  approximates → candidate B is IN it → can't refute by absence; forward under-
  approximates → can't confirm; gap = candidate set). No saturation shortcut.
- ONLY real lever to ~10s = inverse-sound satisfiable-expander cache (reuse satisfiable
  filler subtrees across the 63 builds; Konclude's mechanism). KM_HT_SATCACHE/SATFOLD
  are no-inverse versions; inverse-sound port (cache key must capture inverse-predecessor
  context) = substantial future work. Certified 126s under-budget STANDS as the milestone.
- USES 2a funnel (KM_HT_QO_PC+VERIFY+PMMERGE+PAR=16), NOT the KPSET global gate
  (qo_classify_kpset defers on 7581 — Phase A below).

## KONCLUDE TRACE on 7581 — DEFINITIVE (2026-06-23, commit 1cf52fa)
Ran deployed Konclude binary (unimatrix ~/bench/reasoners/Konclude-.../Binaries/Konclude
classification -v -i ore_ont_7581.owl). 9.7s total: parse 1.4s, preprocess 3.1s,
**saturate(precompute) 3.4s, "sufficiently saturated, extracting data", extract 0.9s.
ZERO tableau tests, ZERO pseudo-model merges** (the "Used N satisfiable/pseudo-model/
calculated tests" log line did NOT fire). Selector = CConfigDependedSubsumptionClassifier
Factory::isClassificationBySaturationCalculationSufficient: if
!ProcessingDataBox->isInsufficientNodeOccured() -> COptimizedClassExtractedSaturation
classifier (read subsumers off saturation, no tests). **Konclude's saturation marks
ZERO insufficient nodes on 7581.** applyALLRule (cpp:6143) WRITES forall/inverse operands:
(a) BACKWARD to predecessors via role backward-prop links (addConceptFilteredToIndividual,
non-critical); (b) forward via per-creation-role ALL-concept EXTENSION (separate from the
subsumer label), marked CRITICAL -> isCriticalALLConceptDescriptorInsufficient sets
insufficient only if a successor lacks the operands. 7581 trips no criticality.

## KM REPLICATION of "sufficient saturation" FAILED (sound+gated, 2026-06-23, commit 1cf52fa)
- KM_HT_QO_KPGUARD: insufficient only for BODY-GUARD operands (non-guard = inert). Sound
  but 7581's inverse operands ARE body-guards -> no reduction (kp_miss still ~930k).
- KM_HT_QO_SAT: separate role-keyed (concept,role) successor nodes so inverse writes miss
  self-nodes. +43k nodes/1.2M inv edges, kp_miss=1.24M, STILL insufficient. Propagating
  operands re-introduces shared-filler pollution ACROSS PREDECESSORS ((concept,role)
  filler shared by all predecessors of that exists).
ROOT CAUSE of gap: Konclude's per-creation-role ALL-concept EXTENSION (separate struct,
consistency/criticality only) + backward-propagation-to-predecessors (the sound named-
subsumer inverse contribution) + narrow criticality, TOGETHER keep the shared-successor
model sound across multiple predecessors. KM's reversed-edge+prop model has none of that
separation. Faithful port = substantial QoSat node-model re-architecture (shared successors
+ per-role extension + backward-prop links + criticality), NOT a flag. Both attempts gated
default-off, gold via forward-only fallback. **Certified 126s pseudo-model-merge STANDS.**
Trace/run harness: unimatrix Konclude binary; ws /tmp/kpsat_7581.sh.

## ROOT CAUSE — PROVEN (supersedes ALL earlier hypotheses below)
7581 tableau input (cb_to_ht): 455583 clauses, **Horn (disj=0)**, inverse=FALSE
*natively* BUT **7 role-head bridging clauses, 4 of them INVERSE** (single role
head with args SWAPPED vs a body role: `r1(x,y)→r2(y,x)`, r1↔r2, r7↔r8) + role
hierarchy; 129286 NF4-backward (`R(x,y)⊓D(y)→E(x)`, head on anchor); 43141 ∃
heads; only **4 range** (non-anchor concept heads); 1 functional.

The 106 spurious come **entirely from the 4 inverse-bridge clauses**. They create
model-specific REVERSED back-edges (`filler→r2→root`); the 129k NF4 rules then
read the shared concept-node's RUNTIME LABEL across that back-edge, deriving
seed-specific consequences as if global (`b⊑∃r2.D` holds only because `root→r1→b`
in THIS model, never in general). Classic shared-filler-in-cycle pollution, now
precisely attributed to inverse — NOT range (only 4), NOT ≥n, NOT a canon artifact.

**PROOF**: `KM_HT_QO_NOINV=1` (drop inverse-bridge clauses) → 7581 = gold EXACTLY
(0/0). So inverse is DECLARED but NON-LOAD-BEARING for 7581's classification:
removing it loses zero real subsumptions and kills all 106 spurious. (This also
DISPROVES the earlier "canon-artifact" and "≥n" theories in the history below.)

## THE FIX (shipped, engine/src/hypertableau.rs, behind KM_HT_QO_PC)
- `QoSat::new_opts(clauses, skip_inverse)`: `skip_inverse=true` drops inverse/
  symmetric bridging clauses (role head with swapped args). The shared-node
  saturation may only read a successor's runtime label across genuine FORWARD
  ∃-edges, never across an inverse back-edge → forward-only is SOUND (monotone:
  dropping clauses never over-derives).
- Per-concept gate `qo_classify_perconcept`: forward-only saturation per concept =
  sound subsumers (the default, returned directly). A forward-only clash = sound
  unsat.
- SOUND+COMPLETE+GENERAL mode (KM_HT_QO_VERIFY): also run the inverse-augmented
  saturation (complete superset) and verify each inverse-only candidate
  `(A,B)∈U\L` with the complete tableau `consistent(A⊓¬B)` — keep iff entailed.
  Result = forward-only ∪ confirmed = exactly truth. **But the per-candidate full
  `consistent()` is too slow on a 73k giant** (177 candidates → 560s timeout after
  the 2 saturations). So VERIFY is OPT-IN, not default. Default = forward-only:
  sound always, complete whenever inverse is non-load-bearing (true for 7581).
- Konclude match (verified vs /tmp/Konclude): `getRoleSuccessorALLConceptExtension
  Data(creationRole)` = per-creation-role ALL/range folding (G1);
  `isCriticalALLConceptDescriptorInsufficient`→`setInsufficientNodeOccured` = mark
  insufficient when a successor doesn't cleanly contain the operand (G3). I ALSO
  implemented role-keyed range folding (`range_class`/`filler_node`/`node_range`,
  fillers keyed by (concept, range-class); `qopc_range_no_cross_role_pollution`
  test) — sound + correct Konclude G1, but INERT on 7581 (only 4 range clauses,
  range isn't the cause). Reduces to old behaviour when no range clauses exist.
- 127 cargo tests pass (incl. the new range-pollution test). Diagnostics gated OFF:
  KM_HT_QO_NOINV, KM_HT_QO_NOPROP. NOT committed yet at time of writing.

## SINGLE-PASS speedup (2026-06-23, matches Konclude) — `qo_classify_global_fwd`
Per-concept gate = 73k single-seed saturations (~109s). Replaced by ONE forward-only
GLOBAL saturation (`saturate_global`, seed every concept as own self-node, shared
∃-fillers) reading subsumers off each concept's OWN self-node label. = Konclude
arch (CCalculationTableauApproximationSaturationTaskHandleAlgorithm +
CPrecomputedSaturationSubsumerExtractor). Tried FIRST under KM_HT_QO_PC; falls to
per-concept only if global can't cleanly decide (`!pending.is_empty()` parked disj,
`qo_insufficient` ∀/range pollution, or unsupported). SOUND b/c forward-only;
COMPLETE == per-concept (no cross-concept pollution: inverse back-edges dropped +
∀/range writes caught by qo_insufficient). Wired in quasi_order_classify.
**ws measured (same HW as Konclude): QO saturation core (km tableau on TInput) =
10.3s/0.69GB gold-exact; end-to-end km classify (CB disabled) = 24s/1.0GB, 0/0.
Konclude = 9.7s/2.5GB. SATURATION CORE MATCHES KONCLUDE; mem LOWER.** 127 tests
pass. Frontend(ofn)=3-8.6s, cb_to_ht=1s, output(174MB,1.19M raw pairs)=~5s.

## VERIFY PASS = INFEASIBLE (measured, do NOT retry global-qu)
User picked "sound+complete verify pass." MEASURED DEAD: global inverse-augmented
saturation over-derives **6,518,962 spurious candidates** on 7581 (cross-concept
shared-filler pollution; the old "5.3M over-approx") → can't verify. Per-concept
inverse bounds candidates (~177) but = 73k saturations(~109s)+177×3s tableau(~530s)
≈600s, NOT Konclude-speed. Cheap STRUCTURAL cert ("reversed roles unused in bodies")
also FAILS: 7581 reversed role ids {1,2,7,8} but role 1 used 109486× in bodies (2 in
2× pairs) — structurally load-bearing yet semantically inert (NOINV=gold). So
CERTIFIED-complete and Konclude-FAST are in TENSION for load-bearing-inverse; shipped
forward-only (sound always, complete on inverse-inert fragment incl 7581). Certified
completeness under load-bearing inverse = the open problem (unchanged).

## HARNESS BUG (cost hours): KM_ENGINE not KM_ENGINE_BIN
Rust orchestrator reads **KM_ENGINE** (config.rs:84 `engine_bin_override`), NOT
KM_ENGINE_BIN. ALL scripts + CLAUDE.md set KM_ENGINE_BIN=/bin/false to disable CB →
SILENTLY IGNORED → real CB ran on 7581 (its native timeout), starved the niced HT
racer (10s→56s) AND fallback waited ht_budget_s=225s (config default) before taking
HT's ready answer → bogus ~238s "QO" time. With KM_ENGINE=/bin/false: CB errors
0.25s, true end-to-end 24s. PRODUCTION: 7581 not EL-safe → races real CB (timeout) →
fallback still waits ~225s for the doomed CB before HT. Deploying at 24s needs a
routing change (QO-primary), a separate decision (forward-only-trusted, sound; the
verify-pass to certify it is the ~600s tension above).

## VERIFY FUNNEL (2026-06-23, KM_HT_QO_VERIFY) — CORRECT but inverse-saturation-bound
Sound+complete path: forward-only global L (sound) + global-inverse SELECTS suspects
(sound superset) + per-concept single-seed inverse DE-CONFLATES suspects → tight
candidates + complete-tableau verify(A⊓¬B). On 7581: 10635 suspects → **177 tight
candidates** (collapses the 6.5M global pollution), all verify as non-subs (fwd =
complete). Verify is CHEAP: **~0.02s median, 0.26s avg, 2.5s max per candidate**
(prior 560s was the saturations, NOT verifies). Sound+complete by construction; defers
(None) on per-concept-inverse unsupported or candidate cap (KM_HT_QO_VERIFY_CAP=50000).
**BUT certified path >280s — DECISIVE ROOT CAUSE: KM's inverse saturation is
fundamentally expensive.** global inverse alone = **111s** (vs 10s fwd) building the
6.5M-fact polluted model; per-concept inverse THRASHES (16M edge-ops for ONE 71-node
concept). KM reads a shared filler's runtime LABEL across back-edges (EL backward-link)
→ inverse back-edges blow up propagation. Forward-only (drops them) = only fast
saturation. **NECESSARY LEVER (answer to "what is necessary"): a SOUND+EFFICIENT
inverse saturation = Konclude KPSet G2 (from a successor propagate STATUS flags, never
labels) — substantial algo extension, NOT a routing tweak.** Until then: sound+complete
& Konclude-FAST are mutually exclusive for load-bearing-inverse onts. Committed gated
(KM_HT_QO_VERIFY), 127 tests, zero baseline risk. Step 3 routing BLOCKED: fast-certified
needs KPSet; routing forward-only-trusted violates the hard sound+complete requirement.

## 2a VERIFY SPEEDUP (2026-06-23) — structural select + parallel; verify-blowup wall
Two sound gated speedups to KM_HT_QO_VERIFY funnel: (1) STRUCTURAL suspect selection
(concept suspect iff forward closure reaches an inverse-having-role edge; O(nodes+edges)
from qf.out_edges/in_edges reverse-reach) replaces the 111s inverse-global pass → **0.03s**
(flags all 72989, fine). KM_HT_QO_GLOBALSEL = old behavior. (2) PARALLEL work-stealing
(per-thread QoSat/Ht, classify_parallel pattern, KM_HT_PAR): per-concept inverse 330s→**7.7s**,
verify parallelized. **7581: 511s → 244s, sound+complete gold-exact (177 cands all dropped).**
**WALL: verify still ~226s on 16 threads (only ~1.5x!) — the 177 tight candidates are HARD
inverse pairs, a FEW consistent(A⊓¬B) tableau tests BLOW UP (~100s+ each, = original 7581
complexity); parallelism can't shrink ONE slow test.** Per-candidate timeout-keep would be
UNSOUND (None=keep over-claims). So 2a hits the budget EDGE (244s vs 240). **2b (KPSet,
docs/KPSET-PLAN.md) is NECESSARY not optional**: decide hard candidates in a SOUND saturation
(G1 own-node subsumers / G2 status-not-labels from successors / G3 insufficient→tableau),
never the blowing-up tableau → ~10s Konclude speed. 2a committed (gated, gold-exact, 127 tests).

## OPEN / NEXT
- Confirm 7581 passes the 240s budget on the benchmark host (saturation ~109s +
  frontend). If over: speed the frontend or the saturation; or accept >240s as a
  sound+complete result that beats the prior timeout.
- Completeness in general: forward-only is sound but silently incomplete if inverse
  IS load-bearing on some other QO_PC-routed ont. Need a CHEAP sound completeness
  check (the full-tableau VERIFY is too slow). Candidate: track provenance so only
  candidates derived via an inverse back-edge to an ancestor/seed (the always-
  spurious shape) are dropped without a tableau test; truly-novel inverse
  candidates would still need verify. Or: detect structurally that inverse cannot
  contribute (no reachable `∃r⁻.C⊑D` position) → forward-only provably complete.
- KM_HT_QO_PC is OPT-IN (not in the default kmbatch config) → committing the fix is
  zero-risk to the 568 corpus baseline.

## Speedups (prior work, COMMITTED f2aca93, stand)
elc-style QoSat saturation: take/restore hot trigger vecs (no per-pop clone); elc
NF4 (role,filler-concept) edge index (role_tgt_trig/role_src_trig/role_noguard);
backward-link prop store `prop[(R,T)]` (NF4 consequence computed once per
(filler,role), broadcast to predecessors); trigger-keyed complete_roles re-fire.
Took 7581 saturation 280s timeout → ~109s/502MB. prop store proven sound
(KM_HT_QO_NOPROP identical).

## Konclude architecture (verified vs /tmp/Konclude source)
ONE non-branching approximation saturation over the TBox → per concept CLASHED/
CLEAN/INSUFFICIENT; only INSUFFICIENT hits the complete tableau (≈0 for 7581).
Shares filler nodes but sound via G1 (subsumers from the concept's OWN self-node,
never a shared successor — CPrecomputedSaturationSubsumerExtractor), G2 (from a
successor propagate only STATUS flags, never labels), G3 (∀-forward/≤n-merge/open-⊔
→ INSUFFICIENT). KPSet 3-valued + pseudo-model merge refuters. docs/KONCLUDE-STUDY.md.
KM's bug was exactly the G2 violation: NF4-backward reads a successor's runtime
LABEL (and, across inverse back-edges, that read is model-specific → unsound).

## See also
[[project_km_shiq_ht]] [[project_km_konclude_study]] [[project_km_rust_elc]]

---
HISTORY (superseded hypotheses, kept for audit): earlier passes wrongly blamed
(a) ≥n cardinality, (b) ∀/range pollution, (c) a definer-IRI localname canon
artifact ("106 is not real unsoundness") — the LAST is decisively WRONG: NOINV
gives gold EXACTLY, so the 106 were genuine inverse-induced reasoning over-
derivations surfaced correctly by the harness. The range-folding fix (G1) is
correct but inert here. The actual lever is dropping the inverse-bridge back-edge
label reads.
