---
name: project_km_rsucc_gap
description: 2026-06-26 root cause of the transitive+inverse under-detected-unsat (7914/T2/mini) — r-Succ forward push missing; pinned + design + soundness hazard
updated: 2026-06-27 — 12698 is the live ORE transitive+inverse INCOMPLETENESS (not unsat): SHI, 10 transitive + 12 inverse roles, completes fast (~40s). KM=126659 pairs vs gold 126761 → MISSING 102, EXTRA 0 (SOUND, incomplete). KM_RSUCC=1 is INERT here (identical output) — so the rsucc forward-push does NOT cover this gap. Missing subs all funnel into a few HUB superclasses (CHEBI:37577 (appears 43x), EFO_0000001, OBI_0100026, Role); NOT a canon artifact (KM derives no form of e.g. CCONT_0000024⊑CHEBI:37577). 7914 is NOT this gap — it's a 15MB throughput GIANT (gold 141521 subs, 0 unsat, KM timeout); my older note conflated the synthetic reproducer with the ORE ont. NEXT for 12698: find the missing inference into the hub classes (examine SubClassOf/Equiv axioms around CHEBI:37577 + the transitive/inverse roles), port it, re-cert. Onts relay: unimatrix ~/ore2015/pool_sample/files/ore_ont_12698.owl. UPDATE same day: 12698 is NOT a clean canon artifact / NOT a clean KM win. RIGOROUS full-IRI KM-vs-HermiT closure diff (HermiT -c, 21306 SubClassOf + 3 Equiv): KM=126659, HermiT-closure=126714, KM MISSES 84 + KM EXTRA 29 (both directions differ!). Root = the ont MIXES IRI forms for the same entity with NO equating axiom: NCBITaxon_10239 has 2 IRIs (purl.org/obo/owl/NCBITaxon# [orphan leaf, 7x] vs purl.obolibrary.org/obo/ [hierarchy, 106x]); CHEBI mixes purl.obolibrary.org/obo/CHEBI_NNNNN vs ebi.ac.uk/chebi/searchId.do?chebiId=CHEBI:NNNNN. KM, HermiT, Konclude ALL disagree (3-way). KM sound vs Konclude-gold (localname-canon, 0 extra) but vs HermiT-full-IRI has 29 extra + 84 miss. NOT cleanly closeable; the "right" answer is genuinely ambiguous given the namespace mess. Lesson: verify canon-artifact hypotheses with full-IRI HermiT closure BEFORE claiming KM-correct. KM output /tmp/km12698.json, HermiT /tmp/h12698.out on unimatrix.
metadata: 
  node_type: memory
  type: project
  originSessionId: 666845f8-0818-4d3e-8e4f-a3e9496633db
---

The transitive+inverse under-detected-unsat gap (ore_ont_7914 UBERON_0001373 /
UBERON_0008977; committed reproducers `tests/completeness-gaps/{trans_inv_reconstruct_unsat,mini7914_unsat}.ofn`).
km reports `:A` satisfiable; HermiT + hand-proof say unsat. Both the CB engine
and the HT `consistent()` miss it. See [[project_km_correctness_audit]].

**Root cause, pinned + rebuild-verified (commit c547e0f doc):**
The refutation needs `__trans__hp__G` derived ABOUT the po-successor `h`.
- km derives `__trans(x)` and the inverse back-edge `hp(f₁,x)` in the predecessor.
- To get `__trans(f₁)` you'd fire clause `__trans(y)∧hp(x,y)→__trans(x)` with
  **x := f₁ (function term)**. km's `unify` (calc.rs, Role case = Sequoia
  `canUnify`) FORBIDS binding an ontology clause's CENTRAL variable to a function
  term. So `__trans(f₁)` is never produced → nothing to push down.
- Removing the `__trans/__chain` exclusion in `is_succ_trigger` (calc.rs ~379) is
  NECESSARY but provably INERT alone (the predicate it would forward is never
  derived; T2/mini still `consistent:true` after rebuild). REVERTED.

**The fix = r-Succ forward push (the sound design):**
predecessor must push its OWN neighbour-relevant central facts `C(x)`
(here `__trans(x)`) to each successor as EDGE-CONDITIONED neighbour facts `C(y)`,
so clause `hp(x',y)∧__trans(y)→__trans(x')` fires IN the successor (x=central h,
y=neighbour a), using the back-edge km already pushes. Then `Q_6(∃hp.G)→Q_5/B→B⊓D=⊥`.

**Soundness hazard (why no quick patch):** central strategy SHARES a successor
context across predecessors (keyed by core). Unconditional forward push of `C(y)`
is UNSOUND for a co-sharing predecessor that doesn't entail `C`. Must be tied to
the specific predecessor edge — forward analogue of Sequoia `PredPush(neighbourCore)`.
km has conditioning for successor→predecessor (`neighbor_pred`/`pred_from_neighbor`,
keyed by edge_label+sender core) but NO forward-direction slot; add one.

**Sequoia note:** cloned kernel `Rules.scala` has only Hyper/Pred/Eq; inverse
roles handled via the Pred round-trip (`neighborIndex` + `getContextStructurePredecessors`),
NOT a liftable standalone r-Succ. Forward push is the direct sound realisation.

**IMPLEMENTED + VALIDATED 2026-06-26 (commit 7ca7c73, gated KM_RSUCC, default OFF):**
- calc.rs: `Sig.rsucc`; `is_succ_trigger` pushes reach-over-function-term when rsucc.
- engine.rs: `Engine::new` reads KM_RSUCC; `Context.rsucc_pool` (central reach
  max-head facts collected at work-off) + `pushed_rsucc` dedup keyed (f,target,p);
  `propagate` forwards reach(x)→reach(y) to every successor via ordinary Msg::Succ.
  The successor fires the transitivity clause NORMALLY across the inverse back-edge;
  conclusion conditioned on reach(y) → existing Pred routing (every body atom in
  edge pushed set) returns it ONLY to predecessors that pushed reach (sound under
  shared-successor central strategy). Predecessor derives reach(f) → forwarded → clash.
- VALIDATION (ws + unimatrix): both reproducers BYTE-EXACT vs HermiT —
  trans_inv_reconstruct_unsat→:A unsat, mini7914_unsat→:X unsat (HermiT: A/X unsat,
  ont consistent; README's "mini :A" was imprecise, real is :X). 159 unit tests pass.
  rsucc INERT (off==on byte-identical) on non-pattern onts (1340/10004 checked).
  `km classify` (pure-Rust, zero python) honors the flag end-to-end on unimatrix.

**Mandatory gates before default-on:** Lean re-cert (DEFERRED per user "ignore Lean")
+ corpus A/B soundness sweep IN FLIGHT: unimatrix Slurm job 7677 (array 0-29),
driver /tmp/rsucc_sweep.py, onts ~/bench/rsucc_sweep/chunks/, results
~/bench/rsucc_sweep/res/res_*.jsonl (per ont: off vs on, each vs Konclude gold;
unsound/incomplete/unsat diffs). Binary deployed unimatrix:bench/km/km-rsucc (multi-call)
+ kobayashi-marust-rsucc (engine). KEY CHECK: no ont gains unsound (off=0→on>0); any
recoveries = on matches gold where off missed. THEN default-on.

**CB corpus A/B sweep DONE (unimatrix job 7707, 584 onts, off vs on, each vs gold):**
- NEW UNSOUND = **0** (critical gate PASSES; shared-successor edge-conditioning holds).
- RECOVERIES = 0 on CB (the under-detected-unsat targets route to HT/elc, not CB).
- 3 RESOURCE regressions (all gated, NOT soundness): 11311 (30s→timeout), 9944
  (38s→timeout), 12698 (68s ok→88s ok but incomplete=84, lost 84 subs — a cap
  tripped under the extra push volume, partial result). ⇒ NOT default-on-ready:
  the unconditional reach-push to ALL successors is too expensive. Before default-on,
  bound it (push only to successors with an inverse back-edge / relevant role).
  Driver /tmp/rsucc_sweep.py, agg /tmp/rsucc_agg.py, res ~/bench/rsucc_sweep/res/.

**QOGF (giant path, 7914) PROVEN NON-VIABLE via flag-to-residue (2026-06-26):** 7914
routes to qo_classify_global_fwd (saturate_global), NOT QOPC. Extended the reach
post-pass with a dual-orientation scan (direct reach-role edges + `reach_via_inv`
over inverse-role forward edges, inv_map built from `R(x,y)→S(y,x)` bridging
clauses) and made saturate_global call kp_finalize under rsucc. RESULT: the reach
post-pass FIRES correctly (flagged=213880 fillers — the reconstruction pattern IS
detected) but OVER-FLAGS catastrophically: part_of/has_part + __trans is pervasive
in UBERON, residue 327→7090 affected concepts, each needs a full consistent() verify
→ 7914 TIMES OUT (rc=137 @500s). Sound but unusable. REVERTED the saturate_global
rsucc trigger (kept the trace + dual detection inert in QOGF). The giant path needs
PER-PREDECESSOR reconstruction (non-shared / copy-on-conflict fillers — the
KM_HT_QO_SHIQ infra in [[project_km_shiq_build]]), NOT a flag-to-residue pass.
7914 does NOT verify; HT fix stays UNCOMMITTED.

**HT fix (UNCOMMITTED, working tree):** added to hypertableau.rs gated KM_RSUCC —
`reach_by_role` (detects `C(y)∧R(x,y)→C(x)` clause shape) + reach post-pass in
`kp_finalize` (flag shared filler whose predecessor carries reach C across an edge)
+ QOPC hook (after qu.saturate, call kp_finalize, route kp_insufficient concepts to
unsat_cands → full-tableau verify). WORKS on the per-concept QOPC path: mini→:X,
ti→:A BYTE-EXACT vs HermiT, 159 tests pass. But **7914 routes to QOGF (global-shared
forward), NOT QOPC** — there the reach post-pass flags 0 nodes (kp_miss=0, even with
inverse-composition on) because the shared-filler model never materialises the
PER-PREDECESSOR inverse back-edge. So **7914 still misses UBERON_0001373/0008977**;
HT fix HELD UNCOMMITTED per user condition "commit once 7914 verifies". To recover
7914 the QOGF shared-model needs per-predecessor reconstruction or a forward-edge +
inverse-role-map detector (scan inv(R) forward edges); residue-explosion risk.

**7914 itself routes to HT** (CB times out), so the CB rsucc (committed) does NOT
recover full ore_ont_7914. mini7914 (distilled from UBERON_0008977) passing on BOTH
CB and HT-QOPC IS the proof the mechanism is right.

Prior stable HEAD c547e0f (e8a16c0 gated KM_HT_QO_RESIDUE_COMPLETE+QMERGE classifies
7914 at 242s but misses the 2 unsats — real incompleteness, the same gap).

**2026-06-28 — 14817's residual incomplete=71 IS THIS GAP (transitive part_of), NOT
disjunction/contested-gold.** After building the full Konclude pseudo-model subsystem
(prune 93ee82b, build 02e6178, approximate-saturation f98993d) + node-certain +
in-place per-concept residue (KM_HT_QO_INPLACE, commit 99b64b7), 14817 stays SOUND
(0 extra) + incomplete=71 at ~10-12s — and the 71 are PROVEN orthogonal to all that
machinery. KM_HT_QO_TESTONE=A,B (adjudicates one pair via complete Ht consistent(A⊓¬B))
on the REAL pairs (NOT my earlier bogus 39245⊑75837 which Konclude also lacks): 39245⊑36889
and 36310⊑36889 BOTH give consistent(a⊓¬b)=SAT ⇒ KM's complete Ht ALSO says a⋢b (both
KM engines miss it, same gap). Source axioms (unimatrix ore_ont_14817.owl) are
decisive: UBERON_0002288⊑∃part_of.UBERON_0002286; UBERON_0002200≡∃part_of.UBERON_0000033⊓UBERON_0002049;
UBERON_0002286⊑∃part_of.UBERON_0001894; **part_of=BFO_0000050 is TRANSITIVE (24 transitive
roles in the ont)** ⇒ 0002288⊑0002200 needs chaining part_of through its transitive
closure = exactly the r-Succ forward-push gap. The 71 funnel into part_of-defined hub
supers (UBERON_0002200/0004120/0012275). So 14817 is the SAME family as 12698/7914 (the
transitive part_of/has_part incompleteness), reachable only by the r-Succ fix (per-pred
reconstruction, [[project_km_shiq_build]]) — NOT by the disjunction/pseudo-model work.
LESSON (repeat of the 12698 lesson): the 14817 effort spent many cycles chasing a
Konclude-classify/disjunction explanation; the residual was the transitive-role gap all
along. Verify with TESTONE (complete Ht) + source axioms BEFORE assuming disjunction/gold.
NB build_nodecertain_map injection + greedy approx BOTH inert on the 71 (they're not
disjunction-mediated). The disjunction machinery IS sound + working (in-place residue
gives 0 false residue); it's just orthogonal to 14817's actual gap.

**2026-06-28 (session 2) RE-CONFIRMED + ALL existing flags PROVEN inert on 14817's 71 (measured, ws).** User: finish 14817 by tracing Konclude + porting exactly, incremental+measured. Re-derived the SAME diagnosis from scratch this session (Konclude baseline 15.5s/3.4GB; KM forward-bulk+INPLACE = 14.4s/3.1GB SOUND but 71-incomplete). Decisive new measurements: (1) real missing set via ore_canon diff = 71 missing / 0 extra / 46 sub-concepts / 7 supers (UBERON_0004120×30, _0012275×25, _0002200×5, _0013749×4, _0010260×3, _0003566×3, _0010314×1); the earlier 39245/75837 was a bogus probe pair (a⋢b correctly). (2) Source has TransitiveObjectProperty(RO_0002202 develops_from) + TransitiveObjectProperty(BFO_0000050 part_of) + 30 ObjectPropertyChains incl. develops_from∘part_of⊑develops_from. (3) recog.tin encodes these via 4982 `__trans__R__C` marker concepts + propagation clauses `R(x,y)∧__trans(y)→__trans(x)` (NOT 2-role-body chain clauses — only 13 of those, all cardinality). (4) TESTONE (complete Ht) on the REAL pair 78095⊑75837 (UBERON_0003229⊑UBERON_0004120) = consistent(a⊓¬b) SAT ⇒ KM complete tableau misses it, on BOTH recog.tin AND cc.tin (composition 3aa77f9). **(5) DECISIVE: KM_RSUCC=1 on the INPLACE per-concept (QOPC) path = byte-identical output (1184621, residue=0, 14s) — INERT on the 71.** So NO existing flag (KM_RSUCC, KM_TRANS_CHAIN_COMPOSE/cc.tin, INPLACE, CERTAIN/DISCHARGE, NODECERTAIN, APPROX) recovers them. The HT rsucc code (has_rsucc/reach_by_role/reach_via_inv/kp_finalize post-pass, current tree) only DETECTS+ROUTES to the complete verify, but the verify (`consistent()`) ITSELF misses the chain composition ⇒ routing is moot. **CONCLUSION: finishing 14817 needs a NEW per-concept-tableau derivation that actually FIRES the `__trans`/chain marker propagation across GENERATED successor edges in `consistent()` (the r-Succ forward push working inside the HT, not just CB) + the develops_from∘part_of chain composition — soundness-delicate under shared successors, Lean re-cert. This is the documented [[project_km_shiq_build]] per-predecessor reconstruction. HermiT classification of 14817 launched (ws /tmp/hermit_14817.txt) for final real-entailment confirmation.** ws probes: /tmp/14817_recog.tin, /tmp/14817_cc.tin, /tmp/km_inplace.out (14s sound 71-miss), /tmp/diff14817.py, /tmp/14817_konclude.out (gold).
