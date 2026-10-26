---
name: project_km_router_sweep_7581
description: 2026-06-26 router sweep (default/cb/ht @120s) + 7581 recovery (gold-exact) via INVCHAIN+GFCERT+short-budget; routing conclusion fallback-only.
metadata: 
  node_type: memory
  type: project
  originSessionId: 666845f8-0818-4d3e-8e4f-a3e9496633db
---

2026-06-26 session. Goal = beat Konclude/HermiT/ELK on all ORE onts (time+mem),
port from Konclude, sound+complete only. [[project_km_7581_qosat]]
[[project_km_shiq_build]] [[project_km_contested_gold]].

**Router sweep (unimatrix01, 120s, parallel-packed --cpus-per-task=8 --mem=22G,
KM_THREADS=8; rough-but-fast per user direction).** Harness committed in-repo at
`results/router-sweep-harness/` (router_runone.py = /proc-poll peak like
ore_runone.py; router_sweep_par.sbatch; fast_soundness.py = sig_sha-match
comparator, 34s vs the 9-min set-diff aggregator). Snapshot:
`results/benchmarks/2026-06-26-router-sweep.md`.
- default 560 ok / cb 556 / **ht-race 566** (ht solves most). wall median ~1s,
  peak median 75-107MB, max ~16GB (giants).
- **0 unsound in EVERY mode vs BOTH Konclude and HermiT.** cb is 0 unsound +0
  incomplete (pure CB sound+complete on what it solves, lightest 75MB median).
- **ht-RACE mode is UNSAFE**: wins races on 15098/12009/6817 where the HT arm is
  INCOMPLETE (ALC+⊔ subset-blocking). ⇒ keep FALLBACK mode (HT answers only via
  the sound CERTIFY_ONLY QO/SHOQ arms or after CB fails). Routing conclusion: CB
  first; certify-or-defer arms add only sound+complete recoveries.
- ELK is NOT a soundness oracle for non-EL onts (drops non-EL axioms; can't see
  8941/10621 inconsistency) — excluded from soundness scoring.

**7581 RECOVERED gold-exact** (was a CB timeout; Horn-ALCHQ 498k cl / 73k
concepts). Konclude-faithful gap-close (commit 16e6749, payg-strategy): the QO
certify funnel deferred on "4 residual inverse bridges (composition not total)".
Three gaps, all in the qo_candidate arm (race.rs:588) / hypertableau.rs:
1. composed only single-role-body bridges → added **KM_HT_QO_INVCHAIN +
   INVONEWAY** (fold one-way + chain-consumed bridges in compose_inverse) → 0
   residual.
2. CERTIFY_ONLY deferred without the clean global certify → added
   **KM_HT_QO_GFCERT**: under certify_only, try qo_classify_global_fwd, which
   returns Some ONLY when the forward closure is COMPLETE (card-split res==0 or 0
   residual bridges) — sound+complete by construction, else defer.
3. fallback race gave the QO arm the full ht_budget_s=225s so its certified-at-20s
   answer was never harvested → QO arm now uses the SHORT (shoq) budget
   (spawn_ht third tuple elem = shoq_candidate || qo_candidate; budget = "start
   accepting HT" threshold, harvests when ready past it). Monotone-safe (CB
   preferred if first; QO is CERTIFY_ONLY so its answer == CB's).
Validated: km sig sha == Konclude gold sha (565317 subs, 0/0). Full sweep job
7550: RECOVERED=[7581] REGRESSED=[] 0 unsound 0 new incomplete; 152 tests pass.

**CB-blowup 'misses' are THREAD/MEMORY artifacts, not algorithmic** (confirmed
ws single-ont + exclusive recheck job 7609): 6212 ok 129s@8thr, 15491 ok 226s@8thr
(but TIMES OUT @16thr — more threads amplifies RSS, [[project_km_threads_vs_algo]]),
6246 ok 109s@16thr. The packed/high-thread sweep over-reports these. Lever =
thread-routing (downshift threads for memory-bound onts BEFORE the RSS watchdog
tips them past budget; run_engine_adaptive currently jumps 16thr->fail->1thr, no
middle tier, engine_run.rs:176). TRIED+REVERTED the half-thread retry (retry
central at N/2 on OOM before single-threaded): INEFFECTIVE — first attempt eats
the budget to central_time_cap=190s before the retry starts, so 6212 still timed
out @235s. Recovery REQUIRES STARTING at fewer threads (structural per-ont router),
NOT a retry tier; needs a full exclusive 16-vs-8 @240s no-regression sweep first
(clause-count alone doesn't separate memory-bound from throughput giants that want
16). Perf/config lever, orthogonal to Konclude port. Only 16444 = genuine ~20GB
CB memout.

**True ALGORITHMIC misses (240s):** giants 9724/7914/9663/14817/7499 + 16444;
all converge on **port #2** (Konclude
per-creation-role ALL-concept extension + copy-on-conflict shared successors for
inverse-∀); disjunction family 1603/541/9540/12653/10702/5303 (pseudo-model +
small per-test graphs). 9724 reconfirmed: forward QO clean=2816/affected=20320 of
23136 → over-defers. 7581 & 9724 TINs cached on ws /tmp/{7581,9724}.tin.
Pre-existing default incomplete: 10702 (disjunction), 12698 (84 missing subs —
investigate). Konclude/HermiT cons-mismatch onts 5940, 8135 (KM follows Konclude).

**SESSION 9 (2026-06-26): port #2 BUILT + the giant lever is CARDINALITY, not ∀.**
Implemented port #2 (Konclude copyDependingIndividualNode) as a sound, monotone,
bounded copy-on-conflict for forward ∀r.C-into-shared-filler:
`KM_HT_QO_SPLIT` redirects the source's r-edge onto a node keyed by
`(base-fil,role,source ∀-operand set)`, base fillers stay unpolluted; commit
`aae23ed`, tests split_certifies_shared_filler_conflict +
split_forall_operand_still_propagates. DECISIVE diagnostic on ore_ont_9724 TIN
(ws, KM_HT_TRACE split-diag): **redirects=0, forall_insuff=0,
card_insuff=98,380,184** ⇒ 9724 defers 100% on cardinality Eq-heads, ZERO ∀, so
port #2 is INERT there. The LEVER-C-CACHE "9724 = ∀-into-shared-filler over-defer"
framing was WRONG (corrected in doc top block). Also landed the sound
self-equality short-circuit for Eq-heads (commit `530064b`: the card_defer branch
ignored s/t and deferred on every Eq(n,n); now sn==tn ⇒ satisfied; tests
card_self_equality_not_insufficient + card_distinct_merge_still_defers) — but it
only trims 9724 98.4M→97.5M Eq-firings (clean 2816→2823), so the 97M residue are
REAL distinct-successor merges. 156 cargo tests pass, 0 regressions, both commits
on payg-strategy. **NEXT LEVER = cardinality Eq-head MERGE** (Konclude ≤-rule /
mergeIndividualNode): a proper union-find node merge (NOT a content copy-on-merge
— the merged content is the union of two EVOLVING labels, so content-keying is
incomplete), under sat_mode only (never merge concept self-nodes), per-source to
avoid polluting predecessors without the ≤n. Forward-only already gives ~99.8% of
subs soundly (clean_subs) ⇒ goal is a TIGHT merge-affected set, not coverage.
Other giant TINs (7914/9663/7499/14817) NOT on ws — relay from unimatrix to find a
∀-dominated one where port #2 DOES pay off. 9724.tin still cached on ws /tmp.

**SESSION 9 cont. — BOTH Konclude giant mechanisms ported + validated.** Built the
cardinality Eq-head union-find MERGE (`KM_HT_QO_CARDMERGE`, commit `0ae502a`,
Konclude ≤-rule/mergeIndividualNode: find/merged_into union-find, privatize=
copyDependingIndividualNode before merge, merge_victim folds victim into survivor,
kill_node defers ∃-sources of a dead filler; only filler nodes merge, never
self-nodes; per-source privatize so a shared filler's unconstrained predecessor is
NOT polluted). 159 cargo tests pass (3 new cardmerge: compatible→certify,
clash→defer, no-pollute-unconstrained). Giants split by which insufficiency channel
dominates (TINs on ws /tmp/{9663,9724,7914}.tin; diag `QOGF split-diag: redirects=
forall_insuff= card_insuff= cardmerges=`):
- **9663 (∀-dominated, the WIN):** port #2 SPLIT alone forall_insuff 325315→0 (114k
  redirects), affected 2451→59. + CARDMERGE: card_insuff 34596→0 (11339 merges),
  BOTH channels closed, forward affected set →~92 of 23k, bounded 92k nodes/546MB.
  Vast majority certify from the sound forward pass; only ~92 to the residue verify
  — which is SLOW (TR dfs times out @175s), a SEPARATE funnel-speed bottleneck. To
  fully solve 9663 = speed the 92-node residue verify.
- **7914 (card 75k) + 9724 (card 98M): cardmerge NODE BLOWUP** (9724→599k cap-bail;
  7914→>1.3GB). privatize copies one node per (shared filler, constrained pred); under
  pervasive functional roles ≈per-edge → explosion. SAFE (gated, bails unsupported
  at cap → defers → CB), never unsound, but inert there. NEXT: cheaper merge =
  content-share merged nodes by fil-set (like port #2 operand keying) + node-budget
  fallback to card_defer so the clean bulk still certifies. Port #2 inert on these
  (card-dominated, forall_insuff=0). Commits aae23ed/530064b/0ae502a, all opt-in,
  no routing change. Full table in docs/LEVER-C-CACHE.md top.

**SESSION 10 (2026-06-26): content-shared cardmerge LANDED (bounds blowup) +
residue-complete BUILT+gated, but giants STILL blocked by a SECOND wall.** Replaced
the union-find privatize (the node blowup above) with **content-shared cardmerge**
(commit `0076764`): a forced cardinality Eq unions both fillers' seeds and redirects
both anchor edges to `seed_filler(r, sorted-seed)` = one node per distinct merged
content. Node count now BOUNDED everywhere (7914 21583, 9724 46822, 9663 81084), no
panic (guard_refire re-reads in/out_edges len each iter — a merge's remove_edge
shrank it mid-loop → index-OOB only at giant volume), 159 tests. `DBG_EQ_*` +
`QOGF eq-defer-why` diagnostic. Per-giant gate (KM_HT_QO_CARDMERGE, KM_HT_TRACE):
- **7914**: `card_insuff=0` — ALL 7785 Eqs merge; cardinality fully handled. Residue
  = 146 ≤-branch points (dead content-shared fillers via kill_node) + 68 parked ⊔.
- **9663**: split-dominated (114350 ∀ redirects), card_insuff=0, 22 insuff + **105
  parked ⊔** = live-disjunction family.
- **9724**: card_insuff=106M but `eq-defer-why nonfiller=73.6M norole=32.5M` — its
  Eqs are NOMINAL/ABox-shaped (operand not an ∃-filler / no shared-role pair), OUTSIDE
  the ∃-filler-pair form content-shared cardmerge handles. Needs mergeIndividualNode
  for individuals, a different mechanism.

Built **residue-restricted complete verify** (commit `e8a16c0`, gated
`KM_HT_QO_RESIDUE_COMPLETE`, default OFF, byte-identical default path): on a
card-split defer, emit the clean bulk (root reverse-reaches no insuff/⊔ → sound+
complete) and run the full tableau ONLY on the residue — per residue concept, one
model `consistent(a)`, take its positive query concepts as the sound+complete
candidate superset, confirm each via `consistent(a ⊓ ¬b)`. Seeds parked-⊔ anchors;
in_edges-only (reverse) closure. `qo_residue_complete` takes &self (worker-owned
cloned Ht). KM_HT_QO_RESIDUE_CAP default 5000, KM_HT_QO_BIDIR A/B.

**WHY IT DOESN'T CRACK THE GIANTS (two independent walls, both MEASURED):**
(1) residues NOT small — in_edges-only affected = 7914 7204/17680, 9724 20313/23136,
9663 48315/58192 (insuff + parked ⊔ ancestrally pervasive). (2) the full-tableau
`consistent()` model build ITSELF explodes on cardinality — 7914 ~18s/residue model
(`TR dfs depth=0` deterministic ≥n forest, Ht ≤-merge/QMERGE doesn't fold it),
8 builds in 145s ⇒ hours. **NEXT = task #10: port content-shared cardinality folding
(seed_filler) into the Ext ≥/≤ machinery so consistent() terminates on the giants;
THEN residue-complete finishes 7914's 7204 bounded builds.** Prior non-shared
qo_parent approach OOM'd ([[project_km_shiq_build]]) — must be content-shared. Giant
TINs cached ws /tmp/{9663,9724,7914,7581}.tin; 7914 Konclude gold relayed to ws
/tmp/gold_konclude_7914.sig.gz (hermit has none — DNF).

**SESSION 10 cont. — 7914 CLASSIFIES (timeout→242s); the Ext port is NOT needed.**
The blocker was NOT cardinality model-build explosion — it was `consistent()`
bailing `None` on `≤n` AtMost heads because **KM_HT_QMERGE was off**. With
`KM_HT_QMERGE=1` the residue-restricted complete verify finishes 7914: card-split
clean=17353 / affected=**327** / clean_subs=137451, residue-complete 327 concepts /
4186 confirms / **241.93s @ 8 threads**, total 141531 subs + 1 unsat, peak 21583
nodes, rc=0. Full run flags: BASE(KM_HT_FORCE KM_HT_QO KM_HT_QO_PC KM_HT_QO_SAT
KM_HT_QO_FPROP KM_HT_QO_CARD KM_HT_QO_VERIFY KM_HT_QO_PMMERGE KM_HT_NUMBER
KM_NO_INVCOMPOSE) + KM_HT_QMERGE KM_HT_QO_CARDMERGE KM_HT_QO_RESIDUE_COMPLETE
KM_HT_QO_RESIDUE_CAP=500 KM_HT_PAR=8. NB the affected count VARIES run-to-run
(327 vs an earlier 7204) — cardmerge merge order is HashMap-iteration-dependent so
the dead-filler set + reverse-reach differ; both SOUND (clean = definitely-
unaffected over-approx), only the tightness varies.

GOLD DIFF (cmp via oracle/ore/ore_canon.py json-canon vs gold .sig, script
/tmp/cmp7914.py on ws): **UNSOUND(km-only)=19, INCOMPLETE(gold-only)=5 subs +2
unsat**. The 19 km-only all hang off UBERON_0001373 / UBERON_0008977, which gold
(Konclude) calls UNSAT and km calls SAT — so the WHOLE diff is km missing the
unsat of those 2 concepts (+5 unrelated missing subs). They are in the CLEAN bulk
(not the 327 residue), so the clean/affected PARTITION let an unsat concept through
= the forward QoSat pass marked them clean (no clash, reverse-reaches no flagged
insufficiency) yet they are unsat. Either a real clean-bulk incompleteness for
unsat-detection (the residue closure must also catch these) OR contested Konclude
gold (HermiT DNF on 7914, can't arbitrate). NEXT: determine clean-bulk vs contested
before trusting/committing the residue-complete as a 7914 solver. Task #10 (Ext
cardinality folding) DEMOTED — not the lever; QMERGE+residue-complete is.

**ARBITRATED: the 2 missed unsats are REAL (km is incomplete), NOT contested gold.**
HermiT (trusted oracle) on the STAR module (1617 axioms, extracted via OWL API
SyntacticLocalityModuleExtractor — preserves unsat over the signature) says
**module consistent=true, UBERON_0001373 satisfiable=FALSE, UBERON_0008977
satisfiable=FALSE** — agrees with Konclude. ELK does NOT flag them (unsat is non-EL
→ needs branching, which is exactly where km's forward QoSat clean-bulk misses it).
Diff is REPRODUCIBLE byte-identical across 2 runs (clean=17353/affected=327 both),
so it is a SYSTEMATIC clean/affected PARTITION incompleteness, not cardmerge
nondeterminism. ⇒ the residue-complete clean bulk can emit a satisfiable verdict for
a genuinely-unsat concept whose unsatisfiability needs branching the forward pass
parks/misses. THIS IS THE BUG TO FIX before residue-complete is a sound 7914 solver:
the affected closure must capture these (the disjunction/cardinality interaction that
makes them unsat is not being reverse-reached). Tooling (all on ws): HermiT 1.4.6 +
owlapi 5.1.9 at ~/minimize/hermit_cp/; ontology /tmp/ore_ont_7914.owl (161922 ax);
groovy scripts /tmp/{explain7914,justify7914}.groovy (module extract + black-box
justification); Konclude binary on unimatrix
~/bench/reasoners/Konclude-v0.7.0-1138-.../Binaries/Konclude. Justification (minimal
MUPS) being computed to pin the exact axiom pattern km's clean-bulk must learn to
flag as affected.
