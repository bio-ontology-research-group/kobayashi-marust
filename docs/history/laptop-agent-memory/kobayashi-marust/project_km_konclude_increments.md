---
name: project_km_konclude_increments
description: "2026-06-18 implemented the 4 Konclude-inspired increments (P1-P4) in KM, all gated default-off, built+unit-tested on IBEX"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-18: implemented all 4 Konclude-study increments (commit b5773be on
payg-strategy), each placed per the universal-vs-tableau analysis. All gated
ENV flags, DEFAULT OFF → production path byte-identical until enabled. Built green
on IBEX km-rustport, 111 lib tests pass (5 new). See docs/KONCLUDE-STUDY.md +
[[project_km_konclude_study]].

- **P3 KM_ABSORB_HOIST** (frontend/clauses.rs `hoist_common_disjuncts`, wired
  frontend/mod.rs next to KM_EMELIM): common-disjunct hoisting. ⊤⊑A₁∨…∨Aₙ ⟹ add
  ⊤⊑X for X subsuming every disjunct (told one-step). Sound clause ADDITION (no
  re-cert). Universal (CB+elc consume it).
- **P1 KM_ELC_HOIST** (elcomplete.rs `hoist_residual_disjuncts`, called in
  classify_inner after the certificate; needs KM_ELC_CERT on to matter):
  SEMANTIC common-disjunct over the COMPLETED sub_super — parked D⊑A∨B ⟹ D⊑X for
  X subsuming all disjuncts. Recovers subs the EL pass dropped; only adds entailed
  pairs. Added Interner::id() non-creating lookup.
- **P2 KM_HT_PMMERGE** (tableau.rs classify): KPSet gate. TC of definite phase-1
  subs seeds known supers; confirm-down to definite subs, refute-up to known
  supers; pseudo-model refute skips A⊑B when a definite super of B is absent from
  a model of A. Cuts phase-2 SAT tests. Sound (skips only entailed-outcome tests).
- **P4 KM_HT_CACHE** (tableau.rs classify, local SatCache struct): (un)sat cache
  over sorted root labels; superset-of-unsat⇒unsat, subset-of-sat⇒sat. Monotone.

Also: json_io.rs JTerm now derives PartialEq/Eq (needed by P1 term compare).

Key design choices: off-path preserved exactly (all new logic guarded by the
flags / cache.on); used lifetime-annotated nested fns not closures (closures that
return refs into captured data hit "lifetime may not live long enough").

STATUS: implemented+unit-tested+committed. PENDING: corpus soundness smoke (job
47616793, KM_ABSORB_HOIST must == base on CB path) then full ORE sweep + gold
table per [[feedback_measurement_reporting]] before any default-on. Build/test on
IBEX km-rustport ONLY (never km-incr — live sweep). Smoke sbatch at
/ibex/scratch/hohndor/km-rustport/smoke.sbatch; build sbatch vp1p3.sbatch.

## 2026-06-18 part 2: disjunction-family attack (5303) — what works, what doesn't
EMELIM (cb_to_ht complementary-pair elim, KM_HT_EMELIM, NO frontend KM_EMELIM) +
HT race recovers 5303 TIMEOUT→0.11s, SOUND but INCOMPLETE-by-1 (CHSubstructure⊑
Hydrocarbon). Root cause: EMELIM drops ⊤⊑Q∨¬Q but ¬Q⊑∃hasComponentPart.Q17 — the
negative side has consequences; dropping loses the forced case-split → spurious model.
Speed/completeness TRADE.
Added + tested (all gated, sound, build green, NONE closes 5303 completely+fast):
- KM_HT_BLOCKSKIP, KM_HT_UNSATCACHE (per-test) — no effect on 5303 (tiny graph, consistent ont).
- KM_HT_EQBLOCK (equality blocking, complete), KM_HT_ALLCAND (test all candidates) —
  EMELIM+EQBLOCK+ALLCAND STILL incomplete-by-1 (gap is dormant constraint, not blocking/pruning).
- KM_HT_LAZY (guarded-before-unguarded disjunction selection) — noEM+LAZY and
  noEM+LAZY+EQ+UC+BS+ALL both TIMEOUT (kept-disjunction search doesn't converge).
RACE MODE UNSAFE: incomplete HT beat correct CB on 1340 (4 unsound+3868 missing).
Only KM_HT_MODE=fallback is monotone-safe. 10702/1603/9540 still TIMEOUT (genuine
non-complementary disjunctions EMELIM can't fold).
CONCLUSION: increment-level levers exhausted. Closing the family completely+fast needs
DECISION-ON-DEMAND rewrite of expand_inc (disjunction never materialised on a node
unless a clause activation/clash forces it) + Lean re-cert — a core rewrite, not a flag.
Commits: b5773be P1-P4, 7ace013 blockskip/unsatcache, 2c66a55 eqblock/allcand, 8b8992d lazy.

## 2026-06-18 part 3: CRITICAL — KM HAS TWO HT ENGINES; the family runs on Ht, not Tableau
run_json (tableau.rs:4482) routes ANY ALC(H) KB (no number/inverse/nominals — 5303
+ whole disjunction family qualify) to **hypertableau::Ht** (engine/src/hypertableau.rs,
2380 lines) whenever KM_HT=1, and the orchestrator ALWAYS sets KM_HT=1 (race.rs:465).
The `Tableau` in tableau.rs is ONLY the out-of-fragment fallback. So 5303 NEVER touches
Tableau. ⇒ This session's KM_HT_DOD + KM_HT_CONTRA additions to tableau.rs::Tableau, AND
the prior KM_HT_EQBLOCK/LAZY/UNSATCACHE/BLOCKSKIP/ALLCAND (also in Tableau), are DEAD
CODE for the family — all those 5303 trials proved nothing (timed out identically because
the flags never executed; stats never printed). LESSON: any HT lever for the family MUST
go in hypertableau.rs::Ht.
Ht ALREADY has decision-on-demand: eval_disj (hypertableau.rs:932-936) = Clash / Unit
(propagate, no branch) / Branch; plus KM_HT_WATCH (incremental unit prop), KM_HT_NEGTRIED
(assert complement of a clashed disjunct = HermiT startNextChoice), KM_HT_EAGER (defer
⊤-disj to unblocked nodes), KM_HT_BLOCK (0=core/1=subset default/2=eq), restarts/VSIDS
(KM_HT_ORD/PICK/RESTART), KM_HT_LEARN. Ht detects a disjunct DEAD iff its complement is
PRESENT (line 924); but a clash clause A⊓B⊑⊥ only raise_clash when BOTH present
(apply_head:667) — Ht NEVER derives ¬A/¬B. So Ht's unit-prop is STARVED of negatives.
⇒ Ported the contrapositive generator into Ht::new (KM_HT_CONTRA, hypertableau.rs):
A⊓B⊑⊥ ⇒ add A→¬B, B→¬A (sound Horn). Feeds negatives to eval_disj. Diagnostic on IBEX
(job 47622423, direct km tableau, KM_HT_STATS visible) tests CONTRA × WATCH/NEGTRIED/EAGER.
Also: Ht default = SUBSET anywhere blocking; documented 5303 incomplete-by-1 = subset
block + TRANSITIVE roles (router must withhold KM_HT from transitive onts), separate from
branching. Konclude divergence (3 pts) traced in docs/konclude-trace-5303.md (showboat,
verify-clean): shared node per concept (not model-size); disjunctions parked never split +
common-disjunct extraction; SAT test only for INSUFFICIENT residue (~5%).

## 2026-06-18 part 4: residue-gate MEASURED — does NOT pay off; lever is bounded per-test, not residue size
Empirical results (CONTRA in the LIVE engine Ht, job 47622423, KM_HT_STATS visible):
contrapositives added=78 (mechanism FIRES) but 5303 still TIMEOUT under CONTRA ×
{WATCH,NEGTRIED,EAGER}; graph ~498 nodes 85% blocked — the structural blow-up the trace
predicted. EAGER made it worse (871 nodes). Per-disjunction levers (DOD/CONTRA/unit-prop)
definitively exhausted IN THE RIGHT ENGINE.
elc residue measurement (KM_ELC_RESIDUE_STATS, new gated diag in elcomplete.rs, job
47622532): INSUFFICIENT residue (concepts touched by a live parked disjunction) =
**100% for EVERY ⊤-disjunction ont**: 5303 426/426, 10702 695/695, 1603 1391/1391, 9540
416/416 — pre AND post common-disjunct hoist (hoist adds subsumptions but resolves ZERO
nodes; ⊤-level disjuncts are Q_ polarity markers domain concepts never derive). CONTROL:
2313 also 100% INSUFFICIENT (1901/1903) yet KM PASSES it fast; 105 (no disj) = 0%.
⇒ DECISIVE: a shared-node residue-GATE routes ~ALL concepts to the tester ⇒ ZERO benefit;
and residue SIZE does not discriminate pass(2313) vs fail(5303) — both 100%. The real and
ONLY remaining lever is Konclude's BOUNDED per-concept SAT over the shared saturation graph
(one node per concept, ∃ reuses filler node), i.e. a from-scratch saturation-reasoner core,
NOT wiring existing pieces, NOT making branches cheaper. Konclude is fast despite ~100%
INSUFFICIENT because each test is O(#concepts), where KM rebuilds a model-size graph per test.
elc repair-cert also FAILS/bails on 5303 (global-model repair explodes; exit 3 → CB → timeout).
VERDICT: 5303-class = from-scratch Konclude core (huge, uncertain, for ~4 onts several with
contested gold) OR bank + redirect. CONTRA/DOD/residue-diag committed gated; default-off.

## 2026-06-18 part 5: full CB+HT ablation + EMELIM completeness fix (5303 no longer incomplete)
Full-corpus KM-only ablation (587 gold, faithful ore_canon via km JSON output +
canonicalize(text,"json") — NOT --lines localname which gave a 56-unsound artifact):
results/benchmarks/2026-06-18-km-cb-ht-ablation.md. base=558/0/0/29. **ht_emelim is the
global winner.** absorb/tabrace now +0 (subsumed by base auto-seqorder+central). CONTRA
neutral (=plain ht, +4). elcport +5 but −2 GIANTS (16744/8737, elc mem race) so ALL<ht_emelim;
a ROUTER beats blanket-on. 
EMELIM completeness FIX (commit 554fc87, cb_to_ht.rs elim_complements): EMELIM dropped the
excluded-middle ⊤⊑A∨B of a complementary pair B≡¬A; each side is only derived VIA that
disjunction, so dropping it silences a consequence keyed on the dropped side (5303 lost
CHSubstructure⊑Hydrocarbon). GUARD: pair unsafe to fold iff a member ∈ body_drives (in a
non-empty-head clause body) AND ∉ head_horn (sole atom of some X⊑B/⊤⊑B head). Unsafe pairs
kept unfolded → sound+complete (slower/timeout, never wrong). Result (re-sweep 47635072):
**ht_emelim 564 clean / 0 unsound / 0 INCOMPLETE / 23 timeout** (+6 vs base; 5303+541 →
honest timeout not incomplete). DEPLOYABLE = base + ht_emelim (monotone-safe, fully
sound+complete) + giant-excluded elcport router → union 567. User HARD REQ: never default to
an incomplete route — met.

## 2026-06-18 part 6: combined router WIRED + made DEFAULT (deployed)
classify() (orchestrate/mod.rs, commit 99a71d8): when elc_portfolio && ht_race, HT races the
INNER (CB-adaptive vs certified-elc) portfolio instead of bare CB → one pass = UNION of both
recovery sets (fixes ALL mutual-exclusion). Giant-exclusion guard (ont >100MB) keeps the 3
giants off the OOM-prone concurrent race. Router sweep 47636078: 565 clean/0 unsound/0 incomplete/
22 t-o = +7 vs base (11460,12141,15491,4604,7246,9024,9635), 0 losses, strict superset of
ht_emelim (+7246). Lands 565 not the 567 union — 15803/6212 (elcport-only) don't survive the
combined race (residual, not regression).
Then FLIPPED DEFAULTS (commit 896e3be, opt-out): elc_portfolio=KM_NO_ELC_PORTFOLIO.is_none(),
ht_race=KM_NO_HT_RACE.is_none() (ht_mode already=fallback default), emelim=KM_NO_HT_EMELIM.is_none()
(cb_to_ht.rs:623). NO-ENV-FLAG confirmation sweep 47636367 = 565/0/0/22 SET-IDENTICAL to explicit
router (+0/-0). km classify ships the +7 router out of the box, sound+complete, monotone-safe.
Build green on IBEX km-rustport, 111 tests. Results: results/benchmarks/2026-06-18-km-cb-ht-ablation.md.
NEW BASELINE = 565 (was 558/564). Build/validate on /ibex/scratch/hohndor/km-rustport sweep/ ONLY.
