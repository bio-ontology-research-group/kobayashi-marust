---
name: project_km_5303_diagnosis
description: "5303 KM_HT incomplete-by-1 is disjunction-family + subset-blocking, NOT a transitivity fix"
metadata:
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-16 (user: "fix 5303 gap first" so subset blocking is complete on
transitive onts). Deep diagnosis on IBEX of the ONE missing subsumption when
KM_HT routes 5303: **CarbonHydrogenSubstructure ⊑ Hydrocarbon** (km=237, gold=238,
0 unsound). The "transitivity / concept-id fragmentation" framing from
[[project_km_hermit_trace]] is WRONG — disproven step by step:

1. **No concept fragmentation.** Earlier "4 ids for CarbonHydrogen" was a
   diag3.py SUBSTRING artifact (matched CarbonHydrogenSubstructure +
   __trans__*__CarbonHydrogenSubstructure). Each named class has exactly 1
   internal id.
2. **5303 is SH** (4 transitive roles hasPart/hasProperPart/partOf/properPartOf +
   role hierarchy hasProperPart⊑hasPart, properPartOf⊑partOf, etc.; NO inverse,
   NO number, NO chains, NO nominals).
3. **Sub-role transitivity propagation does NOT fix it.** moose's
   `transitivity_clauses` (engine/py/preprocess.py) seeds/propagates the
   __trans__ reachability concept ONLY along role R itself. I added a GENERAL
   sub-role extension (seed+propagate P along every S ⊑* R from the role
   hierarchy; sound because S⇒R and R transitive collapses the path) — gated
   `KM_HT_NO_SUBROLE_TRANS`, saved IBEX `preprocess.py.subrole-new` + laptop
   `/tmp/preprocess.py`. Clause count 816→906 (code fires) but 5303 STILL
   misses the same 1. Role-hierarchy edges S(x,y)→R(x,y) already materialise in
   the TInput (12 of them), so the hasPart-propagation already walks sub-role
   edges. Sub-role ext is a legit general improvement but inert here; left gated.
4. **The inference needs roles+disjunction, not Horn.** Forward Horn-concept
   closure from {CHSubstructure} = 15 concepts, does NOT reach Hydrocarbon.
   Hydrocarbon ← {Q_24=PhosphorusAtom∧OxygenAtom, AromaticHydrocarbon,
   AliphaticChain, CyclicAliphatic}. 5303 has 21+ disjunctive GCIs (e.g.
   ⊤→DNA∨Q_38; Q_61→HydrogenAtom∨CarbonAtom∨…). It IS the live ∀+⊔
   disjunction family [[project_km_disjunction_split]].
5. **CB engine OOMs** on 5303 (rc=-9, 15s @20G) — can't cross-check derivability.
   HermiT derives it gold-clean, so it IS entailed.

**ROOT CAUSE: subset (label-⊆) blocking is INCOMPLETE for ALC with disjunctions.**
A subset-blocked node can be under-labeled relative to what a disjunction forces,
so CHSubstructure's model root label misses Hydrocarbon → classify's
possible-subsumer pruning (hypertableau.rs:1667-1751, uses A-model root label)
never tests it → incomplete. Equality blocking (KM_HT_BLOCK=2) is complete but
does NOT terminate on 5303 (disjunction explosion). So 5303 = the project's
hardest residual (disjunction family), surfacing in the HT port as 1 missed
subsumption instead of a timeout. There is NO localized transitivity fix.

**Consequence for deployment:** "make subset blocking complete on transitive
onts" = solve the disjunction family OR add a completeness certificate. Horn-only
routing rule is DEAD: disjcheck job 47565712 shows ALL recovered onts have
disjunctions too (4604=26, 12141=31, 15491=10 disjunctive GCIs; 5303=21) — no
cheap structural rule separates complete from incomplete. Probes on IBEX
km-htport: probe5303{,b,c,d,e}.py, trace_sub.py, cone.py, fwd.py, run_cb.py,
probe_miss.py.

**2026-06-16 OVERTURN — it is NOT a blocking issue, it is a CORE completeness
bug.** User chose "1 then 3" (certificate then disjunction family). eqcert2 job
47565817 ran the 9 small NON-TRANSITIVE ALCH sweep-incomplete onts under BOTH
subset (KM_HT_BLOCK=1) and equality (KM_HT_BLOCK=2, the COMPLETE reference)
blocking: **byte-identical incomplete counts** (16461=1, 13141=2, 14499=2,
6433=4, 14312=11, 8864=21, 11577=21, 12009=26). So eq-block does NOT recover them
— the gap is independent of blocking mode, on plain non-transitive ALC(H). The
"certificate = run eq-block" idea is DEAD. Next decisive split (naive job
47565897): KM_HT_NAIVE=1 (all-pairs, no model-pruning/told) vs default pruned.
If naive recovers → the model-based possible-subsumer pruning (classify Phase 1
root_pos_label, hypertableau.rs:1666-1760) is the bug; if naive ALSO misses →
consistent() wrongly returns SAT for an unsat A⊓¬B (core disjunction-search or
missing-rule incompleteness). THE REAL TARGET is this core HT completeness bug,
not blocking/transitivity.

**2026-06-16 RESOLVED chain (jobs 47565897 naive + manual ofn tests):**
- NAIVE all-pairs == pruned (16461=1, 11577=21, 12009=26) → NOT the pruning.
- Minimal hand-built 3-concept Horn chain (human→mammal→vertebrate) WORKS in
  tableau_cli → basic propagation fine.
- The "incompleteness" is partly a FRONTEND-MISMATCH artifact: KM_HT experiments
  used the PYTHON moose frontend (emit2.py → frontend.ofn_to_clauses) which
  DISAMBIGUATES colliding localnames (semdis/vertebrate vs semdis/umls#vertebrate
  → distinct ids, sound per ore_ont_3978 note), while PRODUCTION + gold use the
  RUST `ofn` frontend which COLLAPSES localnames. Driving KM_HT from `ofn`
  (clauses + iri_map canon, ofn_ht2.py) made **16461 GOLD-CLEAN** (was incomplete
  1). So the ht-port must be driven by `ofn`, not emit2.py, to be evaluated
  fairly. KEY LESSON: emit2.py/frontend.py is the WRONG frontend for KM_HT eval.
- BUT 11577(21)/12009(26)/8864/6433(4) STILL incomplete even via `ofn`. Could
  not settle whether the production CB engine gets them on identical `ofn`
  clauses (raw `kobayashi-marust` pipe returned km=0 — needs owl_classify's
  named/side-data invocation, not a bare {clauses} pipe). UNRESOLVED: real HT
  reasoner gap vs gold/corpus quirk. NOTE 6433 missing = Q_Fever⊑{AGTOP,
  Bacterioses,Zoonoses,...} (multi-parent disease taxonomy); 11577 =
  behavior⊑event etc.
**2026-06-16 ofn-driven KM_HT built + sweeping (user chose this).** Runner
`ht_ofn_runone.py` (IBEX km-htport): ofn → cb_to_ht(clauses,[]) → tableau_cli
→ iri_map+localname canon → gold. Route guard = LOSSLESS conversion (dropped==0,
fenced==[]) AND no inverse roles; number restrictions (ALCQ) ARE routed (cb_to_ht
encodes them). Sweep array `sweep_ofn.sbatch` (job 47566667, 40 tasks over
cmp_onts.txt=584). FRONTEND IS A TRADEOFF, not a clean win: ofn vs Python(moose):
16461 incomplete→GOLD_CLEAN (number ont, artifact fixed) ✓; 15491 clean both;
but 12141 GOLD_CLEAN(8.4s)→TIMEOUT and 5303 incomplete→TIMEOUT (ofn clausifies
HARDER for the HT search — regression); 11577(21)/6433(4)/12009(26) STILL
incomplete via BOTH frontends → these are a real HT-vs-CB gap or gold quirk, NOT
frontend. Partial sweep 156/584: 144 GOLD_CLEAN, 9 incomplete, 3 DIFF_consistency,
0 unsound. Full aggregate pending.

**SWEEP 47566667 ~complete (529/584 routable):** GOLD_CLEAN 399, timeout 86,
INCOMPLETE 36, DIFF_consistency 5 (443/15288/6720/8941/7052), UNSOUND 3 — but
the 3 "unsound" (8135/5940 _hasValue datatype surrogates; 12831 slash-localname
"columnar/cuboidal_epithelial_cell") are CANON ARTIFACTS of my runner's loc()
(splits on '/', and _hasValue surrogates leak in) — VERIFIED: gold CONTAINS
amelocyte→columnar/cuboidal_epithelial_cell, the exact pair flagged unsound. So
KM_HT stays SOUND. Several huge "incompletes" (8982=207408, repeated 6248s) are
the same naming-mismatch noise. THE TWO REAL SIGNALS: (1) 86 TIMEOUTS — ofn
clausifies HARDER for the HT search than moose (12141 clean→timeout regression);
(2) residual incomplete tail. NET: ofn-driven KM_HT is sound but NOT a win over
production CB (564 ok) — too many timeouts. To get TRUE numbers need the
production canon (ore_canon.localname, not loc(); filter _hasValue surrogates).
Path to value = option 3 (disjunction/search convergence) to cut the 86 timeouts.

**2026-06-17 OPTION 3 NEGATIVE RESULT (grid job 47569737).** User chose option 3
(attack HT timeouts). The ht-port ALREADY HAS full CDCL machinery (VSIDS activity,
Luby restarts KM_HT_RESTART, 2-watched conflict-clause learning KM_HT_LEARN,
dep-directed backjump) — all built (commits INCR1-7), gated OFF. Tested 9 family
onts (12653/5303/15672/11016/541/9540/10702/12141/1603) × 4 configs {base,
learn+restart, ofn-absorb, learn+restart+absorb}, parallel array, 180s each:
**ALL 36 TIMEOUT.** Learning+restarts = no effect; KM_ABSORB = no effect;
combined = no effect. The existing search machinery is INEFFECTIVE on the family
(confirms HermiT-trace 1000x gap + [[project_km_family_diagnosis]] "all shortcuts
closed" + [[project_km_threads_vs_algo]] Konclude 0.16s vs KM timeout). These
same onts also defeat the KM_TAB caching tableau and the CB engine. CONCLUSION:
KM_HT cannot be made a net coverage win with ANY available lever — it's sound,
recovers a couple onts (15491, 16461 via ofn) but CANNOT crack the family
timeouts (which ARE the real coverage gap), and on the ofn frontend even
regresses (12141 clean→timeout). The ONLY remaining path is a MAJOR HermiT/
Konclude-grade rebuild (proper absorption + model-merging/QuasiOrder + their
specific pruning) — large, uncertain, coverage-only. KM_HT line is closed for
cheap/medium wins. ht-port stays gated research (local-only branch, not pushed).

- NEXT (needs user OK, substantial): build a proper `ofn`-driven KM_HT pipeline
  (ofn clauses+iri_map → cb_to_ht → tableau_cli → iri_map canon) and re-run the
  full routed sweep to get the TRUE KM_HT completeness, then compare ofn+CB vs
  ofn+HT on the residual onts via owl_classify to isolate any real HT gap.
