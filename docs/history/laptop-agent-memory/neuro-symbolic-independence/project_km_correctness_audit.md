---
name: project_km_correctness_audit
description: "Audit of KM's 10 unsound + 15 incomplete ORE onts: mostly NOT unsound; DataHasValue literal-collapse bug fixed; rest = CB-engine nominal/number incompleteness"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3e94cd1a-f3b7-4c1c-a08d-39c076fa2104
---

Audit of the KM ORE 2015 unsound (10) + incomplete (15) onts (user-requested,
2026-06-09), on the elc-pipeline run. RESULT after DataHasValue fix (re-ran the
29 DataHasValue onts, job 5189): **km ok 550->551, unsound 10->8, agree 525->528,
incomplete 15, 0 regressions**; 13132/9881 now fully AGREE with gold. Net for the
day: ok 544->551 (+7), unsound 10->8. Method: triangulate KM's
extra/missing subsumptions vs Konclude AND HermiT/ELK, and vs each ont's
Konclude-unsat set. Sigs in ~/bench/ore_out{,_kmelc}/*.sig.gz; localname via
ore_canon. Conclusion: KM has essentially NO gratuitous unsoundness.

**Unsound (10) breakdown:**
- ore_ont_13132, 9881 (ALEHOIN(D)): WERE genuinely unsound (125/145 spurious
  subs like Chinese==English). Root cause = DataHasValue normalisation DROPPED
  the literal: `DataHasValue(p v)` -> ∃p.__dt__val with ONE shared __dt__val for
  all values, so `Chinese ≡ ∃langCode."zh"` and `English ≡ ∃langCode."en"`
  collapsed to the same concept. **FIXED**: key the filler by the literal
  (`__dt__val__<v>`), mirroring ObjectHasValue, in BOTH frontends
  (engine/src/frontend/parse.rs `dt_value_concept`, engine/py/frontend.py
  `_dt_value_concept`). The "zh"^^xsd:string literal tokenises to args[1].
  After fix extra drops 125/145 -> 1 (a Description⊑Description localname-collapse
  artifact). compare_classify stays 51/51 (Rust==Python frontend). Commit on
  payg-strategy.
- 15288, 443, 7052 (SHN(D)), 6720 (ALCO), 8941 (SHIF(D)): NOT unsound — 100% of
  KM's "extra" subs involve classes Konclude calls unsatisfiable (39/314/80
  unsat) but KM detects 0. KM UNDER-detects unsatisfiability (CB-engine
  nominal/number/functionality clash incompleteness); the unsat classes' subs
  then leak as "extra". A missing-⊥ incompleteness, not unsound derivation.
- 15516, 2669 (ALCHOIQ(D)): mixed — KM finds 1 extra unsat + extra subs.
- 7901 (SHIN(D)): KM is CORRECT — its 1 extra sub (ChemicalStructure⊑UtilityClass)
  IS derived by ELK (sound EL reasoner); Konclude is the outlier (unsat 2 vs 1).

**Incomplete (15):** all nominal/inverse/number/datatype expressivity (SHOIN(D),
SROIF, ALCRN, ALCOIN, ALCHQ, SHOI). KM missing subs through O/I/N/Q. 7 SHOIN(D)
onts share the identical "Age⊑Container, Period⊑Container" missing=24 pattern
(same ontology family). These are CB-engine completeness gaps.

Takeaway: after the DataHasValue fix, KM's remaining unsound/incomplete flags are
all CB-engine **nominal + number-restriction + inverse** incompleteness
(under-detected unsatisfiability + missed subsumptions) — the hard area the
hypertableau ([[project_km_hybrid_tableau]], [[project_km_nominals_routing]]) is
meant to address. NOT spurious over-derivation. See [[project_km_rust_elc]] for
the coverage side, [[project_km_ore_rerun_cur]] for the gold-disagreement context.
