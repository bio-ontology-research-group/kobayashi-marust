---
name: project_km_unsound_diagnosis
description: "Corrected root-cause diagnosis of KM's 8 ORE \"unsound vs gold\" ontologies (overturns CLAUDE.md's nominal/number theory)"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

The 8 ORE 2015 ontologies flagged "unsound vs Konclude" are NOT all
nominal/number under-detection (as CLAUDE.md's current-state note assumed).
Verified 2026-06-10 against Konclude + HermiT + ELK signatures. Four distinct
causes:

- **ABox-driven inconsistency** (`6720`, `15288`, `443`, `7052`): an individual
  is asserted into two disjoint named classes (witness `6720`:
  `lemon_slice ∈ fruit ⊓ sparqling_wine`, disjoint). Ontology is inconsistent
  (HermiT agrees; Konclude/ELK report all classes unsat). KM missed it because
  the CB engine drops every individual/ABox clause (`reasoner.rs` maps `Ind`/
  `Aux` terms to `None`), so the clash never reaches saturation and KM emitted
  the full taxonomy. **FIXED** by `frontend/abox_consistency.rs` (commit
  `6f2c2f3`) — sound conservative precheck, flag `abox_inconsistent` on the ofn
  meta, `owl_classify` short-circuits.
- **Datatype empty data-range** (`7901`, gold-confirmed real, Konclude=HermiT=2
  unsat): `structureFormat` has two disjoint `DataOneOf` `DataPropertyRange`
  axioms → empty range; `ChemicalStructure ⊑ DataExactCardinality(1 structureFormat)`
  → unsat. KM over-approximates all datatypes as opaque `__dt__*` concepts
  (deliberate soundness-preserving incompleteness; `DataPropertyRange`/
  `FunctionalDataProperty` dropped at `parse.rs:293`). OPEN.
- **ALC `∀`-driven** (`8941`): 58 `ObjectAllValuesFrom`, no disjointness; all
  classes unsat per Konclude. OPEN.
- **Complex-boolean over-derivation** (`15516`, `2669`): KM is *too strong* —
  invents subsumptions + a false unsat (`DBNonKeyAttribute`) on
  `ObjectComplementOf(ObjectSomeValuesFrom(...))` definitions. The only genuinely
  unsound (KM-stronger-than-gold) cases. Engine-level, hardest. OPEN.

After the fix: soundness vs gold = 534 agree / 4 unsound / 17 incomplete / 0
both-disagree (sweep 5329). Coverage unchanged at 555 ok (correctness fix, not
coverage). See [[project_km_aboxcheck_fix]].

**2026-06-11 unified re-diagnosis (sweep 5589 = 552 agree / 6 incomplete / 4
unsound / 0 both-disagree).** The 4 remaining "unsound" onts (15516, 2669, 8941,
13912) all share ONE root cause and ONE caveat:
- ROOT CAUSE: KM UNDER-DETECTS unsatisfiable named classes in ALC / complex-
  boolean ontologies. Konclude reports many unsat (15516/2669: a few via the
  `ObjectComplementOf(ObjectSomeValuesFrom)` defs; 8941: 81; 13912: 33); KM
  detects ~1. KM instead derives a taxonomy among the should-be-unsat classes,
  which the aggregator flags as "extra subsumptions" = unsound. The CB engine
  does not fully propagate the forall/complement clashes (cf. engine.rs note:
  Factor + full nominal rules unimplemented). A real engine completeness gap.
- CAVEAT (gold-suspect): on ALL FOUR, Konclude (gold) says CONSISTENT (1) while
  HermiT says INCONSISTENT (0) -- the references disagree with each other. So
  KM's "unsoundness" here is measured against a contested gold. KM's TRUE
  soundness is better than the 4-unsound figure implies.
The 6 INCOMPLETE onts (KM misses subs): 16461 (1 missing -- a NOMINAL subsumption
`Patient1 ⊑ Systemic_JIA_Patient`, individuals dropped by CB); 12698/2313/4827
(missing `X ⊑ <one superclass>` for many X -- a propagation gap to specific
defined superclasses); 9724 (77731 missing -- systematic); 9944 (772, fly
anatomy). Varied deep propagation/nominal gaps, no single fix.
Neither group moves PASSRATE (all are already `ok`); the 25-ont gap to Konclude
587 is the timeout/memout set -- see [[project_km_disjunction_blowup]].

**2026-06-11 RESOLVED (all 4 "unsound" were GOLD bugs + KM ABox-blindness; KM
was right).** Proved every one genuinely INCONSISTENT via ddmin minimal cases +
HermiT AND Konclude (run directly on the minimal cases: all four report
Thing==Nothing / inconsistent). Two distinct gold-recording bugs:
- 8941, 13912: Konclude emits `EquivalentClasses(Thing Nothing ...)` for an
  inconsistent ontology; the harness `ore_canon.py` mis-canonicalised that into
  "consistent + N unsat classes". FIX: ore_canon detects Thing in the Nothing
  SCC -> inconsistent (empty sig); also json-reasoner `consistent=false` ->
  uniform empty sig.
- 15516, 2669: Konclude FAILS to parse the SWRL `DLSafeRule` ontologies ("All
  parsers failed") yet exits 0 with empty output, recorded as bogus "consistent".
  FIX: ore_runone flags konclude "All parsers failed" stdout as `error`
  (excluded from comparison). Minimal cause is real though: DisjointClasses(
  DBKeyAttribute, DBNonKeyAttribute) + DBNonPrimaryKeyAttribute = union(...) ⊑
  DBKeyAttribute + ClassAssertion(DBNonKeyAttribute, salary) = inconsistent.
KM side: the CB engine drops the ABox, so it missed these. FIX:
`frontend/data_abox.rs` sound datatype-ABox precheck (range-vs-literal-family
clash, functional-data clash, ≤1-driven individual merge + DifferentIndividuals
clash for 13912's symmetric+exact1+dataMax1 chain) + asserted-member-of-unsat
rule (asserted_classes on the ofn meta; owl_classify makes the ontology
inconsistent when an unsat named class has an asserted member). 8941's minimal
witness: `DataPropertyRange(hasTopic xsd:string)` + `..."Tarifvertrag"@de` (a
lang-tagged literal is rdf:PlainLiteral, never in the xsd:string value space).
Minimal cases saved on ws:~/minimize/*.min.owl.

INCOMPLETE fixes (same session): 4827 RECOVERED EXACT (0 missing) via the
complex-domain clausification: `ObjectPropertyDomain(R, ObjectUnionOf(...))` on a
NAMED role was dropped as `complex-domain` Fenced; now `parse.rs` translates a
complex domain/range to `∃R.⊤ ⊑ C` / `⊤ ⊑ ∀R.C` (named-class case stays on the
rbox path = byte-identical).

**2026-06-11 sweep 5754 CONFIRMED the correctness work: 566 ok / 23 timeout / 1
memout; soundness vs gold = 562 agree / 6 incomplete / 0 UNSOUND / 0 genuine
both.** The 4 unsound are gone. The "both=2" in a raw sig diff is 15516/2669 (the
SWRL onts): KM correctly reports inconsistent (`0`), gold says consistent (`1`)
only because Konclude fails to parse the `DLSafeRule` axioms — KM is MORE correct;
exclude them (Konclude provides no valid gold). 6999 newly listed incomplete =
datatype-cardinality unsat (`Distortion_Type_Affine` via DataExactCardinality);
KM over-approximates datatypes (deliberate sound-incompleteness), likely contested.

**Incomplete tail diagnosed via `ddmin` + HermiT-entailment oracle
(ws:~/minimize/ddmin_entail.py, oracle = ont+{C(p),¬D(p)} unsat):**
- **2313 FIXED** (commit 4c4f8cf): root cause = `EquivalentObjectProperties` was
  silently dropped (no parse arm in parse.rs OR rbox.rs rbox_node). 3-axiom core:
  `TO_0000059 ⊑ ∃BFO_0000050.TO_0000056`, `BFO_0000050 ≡ PPIO_0000091`,
  `domain(PPIO_0000091)=PPIO_0000069` ⟹ `TO_0000059 ⊑ PPIO_0000069`. Fix expands
  `R≡..≡Rn` into pairwise both-way inclusions (parse.rs RoleInclusion → normalise
  subrole clause; rbox_node Subrole records). 2313 → exact (88 missing → 0). 57
  ORE onts contain the axiom; sound. Deployed ofn + sweep 5784 to confirm corpus.
- **12698 DEEP** (4-axiom core): `EFO_0000326 ≡ ∃EFO_0000784.(∃BFO_0000050.U17 ⊔
  U17) ⊓ EFO_0000311`, `EFO_0000618 ≡ ∃EFO_0000784.(∃BFO_0000050.U16 ⊔ U16)`,
  `U17 ⊑ ∃BFO_0000050.U16`, `Transitive(BFO_0000050)` ⟹ `EFO_0000326 ⊑
  EFO_0000618`. Needs disjunction-in-existential-filler + transitive-role collapse
  (`∃R.∃R.X⊑∃R.X`) + existential monotonicity (`∃S.C⊑∃S.D` when C⊑D). Has
  ObjectUnionOf → CB path. Hard, same class as the disjunction blowup.
- **9944 MODERATE** (no union; 3 transitive roles, 12 role chains, 2110 equivCls):
  transitive-role / role-chain existential propagation gap (772 FBbt subs). The
  "role-chain propagation volume" residual; possibly EL-tractable.
- **16461** (28-axiom core): `Patient1` has many `∃R.C` superclasses;
  `SubClassOf(IntersectionOf(∃hasDeficiencyOf.Sodium, ∃hasHigh.CRP, …), RHS)` and
  `Systemic_JIA_Patient ≡ ∃hasDisease.Systemic_JIA` ⟹ `Patient1 ⊑
  Systemic_JIA_Patient`. Conjunction-of-existentials on a SubClassOf LHS matching
  a class's existential superclasses. Moderate (EL-ish conjunctive-∃ normalisation).
