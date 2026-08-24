import ContextCalculus.CBRoleChainEncoding

/-! # Concept renaming for the exact CB source language -/

namespace ContextCalculus.CBSourceConceptRenaming

open ContextCalculus Eqv
open ContextCalculus.CBRoleChainEncoding

def mapClause (f : SourceConcept → TargetConcept) :
    OClause SourceConcept Role Individual → OClause TargetConcept Role Individual
  | .gci body head => .gci (body.map f) (head.map f)
  | .exR source role filler => .exR (f source) role (f filler)
  | .allR source role filler => .allR (f source) role (f filler)
  | .exL role filler conclusion => .exL role (f filler) (f conclusion)
  | .subR sub sup => .subR sub sup
  | .inv role inverse => .inv role inverse
  | .func role => .func role
  | .nom concept individual => .nom (f concept) individual
  | .atMost bound role concept => .atMost bound role (f concept)
  | .guardedAtMost source bound role concept =>
      .guardedAtMost (f source) bound role (f concept)
  | .guardedAtLeast source bound role concept =>
      .guardedAtLeast (f source) bound role (f concept)

def mapSource (f : SourceConcept → TargetConcept)
    (source : SourceOntology SourceConcept Role Individual) :
    SourceOntology TargetConcept Role Individual where
  clauses := source.clauses.map (mapClause f)
  chains := source.chains
  roleAxioms := source.roleAxioms

def pullback (f : SourceConcept → TargetConcept)
    (target : Eqv.Interp D TargetConcept Role Individual) :
    Eqv.Interp D SourceConcept Role Individual where
  c concept := target.c (f concept)
  r := target.r
  nm := target.nm

theorem sat_mapClause_iff
    (f : SourceConcept → TargetConcept)
    (target : Eqv.Interp D TargetConcept Role Individual)
    (clause : OClause SourceConcept Role Individual) :
    Eqv.satO target (mapClause f clause) ↔ Eqv.satO (pullback f target) clause := by
  cases clause with
  | gci body head =>
      constructor
      · intro h element hbody
        rcases h element (by
          intro targetConcept hmem
          rcases List.mem_map.mp hmem with ⟨concept, hconcept, rfl⟩
          exact hbody concept hconcept) with ⟨targetConcept, hmem, hholds⟩
        rcases List.mem_map.mp hmem with ⟨concept, hconcept, rfl⟩
        exact ⟨concept, hconcept, hholds⟩
      · intro h element hbody
        rcases h element (by
          intro concept hmem
          exact hbody (f concept) (List.mem_map.mpr ⟨concept, hmem, rfl⟩)) with
          ⟨concept, hmem, hholds⟩
        exact ⟨f concept, List.mem_map.mpr ⟨concept, hmem, rfl⟩, hholds⟩
  | exR source role filler => rfl
  | allR source role filler => rfl
  | exL role filler conclusion => rfl
  | subR sub sup => rfl
  | inv role inverse => rfl
  | func role => rfl
  | nom concept individual => rfl
  | atMost bound role concept => rfl
  | guardedAtMost source bound role concept => rfl
  | guardedAtLeast source bound role concept => rfl

theorem models_mapSource_iff
    (f : SourceConcept → TargetConcept)
    (target : Eqv.Interp D TargetConcept Role Individual)
    (source : SourceOntology SourceConcept Role Individual) :
    CBRoleChainEncoding.models target (mapSource f source) ↔
      CBRoleChainEncoding.models (pullback f target) source := by
  constructor
  · rintro ⟨hclauses, hchains, hroleAxioms⟩
    constructor
    · intro clause hclause
      exact (sat_mapClause_iff f target clause).1
        (hclauses (mapClause f clause) (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
    · constructor
      · simpa [mapSource, pullback] using hchains
      · simpa [mapSource, pullback] using hroleAxioms
  · rintro ⟨hclauses, hchains, hroleAxioms⟩
    constructor
    · intro targetClause htarget
      rcases List.mem_map.mp htarget with ⟨clause, hclause, rfl⟩
      exact (sat_mapClause_iff f target clause).2 (hclauses clause hclause)
    · constructor
      · simpa [mapSource, pullback] using hchains
      · simpa [mapSource, pullback] using hroleAxioms

#print axioms sat_mapClause_iff
#print axioms models_mapSource_iff

end ContextCalculus.CBSourceConceptRenaming
