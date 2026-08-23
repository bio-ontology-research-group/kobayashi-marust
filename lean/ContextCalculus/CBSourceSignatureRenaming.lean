import ContextCalculus.CBRoleChainEncoding

/-! # Concept and role renaming for the exact CB source language -/

namespace ContextCalculus.CBSourceSignatureRenaming

open ContextCalculus Eqv
open ContextCalculus.CBRoleChainEncoding

def mapClause (conceptMap : SourceConcept → TargetConcept)
    (roleMap : SourceRole → TargetRole) :
    OClause SourceConcept SourceRole Individual →
      OClause TargetConcept TargetRole Individual
  | .gci body head => .gci (body.map conceptMap) (head.map conceptMap)
  | .exR source role filler =>
      .exR (conceptMap source) (roleMap role) (conceptMap filler)
  | .allR source role filler =>
      .allR (conceptMap source) (roleMap role) (conceptMap filler)
  | .exL role filler conclusion =>
      .exL (roleMap role) (conceptMap filler) (conceptMap conclusion)
  | .subR sub sup => .subR (roleMap sub) (roleMap sup)
  | .inv role inverse => .inv (roleMap role) (roleMap inverse)
  | .func role => .func (roleMap role)
  | .nom concept individual => .nom (conceptMap concept) individual
  | .atMost bound role concept =>
      .atMost bound (roleMap role) (conceptMap concept)

def mapChain (roleMap : SourceRole → TargetRole)
    (chain : RoleChain SourceRole) : RoleChain TargetRole where
  body := chain.body.map roleMap
  sup := roleMap chain.sup

def mapSource (conceptMap : SourceConcept → TargetConcept)
    (roleMap : SourceRole → TargetRole)
    (source : SourceOntology SourceConcept SourceRole Individual) :
    SourceOntology TargetConcept TargetRole Individual where
  clauses := source.clauses.map (mapClause conceptMap roleMap)
  chains := source.chains.map (mapChain roleMap)

def pullback (conceptMap : SourceConcept → TargetConcept)
    (roleMap : SourceRole → TargetRole)
    (target : Eqv.Interp D TargetConcept TargetRole Individual) :
    Eqv.Interp D SourceConcept SourceRole Individual where
  c concept := target.c (conceptMap concept)
  r role := target.r (roleMap role)
  nm := target.nm

theorem sat_mapClause_iff
    (conceptMap : SourceConcept → TargetConcept)
    (roleMap : SourceRole → TargetRole)
    (target : Eqv.Interp D TargetConcept TargetRole Individual)
    (clause : OClause SourceConcept SourceRole Individual) :
    Eqv.satO target (mapClause conceptMap roleMap clause) ↔
      Eqv.satO (pullback conceptMap roleMap target) clause := by
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
          exact hbody (conceptMap concept)
            (List.mem_map.mpr ⟨concept, hmem, rfl⟩)) with
          ⟨concept, hmem, hholds⟩
        exact ⟨conceptMap concept, List.mem_map.mpr ⟨concept, hmem, rfl⟩,
          hholds⟩
  | exR source role filler => rfl
  | allR source role filler => rfl
  | exL role filler conclusion => rfl
  | subR sub sup => rfl
  | inv role inverse => rfl
  | func role => rfl
  | nom concept individual => rfl
  | atMost bound role concept => rfl

theorem sat_mapChain_iff
    (roleMap : SourceRole → TargetRole)
    (target : TargetRole → D → D → Prop)
    (chain : RoleChain SourceRole) :
    satChain target (mapChain roleMap chain) ↔
      satChain (fun role => target (roleMap role)) chain := by
  constructor
  · intro h values hedges
    let castIndex : Fin (mapChain roleMap chain).body.length →
        Fin chain.body.length :=
      Fin.cast (by simp [mapChain])
    let castValue : Fin ((mapChain roleMap chain).body.length + 1) →
        Fin (chain.body.length + 1) :=
      Fin.cast (by simp [mapChain])
    have hmapped := h (fun index => values (castValue index)) (by
      intro index
      simpa [castIndex, castValue, mapChain] using hedges (castIndex index))
    simpa [castValue, mapChain] using hmapped
  · intro h values hedges
    let castIndex : Fin chain.body.length →
        Fin (mapChain roleMap chain).body.length :=
      Fin.cast (by simp [mapChain])
    let castValue : Fin (chain.body.length + 1) →
        Fin ((mapChain roleMap chain).body.length + 1) :=
      Fin.cast (by simp [mapChain])
    have hsource := h (fun index => values (castValue index)) (by
      intro index
      simpa [castIndex, castValue, mapChain] using hedges (castIndex index))
    simpa [castValue, mapChain] using hsource

theorem models_mapSource_iff
    (conceptMap : SourceConcept → TargetConcept)
    (roleMap : SourceRole → TargetRole)
    (target : Eqv.Interp D TargetConcept TargetRole Individual)
    (source : SourceOntology SourceConcept SourceRole Individual) :
    CBRoleChainEncoding.models target
        (mapSource conceptMap roleMap source) ↔
      CBRoleChainEncoding.models (pullback conceptMap roleMap target) source := by
  constructor
  · rintro ⟨hclauses, hchains⟩
    constructor
    · intro clause hclause
      exact (sat_mapClause_iff conceptMap roleMap target clause).1
        (hclauses (mapClause conceptMap roleMap clause)
          (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
    · intro chain hchain
      exact (sat_mapChain_iff roleMap target.r chain).1
        (hchains (mapChain roleMap chain)
          (List.mem_map.mpr ⟨chain, hchain, rfl⟩))
  · rintro ⟨hclauses, hchains⟩
    constructor
    · intro targetClause htarget
      rcases List.mem_map.mp htarget with ⟨clause, hclause, rfl⟩
      exact (sat_mapClause_iff conceptMap roleMap target clause).2
        (hclauses clause hclause)
    · intro targetChain htarget
      rcases List.mem_map.mp htarget with ⟨chain, hchain, rfl⟩
      exact (sat_mapChain_iff roleMap target.r chain).2
        (hchains chain hchain)

#print axioms sat_mapClause_iff
#print axioms sat_mapChain_iff
#print axioms models_mapSource_iff

end ContextCalculus.CBSourceSignatureRenaming
