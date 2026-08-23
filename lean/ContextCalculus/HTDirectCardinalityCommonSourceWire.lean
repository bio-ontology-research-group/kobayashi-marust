import ContextCalculus.HTDirectCommonSourceWire
import ContextCalculus.HTCardinalityCheckerTermEmbedding
import ContextCalculus.HypertableauDirectCardinalityProjectionWire

/-!
# Direct HT cardinality sources in the common routing language

This module binds the checked finite direct-cardinality projection to the exact
proper-term clauses reconstructed by `HTCardinalityCheckerTermEmbedding`.
The first layer proves that finite concept and role identifiers map to natural
identifiers without changing any projected cardinality model.
-/

namespace ContextCalculus.HTDirectCardinalityCommonSourceWire

open ContextCalculus
open ContextCalculus.CheckerTerm
open ContextCalculus.Hypertableau
open ContextCalculus.HTDirectCommonSourceWire
open ContextCalculus.HTCardinalityCheckerTermEmbedding
open Lean

def mapCardinalityDef
    (definition : CardinalityDef (Fin concepts) (Fin roles)) :
    CardinalityDef Nat Nat where
  marker := definition.marker.val
  kind := definition.kind
  bound := definition.bound
  role := definition.role.val
  filler := definition.filler.val

def mapPairedCardinality
    (pair : PairedCardinality (Fin concepts) (Fin roles)) :
    PairedCardinality Nat Nat where
  maximum := mapCardinalityDef pair.maximum
  minimum := mapCardinalityDef pair.minimum
  complementary := {
    maximum_kind := pair.complementary.maximum_kind
    minimum_kind := pair.complementary.minimum_kind
    minimum_bound := pair.complementary.minimum_bound
    same_role := congrArg Fin.val pair.complementary.same_role
    same_filler := congrArg Fin.val pair.complementary.same_filler
  }

@[simp] theorem cardinalitySuccessor_map_natInterp [Nonempty Domain]
    (I : Interp Domain (Fin concepts) (Fin roles))
    (definition : CardinalityDef (Fin concepts) (Fin roles))
    (source target : Domain) :
    (natInterp I).cardinalitySuccessor (mapCardinalityDef definition)
        source target ↔
      I.cardinalitySuccessor definition source target := by
  simp [Interp.cardinalitySuccessor, mapCardinalityDef, natInterp]

@[simp] theorem modelsCardinalityDef_map_natInterp [Nonempty Domain]
    (I : Interp Domain (Fin concepts) (Fin roles))
    (definition : CardinalityDef (Fin concepts) (Fin roles)) :
    (natInterp I).modelsCardinalityDef (mapCardinalityDef definition) ↔
      I.modelsCardinalityDef definition := by
  simp only [Interp.modelsCardinalityDef]
  constructor <;> intro hmodels source hmarker
  · have hresult := hmodels source (by
      simpa [mapCardinalityDef, natInterp] using hmarker)
    have hsuccessor :
        (natInterp I).cardinalitySuccessor (mapCardinalityDef definition) source =
          I.cardinalitySuccessor definition source := by
      funext target
      apply propext
      exact cardinalitySuccessor_map_natInterp I definition source target
    rw [hsuccessor] at hresult
    cases hkind : definition.kind <;>
      simpa [mapCardinalityDef, hkind] using hresult
  · have hresult := hmodels source (by
      simpa [mapCardinalityDef, natInterp] using hmarker)
    have hsuccessor :
        (natInterp I).cardinalitySuccessor (mapCardinalityDef definition) source =
          I.cardinalitySuccessor definition source := by
      funext target
      apply propext
      exact cardinalitySuccessor_map_natInterp I definition source target
    cases hkind : definition.kind with
    | minimum =>
        simp only [mapCardinalityDef, hkind]
        change HasAtLeast definition.bound
          ((natInterp I).cardinalitySuccessor (mapCardinalityDef definition) source)
        rw [hsuccessor]
        simpa [hkind] using hresult
    | maximum =>
        simp only [mapCardinalityDef, hkind]
        change HasAtMost definition.bound
          ((natInterp I).cardinalitySuccessor (mapCardinalityDef definition) source)
        rw [hsuccessor]
        simpa [hkind] using hresult

@[simp] theorem modelsCardinalityDef_map_finInterp [Nonempty Domain]
    (I : Interp Domain Nat Nat)
    (definition : CardinalityDef (Fin concepts) (Fin roles)) :
    (finInterp I).modelsCardinalityDef definition ↔
      I.modelsCardinalityDef (mapCardinalityDef definition) := by
  simp only [Interp.modelsCardinalityDef]
  constructor <;> intro hmodels source hmarker
  · have hresult := hmodels source hmarker
    cases hkind : definition.kind <;>
      simpa [mapCardinalityDef, hkind, Interp.cardinalitySuccessor, finInterp]
        using hresult
  · have hresult := hmodels source hmarker
    cases hkind : definition.kind <;>
      simpa [mapCardinalityDef, hkind, Interp.cardinalitySuccessor, finInterp]
        using hresult

theorem modelsProjectedDef_map_natInterp [Nonempty Domain]
    (I : Interp Domain (Fin concepts) (Fin roles))
    (definition : CardinalityDef (Fin concepts) (Fin roles)) :
    (natInterp I).modelsProjectedCardinalityDef (mapCardinalityDef definition) ↔
      I.modelsProjectedCardinalityDef definition := by
  rw [modelsProjectedCardinalityDef_iff, modelsProjectedCardinalityDef_iff,
    modelsCardinalityDef_map_natInterp]

theorem modelsProjectedDef_map_finInterp [Nonempty Domain]
    (I : Interp Domain Nat Nat)
    (definition : CardinalityDef (Fin concepts) (Fin roles)) :
    (finInterp I).modelsProjectedCardinalityDef definition ↔
      I.modelsProjectedCardinalityDef (mapCardinalityDef definition) := by
  rw [modelsProjectedCardinalityDef_iff, modelsProjectedCardinalityDef_iff,
    modelsCardinalityDef_map_finInterp]

theorem modelsSplit_map_natInterp [Nonempty Domain]
    (I : Interp Domain (Fin concepts) (Fin roles))
    (pair : PairedCardinality (Fin concepts) (Fin roles)) :
    (natInterp I).models
        (cardinalitySplitTheory (mapPairedCardinality pair).maximum
          (mapPairedCardinality pair).minimum) ↔
      I.models (cardinalitySplitTheory pair.maximum pair.minimum) := by
  rw [models_cardinalitySplitTheory_iff, models_cardinalitySplitTheory_iff]
  simp [Interp.modelsCardinalitySplit, mapPairedCardinality,
    mapCardinalityDef, natInterp]

theorem modelsSplit_map_finInterp [Nonempty Domain]
    (I : Interp Domain Nat Nat)
    (pair : PairedCardinality (Fin concepts) (Fin roles)) :
    (finInterp I).models (cardinalitySplitTheory pair.maximum pair.minimum) ↔
      I.models (cardinalitySplitTheory (mapPairedCardinality pair).maximum
        (mapPairedCardinality pair).minimum) := by
  rw [models_cardinalitySplitTheory_iff, models_cardinalitySplitTheory_iff]
  rfl

theorem modelsProjectedDefs_map_natInterp [Nonempty Domain]
    (I : Interp Domain (Fin concepts) (Fin roles))
    (definitions : List (CardinalityDef (Fin concepts) (Fin roles)))
    (pairs : List (PairedCardinality (Fin concepts) (Fin roles))) :
    (natInterp I).modelsProjectedCardinalityDefs
        (definitions.map mapCardinalityDef) (pairs.map mapPairedCardinality) ↔
      I.modelsProjectedCardinalityDefs definitions pairs := by
  constructor
  · rintro ⟨hdefinitions, hpairs⟩
    constructor
    · intro definition hdefinition
      exact (modelsProjectedDef_map_natInterp I definition).1
        (hdefinitions (mapCardinalityDef definition)
          (List.mem_map.mpr ⟨definition, hdefinition, rfl⟩))
    · intro pair hpair
      exact (modelsSplit_map_natInterp I pair).1
        (hpairs (mapPairedCardinality pair)
          (List.mem_map.mpr ⟨pair, hpair, rfl⟩))
  · rintro ⟨hdefinitions, hpairs⟩
    constructor
    · intro definition hdefinition
      rcases List.mem_map.mp hdefinition with ⟨source, hsource, rfl⟩
      exact (modelsProjectedDef_map_natInterp I source).2
        (hdefinitions source hsource)
    · intro pair hpair
      rcases List.mem_map.mp hpair with ⟨source, hsource, rfl⟩
      exact (modelsSplit_map_natInterp I source).2 (hpairs source hsource)

theorem modelsProjectedDefs_map_finInterp [Nonempty Domain]
    (I : Interp Domain Nat Nat)
    (definitions : List (CardinalityDef (Fin concepts) (Fin roles)))
    (pairs : List (PairedCardinality (Fin concepts) (Fin roles))) :
    (finInterp I).modelsProjectedCardinalityDefs definitions pairs ↔
      I.modelsProjectedCardinalityDefs
        (definitions.map mapCardinalityDef) (pairs.map mapPairedCardinality) := by
  constructor
  · rintro ⟨hdefinitions, hpairs⟩
    constructor
    · intro definition hdefinition
      rcases List.mem_map.mp hdefinition with ⟨source, hsource, rfl⟩
      exact (modelsProjectedDef_map_finInterp I source).1
        (hdefinitions source hsource)
    · intro pair hpair
      rcases List.mem_map.mp hpair with ⟨source, hsource, rfl⟩
      exact (modelsSplit_map_finInterp I source).1 (hpairs source hsource)
  · rintro ⟨hdefinitions, hpairs⟩
    constructor
    · intro definition hdefinition
      exact (modelsProjectedDef_map_finInterp I definition).2
        (hdefinitions (mapCardinalityDef definition)
          (List.mem_map.mpr ⟨definition, hdefinition, rfl⟩))
    · intro pair hpair
      exact (modelsSplit_map_finInterp I pair).2
        (hpairs (mapPairedCardinality pair)
          (List.mem_map.mpr ⟨pair, hpair, rfl⟩))

#print axioms modelsProjectedDefs_map_natInterp
#print axioms modelsProjectedDefs_map_finInterp

end ContextCalculus.HTDirectCardinalityCommonSourceWire
