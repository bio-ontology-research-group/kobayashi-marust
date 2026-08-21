import ContextCalculus.HypertableauCardinalityProjection
import ContextCalculus.HypertableauConceptRenaming

/-!
# Cardinality semantics under concept renaming

Roles and the object domain remain fixed. Markers and fillers are transported
through the same concept embedding used by source-to-hypertableau projection.
-/

namespace ContextCalculus.Hypertableau

def renameCardinalityDef (f : SourceConcept → TargetConcept)
    (definition : CardinalityDef SourceConcept Role) :
    CardinalityDef TargetConcept Role := {
  marker := f definition.marker
  kind := definition.kind
  bound := definition.bound
  role := definition.role
  filler := f definition.filler
}

def renamePairedCardinality (f : SourceConcept → TargetConcept)
    (pair : PairedCardinality SourceConcept Role) :
    PairedCardinality TargetConcept Role := {
  maximum := renameCardinalityDef f pair.maximum
  minimum := renameCardinalityDef f pair.minimum
  complementary := {
    maximum_kind := pair.complementary.maximum_kind
    minimum_kind := pair.complementary.minimum_kind
    minimum_bound := pair.complementary.minimum_bound
    same_role := pair.complementary.same_role
    same_filler := congrArg f pair.complementary.same_filler
  }
}

theorem cardinalitySuccessor_rename_pullback_iff
    (f : SourceConcept → TargetConcept)
    (J : Interp Domain TargetConcept Role)
    (definition : CardinalityDef SourceConcept Role)
    (source target : Domain) :
    J.cardinalitySuccessor (renameCardinalityDef f definition) source target ↔
      (pullbackConcepts f J).cardinalitySuccessor definition source target := by
  rfl

theorem modelsCardinalityDef_rename_pullback_iff
    (f : SourceConcept → TargetConcept)
    (J : Interp Domain TargetConcept Role)
    (definition : CardinalityDef SourceConcept Role) :
    J.modelsCardinalityDef (renameCardinalityDef f definition) ↔
      (pullbackConcepts f J).modelsCardinalityDef definition := by
  rfl

theorem modelsCardinalityDefExact_rename_pullback_iff
    (f : SourceConcept → TargetConcept)
    (J : Interp Domain TargetConcept Role)
    (definition : CardinalityDef SourceConcept Role) :
    J.modelsCardinalityDefExact (renameCardinalityDef f definition) ↔
      (pullbackConcepts f J).modelsCardinalityDefExact definition := by
  rfl

theorem modelsPairedCardinalityTargets_rename_pullback_iff
    (f : SourceConcept → TargetConcept)
    (J : Interp Domain TargetConcept Role)
    (definitions : List (CardinalityDef SourceConcept Role))
    (pairs : List (PairedCardinality SourceConcept Role)) :
    J.modelsPairedCardinalityTargets
        (definitions.map (renameCardinalityDef f))
        (pairs.map (renamePairedCardinality f)) ↔
      (pullbackConcepts f J).modelsPairedCardinalityTargets definitions pairs := by
  constructor
  · rintro ⟨hdefinitions, hpairs⟩
    constructor
    · intro definition hdefinition
      apply (modelsCardinalityDef_rename_pullback_iff f J definition).1
      apply hdefinitions (renameCardinalityDef f definition)
      exact List.mem_map.mpr ⟨definition, hdefinition, rfl⟩
    · intro pair hpair
      have htarget := hpairs (renamePairedCardinality f pair)
        (List.mem_map.mpr ⟨pair, hpair, rfl⟩)
      exact ⟨
        (modelsCardinalityDefExact_rename_pullback_iff f J pair.maximum).1 htarget.1,
        (modelsCardinalityDefExact_rename_pullback_iff f J pair.minimum).1 htarget.2⟩
  · rintro ⟨hdefinitions, hpairs⟩
    constructor
    · intro targetDefinition htarget
      rcases List.mem_map.mp htarget with ⟨definition, hdefinition, rfl⟩
      exact (modelsCardinalityDef_rename_pullback_iff f J definition).2
        (hdefinitions definition hdefinition)
    · intro targetPair htarget
      rcases List.mem_map.mp htarget with ⟨pair, hpair, rfl⟩
      have hsource := hpairs pair hpair
      exact ⟨
        (modelsCardinalityDefExact_rename_pullback_iff f J pair.maximum).2 hsource.1,
        (modelsCardinalityDefExact_rename_pullback_iff f J pair.minimum).2 hsource.2⟩

theorem renameOntology_pairedCardinality_sat_iff_of_leftInverse
    (f : SourceConcept → TargetConcept)
    (g : TargetConcept → SourceConcept)
    (hleft : ∀ concept, g (f concept) = concept)
    (ontology : List (Clause Variable SourceConcept Role))
    (definitions : List (CardinalityDef SourceConcept Role))
    (pairs : List (PairedCardinality SourceConcept Role)) :
    (∃ I : Interp Domain SourceConcept Role,
      I.models ontology ∧
        I.modelsPairedCardinalityTargets definitions pairs) ↔
    (∃ J : Interp Domain TargetConcept Role,
      J.models (renameOntology f ontology) ∧
        J.modelsPairedCardinalityTargets
          (definitions.map (renameCardinalityDef f))
          (pairs.map (renamePairedCardinality f))) := by
  constructor
  · rintro ⟨I, hontology, hcardinality⟩
    let J := pushforwardConcepts g I
    refine ⟨J,
      (models_rename_pushforward_iff f g hleft I ontology).2 hontology, ?_⟩
    apply (modelsPairedCardinalityTargets_rename_pullback_iff
      f J definitions pairs).2
    simpa [J, pullback_pushforward_eq f g hleft I] using hcardinality
  · rintro ⟨J, hontology, hcardinality⟩
    exact ⟨pullbackConcepts f J,
      (models_rename_pullback_iff f J ontology).1 hontology,
      (modelsPairedCardinalityTargets_rename_pullback_iff
        f J definitions pairs).1 hcardinality⟩

#print axioms modelsCardinalityDef_rename_pullback_iff
#print axioms modelsCardinalityDefExact_rename_pullback_iff
#print axioms modelsPairedCardinalityTargets_rename_pullback_iff
#print axioms renameOntology_pairedCardinality_sat_iff_of_leftInverse

end ContextCalculus.Hypertableau
