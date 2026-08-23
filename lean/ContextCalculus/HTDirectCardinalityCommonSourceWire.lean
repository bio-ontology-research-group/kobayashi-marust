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

structure WireDirectCardinalityCommonSource where
  version : Nat
  projection : WireDirectCardinalityProjection
deriving FromJson, ToJson, Repr

structure DecodedDirectCardinalityCommonSource where
  projection : DecodedDirectCardinalityProjection
  direct : ∀ clause ∈ projection.source, clauseNoExistentials clause = true

def WireDirectCardinalityCommonSource.decode
    (wire : WireDirectCardinalityCommonSource) :
    Except String DecodedDirectCardinalityCommonSource := do
  if wire.version != 1 then
    throw s!"unsupported direct-cardinality common-source version {wire.version}"
  let projection ← wire.projection.decode
  if hdirect : ∀ clause ∈ projection.source,
      clauseNoExistentials clause = true then
    return { projection, direct := hdirect }
  else
    throw "direct-cardinality residual contains an existential atom"

def WireDirectCardinalityCommonSource.check
    (wire : WireDirectCardinalityCommonSource) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedDirectCardinalityCommonSource.natDirect
    (decoded : DecodedDirectCardinalityCommonSource) :=
  mapOntology decoded.projection.source

def DecodedDirectCardinalityCommonSource.natDefinitions
    (decoded : DecodedDirectCardinalityCommonSource) :=
  decoded.projection.definitions.map mapCardinalityDef

def DecodedDirectCardinalityCommonSource.natPairs
    (decoded : DecodedDirectCardinalityCommonSource) :=
  decoded.projection.semanticPairs.map mapPairedCardinality

def DecodedDirectCardinalityCommonSource.commonOntology
    (decoded : DecodedDirectCardinalityCommonSource) : List FCL :=
  decoded.natDirect.map HTCheckerTermEmbedding.encodeClause ++
    cardinalityClauses decoded.natDefinitions decoded.natPairs

theorem DecodedDirectCardinalityCommonSource.directOntology
    (decoded : DecodedDirectCardinalityCommonSource) :
    HTCheckerTermEmbedding.DirectOntology decoded.natDirect := by
  intro clause hclause
  rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
  exact direct_mapClause source (decoded.direct source hsource)

def DecodedDirectCardinalityCommonSource.CommonEntails
    (decoded : DecodedDirectCardinalityCommonSource)
    (sub sup : Fin decoded.projection.concepts.length) : Prop :=
  ∀ (Domain : Type) (model : TModel Domain),
    (∀ clause ∈ decoded.commonOntology, valid model clause) →
      ∀ value, model.conc sub.val value → model.conc sup.val value

def DecodedDirectCardinalityCommonSource.FiniteSourceEntails
    (decoded : DecodedDirectCardinalityCommonSource)
    (sub sup : Fin decoded.projection.concepts.length) : Prop :=
  ∀ (Domain : Type)
    (I : Interp Domain (Fin decoded.projection.concepts.length)
      (Fin decoded.projection.roles.length)),
    (I.models decoded.projection.source ∧
      I.modelsProjectedCardinalityDefs decoded.projection.definitions
        decoded.projection.semanticPairs) →
      ∀ value, I.concept sub value → I.concept sup value

def DecodedDirectCardinalityCommonSource.TargetEntails
    (decoded : DecodedDirectCardinalityCommonSource)
    (sub sup : Fin decoded.projection.concepts.length) : Prop :=
  ∀ (Domain : Type)
    (I : Interp Domain (Fin decoded.projection.concepts.length)
      (Fin decoded.projection.roles.length)),
    (I.models decoded.projection.target ∧
      I.modelsProjectedCardinalityTargets decoded.projection.definitions
        decoded.projection.semanticPairs) →
      ∀ value, I.concept sub value → I.concept sup value

theorem DecodedDirectCardinalityCommonSource.finiteSource_entails_iff_target
    (decoded : DecodedDirectCardinalityCommonSource)
    (sub sup : Fin decoded.projection.concepts.length) :
    decoded.FiniteSourceEntails sub sup ↔ decoded.TargetEntails sub sup := by
  constructor
  · intro hsource Domain I htarget
    exact hsource Domain I
      ((decoded.projection.models_source_iff_target I).2 htarget)
  · intro htarget Domain I hsource
    exact htarget Domain I
      ((decoded.projection.models_source_iff_target I).1 hsource)

theorem DecodedDirectCardinalityCommonSource.common_entails_iff_finiteSource
    (decoded : DecodedDirectCardinalityCommonSource)
    (sub sup : Fin decoded.projection.concepts.length) :
    decoded.CommonEntails sub sup ↔ decoded.FiniteSourceEntails sub sup := by
  constructor
  · intro hcommon Domain I hsource value hsub
    letI : Nonempty Domain := ⟨value⟩
    have hcardNat : (natInterp I).modelsProjectedCardinalityDefs
        decoded.natDefinitions decoded.natPairs :=
      (modelsProjectedDefs_map_natInterp I decoded.projection.definitions
        decoded.projection.semanticPairs).2 hsource.2
    rcases projected_implies_exists_cardinalityClauses_model (natInterp I) value
        decoded.natDefinitions decoded.natPairs hcardNat with
      ⟨model, hinterp, hcardCommon⟩
    have hdirectNat : (natInterp I).models decoded.natDirect := by
      intro clause hclause
      rcases List.mem_map.mp hclause with ⟨source, hsourceClause, rfl⟩
      exact (modelsClause_map_natInterp I source).2
        (hsource.1 source hsourceClause)
    have hdirectModel : ∀ clause ∈ decoded.natDirect.map
        HTCheckerTermEmbedding.encodeClause, valid model clause := by
      have hmodelsMapped : (HTCheckerTermEmbedding.htInterp model).models
          decoded.natDirect := by simpa [hinterp] using hdirectNat
      have hencoded := (HTCheckerTermEmbedding.models_encode_iff model
        decoded.natDirect decoded.directOntology).2 hmodelsMapped
      intro clause hclause
      rcases List.mem_map.mp hclause with ⟨source, hsourceClause, rfl⟩
      exact hencoded source hsourceClause
    have hmodels : ∀ clause ∈ decoded.commonOntology, valid model clause := by
      intro clause hclause
      simp only [DecodedDirectCardinalityCommonSource.commonOntology,
        List.mem_append] at hclause
      rcases hclause with hclause | hclause
      · exact hdirectModel clause hclause
      · exact hcardCommon clause hclause
    have hconcept := congrArg (fun interpretation => interpretation.concept) hinterp
    change model.conc = (natInterp I).concept at hconcept
    have hsubModel : model.conc sub.val value := by
      rw [hconcept]
      simpa [natInterp] using hsub
    have hsupModel := hcommon Domain model hmodels value hsubModel
    rw [hconcept] at hsupModel
    simpa [natInterp] using hsupModel
  · intro hfinite Domain model hmodels value hsub
    letI : Nonempty Domain := ⟨value⟩
    have hdirectCommon : ∀ clause ∈ decoded.natDirect.map
        HTCheckerTermEmbedding.encodeClause, valid model clause := by
      intro clause hclause
      exact hmodels clause (by
        simp only [DecodedDirectCardinalityCommonSource.commonOntology,
          List.mem_append]
        exact Or.inl hclause)
    have hdirectNat : (HTCheckerTermEmbedding.htInterp model).models
        decoded.natDirect := by
      apply (HTCheckerTermEmbedding.models_encode_iff model decoded.natDirect
        decoded.directOntology).1
      intro source hsourceClause
      exact hdirectCommon (HTCheckerTermEmbedding.encodeClause source)
        (List.mem_map.mpr ⟨source, hsourceClause, rfl⟩)
    have hdirectFin : (finInterp (HTCheckerTermEmbedding.htInterp model)).models
        decoded.projection.source := by
      intro clause hclause
      exact (modelsClause_map_finInterp
        (HTCheckerTermEmbedding.htInterp model) clause).2
        (hdirectNat (mapClause clause)
          (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
    have hcardCommon : ∀ clause ∈
        cardinalityClauses decoded.natDefinitions decoded.natPairs,
        valid model clause := by
      intro clause hclause
      exact hmodels clause (by
        simp only [DecodedDirectCardinalityCommonSource.commonOntology,
          List.mem_append]
        exact Or.inr hclause)
    have hcardNat := models_cardinalityClauses_implies_projected model
      decoded.natDefinitions decoded.natPairs hcardCommon
    have hcardFin :
        (finInterp (HTCheckerTermEmbedding.htInterp model)).modelsProjectedCardinalityDefs
          decoded.projection.definitions decoded.projection.semanticPairs :=
      (modelsProjectedDefs_map_finInterp (HTCheckerTermEmbedding.htInterp model)
        decoded.projection.definitions decoded.projection.semanticPairs).2 hcardNat
    exact hfinite Domain (finInterp (HTCheckerTermEmbedding.htInterp model))
      ⟨hdirectFin, hcardFin⟩ value (by simpa [finInterp] using hsub)

theorem DecodedDirectCardinalityCommonSource.entails_target_iff
    (decoded : DecodedDirectCardinalityCommonSource)
    (sub sup : Fin decoded.projection.concepts.length) :
    decoded.CommonEntails sub sup ↔ decoded.TargetEntails sub sup :=
  (decoded.common_entails_iff_finiteSource sub sup).trans
    (decoded.finiteSource_entails_iff_target sub sup)

theorem WireDirectCardinalityCommonSource.check_sound
    (wire : WireDirectCardinalityCommonSource)
    (decoded : DecodedDirectCardinalityCommonSource)
    (_hdecode : wire.decode = .ok decoded) (_hcheck : wire.check = .ok true)
    (sub sup : Fin decoded.projection.concepts.length) :
    decoded.CommonEntails sub sup ↔ decoded.TargetEntails sub sup :=
  decoded.entails_target_iff sub sup

#print axioms modelsProjectedDefs_map_natInterp
#print axioms modelsProjectedDefs_map_finInterp
#print axioms DecodedDirectCardinalityCommonSource.entails_target_iff
#print axioms WireDirectCardinalityCommonSource.check_sound

end ContextCalculus.HTDirectCardinalityCommonSourceWire
