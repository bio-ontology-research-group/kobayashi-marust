import ContextCalculus.HTDirectCommonSourceWire
import ContextCalculus.HTCardinalityCheckerTermEmbedding
import ContextCalculus.HypertableauDirectCardinalityProjectionWire
import ContextCalculus.HypertableauCardinalityWire

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

def pairedExactDefinitions
    (pairs : List (PairedCardinality Concept Role)) :
    List (CardinalityDef Concept Role) :=
  pairs.flatMap fun pair => [pair.maximum, pair.minimum]

theorem modelsCardinalityDefsExact_pairedExactDefinitions_iff
    (I : Interp Domain Concept Role)
    (pairs : List (PairedCardinality Concept Role)) :
    I.modelsCardinalityDefsExact (pairedExactDefinitions pairs) ↔
      ∀ pair ∈ pairs,
        I.modelsCardinalityDefExact pair.maximum ∧
          I.modelsCardinalityDefExact pair.minimum := by
  simp only [Interp.modelsCardinalityDefsExact, pairedExactDefinitions,
    List.mem_flatMap, List.mem_cons, List.mem_singleton]
  aesop

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

@[simp] theorem modelsCardinalityDefExact_map_natInterp [Nonempty Domain]
    (I : Interp Domain (Fin concepts) (Fin roles))
    (definition : CardinalityDef (Fin concepts) (Fin roles)) :
    (natInterp I).modelsCardinalityDefExact (mapCardinalityDef definition) ↔
      I.modelsCardinalityDefExact definition := by
  have hsuccessor (source : Domain) :
      (natInterp I).cardinalitySuccessor (mapCardinalityDef definition) source =
        I.cardinalitySuccessor definition source := by
    funext target
    apply propext
    exact cardinalitySuccessor_map_natInterp I definition source target
  constructor <;> intro hmodels source
  · have hresult := hmodels source
    change (natInterp I).concept definition.marker.val source ↔
      match definition.kind with
      | .minimum => HasAtLeast definition.bound
          ((natInterp I).cardinalitySuccessor (mapCardinalityDef definition) source)
      | .maximum => HasAtMost definition.bound
          ((natInterp I).cardinalitySuccessor (mapCardinalityDef definition) source)
      at hresult
    rw [hsuccessor source] at hresult
    simpa [natInterp, Interp.cardinalityCondition] using hresult
  · have hresult := hmodels source
    change I.concept definition.marker source ↔
      match definition.kind with
      | .minimum => HasAtLeast definition.bound
          (I.cardinalitySuccessor definition source)
      | .maximum => HasAtMost definition.bound
          (I.cardinalitySuccessor definition source)
      at hresult
    change (natInterp I).concept definition.marker.val source ↔
      match definition.kind with
      | .minimum => HasAtLeast definition.bound
          ((natInterp I).cardinalitySuccessor (mapCardinalityDef definition) source)
      | .maximum => HasAtMost definition.bound
          ((natInterp I).cardinalitySuccessor (mapCardinalityDef definition) source)
    rw [hsuccessor source]
    simpa [natInterp] using hresult

@[simp] theorem modelsCardinalityDefExact_map_finInterp [Nonempty Domain]
    (I : Interp Domain Nat Nat)
    (definition : CardinalityDef (Fin concepts) (Fin roles)) :
    (finInterp I).modelsCardinalityDefExact definition ↔
      I.modelsCardinalityDefExact (mapCardinalityDef definition) := by
  constructor <;> intro hmodels source
  · simpa [mapCardinalityDef, finInterp, Interp.modelsCardinalityDefExact,
      Interp.cardinalityCondition, Interp.cardinalitySuccessor] using hmodels source
  · simpa [mapCardinalityDef, finInterp, Interp.modelsCardinalityDefExact,
      Interp.cardinalityCondition, Interp.cardinalitySuccessor] using hmodels source

theorem modelsCardinalityDefsExact_map_natInterp [Nonempty Domain]
    (I : Interp Domain (Fin concepts) (Fin roles))
    (definitions : List (CardinalityDef (Fin concepts) (Fin roles))) :
    (natInterp I).modelsCardinalityDefsExact
        (definitions.map mapCardinalityDef) ↔
      I.modelsCardinalityDefsExact definitions := by
  constructor <;> intro hmodels definition hdefinition
  · exact (modelsCardinalityDefExact_map_natInterp I definition).1
      (hmodels (mapCardinalityDef definition)
        (List.mem_map.mpr ⟨definition, hdefinition, rfl⟩))
  · rcases List.mem_map.mp hdefinition with ⟨source, hsource, rfl⟩
    exact (modelsCardinalityDefExact_map_natInterp I source).2
      (hmodels source hsource)

theorem modelsCardinalityDefsExact_map_finInterp [Nonempty Domain]
    (I : Interp Domain Nat Nat)
    (definitions : List (CardinalityDef (Fin concepts) (Fin roles))) :
    (finInterp I).modelsCardinalityDefsExact definitions ↔
      I.modelsCardinalityDefsExact (definitions.map mapCardinalityDef) := by
  constructor
  · intro hmodels definition hdefinition
    rcases List.mem_map.mp hdefinition with ⟨source, hsource, rfl⟩
    exact (modelsCardinalityDefExact_map_finInterp I source).1
      (hmodels source hsource)
  · intro hmodels definition hdefinition
    exact (modelsCardinalityDefExact_map_finInterp I definition).2
      (hmodels (mapCardinalityDef definition)
        (List.mem_map.mpr ⟨definition, hdefinition, rfl⟩))

theorem modelsCardinalityDefs_map_natInterp [Nonempty Domain]
    (I : Interp Domain (Fin concepts) (Fin roles))
    (definitions : List (CardinalityDef (Fin concepts) (Fin roles))) :
    (natInterp I).modelsCardinalityDefs (definitions.map mapCardinalityDef) ↔
      I.modelsCardinalityDefs definitions := by
  constructor <;> intro hmodels definition hdefinition
  · exact (modelsCardinalityDef_map_natInterp I definition).1
      (hmodels _ (List.mem_map.mpr ⟨definition, hdefinition, rfl⟩))
  · rcases List.mem_map.mp hdefinition with ⟨source, hsource, rfl⟩
    exact (modelsCardinalityDef_map_natInterp I source).2 (hmodels source hsource)

theorem modelsCardinalityDefs_map_finInterp [Nonempty Domain]
    (I : Interp Domain Nat Nat)
    (definitions : List (CardinalityDef (Fin concepts) (Fin roles))) :
    (finInterp I).modelsCardinalityDefs definitions ↔
      I.modelsCardinalityDefs (definitions.map mapCardinalityDef) := by
  constructor
  · intro hmodels definition hdefinition
    rcases List.mem_map.mp hdefinition with ⟨source, hsource, rfl⟩
    exact (modelsCardinalityDef_map_finInterp I source).1 (hmodels source hsource)
  · intro hmodels definition hdefinition
    exact (modelsCardinalityDef_map_finInterp I definition).2
      (hmodels _ (List.mem_map.mpr ⟨definition, hdefinition, rfl⟩))

theorem entailsWithExact_mapOntology_iff
    (ontology : List (Hypertableau.Clause (Fin nvars) (Fin concepts) (Fin roles)))
    (definitions exactDefinitions :
      List (CardinalityDef (Fin concepts) (Fin roles)))
    (sub sup : Fin concepts) :
    EntailsSubWithExactCardinality ontology definitions exactDefinitions sub sup ↔
      EntailsSubWithExactCardinality (mapOntology ontology)
        (definitions.map mapCardinalityDef)
        (exactDefinitions.map mapCardinalityDef) sub.val sup.val := by
  constructor
  · intro hfinite Domain I hontology hdefinitions hexact value hsub
    letI : Nonempty Domain := ⟨value⟩
    have hontologyFin : (finInterp I).models ontology := by
      intro clause hclause
      exact (modelsClause_map_finInterp I clause).2
        (hontology (mapClause clause)
          (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
    have hdefinitionsFin : (finInterp I).modelsCardinalityDefs definitions := by
      exact (modelsCardinalityDefs_map_finInterp I definitions).2 hdefinitions
    have hexactFin : (finInterp I).modelsCardinalityDefsExact exactDefinitions := by
      exact (modelsCardinalityDefsExact_map_finInterp I exactDefinitions).2 hexact
    exact hfinite Domain (finInterp I) hontologyFin hdefinitionsFin hexactFin value
      (by simpa [finInterp] using hsub)
  · intro hnat Domain I hontology hdefinitions hexact value hsub
    letI : Nonempty Domain := ⟨value⟩
    have hontologyNat : (natInterp I).models (mapOntology ontology) := by
      intro clause hclause
      rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
      exact (modelsClause_map_natInterp I source).2 (hontology source hsource)
    have hdefinitionsNat : (natInterp I).modelsCardinalityDefs
        (definitions.map mapCardinalityDef) := by
      exact (modelsCardinalityDefs_map_natInterp I definitions).2 hdefinitions
    have hexactNat : (natInterp I).modelsCardinalityDefsExact
        (exactDefinitions.map mapCardinalityDef) := by
      exact (modelsCardinalityDefsExact_map_natInterp I exactDefinitions).2 hexact
    have hresult := hnat Domain (natInterp I) hontologyNat hdefinitionsNat hexactNat value
      (by simpa [natInterp] using hsub)
    simpa [natInterp] using hresult

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

theorem DecodedDirectCardinalityCommonSource.exact_entails_iff_target
    (decoded : DecodedDirectCardinalityCommonSource)
    (sub sup : Fin decoded.projection.concepts.length) :
    EntailsSubWithExactCardinality decoded.projection.target
        decoded.projection.definitions
        (pairedExactDefinitions decoded.projection.semanticPairs) sub sup ↔
      decoded.TargetEntails sub sup := by
  constructor
  · intro hentails Domain I hmodels value hsub
    exact hentails Domain I hmodels.1
      (fun definition hdefinition =>
        (modelsProjectedCardinalityTargets_iff_paired I
          decoded.projection.definitions decoded.projection.semanticPairs
          (fun pair hpair => decoded.projection.semanticPairs_mem pair hpair)).1
          hmodels.2 |>.1 definition hdefinition)
      ((modelsCardinalityDefsExact_pairedExactDefinitions_iff I
        decoded.projection.semanticPairs).2
        ((modelsProjectedCardinalityTargets_iff_paired I
          decoded.projection.definitions decoded.projection.semanticPairs
          (fun pair hpair => decoded.projection.semanticPairs_mem pair hpair)).1
          hmodels.2 |>.2)) value hsub
  · intro hentails Domain I hontology hdefinitions hexact value hsub
    have htargets : I.modelsProjectedCardinalityTargets
        decoded.projection.definitions decoded.projection.semanticPairs := by
      apply (modelsProjectedCardinalityTargets_iff_paired I
        decoded.projection.definitions decoded.projection.semanticPairs
        (fun pair hpair => decoded.projection.semanticPairs_mem pair hpair)).2
      exact ⟨hdefinitions, (modelsCardinalityDefsExact_pairedExactDefinitions_iff I
        decoded.projection.semanticPairs).1 hexact⟩
    exact hentails Domain I ⟨hontology, htargets⟩ value hsub

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
