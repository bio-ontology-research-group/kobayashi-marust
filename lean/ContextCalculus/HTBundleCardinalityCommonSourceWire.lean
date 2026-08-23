import ContextCalculus.HTBundleCommonSourceWire
import ContextCalculus.HTMixedCardinalityCommonSourceWire
import ContextCalculus.HypertableauBundleCardinalityProjectionWire

/-!
# Bundle and cardinality common sources

Bundle Skolem functions occupy the checked finite prefix of the common unary
function namespace. Cardinality witness functions are shifted beyond that
prefix. This module binds the executable bundle-cardinality projection to that
single collision-free proper-term source.
-/

namespace ContextCalculus.HTBundleCardinalityCommonSourceWire

open ContextCalculus
open ContextCalculus.CheckerTerm
open ContextCalculus.Hypertableau
open ContextCalculus.HTDirectCommonSourceWire
open ContextCalculus.HTMixedCommonSourceWire
open ContextCalculus.HTBundleCommonSourceWire
open ContextCalculus.HTDirectCardinalityCommonSourceWire
open ContextCalculus.HTCardinalityCheckerTermEmbedding
open ContextCalculus.HTMixedCardinalityCommonSourceWire
open ContextCalculus.HTSkolemBundleCheckerTermEmbedding

structure WireBundleCardinalityCommonSource where
  version : Nat
  projection : WireBundleCardinalityProjection
deriving Lean.FromJson, Lean.ToJson, Repr

structure DecodedBundleCardinalityCommonSource where
  projection : DecodedBundleCardinalityProjection
  directClauses : ∀ clause ∈ projection.bundle.direct,
    clauseNoExistentials clause = true
  bundleBodies : ∀ bundle ∈ projection.bundle.bundles,
    bundleNoExistentials bundle.spec = true

def WireBundleCardinalityCommonSource.decode
    (wire : WireBundleCardinalityCommonSource) :
    Except String DecodedBundleCardinalityCommonSource := do
  if wire.version != 1 then
    throw s!"unsupported bundle-cardinality common-source version {wire.version}"
  let projection ← wire.projection.decode
  if hdirect : ∀ clause ∈ projection.bundle.direct,
      clauseNoExistentials clause = true then
    if hbundles : ∀ bundle ∈ projection.bundle.bundles,
        bundleNoExistentials bundle.spec = true then
      return { projection, directClauses := hdirect, bundleBodies := hbundles }
    else throw "bundle-cardinality body contains an existential atom"
  else throw "bundle-cardinality direct residual contains an existential atom"

def WireBundleCardinalityCommonSource.check
    (wire : WireBundleCardinalityCommonSource) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedBundleCardinalityCommonSource.commonDirect
    (decoded : DecodedBundleCardinalityCommonSource) :=
  mapOntology decoded.projection.bundle.direct

def DecodedBundleCardinalityCommonSource.commonBundles
    (decoded : DecodedBundleCardinalityCommonSource) :=
  decoded.projection.bundle.bundles.map fun bundle => mapBundle bundle.spec

def DecodedBundleCardinalityCommonSource.natDefinitions
    (decoded : DecodedBundleCardinalityCommonSource) :=
  decoded.projection.definitions.map mapCardinalityDef

def DecodedBundleCardinalityCommonSource.natPairs
    (decoded : DecodedBundleCardinalityCommonSource) :=
  decoded.projection.semanticPairs.map mapPairedCardinality

def DecodedBundleCardinalityCommonSource.commonOntology
    (decoded : DecodedBundleCardinalityCommonSource) : List FCL :=
  HTSkolemBundleCheckerTermEmbedding.encodeBundles decoded.commonDirect
      decoded.commonBundles ++
    shiftOntologyFunctions decoded.projection.bundle.functions.length
      (cardinalityClauses decoded.natDefinitions decoded.natPairs)

theorem DecodedBundleCardinalityCommonSource.directBundles
    (decoded : DecodedBundleCardinalityCommonSource) :
    DirectBundles decoded.commonDirect decoded.commonBundles := by
  constructor
  · intro clause hclause
    rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
    exact direct_mapClause source (decoded.directClauses source hsource)
  · intro bundle hbundle
    rcases List.mem_map.mp hbundle with ⟨source, hsource, rfl⟩
    exact direct_mapBundle source.spec (decoded.bundleBodies source hsource)

def DecodedBundleCardinalityCommonSource.CommonEntails
    (decoded : DecodedBundleCardinalityCommonSource)
    (sub sup : Fin decoded.projection.bundle.sourceConcepts.length) : Prop :=
  ∀ (Domain : Type) (model : TModel Domain),
    (∀ clause ∈ decoded.commonOntology, valid model clause) →
      ∀ value, model.conc sub.val value → model.conc sup.val value

def DecodedBundleCardinalityCommonSource.FiniteSourceEntails
    (decoded : DecodedBundleCardinalityCommonSource)
    (sub sup : Fin decoded.projection.bundle.sourceConcepts.length) : Prop :=
  ∀ (Domain : Type)
    (I : Interp Domain (Fin decoded.projection.bundle.sourceConcepts.length)
      (Fin decoded.projection.bundle.roles.length))
    (functions : SkolemInterp Domain
      (Fin decoded.projection.bundle.functions.length)),
    I.models decoded.projection.bundle.direct →
    ModelsBundles I functions
      (decodedBundleSpecs decoded.projection.bundle.bundles) →
    I.modelsProjectedCardinalityDefs decoded.projection.definitions
      decoded.projection.semanticPairs →
      ∀ value, I.concept sub value → I.concept sup value

def DecodedBundleCardinalityCommonSource.TargetEntails
    (decoded : DecodedBundleCardinalityCommonSource)
    (sub sup : Fin decoded.projection.bundle.sourceConcepts.length) : Prop :=
  ∀ (Domain : Type)
    (J : Interp Domain (Fin decoded.projection.bundle.concepts.length)
      (Fin decoded.projection.bundle.roles.length)),
    J.models decoded.projection.bundle.target →
    J.modelsPairedCardinalityTargets
      ((decoded.projection.definitions.map
          (renameCardinalityDef Sum.inr)).map
        (renameCardinalityDef (bundleConceptEmbedding
          decoded.projection.bundle.sourceTargets
          decoded.projection.bundle.bundles)))
      ((decoded.projection.semanticPairs.map
          (renamePairedCardinality Sum.inr)).map
        (renamePairedCardinality (bundleConceptEmbedding
          decoded.projection.bundle.sourceTargets
          decoded.projection.bundle.bundles))) →
      ∀ value,
        J.concept (decoded.projection.bundle.sourceTargets sub) value →
        J.concept (decoded.projection.bundle.sourceTargets sup) value

theorem modelsSkolemBundle_function_congr
    (I : Interp Domain Concept Role)
    (left right : SkolemInterp Domain Function)
    (body : List (Atom Variable Concept Role)) (source : Variable)
    (function : Function) (role : Role)
    (fillers : List (Hypertableau.Lit Concept))
    (hfunction : ∀ value, left.app function value = right.app function value) :
    ModelsSkolemBundle I left body source function role fillers ↔
      ModelsSkolemBundle I right body source function role fillers := by
  simp only [ModelsSkolemBundle]
  constructor
  · rintro ⟨hrole, hfillers⟩
    constructor
    · intro assignment hbody
      rw [← hfunction]
      exact hrole assignment hbody
    · intro filler hfiller assignment hbody
      rw [← hfunction]
      exact hfillers filler hfiller assignment hbody
  · rintro ⟨hrole, hfillers⟩
    constructor
    · intro assignment hbody
      rw [hfunction]
      exact hrole assignment hbody
    · intro filler hfiller assignment hbody
      rw [hfunction]
      exact hfillers filler hfiller assignment hbody

theorem DecodedBundleCardinalityCommonSource.common_entails_iff_finiteSource
    (decoded : DecodedBundleCardinalityCommonSource)
    (sub sup : Fin decoded.projection.bundle.sourceConcepts.length) :
    decoded.CommonEntails sub sup ↔ decoded.FiniteSourceEntails sub sup := by
  constructor
  · intro hcommon Domain I functions hdirect hbundles hcardinality value hsub
    letI : Nonempty Domain := ⟨value⟩
    let natI := natInterp I
    let natFunctions := HTMixedCommonSourceWire.natFunctions functions
    have hcardNat : natI.modelsProjectedCardinalityDefs
        decoded.natDefinitions decoded.natPairs :=
      (modelsProjectedDefs_map_natInterp I decoded.projection.definitions
        decoded.projection.semanticPairs).2 hcardinality
    rcases projected_implies_exists_cardinalityClauses_model natI value
        decoded.natDefinitions decoded.natPairs hcardNat with
      ⟨cardinalityModel, hcardInterp, hcardClauses⟩
    let model := mergedModel decoded.projection.bundle.functions.length
      natFunctions.app cardinalityModel
    have hcardShifted : ∀ clause ∈ shiftOntologyFunctions
        decoded.projection.bundle.functions.length
          (cardinalityClauses decoded.natDefinitions decoded.natPairs),
        valid model clause := by
      apply (models_shiftOntologyFunctions_iff model
        decoded.projection.bundle.functions.length _).2
      simpa [model] using hcardClauses
    have hdirectNat : natI.models decoded.commonDirect := by
      intro clause hclause
      rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
      exact (modelsClause_map_natInterp I source).2 (hdirect source hsource)
    have hbundleList : ModelsBundleList
        (HTCheckerTermEmbedding.htInterp model)
        (HTSkolemPairCheckerTermEmbedding.skolemInterp model)
        decoded.commonBundles := by
      intro bundle hbundle
      rcases List.mem_map.mp hbundle with ⟨source, hsource, rfl⟩
      rcases List.get_of_mem hsource with ⟨index, hindex⟩
      have hsourceModels := hbundles index
      simp only [decodedBundleSpecs] at hsourceModels
      rw [hindex] at hsourceModels
      have hbundleNat :=
        (models_mapBundle_nat_iff I functions source.spec).2 hsourceModels
      change ModelsSkolemBundle natI natFunctions (mapBundle source.spec).body
        (mapBundle source.spec).source (mapBundle source.spec).function
        (mapBundle source.spec).role (mapBundle source.spec).fillers at hbundleNat
      rw [← hcardInterp] at hbundleNat
      have hfn (sourceValue : Domain) :
          (HTSkolemPairCheckerTermEmbedding.skolemInterp model).app
              source.spec.function.val sourceValue =
            natFunctions.app source.spec.function.val sourceValue :=
        mergeFunctions_prefix decoded.projection.bundle.functions.length
          natFunctions.app cardinalityModel.fn source.spec.function sourceValue
      apply (modelsSkolemBundle_function_congr
        (HTCheckerTermEmbedding.htInterp cardinalityModel)
        (HTSkolemPairCheckerTermEmbedding.skolemInterp model) natFunctions
        (mapBundle source.spec).body (mapBundle source.spec).source
        (mapBundle source.spec).function (mapBundle source.spec).role
        (mapBundle source.spec).fillers hfn).2
      exact hbundleNat
    have hdirectMerged : (HTCheckerTermEmbedding.htInterp model).models
        decoded.commonDirect := by
      rw [← hcardInterp] at hdirectNat
      simpa [model, mergedModel, HTCheckerTermEmbedding.htInterp] using hdirectNat
    have hencoded : ∀ clause ∈
        HTSkolemBundleCheckerTermEmbedding.encodeBundles decoded.commonDirect
          decoded.commonBundles, valid model clause :=
      (HTSkolemBundleCheckerTermEmbedding.models_bundles_encode_iff model
        decoded.commonDirect decoded.commonBundles decoded.directBundles).2
        ⟨hdirectMerged, hbundleList⟩
    have hmodels : ∀ clause ∈ decoded.commonOntology, valid model clause := by
      intro clause hclause
      simp only [DecodedBundleCardinalityCommonSource.commonOntology,
        List.mem_append] at hclause
      exact hclause.elim (hencoded clause) (hcardShifted clause)
    have hconcept := congrArg (fun interpretation => interpretation.concept)
      hcardInterp
    change cardinalityModel.conc = natI.concept at hconcept
    have hsubModel : model.conc sub.val value := by
      simpa [model, mergedModel, natI, natInterp, hconcept] using hsub
    have hresult := hcommon Domain model hmodels value hsubModel
    simpa [model, mergedModel, natI, natInterp, hconcept] using hresult
  · intro hfinite Domain model hmodels value hsub
    letI : Nonempty Domain := ⟨value⟩
    have hencoded : ∀ clause ∈
        HTSkolemBundleCheckerTermEmbedding.encodeBundles decoded.commonDirect
          decoded.commonBundles, valid model clause := by
      intro clause hclause
      exact hmodels clause (by
        simp only [DecodedBundleCardinalityCommonSource.commonOntology,
          List.mem_append]
        exact Or.inl hclause)
    have hbundleSource :=
      (HTSkolemBundleCheckerTermEmbedding.models_bundles_encode_iff model
        decoded.commonDirect decoded.commonBundles decoded.directBundles).1 hencoded
    let natI := HTCheckerTermEmbedding.htInterp model
    let natFunctions := HTSkolemPairCheckerTermEmbedding.skolemInterp model
    let finI : Interp Domain
        (Fin decoded.projection.bundle.sourceConcepts.length)
        (Fin decoded.projection.bundle.roles.length) := finInterp natI
    let finFunctions : SkolemInterp Domain
        (Fin decoded.projection.bundle.functions.length) :=
      HTMixedCommonSourceWire.finFunctions natFunctions
    have hdirectFin : finI.models decoded.projection.bundle.direct := by
      intro clause hclause
      exact (modelsClause_map_finInterp natI clause).2
        (hbundleSource.1 (mapClause clause)
          (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
    have hbundlesFin : ModelsBundles finI finFunctions
        (decodedBundleSpecs decoded.projection.bundle.bundles) := by
      intro index
      have hmapped : mapBundle
          (decoded.projection.bundle.bundles.get index).spec ∈
          decoded.commonBundles := List.mem_map.mpr
            ⟨decoded.projection.bundle.bundles.get index, List.get_mem _ _, rfl⟩
      exact (models_mapBundle_fin_iff natI natFunctions
        (decoded.projection.bundle.bundles.get index).spec).2
          (hbundleSource.2 _ hmapped)
    have hcardShifted : ∀ clause ∈ shiftOntologyFunctions
        decoded.projection.bundle.functions.length
          (cardinalityClauses decoded.natDefinitions decoded.natPairs),
        valid model clause := by
      intro clause hclause
      exact hmodels clause (by
        simp only [DecodedBundleCardinalityCommonSource.commonOntology,
          List.mem_append]
        exact Or.inr hclause)
    have hcardCommon := (models_shiftOntologyFunctions_iff model
      decoded.projection.bundle.functions.length _).1 hcardShifted
    have hcardNat := models_cardinalityClauses_implies_projected
      (functionView model decoded.projection.bundle.functions.length)
      decoded.natDefinitions decoded.natPairs hcardCommon
    have hcardFin : finI.modelsProjectedCardinalityDefs
        decoded.projection.definitions decoded.projection.semanticPairs := by
      apply (modelsProjectedDefs_map_finInterp
        (HTCheckerTermEmbedding.htInterp
          (functionView model decoded.projection.bundle.functions.length))
        decoded.projection.definitions decoded.projection.semanticPairs).2
      simpa [functionView, natI] using hcardNat
    exact hfinite Domain finI finFunctions hdirectFin hbundlesFin hcardFin value
      (by simpa [finI, finInterp, natI, HTCheckerTermEmbedding.htInterp] using hsub)

theorem DecodedBundleCardinalityCommonSource.finiteSource_entails_iff_target
    (decoded : DecodedBundleCardinalityCommonSource)
    (sub sup : Fin decoded.projection.bundle.sourceConcepts.length) :
    decoded.FiniteSourceEntails sub sup ↔ decoded.TargetEntails sub sup := by
  constructor
  · intro hsource Domain J htarget htargetCardinality value hsub
    let embedding := bundleConceptEmbedding
      decoded.projection.bundle.sourceTargets decoded.projection.bundle.bundles
    let combined := indexedBundleOntology decoded.projection.bundle.direct
        (decodedBundleSpecs decoded.projection.bundle.bundles) ++
      indexedBundleDomainOntology
        (decodedBundleSpecs decoded.projection.bundle.bundles)
        decoded.projection.bundle.domainExtras
    have hrenamed : J.models (renameOntology embedding combined) :=
      (models_iff_of_toFinset_eq J _ _
        decoded.projection.bundle.exactProjection).2 htarget
    let K := pullbackConcepts embedding J
    have hcombined : K.models combined :=
      (models_rename_pullback_iff embedding J combined).1 hrenamed
    have hcore : K.models (indexedBundleOntology
        decoded.projection.bundle.direct
        (decodedBundleSpecs decoded.projection.bundle.bundles)) := by
      intro clause hclause
      exact hcombined clause (List.mem_append_left _ hclause)
    let base : SkolemInterp Domain
        (Fin decoded.projection.bundle.functions.length) := ⟨fun _ _ => value⟩
    rcases indexedBundleProjection_complete K base
        decoded.projection.bundle.direct
        (decodedBundleSpecs decoded.projection.bundle.bundles)
        decoded.projection.bundle.uniqueFunctions hcore with
      ⟨functions, hdirect, hbundles⟩
    let I := indexedRestrict K
    have hcombinedCardinality : K.modelsPairedCardinalityTargets
        (decoded.projection.definitions.map (renameCardinalityDef Sum.inr))
        (decoded.projection.semanticPairs.map
          (renamePairedCardinality Sum.inr)) := by
      exact (modelsPairedCardinalityTargets_rename_pullback_iff embedding J
        (decoded.projection.definitions.map (renameCardinalityDef Sum.inr))
        (decoded.projection.semanticPairs.map
          (renamePairedCardinality Sum.inr))).1 htargetCardinality
    have hsourceTargets : I.modelsPairedCardinalityTargets
        decoded.projection.definitions decoded.projection.semanticPairs := by
      apply (modelsPairedCardinalityTargets_rename_pullback_iff Sum.inr K
        decoded.projection.definitions decoded.projection.semanticPairs).1
      simpa [I, indexedRestrict, pullbackConcepts] using hcombinedCardinality
    have hsourceCardinality : I.modelsProjectedCardinalityDefs
        decoded.projection.definitions decoded.projection.semanticPairs :=
      (modelsProjectedCardinalityDefs_iff_pairedTargets I
        decoded.projection.definitions decoded.projection.semanticPairs
        decoded.projection.semanticPairs_mem).2 hsourceTargets
    have hresult := hsource Domain I functions hdirect hbundles
      hsourceCardinality value (by
        simpa [I, K, embedding, indexedRestrict, pullbackConcepts] using hsub)
    simpa [I, K, embedding, indexedRestrict, pullbackConcepts] using hresult
  · intro htarget Domain I functions hdirect hbundles hcardinality value hsub
    have hpositive : 0 < decoded.projection.bundle.bundles.length :=
      List.length_pos_of_ne_nil decoded.projection.bundle.nonemptyBundles
    letI : Nonempty
        (Sum (Fin decoded.projection.bundle.bundles.length)
          (Fin decoded.projection.bundle.sourceConcepts.length)) :=
      ⟨.inl ⟨0, hpositive⟩⟩
    obtain ⟨inverse, hleft⟩ :=
      decoded.projection.bundle.embeddingInjective.hasLeftInverse
    let extended := indexedBundleExtension I
      (decodedBundleSpecs decoded.projection.bundle.bundles)
    have hcore : extended.models (indexedBundleOntology
        decoded.projection.bundle.direct
        (decodedBundleSpecs decoded.projection.bundle.bundles)) :=
      indexedBundleProjection_sound I functions
        decoded.projection.bundle.direct
        (decodedBundleSpecs decoded.projection.bundle.bundles) hdirect hbundles
    have hdomains : extended.models
        (indexedBundleOntology decoded.projection.bundle.direct
            (decodedBundleSpecs decoded.projection.bundle.bundles) ++
          indexedBundleDomainOntology
            (decodedBundleSpecs decoded.projection.bundle.bundles)
            decoded.projection.bundle.domainExtras) :=
      (add_indexedBundleDomainOntology_of_direct_iff extended
        decoded.projection.bundle.direct
        (decodedBundleSpecs decoded.projection.bundle.bundles)
        decoded.projection.bundle.domainExtras
        decoded.projection.bundle.rboxSource decoded.projection.bundle.rboxTarget
        decoded.projection.bundle.rboxDistinct
        decoded.projection.bundle.pathPremises
        decoded.projection.bundle.domainPremises).2 hcore
    have hsourceCardinality : I.modelsPairedCardinalityTargets
        decoded.projection.definitions decoded.projection.semanticPairs :=
      (modelsProjectedCardinalityDefs_iff_pairedTargets I
        decoded.projection.definitions decoded.projection.semanticPairs
        decoded.projection.semanticPairs_mem).1 hcardinality
    have hextendedCardinality : extended.modelsPairedCardinalityTargets
        (decoded.projection.definitions.map (renameCardinalityDef Sum.inr))
        (decoded.projection.semanticPairs.map
          (renamePairedCardinality Sum.inr)) := by
      apply (modelsPairedCardinalityTargets_rename_pullback_iff Sum.inr extended
        decoded.projection.definitions decoded.projection.semanticPairs).2
      simpa [extended, pullbackConcepts, indexedBundleExtension] using
        hsourceCardinality
    let embedding := bundleConceptEmbedding
      decoded.projection.bundle.sourceTargets decoded.projection.bundle.bundles
    let J := pushforwardConcepts inverse extended
    have hrenamed : J.models (renameOntology embedding
        (indexedBundleOntology decoded.projection.bundle.direct
            (decodedBundleSpecs decoded.projection.bundle.bundles) ++
          indexedBundleDomainOntology
            (decodedBundleSpecs decoded.projection.bundle.bundles)
            decoded.projection.bundle.domainExtras)) :=
      (models_rename_pushforward_iff embedding inverse hleft extended _).2 hdomains
    have hmodels : J.models decoded.projection.bundle.target :=
      (models_iff_of_toFinset_eq J _ _
        decoded.projection.bundle.exactProjection).1 hrenamed
    have htargetCardinality : J.modelsPairedCardinalityTargets
        ((decoded.projection.definitions.map
            (renameCardinalityDef Sum.inr)).map
          (renameCardinalityDef embedding))
        ((decoded.projection.semanticPairs.map
            (renamePairedCardinality Sum.inr)).map
          (renamePairedCardinality embedding)) := by
      apply (modelsPairedCardinalityTargets_rename_pullback_iff embedding J
        (decoded.projection.definitions.map (renameCardinalityDef Sum.inr))
        (decoded.projection.semanticPairs.map
          (renamePairedCardinality Sum.inr))).2
      simpa [J, pullback_pushforward_eq embedding inverse hleft extended] using
        hextendedCardinality
    have hsubJ : J.concept
        (decoded.projection.bundle.sourceTargets sub) value := by
      have hinverse : inverse (decoded.projection.bundle.sourceTargets sub) =
          .inr sub := by
        simpa [embedding] using hleft (.inr sub)
      simpa [J, pushforwardConcepts, hinverse, extended,
        indexedBundleExtension] using hsub
    have hsupJ := htarget Domain J hmodels htargetCardinality value hsubJ
    have hinverse : inverse (decoded.projection.bundle.sourceTargets sup) =
        .inr sup := by
      simpa [embedding] using hleft (.inr sup)
    simpa [J, pushforwardConcepts, hinverse, extended,
      indexedBundleExtension] using hsupJ

theorem DecodedBundleCardinalityCommonSource.entails_target_iff
    (decoded : DecodedBundleCardinalityCommonSource)
    (sub sup : Fin decoded.projection.bundle.sourceConcepts.length) :
    decoded.CommonEntails sub sup ↔ decoded.TargetEntails sub sup :=
  (decoded.common_entails_iff_finiteSource sub sup).trans
    (decoded.finiteSource_entails_iff_target sub sup)

theorem WireBundleCardinalityCommonSource.check_sound
    (wire : WireBundleCardinalityCommonSource)
    (decoded : DecodedBundleCardinalityCommonSource)
    (_hdecode : wire.decode = .ok decoded) (_hcheck : wire.check = .ok true)
    (sub sup : Fin decoded.projection.bundle.sourceConcepts.length) :
    decoded.CommonEntails sub sup ↔ decoded.TargetEntails sub sup :=
  decoded.entails_target_iff sub sup

#print axioms modelsSkolemBundle_function_congr
#print axioms DecodedBundleCardinalityCommonSource.entails_target_iff
#print axioms WireBundleCardinalityCommonSource.check_sound

end ContextCalculus.HTBundleCardinalityCommonSourceWire
