import ContextCalculus.HypertableauMixedProjectionWire
import ContextCalculus.HypertableauSkolemBundleListProjection
import ContextCalculus.HypertableauBundleDomainProjection
import ContextCalculus.HypertableauNativeABoxProjection
import ContextCalculus.HypertableauCardinalityRenaming
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Checked finite Skolem-bundle projection wire

This wire format connects source concept names to the target HT concept table
through a checked injection.  Bundle definers and source concepts must have
pairwise distinct target identifiers.  Consequently the structural signature
`Sum (Fin bundles.length) (Fin sourceConcepts.length)` used by the semantic
proof has a left inverse into the production target signature.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireNamedLit where
  concept : String
  neg : Bool
deriving FromJson, ToJson, Repr

structure WireSkolemBundle where
  variableNames : List String
  body : List WireDirectSourceAtom
  source : String
  function : String
  role : String
  fillers : List WireNamedLit
  definer : String
deriving FromJson, ToJson, Repr

structure DecodedWireBundle (Variable Concept Role Function TargetConcept : Type*) where
  spec : BundleSpec Variable Concept Role Function
  definer : TargetConcept

def WireSkolemBundle.decode (variableCount : Nat)
    (sourceConcepts targetConcepts roles functions : List String)
    (wire : WireSkolemBundle) : Except String
      (DecodedWireBundle (Fin variableCount) (Fin sourceConcepts.length)
        (Fin roles.length) (Fin functions.length) (Fin targetConcepts.length)) := do
  if wire.variableNames.Nodup then
    return {
      spec := {
        body := ← wire.body.mapM
          (WireDirectSourceAtom.decode variableCount sourceConcepts roles wire.variableNames)
        source := ← checkedLocalVariable variableCount wire.variableNames wire.source
        function := ← checkedName "function" wire.function functions
        role := ← checkedName "role" wire.role roles
        fillers := ← wire.fillers.mapM fun filler => do
          return ⟨← checkedName "source concept" filler.concept sourceConcepts, filler.neg⟩
      }
      definer := ← checkedName "target definer" wire.definer targetConcepts
    }
  else
    throw "Skolem bundle variable table contains duplicates"

structure WireBundleDomainExtra where
  bundle : Nat
  path : List String
  domain : WireNamedLit
deriving FromJson, ToJson, Repr

def WireBundleDomainExtra.decode
    (sourceConcepts roles : List String) (bundleCount : Nat)
    (wire : WireBundleDomainExtra) : Except String
      (IndexedBundleDomainSpec (Fin sourceConcepts.length) (Fin roles.length)
        bundleCount) := do
  return {
    bundle := ← checkedFin "bundle" bundleCount wire.bundle
    path := ← wire.path.mapM fun role => checkedName "role path" role roles
    domain := ⟨← checkedName "domain concept" wire.domain.concept sourceConcepts,
      wire.domain.neg⟩
  }

def decodedBundleSpecs
    (bundles : List (DecodedWireBundle Variable Concept Role Function TargetConcept)) :
    Fin bundles.length → BundleSpec Variable Concept Role Function :=
  fun index => (bundles.get index).spec

def bundleConceptEmbedding
    (sourceTargets : Fin sourceCount → TargetConcept)
    (bundles : List (DecodedWireBundle Variable Concept Role Function TargetConcept)) :
    Sum (Fin bundles.length) (Fin sourceCount) → TargetConcept
  | .inl index => (bundles.get index).definer
  | .inr index => sourceTargets index

def checkedNameEmbedding (kind : String) (source target : List String) :
    Except String (Fin source.length → Fin target.length) := do
  let values ← source.mapM fun name => checkedName kind name target
  if hlength : values.length = source.length then
    return fun index => values.get (hlength.symm ▸ index)
  else
    throw "internal name-embedding length mismatch"

def bundleEmbeddingValues
    (sourceTargets : Fin sourceCount → TargetConcept)
    (bundles : List (DecodedWireBundle Variable Concept Role Function TargetConcept)) :
    List TargetConcept :=
  List.ofFn fun index : Fin (bundles.length + sourceCount) =>
    bundleConceptEmbedding sourceTargets bundles (finSumFinEquiv.symm index)

theorem bundleConceptEmbedding_injective_of_nodup
    (sourceTargets : Fin sourceCount → TargetConcept)
    (bundles : List (DecodedWireBundle Variable Concept Role Function TargetConcept))
    (hnodup : (bundleEmbeddingValues sourceTargets bundles).Nodup) :
    _root_.Function.Injective (bundleConceptEmbedding sourceTargets bundles) := by
  have hfinite : _root_.Function.Injective
      (fun index : Fin (bundles.length + sourceCount) =>
        bundleConceptEmbedding sourceTargets bundles (finSumFinEquiv.symm index)) :=
    (List.nodup_ofFn).1 hnodup
  intro left right heq
  apply finSumFinEquiv.injective
  apply hfinite
  simpa using heq

structure WireBundleProjection where
  variable_count : Nat
  source_concepts : List String
  concepts : List String
  roles : List String
  functions : List String
  direct : List WireDirectSourceClause
  bundles : List WireSkolemBundle
  domain_extras : List WireBundleDomainExtra
  target : List WireClause
deriving FromJson, ToJson, Repr

structure DecodedBundleProjection where
  variableCount : Nat
  sourceConcepts : List String
  concepts : List String
  roles : List String
  functions : List String
  sourceTargets : Fin sourceConcepts.length → Fin concepts.length
  direct : List
    (Clause (Fin variableCount) (Fin sourceConcepts.length) (Fin roles.length))
  bundles : List
    (DecodedWireBundle (Fin variableCount) (Fin sourceConcepts.length)
      (Fin roles.length) (Fin functions.length) (Fin concepts.length))
  domainExtras : List
    (IndexedBundleDomainSpec (Fin sourceConcepts.length) (Fin roles.length)
      bundles.length)
  target : List
    (Clause (Fin variableCount) (Fin concepts.length) (Fin roles.length))
  nonemptyBundles : bundles ≠ []
  uniqueFunctions :
    (skolemPairFunctions (indexedBundlePairs (decodedBundleSpecs bundles))).Nodup
  embeddingInjective : _root_.Function.Injective
    (bundleConceptEmbedding sourceTargets bundles)
  rboxSource : Fin variableCount
  rboxTarget : Fin variableCount
  rboxDistinct : rboxSource ≠ rboxTarget
  pathPremises : ∀ spec ∈ domainExtras, ∀ clause ∈
    roleInclusionPathClauses
      (decodedBundleSpecs bundles spec.bundle).role spec.path rboxSource rboxTarget,
    clause ∈ direct
  domainPremises : ∀ spec ∈ domainExtras,
    roleDomainClause (spec.superRole (decodedBundleSpecs bundles)) spec.domain
      rboxSource rboxTarget ∈ direct
  exactProjection :
    (renameOntology (bundleConceptEmbedding sourceTargets bundles)
      (indexedBundleOntology direct (decodedBundleSpecs bundles) ++
        indexedBundleDomainOntology (decodedBundleSpecs bundles) domainExtras)).toFinset =
        target.toFinset

def WireBundleProjection.decode (wire : WireBundleProjection) :
    Except String DecodedBundleProjection := do
  if _hsourceConcepts : wire.source_concepts.Nodup then
    if _hconcepts : wire.concepts.Nodup then
      if _hroles : wire.roles.Nodup then
        if _hfunctions : wire.functions.Nodup then
          let sourceTargets ← checkedNameEmbedding "source concept in target"
            wire.source_concepts wire.concepts
          let direct ← wire.direct.mapM
            (WireDirectSourceClause.decode wire.variable_count wire.source_concepts wire.roles)
          let bundles ← wire.bundles.mapM
            (WireSkolemBundle.decode wire.variable_count wire.source_concepts
              wire.concepts wire.roles wire.functions)
          if hnonempty : bundles ≠ [] then
            if hrboxCount : 2 ≤ wire.variable_count then
              let rboxSource : Fin wire.variable_count :=
                ⟨0, lt_of_lt_of_le Nat.zero_lt_two hrboxCount⟩
              let rboxTarget : Fin wire.variable_count := ⟨1, hrboxCount⟩
              have hrboxDistinct : rboxSource ≠ rboxTarget := by
                intro hequal
                have hval := congrArg Fin.val hequal
                simp [rboxSource, rboxTarget] at hval
              let domainExtras ← wire.domain_extras.mapM
                (WireBundleDomainExtra.decode wire.source_concepts wire.roles bundles.length)
              let target ← wire.target.mapM
                (WireClause.decode wire.variable_count wire.concepts.length wire.roles.length)
              if hunique : (skolemPairFunctions
                  (indexedBundlePairs (decodedBundleSpecs bundles))).Nodup then
                if hinjective : (bundleEmbeddingValues sourceTargets bundles).Nodup then
                  if hpaths : ∀ spec ∈ domainExtras, ∀ clause ∈
                      roleInclusionPathClauses
                        (decodedBundleSpecs bundles spec.bundle).role spec.path
                          rboxSource rboxTarget,
                      clause ∈ direct then
                    if hdomains : ∀ spec ∈ domainExtras,
                        roleDomainClause
                          (spec.superRole (decodedBundleSpecs bundles)) spec.domain
                            rboxSource rboxTarget ∈ direct then
                      if hequal :
                          (renameOntology (bundleConceptEmbedding sourceTargets bundles)
                            (indexedBundleOntology direct (decodedBundleSpecs bundles) ++
                              indexedBundleDomainOntology
                                (decodedBundleSpecs bundles) domainExtras)).toFinset =
                            target.toFinset then
                        return {
                          variableCount := wire.variable_count
                          sourceConcepts := wire.source_concepts
                          concepts := wire.concepts
                          roles := wire.roles
                          functions := wire.functions
                          sourceTargets
                          direct
                          bundles
                          domainExtras
                          target
                          nonemptyBundles := hnonempty
                          uniqueFunctions := hunique
                          embeddingInjective :=
                            bundleConceptEmbedding_injective_of_nodup
                              sourceTargets bundles hinjective
                          rboxSource
                          rboxTarget
                          rboxDistinct := hrboxDistinct
                          pathPremises := hpaths
                          domainPremises := hdomains
                          exactProjection := hequal
                        }
                      else
                        throw "bundle source conversion differs from the claimed HT ontology"
                    else
                      throw "bundle domain premise is absent from the source ontology"
                  else
                    throw "bundle role-inclusion path is absent from the source ontology"
                else
                  throw "bundle definers collide with each other or source concepts"
              else
                throw "bundle projection reuses a Skolem function"
            else
              throw "bundle projection with RBox evidence requires two variables"
          else
            throw "bundle projection contains no bundles"
        else
          throw "HT function-name table contains duplicates"
      else
        throw "HT role-name table contains duplicates"
    else
      throw "HT target concept-name table contains duplicates"
  else
    throw "HT source concept-name table contains duplicates"

def WireBundleProjection.check (wire : WireBundleProjection) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedBundleProjection.models_source_iff_target
    (decoded : DecodedBundleProjection)
    (base : SkolemInterp Domain (Fin decoded.functions.length)) :
    (∃ I : Interp Domain (Fin decoded.sourceConcepts.length)
        (Fin decoded.roles.length),
      ∃ functions : SkolemInterp Domain (Fin decoded.functions.length),
        I.models decoded.direct ∧
          ModelsBundles I functions (decodedBundleSpecs decoded.bundles)) ↔
    (∃ J : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length),
      J.models decoded.target) := by
  have hpositive : 0 < decoded.bundles.length :=
    List.length_pos_of_ne_nil decoded.nonemptyBundles
  letI : Nonempty
      (Sum (Fin decoded.bundles.length) (Fin decoded.sourceConcepts.length)) :=
    ⟨.inl ⟨0, hpositive⟩⟩
  obtain ⟨inverse, hleft⟩ := decoded.embeddingInjective.hasLeftInverse
  rw [indexedBundleDomainProjection_renamed_sat_iff base decoded.direct
    (decodedBundleSpecs decoded.bundles) decoded.uniqueFunctions decoded.domainExtras
    decoded.rboxSource decoded.rboxTarget decoded.rboxDistinct
    decoded.pathPremises decoded.domainPremises
    (bundleConceptEmbedding decoded.sourceTargets decoded.bundles) inverse hleft]
  constructor
  · rintro ⟨J, hmodels⟩
    exact ⟨J, (models_iff_of_toFinset_eq J _ _ decoded.exactProjection).1 hmodels⟩
  · rintro ⟨J, hmodels⟩
    exact ⟨J, (models_iff_of_toFinset_eq J _ _ decoded.exactProjection).2 hmodels⟩

/-- Forward bundle projection while preserving a native ABox whose concepts
are all checked images of source concepts. This strengthening is needed for a
joint source/ABox decision theorem; plain equisatisfiability is insufficient. -/
theorem DecodedBundleProjection.source_model_to_target_model_preserving_nativeABox
    (decoded : DecodedBundleProjection)
    (abox : NativeABox Individual (Fin decoded.concepts.length)
      (Fin decoded.roles.length))
    (sourceOf : Fin decoded.concepts.length → Fin decoded.sourceConcepts.length)
    (hembedded : ∀ individual concept,
      concept ∈ abox.proxies individual ++ abox.assertions individual →
      bundleConceptEmbedding decoded.sourceTargets decoded.bundles
        (.inr (sourceOf concept)) = concept)
    (I : Interp Domain (Fin decoded.sourceConcepts.length)
      (Fin decoded.roles.length))
    (functions : SkolemInterp Domain (Fin decoded.functions.length))
    (value : Individual → Domain)
    (hdirect : I.models decoded.direct)
    (hbundles : ModelsBundles I functions (decodedBundleSpecs decoded.bundles))
    (habox : (abox.mapConcepts sourceOf).models I value) :
    ∃ J : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length),
      J.models decoded.target ∧ abox.models J value := by
  have hpositive : 0 < decoded.bundles.length :=
    List.length_pos_of_ne_nil decoded.nonemptyBundles
  letI : Nonempty
      (Sum (Fin decoded.bundles.length) (Fin decoded.sourceConcepts.length)) :=
    ⟨.inl ⟨0, hpositive⟩⟩
  obtain ⟨inverse, hleft⟩ := decoded.embeddingInjective.hasLeftInverse
  let extended := indexedBundleExtension I (decodedBundleSpecs decoded.bundles)
  have hcore : extended.models
      (indexedBundleOntology decoded.direct (decodedBundleSpecs decoded.bundles)) :=
    indexedBundleProjection_sound I functions decoded.direct
      (decodedBundleSpecs decoded.bundles) hdirect hbundles
  have hdomains : extended.models
      (indexedBundleOntology decoded.direct (decodedBundleSpecs decoded.bundles) ++
        indexedBundleDomainOntology (decodedBundleSpecs decoded.bundles)
          decoded.domainExtras) :=
    (add_indexedBundleDomainOntology_of_direct_iff extended decoded.direct
      (decodedBundleSpecs decoded.bundles) decoded.domainExtras
      decoded.rboxSource decoded.rboxTarget decoded.rboxDistinct
      decoded.pathPremises decoded.domainPremises).2 hcore
  let J := pushforwardConcepts inverse extended
  have hrenamed : J.models
      (renameOntology (bundleConceptEmbedding decoded.sourceTargets decoded.bundles)
        (indexedBundleOntology decoded.direct (decodedBundleSpecs decoded.bundles) ++
          indexedBundleDomainOntology (decodedBundleSpecs decoded.bundles)
            decoded.domainExtras)) :=
    (models_rename_pushforward_iff
      (bundleConceptEmbedding decoded.sourceTargets decoded.bundles)
      inverse hleft extended _).2 hdomains
  refine ⟨J, (models_iff_of_toFinset_eq J _ _ decoded.exactProjection).1 hrenamed, ?_⟩
  apply abox.models_of_mapConcepts sourceOf I J value
  · intro individual concept hused
    have hembed := hembedded individual concept hused
    have hinverse : inverse concept = .inr (sourceOf concept) := by
      calc
        inverse concept = inverse (bundleConceptEmbedding decoded.sourceTargets
            decoded.bundles (.inr (sourceOf concept))) := congrArg inverse hembed.symm
        _ = .inr (sourceOf concept) := hleft _
    simp [J, pushforwardConcepts, hinverse, extended, indexedBundleExtension]
  · rfl
  · exact habox

/-- Recover a source bundle model from a checked target model while pulling the
native ABox back to its source concept names.  Unlike bare equisatisfiability,
this theorem keeps the target ABox and source ontology in one shared domain and
therefore supports a source-level SAT decision certificate. -/
theorem DecodedBundleProjection.target_model_to_source_model_preserving_nativeABox
    (decoded : DecodedBundleProjection)
    (abox : NativeABox Individual (Fin decoded.concepts.length)
      (Fin decoded.roles.length))
    (sourceOf : Fin decoded.concepts.length → Fin decoded.sourceConcepts.length)
    (hembedded : ∀ individual concept,
      concept ∈ abox.proxies individual ++ abox.assertions individual →
      bundleConceptEmbedding decoded.sourceTargets decoded.bundles
        (.inr (sourceOf concept)) = concept)
    (J : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length))
    (base : SkolemInterp Domain (Fin decoded.functions.length))
    (value : Individual → Domain)
    (htarget : J.models decoded.target)
    (habox : abox.models J value) :
    ∃ I : Interp Domain (Fin decoded.sourceConcepts.length)
        (Fin decoded.roles.length),
      ∃ functions : SkolemInterp Domain (Fin decoded.functions.length),
        I.models decoded.direct ∧
          ModelsBundles I functions (decodedBundleSpecs decoded.bundles) ∧
          (abox.mapConcepts sourceOf).models I value := by
  let embedding := bundleConceptEmbedding decoded.sourceTargets decoded.bundles
  let combined := indexedBundleOntology decoded.direct
      (decodedBundleSpecs decoded.bundles) ++
    indexedBundleDomainOntology (decodedBundleSpecs decoded.bundles)
      decoded.domainExtras
  have hrenamed : J.models (renameOntology embedding combined) :=
    (models_iff_of_toFinset_eq J _ _ decoded.exactProjection).2 htarget
  let K := pullbackConcepts embedding J
  have hcombined : K.models combined :=
    (models_rename_pullback_iff embedding J combined).1 hrenamed
  have hcore : K.models
      (indexedBundleOntology decoded.direct
        (decodedBundleSpecs decoded.bundles)) := by
    intro clause hclause
    exact hcombined clause (List.mem_append_left _ hclause)
  rcases indexedBundleProjection_complete K base decoded.direct
      (decodedBundleSpecs decoded.bundles) decoded.uniqueFunctions hcore with
    ⟨functions, hdirect, hbundles⟩
  let I := indexedRestrict K
  have haboxSource : (abox.mapConcepts sourceOf).models I value :=
    abox.mapConcepts_models_of sourceOf I J value
      (by
        intro individual concept hused
        change J.concept concept = J.concept (embedding (.inr (sourceOf concept)))
        simpa [embedding] using
          congrArg J.concept (hembedded individual concept hused).symm)
      rfl habox
  exact ⟨I, functions, hdirect, hbundles, haboxSource⟩

/-- Recover one source interpretation that simultaneously realizes the bundle
source, the pulled-back native ABox, and every projected cardinality family.
This strengthens bare bundle equisatisfiability: all three source obligations
come from the same checked target quotient. -/
theorem DecodedBundleProjection.target_model_to_source_model_preserving_nativeABox_cardinality
    (decoded : DecodedBundleProjection)
    (abox : NativeABox Individual (Fin decoded.concepts.length)
      (Fin decoded.roles.length))
    (sourceOf : Fin decoded.concepts.length → Fin decoded.sourceConcepts.length)
    (hembedded : ∀ individual concept,
      concept ∈ abox.proxies individual ++ abox.assertions individual →
      bundleConceptEmbedding decoded.sourceTargets decoded.bundles
        (.inr (sourceOf concept)) = concept)
    (definitions : List (CardinalityDef (Fin decoded.sourceConcepts.length)
      (Fin decoded.roles.length)))
    (pairs : List (PairedCardinality (Fin decoded.sourceConcepts.length)
      (Fin decoded.roles.length)))
    (hpairs : ∀ pair ∈ pairs,
      pair.maximum ∈ definitions ∧ pair.minimum ∈ definitions)
    (J : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length))
    (base : SkolemInterp Domain (Fin decoded.functions.length))
    (value : Individual → Domain)
    (htarget : J.models decoded.target)
    (habox : abox.models J value)
    (hcardinality : J.modelsPairedCardinalityTargets
      ((definitions.map (renameCardinalityDef Sum.inr)).map
        (renameCardinalityDef
          (bundleConceptEmbedding decoded.sourceTargets decoded.bundles)))
      ((pairs.map (renamePairedCardinality Sum.inr)).map
        (renamePairedCardinality
          (bundleConceptEmbedding decoded.sourceTargets decoded.bundles)))) :
    ∃ I : Interp Domain (Fin decoded.sourceConcepts.length)
        (Fin decoded.roles.length),
      ∃ functions : SkolemInterp Domain (Fin decoded.functions.length),
        I.models decoded.direct ∧
          ModelsBundles I functions (decodedBundleSpecs decoded.bundles) ∧
          (abox.mapConcepts sourceOf).models I value ∧
          I.modelsProjectedCardinalityDefs definitions pairs := by
  let embedding := bundleConceptEmbedding decoded.sourceTargets decoded.bundles
  let combined := indexedBundleOntology decoded.direct
      (decodedBundleSpecs decoded.bundles) ++
    indexedBundleDomainOntology (decodedBundleSpecs decoded.bundles)
      decoded.domainExtras
  have hrenamed : J.models (renameOntology embedding combined) :=
    (models_iff_of_toFinset_eq J _ _ decoded.exactProjection).2 htarget
  let K := pullbackConcepts embedding J
  have hcombined : K.models combined :=
    (models_rename_pullback_iff embedding J combined).1 hrenamed
  have hcore : K.models
      (indexedBundleOntology decoded.direct
        (decodedBundleSpecs decoded.bundles)) := by
    intro clause hclause
    exact hcombined clause (List.mem_append_left _ hclause)
  rcases indexedBundleProjection_complete K base decoded.direct
      (decodedBundleSpecs decoded.bundles) decoded.uniqueFunctions hcore with
    ⟨functions, hdirect, hbundles⟩
  let I := indexedRestrict K
  have haboxSource : (abox.mapConcepts sourceOf).models I value :=
    abox.mapConcepts_models_of sourceOf I J value
      (by
        intro individual concept hused
        change J.concept concept = J.concept (embedding (.inr (sourceOf concept)))
        simpa [embedding] using
          congrArg J.concept (hembedded individual concept hused).symm)
      rfl habox
  have hcombinedCardinality : K.modelsPairedCardinalityTargets
      (definitions.map (renameCardinalityDef Sum.inr))
      (pairs.map (renamePairedCardinality Sum.inr)) := by
    exact (modelsPairedCardinalityTargets_rename_pullback_iff
      embedding J (definitions.map (renameCardinalityDef Sum.inr))
      (pairs.map (renamePairedCardinality Sum.inr))).1 hcardinality
  have hsourceTargets : I.modelsPairedCardinalityTargets definitions pairs := by
    apply (modelsPairedCardinalityTargets_rename_pullback_iff
      Sum.inr K definitions pairs).1
    simpa [I, indexedRestrict, pullbackConcepts] using hcombinedCardinality
  have hsourceCardinality : I.modelsProjectedCardinalityDefs definitions pairs :=
    (modelsProjectedCardinalityDefs_iff_pairedTargets I definitions pairs hpairs).2
      hsourceTargets
  exact ⟨I, functions, hdirect, hbundles, haboxSource, hsourceCardinality⟩

/-- Forward bundle projection while preserving both a checked native ABox and
the cardinality target contract in the same constructed interpretation. -/
theorem DecodedBundleProjection.source_model_to_target_model_preserving_nativeABox_cardinality
    (decoded : DecodedBundleProjection)
    (abox : NativeABox Individual (Fin decoded.concepts.length)
      (Fin decoded.roles.length))
    (sourceOf : Fin decoded.concepts.length → Fin decoded.sourceConcepts.length)
    (hembedded : ∀ individual concept,
      concept ∈ abox.proxies individual ++ abox.assertions individual →
      bundleConceptEmbedding decoded.sourceTargets decoded.bundles
        (.inr (sourceOf concept)) = concept)
    (definitions : List (CardinalityDef (Fin decoded.sourceConcepts.length)
      (Fin decoded.roles.length)))
    (pairs : List (PairedCardinality (Fin decoded.sourceConcepts.length)
      (Fin decoded.roles.length)))
    (hpairs : ∀ pair ∈ pairs,
      pair.maximum ∈ definitions ∧ pair.minimum ∈ definitions)
    (I : Interp Domain (Fin decoded.sourceConcepts.length)
      (Fin decoded.roles.length))
    (functions : SkolemInterp Domain (Fin decoded.functions.length))
    (value : Individual → Domain)
    (hdirect : I.models decoded.direct)
    (hbundles : ModelsBundles I functions (decodedBundleSpecs decoded.bundles))
    (habox : (abox.mapConcepts sourceOf).models I value)
    (hcardinality : I.modelsProjectedCardinalityDefs definitions pairs) :
    ∃ J : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length),
      J.models decoded.target ∧ abox.models J value ∧
      J.modelsPairedCardinalityTargets
        ((definitions.map (renameCardinalityDef Sum.inr)).map
          (renameCardinalityDef
            (bundleConceptEmbedding decoded.sourceTargets decoded.bundles)))
        ((pairs.map (renamePairedCardinality Sum.inr)).map
          (renamePairedCardinality
            (bundleConceptEmbedding decoded.sourceTargets decoded.bundles))) := by
  have hpositive : 0 < decoded.bundles.length :=
    List.length_pos_of_ne_nil decoded.nonemptyBundles
  letI : Nonempty
      (Sum (Fin decoded.bundles.length) (Fin decoded.sourceConcepts.length)) :=
    ⟨.inl ⟨0, hpositive⟩⟩
  obtain ⟨inverse, hleft⟩ := decoded.embeddingInjective.hasLeftInverse
  let extended := indexedBundleExtension I (decodedBundleSpecs decoded.bundles)
  have hcore : extended.models
      (indexedBundleOntology decoded.direct (decodedBundleSpecs decoded.bundles)) :=
    indexedBundleProjection_sound I functions decoded.direct
      (decodedBundleSpecs decoded.bundles) hdirect hbundles
  have hdomains : extended.models
      (indexedBundleOntology decoded.direct (decodedBundleSpecs decoded.bundles) ++
        indexedBundleDomainOntology (decodedBundleSpecs decoded.bundles)
          decoded.domainExtras) :=
    (add_indexedBundleDomainOntology_of_direct_iff extended decoded.direct
      (decodedBundleSpecs decoded.bundles) decoded.domainExtras
      decoded.rboxSource decoded.rboxTarget decoded.rboxDistinct
      decoded.pathPremises decoded.domainPremises).2 hcore
  have hsourceCardinality : I.modelsPairedCardinalityTargets definitions pairs :=
    (modelsProjectedCardinalityDefs_iff_pairedTargets I definitions pairs hpairs).1
      hcardinality
  have hextendedCardinality : extended.modelsPairedCardinalityTargets
      (definitions.map (renameCardinalityDef Sum.inr))
      (pairs.map (renamePairedCardinality Sum.inr)) := by
    apply (modelsPairedCardinalityTargets_rename_pullback_iff
      Sum.inr extended definitions pairs).2
    simpa [extended, pullbackConcepts, indexedBundleExtension] using hsourceCardinality
  let J := pushforwardConcepts inverse extended
  have hrenamed : J.models
      (renameOntology (bundleConceptEmbedding decoded.sourceTargets decoded.bundles)
        (indexedBundleOntology decoded.direct (decodedBundleSpecs decoded.bundles) ++
          indexedBundleDomainOntology (decodedBundleSpecs decoded.bundles)
            decoded.domainExtras)) :=
    (models_rename_pushforward_iff
      (bundleConceptEmbedding decoded.sourceTargets decoded.bundles)
      inverse hleft extended _).2 hdomains
  have htargetCardinality : J.modelsPairedCardinalityTargets
      ((definitions.map (renameCardinalityDef Sum.inr)).map
        (renameCardinalityDef
          (bundleConceptEmbedding decoded.sourceTargets decoded.bundles)))
      ((pairs.map (renamePairedCardinality Sum.inr)).map
        (renamePairedCardinality
          (bundleConceptEmbedding decoded.sourceTargets decoded.bundles))) := by
    apply (modelsPairedCardinalityTargets_rename_pullback_iff
      (bundleConceptEmbedding decoded.sourceTargets decoded.bundles) J
      (definitions.map (renameCardinalityDef Sum.inr))
      (pairs.map (renamePairedCardinality Sum.inr))).2
    simpa [J, pullback_pushforward_eq
      (bundleConceptEmbedding decoded.sourceTargets decoded.bundles)
      inverse hleft extended] using hextendedCardinality
  refine ⟨J, (models_iff_of_toFinset_eq J _ _ decoded.exactProjection).1 hrenamed,
    ?_, htargetCardinality⟩
  apply abox.models_of_mapConcepts sourceOf I J value
  · intro individual concept hused
    have hembed := hembedded individual concept hused
    have hinverse : inverse concept = .inr (sourceOf concept) := by
      calc
        inverse concept = inverse (bundleConceptEmbedding decoded.sourceTargets
            decoded.bundles (.inr (sourceOf concept))) := congrArg inverse hembed.symm
        _ = .inr (sourceOf concept) := hleft _
    simp [J, pushforwardConcepts, hinverse, extended, indexedBundleExtension]
  · rfl
  · exact habox

theorem WireBundleProjection.check_sound (wire : WireBundleProjection)
    (decoded : DecodedBundleProjection) (_hdecode : wire.decode = .ok decoded)
    (_hcheck : wire.check = .ok true)
    (base : SkolemInterp Domain (Fin decoded.functions.length)) :
    (∃ I : Interp Domain (Fin decoded.sourceConcepts.length)
        (Fin decoded.roles.length),
      ∃ functions : SkolemInterp Domain (Fin decoded.functions.length),
        I.models decoded.direct ∧
          ModelsBundles I functions (decodedBundleSpecs decoded.bundles)) ↔
    (∃ J : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length),
      J.models decoded.target) := by
  exact decoded.models_source_iff_target base

section Tests

private def bundleExample : WireBundleProjection where
  variable_count := 2
  source_concepts := ["A", "B", "C"]
  concepts := ["A", "def_exfil_f", "C", "B"]
  roles := ["r"]
  functions := ["f"]
  direct := [{
    variableNames := ["x"]
    body := [.con "A" "x" false]
    head := [.con "B" "x" false]
  }]
  bundles := [{
    variableNames := ["x"]
    body := [.con "A" "x" false]
    source := "x"
    function := "f"
    role := "r"
    fillers := [⟨"B", false⟩, ⟨"C", false⟩]
    definer := "def_exfil_f"
  }]
  domain_extras := []
  target := [
    {
      body := [.concept ⟨0, false⟩ 0]
      head := [.concept ⟨3, false⟩ 0]
    },
    {
      body := [.concept ⟨0, false⟩ 0]
      head := [.exists_ 0 ⟨1, false⟩ 0]
    },
    {
      body := [.concept ⟨1, false⟩ 0]
      head := [.concept ⟨3, false⟩ 0]
    },
    {
      body := [.concept ⟨1, false⟩ 0]
      head := [.concept ⟨2, false⟩ 0]
    }
  ]

private def bundleRejected (result : Except String Bool) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

example : bundleExample.check = .ok true := by native_decide

example : bundleRejected ({ bundleExample with
    concepts := ["A", "B", "C"]
    bundles := [{
      variableNames := ["x"]
      body := [.con "A" "x" false]
      source := "x"
      function := "f"
      role := "r"
      fillers := [⟨"B", false⟩, ⟨"C", false⟩]
      definer := "B"
    }]
    target := [] }).check = true := by native_decide

example : bundleRejected ({ bundleExample with target := bundleExample.target.drop 1 }).check = true := by
  native_decide

#print axioms DecodedBundleProjection.models_source_iff_target
#print axioms DecodedBundleProjection.source_model_to_target_model_preserving_nativeABox
#print axioms DecodedBundleProjection.target_model_to_source_model_preserving_nativeABox
#print axioms DecodedBundleProjection.source_model_to_target_model_preserving_nativeABox_cardinality
#print axioms DecodedBundleProjection.target_model_to_source_model_preserving_nativeABox_cardinality
#print axioms WireBundleProjection.check_sound

end Tests

end ContextCalculus.Hypertableau
