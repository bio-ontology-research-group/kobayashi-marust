import ContextCalculus.HypertableauMixedProjectionWire
import ContextCalculus.HypertableauSkolemBundleListProjection
import ContextCalculus.HypertableauBundleDomainProjection
import ContextCalculus.HypertableauNativeABoxProjection
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
#print axioms WireBundleProjection.check_sound

end Tests

end ContextCalculus.Hypertableau
