import ContextCalculus.HypertableauNativeABoxModelWire
import ContextCalculus.HypertableauBundleProjectionWire

/-!
# Source-composed native-ABox HT decisions

These certificates prevent the source projection and target decision from
being checked as unrelated documents.  Every branch decodes its source theory
against the exact ontology carried by the finite HT state and then proves the
published SAT or UNSAT result about that source theory.
-/

namespace ContextCalculus.Hypertableau

open Lean

/-! ## Direct source projection -/

structure WireDirectNativeABoxSatCertificate where
  source : List WireDirectSourceClause
  certificate : WireNativeABoxSatCertificate
deriving FromJson, ToJson, Repr

structure DecodedDirectNativeABoxSatCertificate where
  certificate : DecodedNativeABoxSatCertificate
  variable_ge_two : 2 ≤ certificate.seed.variableCount
  source : List (Clause (Fin certificate.seed.variableCount)
    (Fin certificate.seed.abox.concepts.length)
    (Fin certificate.seed.abox.roles.length))
  exact_projection : source ++ certificate.seed.abox.negativeRoleClausesAt
      certificate.seed.variableCount variable_ge_two =
    certificate.seed.state.base.base.ontology

def WireDirectNativeABoxSatCertificate.decode
    (wire : WireDirectNativeABoxSatCertificate) :
    Except String DecodedDirectNativeABoxSatCertificate := do
  let certificate ← wire.certificate.decode
  let variableWitness ← requireAtLeastTwoVariables certificate.seed.variableCount
  let hvariables := variableWitness.proof
  let source ← wire.source.mapM (WireDirectSourceClause.decode
    certificate.seed.variableCount certificate.seed.abox.concepts
    certificate.seed.abox.roles)
  if hequal : source ++ certificate.seed.abox.negativeRoleClausesAt
      certificate.seed.variableCount hvariables =
      certificate.seed.state.base.base.ontology then
    return {
      certificate
      variable_ge_two := hvariables
      source
      exact_projection := hequal
    }
  else throw "direct source conversion differs from the native ABox SAT ontology"

def WireDirectNativeABoxSatCertificate.check
    (wire : WireDirectNativeABoxSatCertificate) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedDirectNativeABoxSatCertificate.source_satisfiable
    (decoded : DecodedDirectNativeABoxSatCertificate) :
    decoded.certificate.seed.abox.abox.SatisfiableWith decoded.source := by
  rcases decoded.certificate.satisfiable with
    ⟨Domain, I, value, hdomain, htarget, habox⟩
  have happended : I.models (decoded.source ++
      decoded.certificate.seed.abox.negativeRoleClausesAt
        decoded.certificate.seed.variableCount decoded.variable_ge_two) := by
    simpa only [decoded.exact_projection] using htarget
  have hsource : I.models decoded.source := by
    intro clause hclause
    exact happended clause (List.mem_append_left _ hclause)
  exact ⟨Domain, I, value, hdomain, hsource, habox⟩

inductive WireDirectNativeABoxDecisionEvidence where
  | sat (certificate : WireDirectNativeABoxSatCertificate)
  | unsat (refutation : WireDirectNativeABoxRefutation)
deriving FromJson, ToJson, Repr

structure WireDirectNativeABoxDecisionCertificate where
  version : Nat
  evidence : WireDirectNativeABoxDecisionEvidence
deriving FromJson, ToJson, Repr

inductive DecodedDirectNativeABoxDecision where
  | sat (certificate : DecodedDirectNativeABoxSatCertificate)
  | unsat (refutation : DecodedDirectNativeABoxRefutation)

def WireDirectNativeABoxDecisionCertificate.decode
    (wire : WireDirectNativeABoxDecisionCertificate) :
    Except String DecodedDirectNativeABoxDecision := do
  if wire.version != 1 then
    throw s!"unsupported direct native ABox source decision version {wire.version}"
  match wire.evidence with
  | .sat certificate => return .sat (← certificate.decode)
  | .unsat refutation => return .unsat (← refutation.decode)

def WireDirectNativeABoxDecisionCertificate.check
    (wire : WireDirectNativeABoxDecisionCertificate) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedDirectNativeABoxDecision.SemanticallyValid :
    DecodedDirectNativeABoxDecision → Prop
  | .sat certificate => certificate.certificate.seed.abox.abox.SatisfiableWith
      certificate.source
  | .unsat refutation => ¬refutation.refutation.initial.seed.abox.abox.SatisfiableWith
      refutation.source

theorem DecodedDirectNativeABoxDecision.semantic_valid
    (decoded : DecodedDirectNativeABoxDecision) : decoded.SemanticallyValid := by
  cases decoded with
  | sat certificate => exact certificate.source_satisfiable
  | unsat refutation => exact refutation.source_unsatisfiable

/-! ## Mixed direct/Skolem-pair source projection -/

def NativeABox.SatisfiableWithMixed
    (abox : NativeABox Individual Concept Role)
    (direct : List (Clause Variable Concept Role))
    (pairs : List (SkolemPairSpec Variable Concept Role Function)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role)
      (value : Individual → Domain),
    Nonempty Domain ∧ abox.models I value ∧
      ∃ functions : SkolemInterp Domain Function,
        I.models direct ∧ ModelsSkolemPairs I functions pairs

structure WireMixedNativeABoxSatCertificate where
  functions : List String
  direct : List WireDirectSourceClause
  pairs : List WireSkolemPair
  certificate : WireNativeABoxSatCertificate
deriving FromJson, ToJson, Repr

structure DecodedMixedNativeABoxSatCertificate where
  certificate : DecodedNativeABoxSatCertificate
  variable_ge_two : 2 ≤ certificate.seed.variableCount
  functions : List String
  direct : List (Clause (Fin certificate.seed.variableCount)
    (Fin certificate.seed.abox.concepts.length)
    (Fin certificate.seed.abox.roles.length))
  pairs : List (SkolemPairSpec (Fin certificate.seed.variableCount)
    (Fin certificate.seed.abox.concepts.length)
    (Fin certificate.seed.abox.roles.length) (Fin functions.length))
  unique_functions : (skolemPairFunctions pairs).Nodup
  exact_projection :
    (skolemProjectionOntology direct pairs ++
      certificate.seed.abox.negativeRoleClausesAt certificate.seed.variableCount
        variable_ge_two).toFinset =
      certificate.seed.state.base.base.ontology.toFinset

def WireMixedNativeABoxSatCertificate.decode
    (wire : WireMixedNativeABoxSatCertificate) :
    Except String DecodedMixedNativeABoxSatCertificate := do
  let certificate ← wire.certificate.decode
  let variableWitness ← requireAtLeastTwoVariables certificate.seed.variableCount
  let hvariables := variableWitness.proof
  if _hfunctions : wire.functions.Nodup then
    let direct ← wire.direct.mapM (WireDirectSourceClause.decode
      certificate.seed.variableCount certificate.seed.abox.concepts
      certificate.seed.abox.roles)
    let pairs ← wire.pairs.mapM (WireSkolemPair.decode
      certificate.seed.variableCount certificate.seed.abox.concepts
      certificate.seed.abox.roles wire.functions)
    if hunique : (skolemPairFunctions pairs).Nodup then
      if hequal : (skolemProjectionOntology direct pairs ++
          certificate.seed.abox.negativeRoleClausesAt
            certificate.seed.variableCount hvariables).toFinset =
          certificate.seed.state.base.base.ontology.toFinset then
        return {
          certificate
          variable_ge_two := hvariables
          functions := wire.functions
          direct
          pairs
          unique_functions := hunique
          exact_projection := hequal
        }
      else throw "mixed source conversion differs from the native ABox SAT ontology"
    else throw "mixed native ABox SAT projection reuses a Skolem function"
  else throw "mixed native ABox function-name table contains duplicates"

def WireMixedNativeABoxSatCertificate.check
    (wire : WireMixedNativeABoxSatCertificate) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedMixedNativeABoxSatCertificate.source_satisfiable
    (decoded : DecodedMixedNativeABoxSatCertificate) :
    decoded.certificate.seed.abox.abox.SatisfiableWithMixed
      decoded.direct decoded.pairs := by
  rcases decoded.certificate.satisfiable with
    ⟨Domain, I, value, hdomain, htarget, habox⟩
  have happended : I.models (skolemProjectionOntology decoded.direct decoded.pairs ++
      decoded.certificate.seed.abox.negativeRoleClausesAt
        decoded.certificate.seed.variableCount decoded.variable_ge_two) :=
    (models_iff_of_toFinset_eq I _ _ decoded.exact_projection).2 htarget
  have hprojected : I.models
      (skolemProjectionOntology decoded.direct decoded.pairs) := by
    intro clause hclause
    exact happended clause (List.mem_append_left _ hclause)
  let fallback : Domain := Classical.choice hdomain
  let base : SkolemInterp Domain (Fin decoded.functions.length) :=
    { app := fun _ _ => fallback }
  rcases (mixedSkolemProjection_sat_iff I base decoded.direct decoded.pairs
      decoded.unique_functions).2 hprojected with
    ⟨functions, hdirect, hpairs⟩
  exact ⟨Domain, I, value, hdomain, habox, functions, hdirect, hpairs⟩

inductive WireMixedNativeABoxDecisionEvidence where
  | sat (certificate : WireMixedNativeABoxSatCertificate)
  | unsat (refutation : WireMixedNativeABoxRefutation)
deriving FromJson, ToJson, Repr

structure WireMixedNativeABoxDecisionCertificate where
  version : Nat
  evidence : WireMixedNativeABoxDecisionEvidence
deriving FromJson, ToJson, Repr

inductive DecodedMixedNativeABoxDecision where
  | sat (certificate : DecodedMixedNativeABoxSatCertificate)
  | unsat (refutation : DecodedMixedNativeABoxRefutation)

def WireMixedNativeABoxDecisionCertificate.decode
    (wire : WireMixedNativeABoxDecisionCertificate) :
    Except String DecodedMixedNativeABoxDecision := do
  if wire.version != 1 then
    throw s!"unsupported mixed native ABox source decision version {wire.version}"
  match wire.evidence with
  | .sat certificate => return .sat (← certificate.decode)
  | .unsat refutation => return .unsat (← refutation.decode)

def WireMixedNativeABoxDecisionCertificate.check
    (wire : WireMixedNativeABoxDecisionCertificate) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedMixedNativeABoxDecision.SemanticallyValid :
    DecodedMixedNativeABoxDecision → Prop
  | .sat certificate => certificate.certificate.seed.abox.abox.SatisfiableWithMixed
      certificate.direct certificate.pairs
  | .unsat refutation => ¬refutation.refutation.initial.seed.abox.abox.SatisfiableWithMixed
      refutation.direct refutation.pairs

theorem DecodedMixedNativeABoxDecision.semantic_valid
    (decoded : DecodedMixedNativeABoxDecision) : decoded.SemanticallyValid := by
  cases decoded with
  | sat certificate => exact certificate.source_satisfiable
  | unsat refutation => exact refutation.source_unsatisfiable

/-! ## Skolem-bundle source projection -/

def NativeABox.SatisfiableWithBundle
    (abox : NativeABox Individual TargetConcept Role)
    (sourceOf : TargetConcept → SourceConcept)
    (direct : List (Clause Variable SourceConcept Role))
    (bundles : Fin n → BundleSpec Variable SourceConcept Role Function) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain SourceConcept Role)
      (functions : SkolemInterp Domain Function) (value : Individual → Domain),
    Nonempty Domain ∧ I.models direct ∧ ModelsBundles I functions bundles ∧
      (abox.mapConcepts sourceOf).models I value

structure WireBundleNativeABoxSatCertificate where
  source_concepts : List String
  functions : List String
  direct : List WireDirectSourceClause
  bundles : List WireSkolemBundle
  domain_extras : List WireBundleDomainExtra
  abox_source_map : List Nat
  certificate : WireNativeABoxSatCertificate
deriving FromJson, ToJson, Repr

structure DecodedBundleNativeABoxSatCertificate where
  certificate : DecodedNativeABoxSatCertificate
  variable_ge_two : 2 ≤ certificate.seed.variableCount
  sourceConcepts : List String
  functions : List String
  sourceTargets : Fin sourceConcepts.length →
    Fin certificate.seed.abox.concepts.length
  direct : List (Clause (Fin certificate.seed.variableCount)
    (Fin sourceConcepts.length) (Fin certificate.seed.abox.roles.length))
  bundles : List (DecodedWireBundle (Fin certificate.seed.variableCount)
    (Fin sourceConcepts.length) (Fin certificate.seed.abox.roles.length)
    (Fin functions.length) (Fin certificate.seed.abox.concepts.length))
  domainExtras : List (IndexedBundleDomainSpec (Fin sourceConcepts.length)
    (Fin certificate.seed.abox.roles.length) bundles.length)
  nonemptyBundles : bundles ≠ []
  uniqueFunctions :
    (skolemPairFunctions (indexedBundlePairs (decodedBundleSpecs bundles))).Nodup
  embeddingInjective : Function.Injective
    (bundleConceptEmbedding sourceTargets bundles)
  rboxSource : Fin certificate.seed.variableCount
  rboxTarget : Fin certificate.seed.variableCount
  rboxDistinct : rboxSource ≠ rboxTarget
  pathPremises : ∀ spec ∈ domainExtras, ∀ clause ∈
    roleInclusionPathClauses
      (decodedBundleSpecs bundles spec.bundle).role spec.path rboxSource rboxTarget,
    clause ∈ direct
  domainPremises : ∀ spec ∈ domainExtras,
    roleDomainClause (spec.superRole (decodedBundleSpecs bundles)) spec.domain
      rboxSource rboxTarget ∈ direct
  sourceOf : Fin certificate.seed.abox.concepts.length → Fin sourceConcepts.length
  abox_embedded : ∀ individual concept,
    concept ∈ certificate.seed.abox.abox.proxies individual ++
      certificate.seed.abox.abox.assertions individual →
    bundleConceptEmbedding sourceTargets bundles (.inr (sourceOf concept)) = concept
  exact_ontology :
    (renameOntology (bundleConceptEmbedding sourceTargets bundles)
      (indexedBundleOntology direct (decodedBundleSpecs bundles) ++
        indexedBundleDomainOntology (decodedBundleSpecs bundles) domainExtras) ++
      certificate.seed.abox.negativeRoleClausesAt certificate.seed.variableCount
        variable_ge_two).toFinset =
      certificate.seed.state.base.base.ontology.toFinset

def WireBundleNativeABoxSatCertificate.decode
    (wire : WireBundleNativeABoxSatCertificate) :
    Except String DecodedBundleNativeABoxSatCertificate := do
  let certificate ← wire.certificate.decode
  let variableWitness ← requireAtLeastTwoVariables certificate.seed.variableCount
  let hvariables := variableWitness.proof
  if _hsourceConcepts : wire.source_concepts.Nodup then
    if _hfunctions : wire.functions.Nodup then
      let sourceTargets ← checkedNameEmbedding "source concept in target"
        wire.source_concepts certificate.seed.abox.concepts
      let direct ← wire.direct.mapM (WireDirectSourceClause.decode
        certificate.seed.variableCount wire.source_concepts
        certificate.seed.abox.roles)
      let bundles ← wire.bundles.mapM (WireSkolemBundle.decode
        certificate.seed.variableCount wire.source_concepts
        certificate.seed.abox.concepts certificate.seed.abox.roles wire.functions)
      if hnonempty : bundles ≠ [] then
        let rboxSource : Fin certificate.seed.variableCount :=
          ⟨0, lt_of_lt_of_le Nat.zero_lt_two hvariables⟩
        let rboxTarget : Fin certificate.seed.variableCount := ⟨1, hvariables⟩
        have hrboxDistinct : rboxSource ≠ rboxTarget := by
          intro hequal
          have hval := congrArg Fin.val hequal
          simp [rboxSource, rboxTarget] at hval
        let domainExtras ← wire.domain_extras.mapM
          (WireBundleDomainExtra.decode wire.source_concepts
            certificate.seed.abox.roles bundles.length)
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
                let sourceOf ← decodeConceptMap "native ABox source concept"
                  wire.source_concepts.length certificate.seed.abox.concepts.length
                  wire.abox_source_map
                if hembedded : certificate.seed.abox.abox.conceptsEmbeddedB sourceOf
                    (fun source => bundleConceptEmbedding sourceTargets bundles
                      (.inr source)) = true then
                  if hequal :
                      (renameOntology (bundleConceptEmbedding sourceTargets bundles)
                        (indexedBundleOntology direct (decodedBundleSpecs bundles) ++
                          indexedBundleDomainOntology
                            (decodedBundleSpecs bundles) domainExtras) ++
                        certificate.seed.abox.negativeRoleClausesAt
                          certificate.seed.variableCount hvariables).toFinset =
                        certificate.seed.state.base.base.ontology.toFinset then
                    return {
                      certificate
                      variable_ge_two := hvariables
                      sourceConcepts := wire.source_concepts
                      functions := wire.functions
                      sourceTargets
                      direct
                      bundles
                      domainExtras
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
                      sourceOf
                      abox_embedded := certificate.seed.abox.abox.conceptsEmbeddedB_sound
                        sourceOf (fun source =>
                          bundleConceptEmbedding sourceTargets bundles (.inr source))
                        hembedded
                      exact_ontology := hequal
                    }
                  else throw "bundle source conversion differs from the native ABox SAT ontology"
                else throw "native ABox concept is not an embedded bundle source concept"
              else throw "bundle domain premise is absent from the source ontology"
            else throw "bundle role-inclusion path is absent from the source ontology"
          else throw "bundle definers collide with each other or source concepts"
        else throw "bundle native ABox SAT projection reuses a Skolem function"
      else throw "bundle native ABox SAT projection contains no bundles"
    else throw "bundle native ABox function-name table contains duplicates"
  else throw "bundle native ABox source concept-name table contains duplicates"

def WireBundleNativeABoxSatCertificate.check
    (wire : WireBundleNativeABoxSatCertificate) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedBundleNativeABoxSatCertificate.source_satisfiable
    (decoded : DecodedBundleNativeABoxSatCertificate) :
    decoded.certificate.seed.abox.abox.SatisfiableWithBundle decoded.sourceOf
      decoded.direct (decodedBundleSpecs decoded.bundles) := by
  rcases decoded.certificate.satisfiable with
    ⟨Domain, J, value, hdomain, htarget, habox⟩
  let targetCore := renameOntology
    (bundleConceptEmbedding decoded.sourceTargets decoded.bundles)
    (indexedBundleOntology decoded.direct (decodedBundleSpecs decoded.bundles) ++
      indexedBundleDomainOntology (decodedBundleSpecs decoded.bundles)
        decoded.domainExtras)
  have happended : J.models (targetCore ++
      decoded.certificate.seed.abox.negativeRoleClausesAt
        decoded.certificate.seed.variableCount decoded.variable_ge_two) :=
    (models_iff_of_toFinset_eq J _ _ decoded.exact_ontology).2 htarget
  have hcore : J.models targetCore := by
    intro clause hclause
    exact happended clause (List.mem_append_left _ hclause)
  let projection : DecodedBundleProjection := {
    variableCount := decoded.certificate.seed.variableCount
    sourceConcepts := decoded.sourceConcepts
    concepts := decoded.certificate.seed.abox.concepts
    roles := decoded.certificate.seed.abox.roles
    functions := decoded.functions
    sourceTargets := decoded.sourceTargets
    direct := decoded.direct
    bundles := decoded.bundles
    domainExtras := decoded.domainExtras
    target := targetCore
    nonemptyBundles := decoded.nonemptyBundles
    uniqueFunctions := decoded.uniqueFunctions
    embeddingInjective := decoded.embeddingInjective
    rboxSource := decoded.rboxSource
    rboxTarget := decoded.rboxTarget
    rboxDistinct := decoded.rboxDistinct
    pathPremises := decoded.pathPremises
    domainPremises := decoded.domainPremises
    exactProjection := rfl
  }
  let fallback : Domain := Classical.choice hdomain
  let base : SkolemInterp Domain (Fin decoded.functions.length) :=
    { app := fun _ _ => fallback }
  rcases projection.target_model_to_source_model_preserving_nativeABox
      decoded.certificate.seed.abox.abox decoded.sourceOf decoded.abox_embedded
      J base value hcore habox with
    ⟨I, functions, hdirect, hbundles, haboxSource⟩
  exact ⟨Domain, I, functions, value, hdomain, hdirect, hbundles, haboxSource⟩

inductive WireBundleNativeABoxDecisionEvidence where
  | sat (certificate : WireBundleNativeABoxSatCertificate)
  | unsat (refutation : WireBundleNativeABoxRefutation)
deriving FromJson, ToJson, Repr

structure WireBundleNativeABoxDecisionCertificate where
  version : Nat
  evidence : WireBundleNativeABoxDecisionEvidence
deriving FromJson, ToJson, Repr

inductive DecodedBundleNativeABoxDecision where
  | sat (certificate : DecodedBundleNativeABoxSatCertificate)
  | unsat (refutation : DecodedBundleNativeABoxRefutation)

def WireBundleNativeABoxDecisionCertificate.decode
    (wire : WireBundleNativeABoxDecisionCertificate) :
    Except String DecodedBundleNativeABoxDecision := do
  if wire.version != 1 then
    throw s!"unsupported bundle native ABox source decision version {wire.version}"
  match wire.evidence with
  | .sat certificate => return .sat (← certificate.decode)
  | .unsat refutation => return .unsat (← refutation.decode)

def WireBundleNativeABoxDecisionCertificate.check
    (wire : WireBundleNativeABoxDecisionCertificate) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedBundleNativeABoxDecision.SemanticallyValid :
    DecodedBundleNativeABoxDecision → Prop
  | .sat certificate => certificate.certificate.seed.abox.abox.SatisfiableWithBundle
      certificate.sourceOf certificate.direct
        (decodedBundleSpecs certificate.bundles)
  | .unsat refutation =>
      ¬refutation.refutation.initial.seed.abox.abox.SatisfiableWithBundle
        refutation.sourceOf refutation.direct (decodedBundleSpecs refutation.bundles)

theorem DecodedBundleNativeABoxDecision.semantic_valid
    (decoded : DecodedBundleNativeABoxDecision) : decoded.SemanticallyValid := by
  cases decoded with
  | sat certificate => exact certificate.source_satisfiable
  | unsat refutation => exact refutation.source_unsatisfiable

#print axioms DecodedDirectNativeABoxSatCertificate.source_satisfiable
#print axioms DecodedDirectNativeABoxDecision.semantic_valid
#print axioms DecodedMixedNativeABoxSatCertificate.source_satisfiable
#print axioms DecodedMixedNativeABoxDecision.semantic_valid
#print axioms DecodedBundleNativeABoxSatCertificate.source_satisfiable
#print axioms DecodedBundleNativeABoxDecision.semantic_valid

end ContextCalculus.Hypertableau
