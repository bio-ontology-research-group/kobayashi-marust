import ContextCalculus.HypertableauNativeABoxModelWire
import ContextCalculus.HypertableauNativeABoxProjectionWire

/-!
# Source-composed native-ABox cardinality decisions

The target cardinality model and source projection must be checked as one
document.  In particular, every complementary frontend pair must be covered by
the exact-cardinality checks carried by the finite quotient certificate.
-/

namespace ContextCalculus.Hypertableau

open Lean

def NativeABox.SatisfiableWithProjectedCardinality
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (pairs : List (PairedCardinality Concept Role)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role)
      (value : Individual → Domain),
    Nonempty Domain ∧ I.models ontology ∧
      I.modelsProjectedCardinalityDefs definitions pairs ∧ abox.models I value

/-! ## Direct projection -/

structure WireDirectNativeABoxCardinalitySatCertificate where
  source : List WireDirectSourceClause
  target : List WireClause
  definitions : List WireProjectionCardinalityDef
  exact_pairs : List WireComplementaryCardinalityPair
  certificate : WireNativeABoxCardinalitySatCertificate
deriving FromJson, ToJson, Repr

structure DecodedNativeDirectCardinalitySatProjection
    (certificate : DecodedNativeABoxCardinalitySatCertificate) where
  source : List (Clause (Fin certificate.seed.variableCount)
    (Fin certificate.seed.abox.concepts.length)
    (Fin certificate.seed.abox.roles.length))
  target : List (Clause (Fin certificate.seed.variableCount)
    (Fin certificate.seed.abox.concepts.length)
    (Fin certificate.seed.abox.roles.length))
  exactProjection : source.toFinset = target.toFinset
  definitionWires : List WireProjectionCardinalityDef
  wireLength : definitionWires.length = certificate.definitions.length
  uniqueDefinitions : certificate.definitions.Nodup
  pairs : List (IndexedComplementaryCardinalityPair certificate.definitions)
  uniquePairIndices : (exactPairIndices pairs).Nodup
  exactFlags : ∀ index : Fin certificate.definitions.length,
    (definitionWires.get (wireLength.symm ▸ index)).exact =
      decide (index.val ∈ exactPairIndices pairs)

def DecodedNativeDirectCardinalitySatProjection.semanticPairs
    {certificate : DecodedNativeABoxCardinalitySatCertificate}
    (projection : DecodedNativeDirectCardinalitySatProjection certificate) :
    List (PairedCardinality
      (Fin certificate.seed.abox.concepts.length)
      (Fin certificate.seed.abox.roles.length)) :=
  projection.pairs.map IndexedComplementaryCardinalityPair.toPair

theorem DecodedNativeDirectCardinalitySatProjection.semanticPairs_mem
    {certificate : DecodedNativeABoxCardinalitySatCertificate}
    (projection : DecodedNativeDirectCardinalitySatProjection certificate)
    (pair : PairedCardinality
      (Fin certificate.seed.abox.concepts.length)
      (Fin certificate.seed.abox.roles.length))
    (hpair : pair ∈ projection.semanticPairs) :
    pair.maximum ∈ certificate.definitions ∧
      pair.minimum ∈ certificate.definitions := by
  simp only [DecodedNativeDirectCardinalitySatProjection.semanticPairs,
    List.mem_map] at hpair
  rcases hpair with ⟨indexed, _, rfl⟩
  exact ⟨List.get_mem certificate.definitions indexed.maximum,
    List.get_mem certificate.definitions indexed.minimum⟩

theorem DecodedNativeDirectCardinalitySatProjection.models_source_iff_target
    {certificate : DecodedNativeABoxCardinalitySatCertificate}
    (projection : DecodedNativeDirectCardinalitySatProjection certificate)
    (I : Interp Domain (Fin certificate.seed.abox.concepts.length)
      (Fin certificate.seed.abox.roles.length)) :
    (I.models projection.source ∧
      I.modelsProjectedCardinalityDefs certificate.definitions
        projection.semanticPairs) ↔
    (I.models projection.target ∧
      I.modelsPairedCardinalityTargets certificate.definitions
        projection.semanticPairs) := by
  have hdirect : I.models projection.source ↔ I.models projection.target :=
    models_iff_of_toFinset_eq I projection.source projection.target
      projection.exactProjection
  rw [hdirect]
  exact and_congr_right fun _ =>
    modelsProjectedCardinalityDefs_iff_pairedTargets I certificate.definitions
      projection.semanticPairs
      (fun pair hpair => projection.semanticPairs_mem pair hpair)

structure DecodedDirectNativeABoxCardinalitySatCertificate where
  certificate : DecodedNativeABoxCardinalitySatCertificate
  variable_ge_two : 2 ≤ certificate.seed.variableCount
  projection : DecodedNativeDirectCardinalitySatProjection certificate
  exact_pair_coverage : ∀ pair ∈ projection.semanticPairs,
    pair.maximum ∈ certificate.exactDefinitions ∧
      pair.minimum ∈ certificate.exactDefinitions
  exact_ontology : projection.target ++
      certificate.seed.abox.negativeRoleClausesAt
        certificate.seed.variableCount variable_ge_two =
    certificate.seed.state.base.base.ontology

def WireDirectNativeABoxCardinalitySatCertificate.decode
    (wire : WireDirectNativeABoxCardinalitySatCertificate) :
    Except String DecodedDirectNativeABoxCardinalitySatCertificate := do
  let certificate ← wire.certificate.decode
  let variableWitness ← requireAtLeastTwoVariables certificate.seed.variableCount
  let hvariables := variableWitness.proof
  let source ← wire.source.mapM (WireDirectSourceClause.decode
    certificate.seed.variableCount certificate.seed.abox.concepts
    certificate.seed.abox.roles)
  let target ← wire.target.mapM (WireClause.decode
    certificate.seed.variableCount certificate.seed.abox.concepts.length
    certificate.seed.abox.roles.length)
  if hprojection : source.toFinset = target.toFinset then
    let definitions ← wire.definitions.mapM (WireProjectionCardinalityDef.decode
      certificate.seed.abox.concepts.length certificate.seed.abox.roles.length)
    if hdefinitions : definitions = certificate.definitions then
      if hlength : wire.definitions.length = certificate.definitions.length then
        if hunique : certificate.definitions.Nodup then
          let pairs ← wire.exact_pairs.mapM
            (WireComplementaryCardinalityPair.decode certificate.definitions)
          if hpairs : (exactPairIndices pairs).Nodup then
            if hflags : ∀ index : Fin certificate.definitions.length,
                (wire.definitions.get (hlength.symm ▸ index)).exact =
                  decide (index.val ∈ exactPairIndices pairs) then
              let projection : DecodedNativeDirectCardinalitySatProjection certificate := {
                source
                target
                exactProjection := hprojection
                definitionWires := wire.definitions
                wireLength := hlength
                uniqueDefinitions := hunique
                pairs
                uniquePairIndices := hpairs
                exactFlags := hflags
              }
              if hcoverage : ∀ pair ∈ projection.semanticPairs,
                  pair.maximum ∈ certificate.exactDefinitions ∧
                    pair.minimum ∈ certificate.exactDefinitions then
                if hontology : projection.target ++
                    certificate.seed.abox.negativeRoleClausesAt
                      certificate.seed.variableCount hvariables =
                    certificate.seed.state.base.base.ontology then
                  return {
                    certificate
                    variable_ge_two := hvariables
                    projection
                    exact_pair_coverage := hcoverage
                    exact_ontology := hontology
                  }
                else throw "direct cardinality target differs from the native ABox SAT ontology"
              else throw "frontend exact pair is absent from the checked quotient exact definitions"
            else throw "cardinality exact flags differ from checked complementary-pair provenance"
          else throw "an exact cardinality definition occurs in more than one complementary pair"
        else throw "cardinality projection contains duplicate definitions"
      else throw "internal cardinality-definition decode length mismatch"
    else throw "direct cardinality definitions differ from the native ABox SAT certificate"
  else throw "direct residual conversion differs from the claimed HT ontology"

def WireDirectNativeABoxCardinalitySatCertificate.check
    (wire : WireDirectNativeABoxCardinalitySatCertificate) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedDirectNativeABoxCardinalitySatCertificate.source_satisfiable
    (decoded : DecodedDirectNativeABoxCardinalitySatCertificate) :
    decoded.certificate.seed.abox.abox.SatisfiableWithProjectedCardinality
      decoded.projection.source decoded.certificate.definitions
      decoded.projection.semanticPairs := by
  rcases decoded.certificate.canonical_model with
    ⟨value, hdomain, htarget, hdefinitions, habox⟩
  let I := decoded.certificate.seed.state.base.state.quotientCanonical
  have happended : I.models (decoded.projection.target ++
      decoded.certificate.seed.abox.negativeRoleClausesAt
        decoded.certificate.seed.variableCount decoded.variable_ge_two) := by
    simpa only [decoded.exact_ontology] using htarget
  have htargetCore : I.models decoded.projection.target := by
    intro clause hclause
    exact happended clause (List.mem_append_left _ hclause)
  have hexact := decoded.certificate.models_exact_definitions
  have hpairs : I.modelsPairedCardinalityTargets decoded.certificate.definitions
      decoded.projection.semanticPairs := by
    refine ⟨hdefinitions, ?_⟩
    intro pair hpair
    exact ⟨hexact pair.maximum (decoded.exact_pair_coverage pair hpair).1,
      hexact pair.minimum (decoded.exact_pair_coverage pair hpair).2⟩
  have hsource :=
    (decoded.projection.models_source_iff_target I).2 ⟨htargetCore, hpairs⟩
  exact ⟨decoded.certificate.seed.state.base.state.QuotientDomain,
    I, value, hdomain, hsource.1, hsource.2, habox⟩

inductive WireDirectNativeABoxCardinalityDecisionEvidence where
  | sat (certificate : WireDirectNativeABoxCardinalitySatCertificate)
  | unsat (refutation : WireDirectNativeABoxCardinalityRefutation)
deriving FromJson, ToJson, Repr

structure WireDirectNativeABoxCardinalityDecisionCertificate where
  version : Nat
  evidence : WireDirectNativeABoxCardinalityDecisionEvidence
deriving FromJson, ToJson, Repr

inductive DecodedDirectNativeABoxCardinalityDecision where
  | sat (certificate : DecodedDirectNativeABoxCardinalitySatCertificate)
  | unsat (refutation : DecodedDirectNativeABoxCardinalityRefutation)

def WireDirectNativeABoxCardinalityDecisionCertificate.decode
    (wire : WireDirectNativeABoxCardinalityDecisionCertificate) :
    Except String DecodedDirectNativeABoxCardinalityDecision := do
  if wire.version != 1 then
    throw s!"unsupported direct native ABox cardinality source decision version {wire.version}"
  match wire.evidence with
  | .sat certificate => return .sat (← certificate.decode)
  | .unsat refutation => return .unsat (← refutation.decode)

def WireDirectNativeABoxCardinalityDecisionCertificate.check
    (wire : WireDirectNativeABoxCardinalityDecisionCertificate) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedDirectNativeABoxCardinalityDecision.SemanticallyValid :
    DecodedDirectNativeABoxCardinalityDecision → Prop
  | .sat certificate =>
      certificate.certificate.seed.abox.abox.SatisfiableWithProjectedCardinality
        certificate.projection.source certificate.certificate.definitions
        certificate.projection.semanticPairs
  | .unsat refutation =>
      ¬refutation.refutation.initial.initial.seed.abox.abox.SatisfiableWithProjectedCardinality
        refutation.projection.source refutation.refutation.definitions
        refutation.projection.semanticPairs

theorem DecodedDirectNativeABoxCardinalityDecision.semantic_valid
    (decoded : DecodedDirectNativeABoxCardinalityDecision) :
    decoded.SemanticallyValid := by
  cases decoded with
  | sat certificate => exact certificate.source_satisfiable
  | unsat refutation => exact refutation.source_unsatisfiable

/-! ## Mixed direct and Skolem-pair projection -/

def NativeABox.SatisfiableWithMixedProjectedCardinality
    (abox : NativeABox Individual Concept Role)
    (direct : List (Clause Variable Concept Role))
    (pairs : List (SkolemPairSpec Variable Concept Role Function))
    (definitions : List (CardinalityDef Concept Role))
    (cardinalityPairs : List (PairedCardinality Concept Role)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role)
      (value : Individual → Domain),
    Nonempty Domain ∧ abox.models I value ∧
      (∃ functions : SkolemInterp Domain Function,
        I.models direct ∧ ModelsSkolemPairs I functions pairs) ∧
      I.modelsProjectedCardinalityDefs definitions cardinalityPairs

structure WireMixedNativeABoxCardinalitySatCertificate where
  functions : List String
  direct : List WireDirectSourceClause
  pairs : List WireSkolemPair
  definitions : List WireProjectionCardinalityDef
  exact_pairs : List WireComplementaryCardinalityPair
  certificate : WireNativeABoxCardinalitySatCertificate
deriving FromJson, ToJson, Repr

structure DecodedMixedNativeABoxCardinalitySatCertificate where
  certificate : DecodedNativeABoxCardinalitySatCertificate
  variable_ge_two : 2 ≤ certificate.seed.variableCount
  functions : List String
  direct : List (Clause (Fin certificate.seed.variableCount)
    (Fin certificate.seed.abox.concepts.length)
    (Fin certificate.seed.abox.roles.length))
  pairs : List (SkolemPairSpec (Fin certificate.seed.variableCount)
    (Fin certificate.seed.abox.concepts.length)
    (Fin certificate.seed.abox.roles.length) (Fin functions.length))
  unique_functions : (skolemPairFunctions pairs).Nodup
  definitionWires : List WireProjectionCardinalityDef
  wireLength : definitionWires.length = certificate.definitions.length
  uniqueDefinitions : certificate.definitions.Nodup
  cardinalityPairs : List
    (IndexedComplementaryCardinalityPair certificate.definitions)
  uniquePairIndices : (exactPairIndices cardinalityPairs).Nodup
  exactFlags : ∀ index : Fin certificate.definitions.length,
    (definitionWires.get (wireLength.symm ▸ index)).exact =
      decide (index.val ∈ exactPairIndices cardinalityPairs)
  exact_pair_coverage : ∀ pair ∈
      cardinalityPairs.map IndexedComplementaryCardinalityPair.toPair,
    pair.maximum ∈ certificate.exactDefinitions ∧
      pair.minimum ∈ certificate.exactDefinitions
  exact_projection :
    (skolemProjectionOntology direct pairs ++
      certificate.seed.abox.negativeRoleClausesAt
        certificate.seed.variableCount variable_ge_two).toFinset =
      certificate.seed.state.base.base.ontology.toFinset

def DecodedMixedNativeABoxCardinalitySatCertificate.semanticPairs
    (decoded : DecodedMixedNativeABoxCardinalitySatCertificate) :
    List (PairedCardinality
      (Fin decoded.certificate.seed.abox.concepts.length)
      (Fin decoded.certificate.seed.abox.roles.length)) :=
  decoded.cardinalityPairs.map IndexedComplementaryCardinalityPair.toPair

theorem DecodedMixedNativeABoxCardinalitySatCertificate.semanticPairs_mem
    (decoded : DecodedMixedNativeABoxCardinalitySatCertificate)
    (pair : PairedCardinality
      (Fin decoded.certificate.seed.abox.concepts.length)
      (Fin decoded.certificate.seed.abox.roles.length))
    (hpair : pair ∈ decoded.semanticPairs) :
    pair.maximum ∈ decoded.certificate.definitions ∧
      pair.minimum ∈ decoded.certificate.definitions := by
  simp only [DecodedMixedNativeABoxCardinalitySatCertificate.semanticPairs,
    List.mem_map] at hpair
  rcases hpair with ⟨indexed, _, rfl⟩
  exact ⟨List.get_mem decoded.certificate.definitions indexed.maximum,
    List.get_mem decoded.certificate.definitions indexed.minimum⟩

def WireMixedNativeABoxCardinalitySatCertificate.decode
    (wire : WireMixedNativeABoxCardinalitySatCertificate) :
    Except String DecodedMixedNativeABoxCardinalitySatCertificate := do
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
      let definitions ← wire.definitions.mapM
        (WireProjectionCardinalityDef.decode certificate.seed.abox.concepts.length
          certificate.seed.abox.roles.length)
      if _hdefinitions : definitions = certificate.definitions then
        if hlength : wire.definitions.length = certificate.definitions.length then
          if hdefinitionUnique : certificate.definitions.Nodup then
            let cardinalityPairs ← wire.exact_pairs.mapM
              (WireComplementaryCardinalityPair.decode certificate.definitions)
            if hpairs : (exactPairIndices cardinalityPairs).Nodup then
              if hflags : ∀ index : Fin certificate.definitions.length,
                  (wire.definitions.get (hlength.symm ▸ index)).exact =
                    decide (index.val ∈ exactPairIndices cardinalityPairs) then
                let semanticPairs := cardinalityPairs.map
                  IndexedComplementaryCardinalityPair.toPair
                if hcoverage : ∀ pair ∈ semanticPairs,
                    pair.maximum ∈ certificate.exactDefinitions ∧
                      pair.minimum ∈ certificate.exactDefinitions then
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
                      definitionWires := wire.definitions
                      wireLength := hlength
                      uniqueDefinitions := hdefinitionUnique
                      cardinalityPairs
                      uniquePairIndices := hpairs
                      exactFlags := hflags
                      exact_pair_coverage := hcoverage
                      exact_projection := hequal
                    }
                  else throw "mixed source conversion differs from the native ABox cardinality SAT ontology"
                else throw "frontend exact pair is absent from the checked quotient exact definitions"
              else throw "cardinality exact flags differ from checked complementary-pair provenance"
            else throw "an exact cardinality definition occurs in more than one complementary pair"
          else throw "cardinality projection contains duplicate definitions"
        else throw "internal cardinality-definition decode length mismatch"
      else throw "mixed cardinality definitions differ from the native ABox SAT certificate"
    else throw "mixed native ABox projection reuses a Skolem function"
  else throw "mixed native ABox function-name table contains duplicates"

def WireMixedNativeABoxCardinalitySatCertificate.check
    (wire : WireMixedNativeABoxCardinalitySatCertificate) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedMixedNativeABoxCardinalitySatCertificate.source_satisfiable
    (decoded : DecodedMixedNativeABoxCardinalitySatCertificate) :
    decoded.certificate.seed.abox.abox.SatisfiableWithMixedProjectedCardinality
      decoded.direct decoded.pairs decoded.certificate.definitions
      decoded.semanticPairs := by
  rcases decoded.certificate.canonical_model with
    ⟨value, hdomain, htarget, hdefinitions, habox⟩
  let I := decoded.certificate.seed.state.base.state.quotientCanonical
  have happended : I.models (skolemProjectionOntology decoded.direct decoded.pairs ++
      decoded.certificate.seed.abox.negativeRoleClausesAt
        decoded.certificate.seed.variableCount decoded.variable_ge_two) :=
    (models_iff_of_toFinset_eq I _ _ decoded.exact_projection).2 htarget
  have hprojected : I.models (skolemProjectionOntology decoded.direct decoded.pairs) := by
    intro clause hclause
    exact happended clause (List.mem_append_left _ hclause)
  have hexact := decoded.certificate.models_exact_definitions
  have hpairs : I.modelsPairedCardinalityTargets decoded.certificate.definitions
      decoded.semanticPairs := by
    refine ⟨hdefinitions, ?_⟩
    intro pair hpair
    exact ⟨hexact pair.maximum (decoded.exact_pair_coverage pair hpair).1,
      hexact pair.minimum (decoded.exact_pair_coverage pair hpair).2⟩
  letI : Nonempty decoded.certificate.seed.state.base.state.QuotientDomain := hdomain
  let base : SkolemInterp
      decoded.certificate.seed.state.base.state.QuotientDomain
      (Fin decoded.functions.length) :=
    ⟨fun _ _ => Classical.choice hdomain⟩
  rcases (mixedSkolemProjection_sat_iff I base decoded.direct decoded.pairs
    decoded.unique_functions).2 hprojected with ⟨functions, hdirect, hskolem⟩
  have hsourceCardinality :=
    (modelsProjectedCardinalityDefs_iff_pairedTargets I
      decoded.certificate.definitions decoded.semanticPairs
      (fun pair hpair => decoded.semanticPairs_mem pair hpair)).2 hpairs
  exact ⟨decoded.certificate.seed.state.base.state.QuotientDomain,
    I, value, hdomain, habox, ⟨functions, hdirect, hskolem⟩,
    hsourceCardinality⟩

inductive WireMixedNativeABoxCardinalityDecisionEvidence where
  | sat (certificate : WireMixedNativeABoxCardinalitySatCertificate)
  | unsat (refutation : WireMixedNativeABoxCardinalityRefutation)
deriving FromJson, ToJson, Repr

structure WireMixedNativeABoxCardinalityDecisionCertificate where
  version : Nat
  evidence : WireMixedNativeABoxCardinalityDecisionEvidence
deriving FromJson, ToJson, Repr

inductive DecodedMixedNativeABoxCardinalityDecision where
  | sat (certificate : DecodedMixedNativeABoxCardinalitySatCertificate)
  | unsat (refutation : DecodedMixedNativeABoxCardinalityRefutation)

def WireMixedNativeABoxCardinalityDecisionCertificate.decode
    (wire : WireMixedNativeABoxCardinalityDecisionCertificate) :
    Except String DecodedMixedNativeABoxCardinalityDecision := do
  if wire.version != 1 then
    throw s!"unsupported mixed native ABox cardinality source decision version {wire.version}"
  match wire.evidence with
  | .sat certificate => return .sat (← certificate.decode)
  | .unsat refutation => return .unsat (← refutation.decode)

def WireMixedNativeABoxCardinalityDecisionCertificate.check
    (wire : WireMixedNativeABoxCardinalityDecisionCertificate) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedMixedNativeABoxCardinalityDecision.SemanticallyValid :
    DecodedMixedNativeABoxCardinalityDecision → Prop
  | .sat certificate =>
      certificate.certificate.seed.abox.abox.SatisfiableWithMixedProjectedCardinality
        certificate.direct certificate.pairs certificate.certificate.definitions
        certificate.semanticPairs
  | .unsat refutation =>
      ¬refutation.refutation.initial.initial.seed.abox.abox.SatisfiableWithMixedProjectedCardinality
        refutation.direct refutation.pairs refutation.refutation.definitions
        refutation.semanticPairs

theorem DecodedMixedNativeABoxCardinalityDecision.semantic_valid
    (decoded : DecodedMixedNativeABoxCardinalityDecision) :
    decoded.SemanticallyValid := by
  cases decoded with
  | sat certificate => exact certificate.source_satisfiable
  | unsat refutation => exact refutation.source_unsatisfiable

/-! ## Bundle, RBox, and definer projection -/

def NativeABox.SatisfiableWithBundleProjectedCardinality
    (abox : NativeABox Individual TargetConcept Role)
    (sourceOf : TargetConcept → SourceConcept)
    (direct : List (Clause Variable SourceConcept Role))
    (bundles : Fin n → BundleSpec Variable SourceConcept Role Function)
    (definitions : List (CardinalityDef SourceConcept Role))
    (pairs : List (PairedCardinality SourceConcept Role)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain SourceConcept Role)
      (functions : SkolemInterp Domain Function) (value : Individual → Domain),
    Nonempty Domain ∧ I.models direct ∧ ModelsBundles I functions bundles ∧
      (abox.mapConcepts sourceOf).models I value ∧
      I.modelsProjectedCardinalityDefs definitions pairs

structure WireBundleNativeABoxCardinalitySatCertificate where
  source_concepts : List String
  functions : List String
  direct : List WireDirectSourceClause
  bundles : List WireSkolemBundle
  domain_extras : List WireBundleDomainExtra
  definitions : List WireProjectionCardinalityDef
  exact_pairs : List WireComplementaryCardinalityPair
  abox_source_map : List Nat
  certificate : WireNativeABoxCardinalitySatCertificate
deriving FromJson, ToJson, Repr

structure DecodedBundleNativeABoxCardinalitySatCertificate where
  certificate : DecodedNativeABoxCardinalitySatCertificate
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
  definitions : List (CardinalityDef (Fin sourceConcepts.length)
    (Fin certificate.seed.abox.roles.length))
  definitionWires : List WireProjectionCardinalityDef
  wireLength : definitionWires.length = definitions.length
  uniqueDefinitions : definitions.Nodup
  cardinalityPairs : List (IndexedComplementaryCardinalityPair definitions)
  uniquePairIndices : (exactPairIndices cardinalityPairs).Nodup
  exactFlags : ∀ index : Fin definitions.length,
    (definitionWires.get (wireLength.symm ▸ index)).exact =
      decide (index.val ∈ exactPairIndices cardinalityPairs)
  definitions_equal :
    ((definitions.map (renameCardinalityDef Sum.inr)).map
      (renameCardinalityDef (bundleConceptEmbedding sourceTargets bundles))) =
      certificate.definitions
  exact_pair_coverage : ∀ pair ∈
      cardinalityPairs.map IndexedComplementaryCardinalityPair.toPair,
    renameCardinalityDef (bundleConceptEmbedding sourceTargets bundles)
        (renameCardinalityDef Sum.inr pair.maximum) ∈ certificate.exactDefinitions ∧
      renameCardinalityDef (bundleConceptEmbedding sourceTargets bundles)
        (renameCardinalityDef Sum.inr pair.minimum) ∈ certificate.exactDefinitions
  exact_ontology :
    (renameOntology (bundleConceptEmbedding sourceTargets bundles)
      (indexedBundleOntology direct (decodedBundleSpecs bundles) ++
        indexedBundleDomainOntology (decodedBundleSpecs bundles) domainExtras) ++
      certificate.seed.abox.negativeRoleClausesAt certificate.seed.variableCount
        variable_ge_two).toFinset =
      certificate.seed.state.base.base.ontology.toFinset

def DecodedBundleNativeABoxCardinalitySatCertificate.semanticPairs
    (decoded : DecodedBundleNativeABoxCardinalitySatCertificate) :
    List (PairedCardinality (Fin decoded.sourceConcepts.length)
      (Fin decoded.certificate.seed.abox.roles.length)) :=
  decoded.cardinalityPairs.map IndexedComplementaryCardinalityPair.toPair

theorem DecodedBundleNativeABoxCardinalitySatCertificate.semanticPairs_mem
    (decoded : DecodedBundleNativeABoxCardinalitySatCertificate)
    (pair : PairedCardinality (Fin decoded.sourceConcepts.length)
      (Fin decoded.certificate.seed.abox.roles.length))
    (hpair : pair ∈ decoded.semanticPairs) :
    pair.maximum ∈ decoded.definitions ∧ pair.minimum ∈ decoded.definitions := by
  simp only [DecodedBundleNativeABoxCardinalitySatCertificate.semanticPairs,
    List.mem_map] at hpair
  rcases hpair with ⟨indexed, _, rfl⟩
  exact ⟨List.get_mem decoded.definitions indexed.maximum,
    List.get_mem decoded.definitions indexed.minimum⟩

def WireBundleNativeABoxCardinalitySatCertificate.decode
    (wire : WireBundleNativeABoxCardinalitySatCertificate) :
    Except String DecodedBundleNativeABoxCardinalitySatCertificate := do
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
                  let definitions ← wire.definitions.mapM
                    (WireProjectionCardinalityDef.decode wire.source_concepts.length
                      certificate.seed.abox.roles.length)
                  if hlength : wire.definitions.length = definitions.length then
                    if hdefinitionUnique : definitions.Nodup then
                      let cardinalityPairs ← wire.exact_pairs.mapM
                        (WireComplementaryCardinalityPair.decode definitions)
                      if hpairs : (exactPairIndices cardinalityPairs).Nodup then
                        if hflags : ∀ index : Fin definitions.length,
                            (wire.definitions.get (hlength.symm ▸ index)).exact =
                              decide (index.val ∈ exactPairIndices cardinalityPairs) then
                          if hdefinitions :
                              ((definitions.map (renameCardinalityDef Sum.inr)).map
                                (renameCardinalityDef
                                  (bundleConceptEmbedding sourceTargets bundles))) =
                                certificate.definitions then
                            let semanticPairs := cardinalityPairs.map
                              IndexedComplementaryCardinalityPair.toPair
                            if hcoverage : ∀ pair ∈ semanticPairs,
                                renameCardinalityDef
                                    (bundleConceptEmbedding sourceTargets bundles)
                                    (renameCardinalityDef Sum.inr pair.maximum) ∈
                                  certificate.exactDefinitions ∧
                                renameCardinalityDef
                                    (bundleConceptEmbedding sourceTargets bundles)
                                    (renameCardinalityDef Sum.inr pair.minimum) ∈
                                  certificate.exactDefinitions then
                              if hequal :
                                  (renameOntology
                                    (bundleConceptEmbedding sourceTargets bundles)
                                    (indexedBundleOntology direct
                                        (decodedBundleSpecs bundles) ++
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
                                      bundleConceptEmbedding sourceTargets bundles
                                        (.inr source)) hembedded
                                  definitions
                                  definitionWires := wire.definitions
                                  wireLength := hlength
                                  uniqueDefinitions := hdefinitionUnique
                                  cardinalityPairs
                                  uniquePairIndices := hpairs
                                  exactFlags := hflags
                                  definitions_equal := hdefinitions
                                  exact_pair_coverage := hcoverage
                                  exact_ontology := hequal
                                }
                              else throw "bundle source conversion differs from the native ABox cardinality SAT ontology"
                            else throw "frontend exact pair is absent from the checked quotient exact definitions"
                          else throw "bundle cardinality definitions differ from the native ABox SAT certificate"
                        else throw "cardinality exact flags differ from checked complementary-pair provenance"
                      else throw "an exact cardinality definition occurs in more than one complementary pair"
                    else throw "cardinality projection contains duplicate definitions"
                  else throw "internal cardinality-definition decode length mismatch"
                else throw "native ABox concept is not an embedded bundle source concept"
              else throw "bundle domain premise is absent from the source ontology"
            else throw "bundle role-inclusion path is absent from the source ontology"
          else throw "bundle definers collide with each other or source concepts"
        else throw "bundle native ABox cardinality SAT projection reuses a Skolem function"
      else throw "bundle native ABox cardinality SAT projection contains no bundles"
    else throw "bundle native ABox function-name table contains duplicates"
  else throw "bundle native ABox source concept-name table contains duplicates"

def WireBundleNativeABoxCardinalitySatCertificate.check
    (wire : WireBundleNativeABoxCardinalitySatCertificate) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedBundleNativeABoxCardinalitySatCertificate.source_satisfiable
    (decoded : DecodedBundleNativeABoxCardinalitySatCertificate) :
    decoded.certificate.seed.abox.abox.SatisfiableWithBundleProjectedCardinality
      decoded.sourceOf decoded.direct (decodedBundleSpecs decoded.bundles)
      decoded.definitions decoded.semanticPairs := by
  rcases decoded.certificate.canonical_model with
    ⟨value, hdomain, htarget, hdefinitions, habox⟩
  let J := decoded.certificate.seed.state.base.state.quotientCanonical
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
  have hexact := decoded.certificate.models_exact_definitions
  have htargetPairs : J.modelsPairedCardinalityTargets
      ((decoded.definitions.map (renameCardinalityDef Sum.inr)).map
        (renameCardinalityDef
          (bundleConceptEmbedding decoded.sourceTargets decoded.bundles)))
      ((decoded.semanticPairs.map (renamePairedCardinality Sum.inr)).map
        (renamePairedCardinality
          (bundleConceptEmbedding decoded.sourceTargets decoded.bundles))) := by
    refine ⟨?_, ?_⟩
    · rw [decoded.definitions_equal]
      exact hdefinitions
    · intro pair hpair
      simp only [List.mem_map] at hpair
      rcases hpair with ⟨intermediate, hintermediate, rfl⟩
      rcases hintermediate with ⟨sourcePair, hsourcePair, rfl⟩
      exact ⟨hexact _ (decoded.exact_pair_coverage sourcePair hsourcePair).1,
        hexact _ (decoded.exact_pair_coverage sourcePair hsourcePair).2⟩
  letI : Nonempty decoded.certificate.seed.state.base.state.QuotientDomain := hdomain
  let base : SkolemInterp
      decoded.certificate.seed.state.base.state.QuotientDomain
      (Fin decoded.functions.length) :=
    ⟨fun _ _ => Classical.choice hdomain⟩
  rcases projection.target_model_to_source_model_preserving_nativeABox_cardinality
      decoded.certificate.seed.abox.abox decoded.sourceOf decoded.abox_embedded
      decoded.definitions decoded.semanticPairs
      (fun pair hpair => decoded.semanticPairs_mem pair hpair)
      J base value hcore habox htargetPairs with
    ⟨I, functions, hdirect, hbundles, haboxSource, hcardinality⟩
  exact ⟨decoded.certificate.seed.state.base.state.QuotientDomain,
    I, functions, value, hdomain, hdirect, hbundles, haboxSource, hcardinality⟩

inductive WireBundleNativeABoxCardinalityDecisionEvidence where
  | sat (certificate : WireBundleNativeABoxCardinalitySatCertificate)
  | unsat (refutation : WireBundleNativeABoxCardinalityRefutation)
deriving FromJson, ToJson, Repr

structure WireBundleNativeABoxCardinalityDecisionCertificate where
  version : Nat
  evidence : WireBundleNativeABoxCardinalityDecisionEvidence
deriving FromJson, ToJson, Repr

inductive DecodedBundleNativeABoxCardinalityDecision where
  | sat (certificate : DecodedBundleNativeABoxCardinalitySatCertificate)
  | unsat (refutation : DecodedBundleNativeABoxCardinalityRefutation)

def WireBundleNativeABoxCardinalityDecisionCertificate.decode
    (wire : WireBundleNativeABoxCardinalityDecisionCertificate) :
    Except String DecodedBundleNativeABoxCardinalityDecision := do
  if wire.version != 1 then
    throw s!"unsupported bundle native ABox cardinality source decision version {wire.version}"
  match wire.evidence with
  | .sat certificate => return .sat (← certificate.decode)
  | .unsat refutation => return .unsat (← refutation.decode)

def WireBundleNativeABoxCardinalityDecisionCertificate.check
    (wire : WireBundleNativeABoxCardinalityDecisionCertificate) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedBundleNativeABoxCardinalityDecision.SemanticallyValid :
    DecodedBundleNativeABoxCardinalityDecision → Prop
  | .sat certificate =>
      certificate.certificate.seed.abox.abox.SatisfiableWithBundleProjectedCardinality
        certificate.sourceOf certificate.direct
        (decodedBundleSpecs certificate.bundles) certificate.definitions
        certificate.semanticPairs
  | .unsat refutation =>
      ¬refutation.refutation.initial.initial.seed.abox.abox.SatisfiableWithBundleProjectedCardinality
        refutation.sourceOf refutation.direct (decodedBundleSpecs refutation.bundles)
        refutation.definitions refutation.semanticPairs

theorem DecodedBundleNativeABoxCardinalityDecision.semantic_valid
    (decoded : DecodedBundleNativeABoxCardinalityDecision) :
    decoded.SemanticallyValid := by
  cases decoded with
  | sat certificate => exact certificate.source_satisfiable
  | unsat refutation => exact refutation.source_unsatisfiable

#print axioms DecodedDirectNativeABoxCardinalitySatCertificate.source_satisfiable
#print axioms DecodedDirectNativeABoxCardinalityDecision.semantic_valid
#print axioms DecodedMixedNativeABoxCardinalitySatCertificate.source_satisfiable
#print axioms DecodedMixedNativeABoxCardinalityDecision.semantic_valid
#print axioms DecodedBundleNativeABoxCardinalitySatCertificate.source_satisfiable
#print axioms DecodedBundleNativeABoxCardinalityDecision.semantic_valid

end ContextCalculus.Hypertableau
