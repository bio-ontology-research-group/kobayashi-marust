import ContextCalculus.HypertableauNativeABoxCardinalityTaxonomyWire
import ContextCalculus.HypertableauNativeABoxCardinalitySourceDecisionWire

/-!
# Source-composed native-ABox cardinality taxonomies

The direct wrapper checks the frontend cardinality projection and one complete
taxonomy matrix as a single document.  Every cell therefore denotes the source
clauses, projected number restrictions, complete native ABox, and exact query.
-/

namespace ContextCalculus.Hypertableau

open Lean

def NativeABox.SatisfiableWithProjectedCardinalityQuery
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (pairs : List (PairedCardinality Concept Role))
    (query : List (Lit Concept)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role)
      (value : Individual → Domain) (element : Domain),
    Nonempty Domain ∧ I.models ontology ∧
      I.modelsProjectedCardinalityDefs definitions pairs ∧
      abox.models I value ∧ I.RealizesLiterals query element

structure WireDirectNativeABoxCardinalityTaxonomyProjection where
  source : List WireDirectSourceClause
  target : List WireClause
  definitions : List WireProjectionCardinalityDef
  exact_pairs : List WireComplementaryCardinalityPair
deriving FromJson, ToJson, Repr

structure DecodedDirectNativeABoxCardinalityTaxonomySat where
  sourceProjection : DecodedDirectNativeABoxCardinalitySatCertificate
  query : DecodedNativeABoxTaxonomyQuery
    sourceProjection.certificate.seed.nodeCount
    sourceProjection.certificate.seed.abox.concepts.length
  query_present : ∀ literal ∈ query.literals,
    (query.root, literal) ∈
      sourceProjection.certificate.seed.state.base.base.labels

structure DecodedDirectNativeABoxCardinalityTaxonomyUnsat where
  taxonomy : DecodedNativeABoxCardinalityTaxonomyUnsat
  variable_ge_two : 2 ≤ taxonomy.initial.variableCount
  source : List (Clause (Fin taxonomy.initial.variableCount)
    (Fin taxonomy.initial.abox.concepts.length)
    (Fin taxonomy.initial.abox.roles.length))
  target : List (Clause (Fin taxonomy.initial.variableCount)
    (Fin taxonomy.initial.abox.concepts.length)
    (Fin taxonomy.initial.abox.roles.length))
  exact_projection : source.toFinset = target.toFinset
  definitionWires : List WireProjectionCardinalityDef
  wire_length : definitionWires.length = taxonomy.definitions.length
  unique_definitions : taxonomy.definitions.Nodup
  pairs : List (IndexedComplementaryCardinalityPair taxonomy.definitions)
  unique_pair_indices : (exactPairIndices pairs).Nodup
  exact_flags : ∀ index : Fin taxonomy.definitions.length,
    (definitionWires.get (wire_length.symm ▸ index)).exact =
      decide (index.val ∈ exactPairIndices pairs)
  exact_ontology : target ++ taxonomy.initial.abox.negativeRoleClausesAt
      taxonomy.initial.variableCount variable_ge_two =
    taxonomy.initial.state.base.base.ontology

def DecodedDirectNativeABoxCardinalityTaxonomyUnsat.semanticPairs
    (decoded : DecodedDirectNativeABoxCardinalityTaxonomyUnsat) :
    List (PairedCardinality (Fin decoded.taxonomy.initial.abox.concepts.length)
      (Fin decoded.taxonomy.initial.abox.roles.length)) :=
  decoded.pairs.map IndexedComplementaryCardinalityPair.toPair

theorem DecodedDirectNativeABoxCardinalityTaxonomyUnsat.semanticPairs_mem
    (decoded : DecodedDirectNativeABoxCardinalityTaxonomyUnsat)
    (pair : PairedCardinality (Fin decoded.taxonomy.initial.abox.concepts.length)
      (Fin decoded.taxonomy.initial.abox.roles.length))
    (hpair : pair ∈ decoded.semanticPairs) :
    pair.maximum ∈ decoded.taxonomy.definitions ∧
      pair.minimum ∈ decoded.taxonomy.definitions := by
  simp only [DecodedDirectNativeABoxCardinalityTaxonomyUnsat.semanticPairs,
    List.mem_map] at hpair
  rcases hpair with ⟨indexed, _, rfl⟩
  exact ⟨List.get_mem decoded.taxonomy.definitions indexed.maximum,
    List.get_mem decoded.taxonomy.definitions indexed.minimum⟩

inductive DecodedDirectNativeABoxCardinalityTaxonomyDecision where
  | sat (decoded : DecodedDirectNativeABoxCardinalityTaxonomySat)
  | unsat (decoded : DecodedDirectNativeABoxCardinalityTaxonomyUnsat)

structure WireDirectNativeABoxCardinalityTaxonomyDecision where
  version : Nat
  projection : WireDirectNativeABoxCardinalityTaxonomyProjection
  decision : WireNativeABoxCardinalityTaxonomyDecision
deriving FromJson, ToJson, Repr

def WireDirectNativeABoxCardinalityTaxonomyDecision.decode
    (wire : WireDirectNativeABoxCardinalityTaxonomyDecision) :
    Except String DecodedDirectNativeABoxCardinalityTaxonomyDecision := do
  if wire.version != 1 then
    throw s!"unsupported direct native ABox cardinality taxonomy version {wire.version}"
  match wire.decision.evidence with
  | .sat certificateWire =>
      let sourceProjection ← ({
        source := wire.projection.source
        target := wire.projection.target
        definitions := wire.projection.definitions
        exact_pairs := wire.projection.exact_pairs
        certificate := certificateWire
      } : WireDirectNativeABoxCardinalitySatCertificate).decode
      let query ← wire.decision.query.decode
        sourceProjection.certificate.seed.nodeCount
        sourceProjection.certificate.seed.abox.concepts.length
      if hquery : query.labelsPresentB
          sourceProjection.certificate.seed.state.base.base.labels = true then
        return .sat {
          sourceProjection
          query
          query_present := query.labelsPresentB_sound _ hquery
        }
      else throw "direct cardinality taxonomy countermodel omits its query literals"
  | .unsat .. =>
      let taxonomy ← wire.decision.decode
      let taxonomy ← match taxonomy with
        | .unsat decoded => pure decoded
        | .sat _ => throw "internal cardinality taxonomy evidence mismatch"
      let variableWitness ← requireAtLeastTwoVariables taxonomy.initial.variableCount
      let hvariables := variableWitness.proof
      let source ← wire.projection.source.mapM (WireDirectSourceClause.decode
        taxonomy.initial.variableCount taxonomy.initial.abox.concepts
        taxonomy.initial.abox.roles)
      let target ← wire.projection.target.mapM (WireClause.decode
        taxonomy.initial.variableCount taxonomy.initial.abox.concepts.length
        taxonomy.initial.abox.roles.length)
      if hprojection : source.toFinset = target.toFinset then
        let definitions ← wire.projection.definitions.mapM
          (WireProjectionCardinalityDef.decode taxonomy.initial.abox.concepts.length
            taxonomy.initial.abox.roles.length)
        if _hdefinitions : definitions = taxonomy.definitions then
          if hlength : wire.projection.definitions.length = taxonomy.definitions.length then
            if hunique : taxonomy.definitions.Nodup then
              let pairs ← wire.projection.exact_pairs.mapM
                (WireComplementaryCardinalityPair.decode taxonomy.definitions)
              if hpairs : (exactPairIndices pairs).Nodup then
                if hflags : ∀ index : Fin taxonomy.definitions.length,
                    (wire.projection.definitions.get (hlength.symm ▸ index)).exact =
                      decide (index.val ∈ exactPairIndices pairs) then
                  if hontology : target ++
                      taxonomy.initial.abox.negativeRoleClausesAt
                        taxonomy.initial.variableCount hvariables =
                      taxonomy.initial.state.base.base.ontology then
                    return .unsat {
                      taxonomy
                      variable_ge_two := hvariables
                      source
                      target
                      exact_projection := hprojection
                      definitionWires := wire.projection.definitions
                      wire_length := hlength
                      unique_definitions := hunique
                      pairs
                      unique_pair_indices := hpairs
                      exact_flags := hflags
                      exact_ontology := hontology
                    }
                  else throw "direct cardinality target differs from the taxonomy refutation ontology"
                else throw "cardinality exact flags differ from complementary-pair provenance"
              else throw "an exact cardinality definition occurs in more than one pair"
            else throw "cardinality taxonomy contains duplicate definitions"
          else throw "internal cardinality taxonomy definition length mismatch"
        else throw "source cardinality definitions differ from the taxonomy refutation"
      else throw "direct source residual differs from its cardinality target"

def WireDirectNativeABoxCardinalityTaxonomyDecision.check
    (wire : WireDirectNativeABoxCardinalityTaxonomyDecision) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedDirectNativeABoxCardinalityTaxonomySat.source_satisfiable
    (decoded : DecodedDirectNativeABoxCardinalityTaxonomySat) :
    NativeABox.SatisfiableWithProjectedCardinalityQuery
      decoded.sourceProjection.certificate.seed.abox.abox
      decoded.sourceProjection.projection.source
      decoded.sourceProjection.certificate.definitions
      decoded.sourceProjection.projection.semanticPairs decoded.query.literals := by
  let certificate := decoded.sourceProjection.certificate
  rcases certificate.canonical_model with
    ⟨value, hdomain, htarget, hdefinitions, habox⟩
  let I := certificate.seed.state.base.state.quotientCanonical
  let nodeValue : Fin certificate.seed.nodeCount →
      certificate.seed.state.base.state.QuotientDomain :=
    fun node => Quotient.mk certificate.seed.state.base.state.nodeSetoid node
  have hparts := certificate.cardinality
  simp only [FiniteEqCertificate.checkEqSatWithCardinality,
    Bool.and_eq_true] at hparts
  have hrealized : certificate.seed.state.base.state.RealizedBy I nodeValue :=
    certificate.seed.state.base.checkEqSat_realizes hparts.1
  have hquery : I.RealizesLiterals decoded.query.literals
      (nodeValue decoded.query.root) := by
    intro literal hliteral
    exact hrealized.1.1 decoded.query.root literal
      (decoded.query_present literal hliteral)
  have happended : I.models (decoded.sourceProjection.projection.target ++
      certificate.seed.abox.negativeRoleClausesAt certificate.seed.variableCount
        decoded.sourceProjection.variable_ge_two) := by
    rw [decoded.sourceProjection.exact_ontology]
    exact htarget
  have htargetCore : I.models decoded.sourceProjection.projection.target := by
    intro clause hclause
    exact happended clause (List.mem_append_left _ hclause)
  have hexact := certificate.models_exact_definitions
  have hpairs : I.modelsPairedCardinalityTargets certificate.definitions
      decoded.sourceProjection.projection.semanticPairs := by
    refine ⟨hdefinitions, ?_⟩
    intro pair hpair
    exact ⟨hexact pair.maximum
      (decoded.sourceProjection.exact_pair_coverage pair hpair).1,
      hexact pair.minimum
      (decoded.sourceProjection.exact_pair_coverage pair hpair).2⟩
  have hsource :=
    (decoded.sourceProjection.projection.models_source_iff_target I).2
      ⟨htargetCore, hpairs⟩
  exact ⟨certificate.seed.state.base.state.QuotientDomain, I,
    value, nodeValue decoded.query.root, hdomain, hsource.1, hsource.2, habox, hquery⟩

theorem DecodedDirectNativeABoxCardinalityTaxonomyUnsat.source_unsatisfiable
    (decoded : DecodedDirectNativeABoxCardinalityTaxonomyUnsat) :
    ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithProjectedCardinalityQuery
      decoded.source decoded.taxonomy.definitions decoded.semanticPairs
      decoded.taxonomy.query.literals := by
  rintro ⟨Domain, I, value, element, hdomain, hsource, hprojected, habox, hquery⟩
  have htargetCore : I.models decoded.target :=
    (models_iff_of_toFinset_eq I decoded.source decoded.target
      decoded.exact_projection).1 hsource
  have hdefinitions : I.modelsCardinalityDefs decoded.taxonomy.definitions :=
    (modelsProjectedCardinalityDefs_iff_pairedTargets I decoded.taxonomy.definitions
      decoded.semanticPairs
      (fun pair hpair => decoded.semanticPairs_mem pair hpair)).1 hprojected |>.1
  have htarget : I.models decoded.taxonomy.initial.state.base.base.ontology := by
    rw [← decoded.exact_ontology]
    exact (decoded.taxonomy.initial.abox.models_append_negativeRoleClausesAt_iff
      I value habox.1 decoded.variable_ge_two decoded.target).2
        ⟨htargetCore, habox.2.2.2.2⟩
  exact decoded.taxonomy.unsatisfiable
    ⟨Domain, I, value, element, hdomain, htarget, hdefinitions, habox, hquery⟩

def DecodedDirectNativeABoxCardinalityTaxonomyDecision.SemanticallyValid :
    DecodedDirectNativeABoxCardinalityTaxonomyDecision → Prop
  | .sat decoded =>
      NativeABox.SatisfiableWithProjectedCardinalityQuery
        decoded.sourceProjection.certificate.seed.abox.abox
        decoded.sourceProjection.projection.source
        decoded.sourceProjection.certificate.definitions
        decoded.sourceProjection.projection.semanticPairs decoded.query.literals
  | .unsat decoded =>
      ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithProjectedCardinalityQuery
        decoded.source decoded.taxonomy.definitions decoded.semanticPairs
        decoded.taxonomy.query.literals

theorem DecodedDirectNativeABoxCardinalityTaxonomyDecision.semantic_valid
    (decoded : DecodedDirectNativeABoxCardinalityTaxonomyDecision) :
    decoded.SemanticallyValid := by
  cases decoded with
  | sat result => exact result.source_satisfiable
  | unsat result => exact result.source_unsatisfiable

structure WireDirectNativeABoxCardinalityTaxonomyMatrix where
  version : Nat
  projection : WireDirectNativeABoxCardinalityTaxonomyProjection
  matrix : WireNativeABoxCardinalityTaxonomyMatrix
deriving FromJson, ToJson, Repr

structure DecodedDirectNativeABoxCardinalityTaxonomyMatrix where
  matrix : DecodedNativeABoxCardinalityTaxonomyMatrix
  concepts : List DecodedDirectNativeABoxCardinalityTaxonomyDecision
  subsumptions : List (List DecodedDirectNativeABoxCardinalityTaxonomyDecision)

def WireDirectNativeABoxCardinalityTaxonomyMatrix.decode
    (wire : WireDirectNativeABoxCardinalityTaxonomyMatrix) :
    Except String DecodedDirectNativeABoxCardinalityTaxonomyMatrix := do
  if wire.version != 1 then
    throw s!"unsupported direct native ABox cardinality taxonomy matrix version {wire.version}"
  let matrix ← wire.matrix.decode
  let wrap := fun decision => ({
    version := 1
    projection := wire.projection
    decision
  } : WireDirectNativeABoxCardinalityTaxonomyDecision)
  let concepts ← wire.matrix.concepts.mapM fun decision => (wrap decision).decode
  let subsumptions ← wire.matrix.subsumptions.mapM fun row =>
    row.mapM fun decision => (wrap decision).decode
  return { matrix, concepts, subsumptions }

def WireDirectNativeABoxCardinalityTaxonomyMatrix.check
    (wire : WireDirectNativeABoxCardinalityTaxonomyMatrix) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedDirectNativeABoxCardinalityTaxonomyMatrix.allDecisions
    (decoded : DecodedDirectNativeABoxCardinalityTaxonomyMatrix) :
    List DecodedDirectNativeABoxCardinalityTaxonomyDecision :=
  decoded.concepts ++ decoded.subsumptions.flatten

def DecodedDirectNativeABoxCardinalityTaxonomyMatrix.SemanticallyValid
    (decoded : DecodedDirectNativeABoxCardinalityTaxonomyMatrix) : Prop :=
  decoded.matrix.wire.shapeB = true ∧ decoded.matrix.wire.queriesB = true ∧
  decoded.matrix.wire.sharedProblemB = true ∧
  ∀ decision ∈ decoded.allDecisions, decision.SemanticallyValid

theorem DecodedDirectNativeABoxCardinalityTaxonomyMatrix.semantic_valid
    (decoded : DecodedDirectNativeABoxCardinalityTaxonomyMatrix) :
    decoded.SemanticallyValid := by
  refine ⟨decoded.matrix.complete_shape, decoded.matrix.exact_queries,
    decoded.matrix.shared_problem, ?_⟩
  intro decision _
  exact decision.semantic_valid

/-! ## Mixed direct/Skolem-pair source projection -/

def NativeABox.SatisfiableWithMixedProjectedCardinalityQuery
    (abox : NativeABox Individual Concept Role)
    (direct : List (Clause Variable Concept Role))
    (pairs : List (SkolemPairSpec Variable Concept Role Function))
    (definitions : List (CardinalityDef Concept Role))
    (cardinalityPairs : List (PairedCardinality Concept Role))
    (query : List (Lit Concept)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role)
      (value : Individual → Domain) (element : Domain),
    Nonempty Domain ∧ abox.models I value ∧ I.RealizesLiterals query element ∧
      (∃ functions : SkolemInterp Domain Function,
        I.models direct ∧ ModelsSkolemPairs I functions pairs) ∧
      I.modelsProjectedCardinalityDefs definitions cardinalityPairs

structure WireMixedNativeABoxCardinalityTaxonomyProjection where
  functions : List String
  direct : List WireDirectSourceClause
  pairs : List WireSkolemPair
  definitions : List WireProjectionCardinalityDef
  exact_pairs : List WireComplementaryCardinalityPair
deriving FromJson, ToJson, Repr

structure DecodedMixedNativeABoxCardinalityTaxonomySat where
  sourceProjection : DecodedMixedNativeABoxCardinalitySatCertificate
  query : DecodedNativeABoxTaxonomyQuery
    sourceProjection.certificate.seed.nodeCount
    sourceProjection.certificate.seed.abox.concepts.length
  query_present : ∀ literal ∈ query.literals,
    (query.root, literal) ∈
      sourceProjection.certificate.seed.state.base.base.labels

structure DecodedMixedNativeABoxCardinalityTaxonomyUnsat where
  taxonomy : DecodedNativeABoxCardinalityTaxonomyUnsat
  variable_ge_two : 2 ≤ taxonomy.initial.variableCount
  functions : List String
  direct : List (Clause (Fin taxonomy.initial.variableCount)
    (Fin taxonomy.initial.abox.concepts.length)
    (Fin taxonomy.initial.abox.roles.length))
  pairs : List (SkolemPairSpec (Fin taxonomy.initial.variableCount)
    (Fin taxonomy.initial.abox.concepts.length)
    (Fin taxonomy.initial.abox.roles.length) (Fin functions.length))
  unique_functions : (skolemPairFunctions pairs).Nodup
  definitionWires : List WireProjectionCardinalityDef
  wire_length : definitionWires.length = taxonomy.definitions.length
  unique_definitions : taxonomy.definitions.Nodup
  cardinalityPairs : List
    (IndexedComplementaryCardinalityPair taxonomy.definitions)
  unique_pair_indices : (exactPairIndices cardinalityPairs).Nodup
  exact_flags : ∀ index : Fin taxonomy.definitions.length,
    (definitionWires.get (wire_length.symm ▸ index)).exact =
      decide (index.val ∈ exactPairIndices cardinalityPairs)
  exact_projection :
    (skolemProjectionOntology direct pairs ++
      taxonomy.initial.abox.negativeRoleClausesAt taxonomy.initial.variableCount
        variable_ge_two).toFinset =
      taxonomy.initial.state.base.base.ontology.toFinset

def DecodedMixedNativeABoxCardinalityTaxonomyUnsat.semanticPairs
    (decoded : DecodedMixedNativeABoxCardinalityTaxonomyUnsat) :
    List (PairedCardinality (Fin decoded.taxonomy.initial.abox.concepts.length)
      (Fin decoded.taxonomy.initial.abox.roles.length)) :=
  decoded.cardinalityPairs.map IndexedComplementaryCardinalityPair.toPair

theorem DecodedMixedNativeABoxCardinalityTaxonomyUnsat.semanticPairs_mem
    (decoded : DecodedMixedNativeABoxCardinalityTaxonomyUnsat)
    (pair : PairedCardinality (Fin decoded.taxonomy.initial.abox.concepts.length)
      (Fin decoded.taxonomy.initial.abox.roles.length))
    (hpair : pair ∈ decoded.semanticPairs) :
    pair.maximum ∈ decoded.taxonomy.definitions ∧
      pair.minimum ∈ decoded.taxonomy.definitions := by
  simp only [DecodedMixedNativeABoxCardinalityTaxonomyUnsat.semanticPairs,
    List.mem_map] at hpair
  rcases hpair with ⟨indexed, _, rfl⟩
  exact ⟨List.get_mem decoded.taxonomy.definitions indexed.maximum,
    List.get_mem decoded.taxonomy.definitions indexed.minimum⟩

inductive DecodedMixedNativeABoxCardinalityTaxonomyDecision where
  | sat (decoded : DecodedMixedNativeABoxCardinalityTaxonomySat)
  | unsat (decoded : DecodedMixedNativeABoxCardinalityTaxonomyUnsat)

structure WireMixedNativeABoxCardinalityTaxonomyDecision where
  version : Nat
  projection : WireMixedNativeABoxCardinalityTaxonomyProjection
  decision : WireNativeABoxCardinalityTaxonomyDecision
deriving FromJson, ToJson, Repr

def WireMixedNativeABoxCardinalityTaxonomyDecision.decode
    (wire : WireMixedNativeABoxCardinalityTaxonomyDecision) :
    Except String DecodedMixedNativeABoxCardinalityTaxonomyDecision := do
  if wire.version != 1 then
    throw s!"unsupported mixed native ABox cardinality taxonomy version {wire.version}"
  match wire.decision.evidence with
  | .sat certificateWire =>
      let sourceProjection ← ({
        functions := wire.projection.functions
        direct := wire.projection.direct
        pairs := wire.projection.pairs
        definitions := wire.projection.definitions
        exact_pairs := wire.projection.exact_pairs
        certificate := certificateWire
      } : WireMixedNativeABoxCardinalitySatCertificate).decode
      let query ← wire.decision.query.decode
        sourceProjection.certificate.seed.nodeCount
        sourceProjection.certificate.seed.abox.concepts.length
      if hquery : query.labelsPresentB
          sourceProjection.certificate.seed.state.base.base.labels = true then
        return .sat {
          sourceProjection
          query
          query_present := query.labelsPresentB_sound _ hquery
        }
      else throw "mixed cardinality taxonomy countermodel omits its query literals"
  | .unsat .. =>
      let taxonomy ← wire.decision.decode
      let taxonomy ← match taxonomy with
        | .unsat decoded => pure decoded
        | .sat _ => throw "internal mixed cardinality taxonomy evidence mismatch"
      let variableWitness ← requireAtLeastTwoVariables taxonomy.initial.variableCount
      let hvariables := variableWitness.proof
      if _hfunctions : wire.projection.functions.Nodup then
        let direct ← wire.projection.direct.mapM (WireDirectSourceClause.decode
          taxonomy.initial.variableCount taxonomy.initial.abox.concepts
          taxonomy.initial.abox.roles)
        let pairs ← wire.projection.pairs.mapM (WireSkolemPair.decode
          taxonomy.initial.variableCount taxonomy.initial.abox.concepts
          taxonomy.initial.abox.roles wire.projection.functions)
        if hunique : (skolemPairFunctions pairs).Nodup then
          let definitions ← wire.projection.definitions.mapM
            (WireProjectionCardinalityDef.decode
              taxonomy.initial.abox.concepts.length
              taxonomy.initial.abox.roles.length)
          if _hdefinitions : definitions = taxonomy.definitions then
            if hlength : wire.projection.definitions.length =
                taxonomy.definitions.length then
              if hdefinitionUnique : taxonomy.definitions.Nodup then
                let cardinalityPairs ← wire.projection.exact_pairs.mapM
                  (WireComplementaryCardinalityPair.decode taxonomy.definitions)
                if hpairs : (exactPairIndices cardinalityPairs).Nodup then
                  if hflags : ∀ index : Fin taxonomy.definitions.length,
                      (wire.projection.definitions.get (hlength.symm ▸ index)).exact =
                        decide (index.val ∈ exactPairIndices cardinalityPairs) then
                    if hequal : (skolemProjectionOntology direct pairs ++
                        taxonomy.initial.abox.negativeRoleClausesAt
                          taxonomy.initial.variableCount hvariables).toFinset =
                        taxonomy.initial.state.base.base.ontology.toFinset then
                      return .unsat {
                        taxonomy
                        variable_ge_two := hvariables
                        functions := wire.projection.functions
                        direct
                        pairs
                        unique_functions := hunique
                        definitionWires := wire.projection.definitions
                        wire_length := hlength
                        unique_definitions := hdefinitionUnique
                        cardinalityPairs
                        unique_pair_indices := hpairs
                        exact_flags := hflags
                        exact_projection := hequal
                      }
                    else throw "mixed source conversion differs from the taxonomy refutation ontology"
                  else throw "cardinality exact flags differ from complementary-pair provenance"
                else throw "an exact cardinality definition occurs in more than one pair"
              else throw "mixed cardinality taxonomy contains duplicate definitions"
            else throw "internal mixed cardinality taxonomy definition length mismatch"
          else throw "mixed cardinality definitions differ from the taxonomy refutation"
        else throw "mixed taxonomy projection reuses a Skolem function"
      else throw "mixed taxonomy function-name table contains duplicates"

def WireMixedNativeABoxCardinalityTaxonomyDecision.check
    (wire : WireMixedNativeABoxCardinalityTaxonomyDecision) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedMixedNativeABoxCardinalityTaxonomySat.source_satisfiable
    (decoded : DecodedMixedNativeABoxCardinalityTaxonomySat) :
    NativeABox.SatisfiableWithMixedProjectedCardinalityQuery
      decoded.sourceProjection.certificate.seed.abox.abox
      decoded.sourceProjection.direct decoded.sourceProjection.pairs
      decoded.sourceProjection.certificate.definitions
      decoded.sourceProjection.semanticPairs decoded.query.literals := by
  let certificate := decoded.sourceProjection.certificate
  rcases certificate.canonical_model with
    ⟨value, hdomain, htarget, hdefinitions, habox⟩
  let I := certificate.seed.state.base.state.quotientCanonical
  let nodeValue : Fin certificate.seed.nodeCount →
      certificate.seed.state.base.state.QuotientDomain :=
    fun node => Quotient.mk certificate.seed.state.base.state.nodeSetoid node
  have hparts := certificate.cardinality
  simp only [FiniteEqCertificate.checkEqSatWithCardinality,
    Bool.and_eq_true] at hparts
  have hrealized : certificate.seed.state.base.state.RealizedBy I nodeValue :=
    certificate.seed.state.base.checkEqSat_realizes hparts.1
  have hquery : I.RealizesLiterals decoded.query.literals
      (nodeValue decoded.query.root) := by
    intro literal hliteral
    exact hrealized.1.1 decoded.query.root literal
      (decoded.query_present literal hliteral)
  have happended : I.models
      (skolemProjectionOntology decoded.sourceProjection.direct
          decoded.sourceProjection.pairs ++
        certificate.seed.abox.negativeRoleClausesAt certificate.seed.variableCount
          decoded.sourceProjection.variable_ge_two) :=
    (models_iff_of_toFinset_eq I _ _
      decoded.sourceProjection.exact_projection).2 htarget
  have hprojected : I.models (skolemProjectionOntology
      decoded.sourceProjection.direct decoded.sourceProjection.pairs) := by
    intro clause hclause
    exact happended clause (List.mem_append_left _ hclause)
  have hexact := certificate.models_exact_definitions
  have hpairs : I.modelsPairedCardinalityTargets certificate.definitions
      decoded.sourceProjection.semanticPairs := by
    refine ⟨hdefinitions, ?_⟩
    intro pair hpair
    exact ⟨hexact pair.maximum
      (decoded.sourceProjection.exact_pair_coverage pair hpair).1,
      hexact pair.minimum
      (decoded.sourceProjection.exact_pair_coverage pair hpair).2⟩
  letI : Nonempty certificate.seed.state.base.state.QuotientDomain := hdomain
  let base : SkolemInterp certificate.seed.state.base.state.QuotientDomain
      (Fin decoded.sourceProjection.functions.length) :=
    ⟨fun _ _ => Classical.choice hdomain⟩
  rcases (mixedSkolemProjection_sat_iff I base decoded.sourceProjection.direct
    decoded.sourceProjection.pairs decoded.sourceProjection.unique_functions).2
      hprojected with ⟨functions, hdirect, hskolem⟩
  have hsourceCardinality :=
    (modelsProjectedCardinalityDefs_iff_pairedTargets I certificate.definitions
      decoded.sourceProjection.semanticPairs
      (fun pair hpair => decoded.sourceProjection.semanticPairs_mem pair hpair)).2 hpairs
  exact ⟨certificate.seed.state.base.state.QuotientDomain, I, value,
    nodeValue decoded.query.root, hdomain, habox, hquery,
    ⟨functions, hdirect, hskolem⟩, hsourceCardinality⟩

theorem DecodedMixedNativeABoxCardinalityTaxonomyUnsat.source_unsatisfiable
    (decoded : DecodedMixedNativeABoxCardinalityTaxonomyUnsat) :
    ¬NativeABox.SatisfiableWithMixedProjectedCardinalityQuery
      decoded.taxonomy.initial.abox.abox decoded.direct decoded.pairs
      decoded.taxonomy.definitions decoded.semanticPairs
      decoded.taxonomy.query.literals := by
  rintro ⟨Domain, I, value, element, hdomain, habox, hquery,
    ⟨functions, hdirect, hpairs⟩, hcardinality⟩
  letI : Nonempty Domain := hdomain
  let base : SkolemInterp Domain (Fin decoded.functions.length) :=
    ⟨fun _ _ => Classical.choice hdomain⟩
  have hprojected : I.models (skolemProjectionOntology decoded.direct decoded.pairs) :=
    (mixedSkolemProjection_sat_iff I base decoded.direct decoded.pairs
      decoded.unique_functions).1 ⟨functions, hdirect, hpairs⟩
  have happended : I.models (skolemProjectionOntology decoded.direct decoded.pairs ++
      decoded.taxonomy.initial.abox.negativeRoleClausesAt
        decoded.taxonomy.initial.variableCount decoded.variable_ge_two) :=
    (DecodedNativeABox.models_append_negativeRoleClausesAt_iff
      decoded.taxonomy.initial.abox I value habox.1 decoded.variable_ge_two
      (skolemProjectionOntology decoded.direct decoded.pairs)).2
        ⟨hprojected, habox.2.2.2.2⟩
  have htarget : I.models decoded.taxonomy.initial.state.base.base.ontology :=
    (models_iff_of_toFinset_eq I _ _ decoded.exact_projection).1 happended
  have hdefinitions : I.modelsCardinalityDefs decoded.taxonomy.definitions :=
    (modelsProjectedCardinalityDefs_iff_pairedTargets I
      decoded.taxonomy.definitions decoded.semanticPairs
      (fun pair hpair => decoded.semanticPairs_mem pair hpair)).1 hcardinality |>.1
  exact decoded.taxonomy.unsatisfiable
    ⟨Domain, I, value, element, hdomain, htarget, hdefinitions, habox, hquery⟩

def DecodedMixedNativeABoxCardinalityTaxonomyDecision.SemanticallyValid :
    DecodedMixedNativeABoxCardinalityTaxonomyDecision → Prop
  | .sat decoded =>
      NativeABox.SatisfiableWithMixedProjectedCardinalityQuery
        decoded.sourceProjection.certificate.seed.abox.abox
        decoded.sourceProjection.direct decoded.sourceProjection.pairs
        decoded.sourceProjection.certificate.definitions
        decoded.sourceProjection.semanticPairs decoded.query.literals
  | .unsat decoded =>
      ¬NativeABox.SatisfiableWithMixedProjectedCardinalityQuery
        decoded.taxonomy.initial.abox.abox decoded.direct decoded.pairs
        decoded.taxonomy.definitions decoded.semanticPairs
        decoded.taxonomy.query.literals

theorem DecodedMixedNativeABoxCardinalityTaxonomyDecision.semantic_valid
    (decoded : DecodedMixedNativeABoxCardinalityTaxonomyDecision) :
    decoded.SemanticallyValid := by
  cases decoded with
  | sat result => exact result.source_satisfiable
  | unsat result => exact result.source_unsatisfiable

structure WireMixedNativeABoxCardinalityTaxonomyMatrix where
  version : Nat
  projection : WireMixedNativeABoxCardinalityTaxonomyProjection
  matrix : WireNativeABoxCardinalityTaxonomyMatrix
deriving FromJson, ToJson, Repr

structure DecodedMixedNativeABoxCardinalityTaxonomyMatrix where
  matrix : DecodedNativeABoxCardinalityTaxonomyMatrix
  concepts : List DecodedMixedNativeABoxCardinalityTaxonomyDecision
  subsumptions : List (List DecodedMixedNativeABoxCardinalityTaxonomyDecision)

def WireMixedNativeABoxCardinalityTaxonomyMatrix.decode
    (wire : WireMixedNativeABoxCardinalityTaxonomyMatrix) :
    Except String DecodedMixedNativeABoxCardinalityTaxonomyMatrix := do
  if wire.version != 1 then
    throw s!"unsupported mixed native ABox cardinality taxonomy matrix version {wire.version}"
  let matrix ← wire.matrix.decode
  let wrap := fun decision => ({
    version := 1
    projection := wire.projection
    decision
  } : WireMixedNativeABoxCardinalityTaxonomyDecision)
  let concepts ← wire.matrix.concepts.mapM fun decision => (wrap decision).decode
  let subsumptions ← wire.matrix.subsumptions.mapM fun row =>
    row.mapM fun decision => (wrap decision).decode
  return { matrix, concepts, subsumptions }

def WireMixedNativeABoxCardinalityTaxonomyMatrix.check
    (wire : WireMixedNativeABoxCardinalityTaxonomyMatrix) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedMixedNativeABoxCardinalityTaxonomyMatrix.allDecisions
    (decoded : DecodedMixedNativeABoxCardinalityTaxonomyMatrix) :
    List DecodedMixedNativeABoxCardinalityTaxonomyDecision :=
  decoded.concepts ++ decoded.subsumptions.flatten

def DecodedMixedNativeABoxCardinalityTaxonomyMatrix.SemanticallyValid
    (decoded : DecodedMixedNativeABoxCardinalityTaxonomyMatrix) : Prop :=
  decoded.matrix.wire.shapeB = true ∧ decoded.matrix.wire.queriesB = true ∧
  decoded.matrix.wire.sharedProblemB = true ∧
  ∀ decision ∈ decoded.allDecisions, decision.SemanticallyValid

theorem DecodedMixedNativeABoxCardinalityTaxonomyMatrix.semantic_valid
    (decoded : DecodedMixedNativeABoxCardinalityTaxonomyMatrix) :
    decoded.SemanticallyValid := by
  refine ⟨decoded.matrix.complete_shape, decoded.matrix.exact_queries,
    decoded.matrix.shared_problem, ?_⟩
  intro decision _
  exact decision.semantic_valid

#print axioms DecodedDirectNativeABoxCardinalityTaxonomyDecision.semantic_valid
#print axioms DecodedDirectNativeABoxCardinalityTaxonomyMatrix.semantic_valid
#print axioms DecodedMixedNativeABoxCardinalityTaxonomyDecision.semantic_valid
#print axioms DecodedMixedNativeABoxCardinalityTaxonomyMatrix.semantic_valid

end ContextCalculus.Hypertableau
