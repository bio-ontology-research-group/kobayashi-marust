import ContextCalculus.HypertableauNativeABoxCardinalityTaxonomyWire
import ContextCalculus.HypertableauNativeABoxCardinalitySourceDecisionWire
import ContextCalculus.HypertableauNativeABoxTaxonomySourceWire

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

def DecodedDirectNativeABoxCardinalityTaxonomyDecision.positive :
    DecodedDirectNativeABoxCardinalityTaxonomyDecision → Bool
  | .sat _ => false
  | .unsat _ => true

def DecodedDirectNativeABoxCardinalityTaxonomyDecision.QueryEntailed :
    DecodedDirectNativeABoxCardinalityTaxonomyDecision → Prop
  | .sat decoded =>
      ¬NativeABox.SatisfiableWithProjectedCardinalityQuery
        decoded.sourceProjection.certificate.seed.abox.abox
        decoded.sourceProjection.projection.source
        decoded.sourceProjection.certificate.definitions
        decoded.sourceProjection.projection.semanticPairs decoded.query.literals
  | .unsat decoded =>
      ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithProjectedCardinalityQuery
        decoded.source decoded.taxonomy.definitions decoded.semanticPairs
        decoded.taxonomy.query.literals

theorem DecodedDirectNativeABoxCardinalityTaxonomyDecision.positive_eq_true_iff
    (decision : DecodedDirectNativeABoxCardinalityTaxonomyDecision) :
    decision.positive = true ↔ decision.QueryEntailed := by
  cases decision with
  | sat decoded =>
      have hsemantic := decoded.source_satisfiable
      change (false = true ↔
        ¬NativeABox.SatisfiableWithProjectedCardinalityQuery
          decoded.sourceProjection.certificate.seed.abox.abox
          decoded.sourceProjection.projection.source
          decoded.sourceProjection.certificate.definitions
          decoded.sourceProjection.projection.semanticPairs decoded.query.literals)
      exact ⟨fun hfalse => by contradiction,
        fun hnot => False.elim (hnot hsemantic)⟩
  | unsat decoded =>
      have hsemantic := decoded.source_unsatisfiable
      change (true = true ↔
        ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithProjectedCardinalityQuery
          decoded.source decoded.taxonomy.definitions decoded.semanticPairs
          decoded.taxonomy.query.literals)
      exact ⟨fun _ => hsemantic, fun _ => rfl⟩

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

def DecodedMixedNativeABoxCardinalityTaxonomyDecision.positive :
    DecodedMixedNativeABoxCardinalityTaxonomyDecision → Bool
  | .sat _ => false
  | .unsat _ => true

def DecodedMixedNativeABoxCardinalityTaxonomyDecision.QueryEntailed :
    DecodedMixedNativeABoxCardinalityTaxonomyDecision → Prop
  | .sat decoded =>
      ¬NativeABox.SatisfiableWithMixedProjectedCardinalityQuery
        decoded.sourceProjection.certificate.seed.abox.abox
        decoded.sourceProjection.direct decoded.sourceProjection.pairs
        decoded.sourceProjection.certificate.definitions
        decoded.sourceProjection.semanticPairs decoded.query.literals
  | .unsat decoded =>
      ¬NativeABox.SatisfiableWithMixedProjectedCardinalityQuery
        decoded.taxonomy.initial.abox.abox decoded.direct decoded.pairs
        decoded.taxonomy.definitions decoded.semanticPairs
        decoded.taxonomy.query.literals

theorem DecodedMixedNativeABoxCardinalityTaxonomyDecision.positive_eq_true_iff
    (decision : DecodedMixedNativeABoxCardinalityTaxonomyDecision) :
    decision.positive = true ↔ decision.QueryEntailed := by
  cases decision with
  | sat decoded =>
      have hsemantic := decoded.source_satisfiable
      change (false = true ↔
        ¬NativeABox.SatisfiableWithMixedProjectedCardinalityQuery
          decoded.sourceProjection.certificate.seed.abox.abox
          decoded.sourceProjection.direct decoded.sourceProjection.pairs
          decoded.sourceProjection.certificate.definitions
          decoded.sourceProjection.semanticPairs decoded.query.literals)
      exact ⟨fun hfalse => by contradiction,
        fun hnot => False.elim (hnot hsemantic)⟩
  | unsat decoded =>
      have hsemantic := decoded.source_unsatisfiable
      change (true = true ↔
        ¬NativeABox.SatisfiableWithMixedProjectedCardinalityQuery
          decoded.taxonomy.initial.abox.abox decoded.direct decoded.pairs
          decoded.taxonomy.definitions decoded.semanticPairs
          decoded.taxonomy.query.literals)
      exact ⟨fun _ => hsemantic, fun _ => rfl⟩

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

/-! ## Bundle transport preserving ABox, cardinality, and query together -/

theorem DecodedBundleProjection.target_model_to_source_model_preserving_nativeABox_cardinality_query
    (decoded : DecodedBundleProjection)
    (abox : NativeABox Individual (Fin decoded.concepts.length)
      (Fin decoded.roles.length))
    (sourceOf : Fin decoded.concepts.length → Fin decoded.sourceConcepts.length)
    (hembedded : ∀ individual concept,
      concept ∈ abox.proxies individual ++ abox.assertions individual →
      decoded.sourceQueryEmbedding (sourceOf concept) = concept)
    (definitions : List (CardinalityDef (Fin decoded.sourceConcepts.length)
      (Fin decoded.roles.length)))
    (pairs : List (PairedCardinality (Fin decoded.sourceConcepts.length)
      (Fin decoded.roles.length)))
    (hpairs : ∀ pair ∈ pairs,
      pair.maximum ∈ definitions ∧ pair.minimum ∈ definitions)
    (query : List (Lit (Fin decoded.sourceConcepts.length)))
    (J : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length))
    (base : SkolemInterp Domain (Fin decoded.functions.length))
    (value : Individual → Domain) (element : Domain)
    (htarget : J.models decoded.target) (habox : abox.models J value)
    (hcardinality : J.modelsPairedCardinalityTargets
      ((definitions.map (renameCardinalityDef Sum.inr)).map
        (renameCardinalityDef
          (bundleConceptEmbedding decoded.sourceTargets decoded.bundles)))
      ((pairs.map (renamePairedCardinality Sum.inr)).map
        (renamePairedCardinality
          (bundleConceptEmbedding decoded.sourceTargets decoded.bundles))))
    (hquery : J.RealizesLiterals
      (query.map (renameLit decoded.sourceQueryEmbedding)) element) :
    ∃ I : Interp Domain (Fin decoded.sourceConcepts.length)
        (Fin decoded.roles.length),
      ∃ functions : SkolemInterp Domain (Fin decoded.functions.length),
        I.models decoded.direct ∧
        ModelsBundles I functions (decodedBundleSpecs decoded.bundles) ∧
        (abox.mapConcepts sourceOf).models I value ∧
        I.modelsProjectedCardinalityDefs definitions pairs ∧
        I.RealizesLiterals query element := by
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
      (indexedBundleOntology decoded.direct (decodedBundleSpecs decoded.bundles)) := by
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
        simpa [DecodedBundleProjection.sourceQueryEmbedding, embedding] using
          congrArg J.concept (hembedded individual concept hused).symm)
      rfl habox
  have hcombinedCardinality : K.modelsPairedCardinalityTargets
      (definitions.map (renameCardinalityDef Sum.inr))
      (pairs.map (renamePairedCardinality Sum.inr)) :=
    (modelsPairedCardinalityTargets_rename_pullback_iff embedding J
      (definitions.map (renameCardinalityDef Sum.inr))
      (pairs.map (renamePairedCardinality Sum.inr))).1 hcardinality
  have hsourceTargets : I.modelsPairedCardinalityTargets definitions pairs := by
    apply (modelsPairedCardinalityTargets_rename_pullback_iff
      Sum.inr K definitions pairs).1
    simpa [I, indexedRestrict, pullbackConcepts] using hcombinedCardinality
  have hsourceCardinality : I.modelsProjectedCardinalityDefs definitions pairs :=
    (modelsProjectedCardinalityDefs_iff_pairedTargets I definitions pairs hpairs).2
      hsourceTargets
  have hquerySource : I.RealizesLiterals query element := by
    intro literal hliteral
    have htargetLiteral := hquery (renameLit decoded.sourceQueryEmbedding literal)
      (List.mem_map.mpr ⟨literal, hliteral, rfl⟩)
    change K.satLit (indexedLiftLit literal) element
    rw [← satLit_rename_pullback_iff embedding J]
    simpa [DecodedBundleProjection.sourceQueryEmbedding, embedding,
      indexedLiftLit, renameLit] using htargetLiteral
  exact ⟨I, functions, hdirect, hbundles, haboxSource, hsourceCardinality,
    hquerySource⟩

theorem DecodedBundleProjection.source_model_to_target_model_preserving_nativeABox_cardinality_query
    (decoded : DecodedBundleProjection)
    (abox : NativeABox Individual (Fin decoded.concepts.length)
      (Fin decoded.roles.length))
    (sourceOf : Fin decoded.concepts.length → Fin decoded.sourceConcepts.length)
    (hembedded : ∀ individual concept,
      concept ∈ abox.proxies individual ++ abox.assertions individual →
      decoded.sourceQueryEmbedding (sourceOf concept) = concept)
    (definitions : List (CardinalityDef (Fin decoded.sourceConcepts.length)
      (Fin decoded.roles.length)))
    (pairs : List (PairedCardinality (Fin decoded.sourceConcepts.length)
      (Fin decoded.roles.length)))
    (hpairs : ∀ pair ∈ pairs,
      pair.maximum ∈ definitions ∧ pair.minimum ∈ definitions)
    (query : List (Lit (Fin decoded.sourceConcepts.length)))
    (I : Interp Domain (Fin decoded.sourceConcepts.length)
      (Fin decoded.roles.length))
    (functions : SkolemInterp Domain (Fin decoded.functions.length))
    (value : Individual → Domain) (element : Domain)
    (hdirect : I.models decoded.direct)
    (hbundles : ModelsBundles I functions (decodedBundleSpecs decoded.bundles))
    (habox : (abox.mapConcepts sourceOf).models I value)
    (hcardinality : I.modelsProjectedCardinalityDefs definitions pairs)
    (hquery : I.RealizesLiterals query element) :
    ∃ J : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length),
      J.models decoded.target ∧ abox.models J value ∧
      J.modelsPairedCardinalityTargets
        ((definitions.map (renameCardinalityDef Sum.inr)).map
          (renameCardinalityDef
            (bundleConceptEmbedding decoded.sourceTargets decoded.bundles)))
        ((pairs.map (renamePairedCardinality Sum.inr)).map
          (renamePairedCardinality
            (bundleConceptEmbedding decoded.sourceTargets decoded.bundles))) ∧
      J.RealizesLiterals
        (query.map (renameLit decoded.sourceQueryEmbedding)) element := by
  have hpositive : 0 < decoded.bundles.length :=
    List.length_pos_of_ne_nil decoded.nonemptyBundles
  letI : Nonempty
      (Sum (Fin decoded.bundles.length) (Fin decoded.sourceConcepts.length)) :=
    ⟨.inl ⟨0, hpositive⟩⟩
  obtain ⟨inverse, hleft⟩ := decoded.embeddingInjective.hasLeftInverse
  let embedding := bundleConceptEmbedding decoded.sourceTargets decoded.bundles
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
  have hsourceTargets : I.modelsPairedCardinalityTargets definitions pairs :=
    (modelsProjectedCardinalityDefs_iff_pairedTargets I definitions pairs hpairs).1
      hcardinality
  have hextendedCardinality : extended.modelsPairedCardinalityTargets
      (definitions.map (renameCardinalityDef Sum.inr))
      (pairs.map (renamePairedCardinality Sum.inr)) := by
    apply (modelsPairedCardinalityTargets_rename_pullback_iff
      Sum.inr extended definitions pairs).2
    simpa [extended, pullbackConcepts, indexedBundleExtension] using hsourceTargets
  let J := pushforwardConcepts inverse extended
  have hrenamed : J.models (renameOntology embedding
      (indexedBundleOntology decoded.direct (decodedBundleSpecs decoded.bundles) ++
        indexedBundleDomainOntology (decodedBundleSpecs decoded.bundles)
          decoded.domainExtras)) :=
    (models_rename_pushforward_iff embedding inverse hleft extended _).2 hdomains
  have htargetCardinality : J.modelsPairedCardinalityTargets
      ((definitions.map (renameCardinalityDef Sum.inr)).map
        (renameCardinalityDef embedding))
      ((pairs.map (renamePairedCardinality Sum.inr)).map
        (renamePairedCardinality embedding)) := by
    apply (modelsPairedCardinalityTargets_rename_pullback_iff embedding J
      (definitions.map (renameCardinalityDef Sum.inr))
      (pairs.map (renamePairedCardinality Sum.inr))).2
    simpa [J, pullback_pushforward_eq embedding inverse hleft] using
      hextendedCardinality
  have haboxTarget : abox.models J value := by
    apply abox.models_of_mapConcepts sourceOf I J value
    · intro individual concept hused
      have hinverse : inverse concept = .inr (sourceOf concept) := by
        calc
          inverse concept = inverse (embedding (.inr (sourceOf concept))) :=
            congrArg inverse (hembedded individual concept hused).symm
          _ = .inr (sourceOf concept) := hleft _
      simp [J, pushforwardConcepts, hinverse, extended, indexedBundleExtension]
    · rfl
    · exact habox
  have hqueryTarget : J.RealizesLiterals
      (query.map (renameLit decoded.sourceQueryEmbedding)) element := by
    intro targetLiteral htargetLiteral
    rcases List.mem_map.mp htargetLiteral with ⟨literal, hliteral, rfl⟩
    have hsourceLiteral := hquery literal hliteral
    have hinverse : inverse (embedding (.inr literal.concept)) =
        .inr literal.concept := hleft _
    rw [satLit_rename_pullback_iff]
    cases literal <;>
      simpa [pullbackConcepts, DecodedBundleProjection.sourceQueryEmbedding,
        embedding, J, pushforwardConcepts, extended, indexedBundleExtension,
        renameLit, hinverse, Interp.satLit] using hsourceLiteral
  exact ⟨J, (models_iff_of_toFinset_eq J _ _ decoded.exactProjection).1 hrenamed,
    haboxTarget, htargetCardinality, hqueryTarget⟩

/-! ## Bundle source cardinality taxonomy wire -/

def NativeABox.SatisfiableWithBundleProjectedCardinalityQuery
    (abox : NativeABox Individual TargetConcept Role)
    (sourceOf : TargetConcept → SourceConcept)
    (direct : List (Clause Variable SourceConcept Role))
    (bundles : Fin n → BundleSpec Variable SourceConcept Role Function)
    (definitions : List (CardinalityDef SourceConcept Role))
    (pairs : List (PairedCardinality SourceConcept Role))
    (query : List (Lit SourceConcept)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain SourceConcept Role)
      (functions : SkolemInterp Domain Function) (value : Individual → Domain)
      (element : Domain),
    Nonempty Domain ∧ I.models direct ∧ ModelsBundles I functions bundles ∧
      (abox.mapConcepts sourceOf).models I value ∧
      I.modelsProjectedCardinalityDefs definitions pairs ∧
      I.RealizesLiterals query element

structure WireBundleNativeABoxCardinalityTaxonomyProjection where
  source_concepts : List String
  functions : List String
  direct : List WireDirectSourceClause
  bundles : List WireSkolemBundle
  domain_extras : List WireBundleDomainExtra
  definitions : List WireProjectionCardinalityDef
  exact_pairs : List WireComplementaryCardinalityPair
  abox_source_map : List Nat
deriving FromJson, ToJson, Repr

structure DecodedBundleNativeABoxCardinalityTaxonomySat where
  sourceProjection : DecodedBundleNativeABoxCardinalitySatCertificate
  query : DecodedNativeABoxTaxonomyQuery
    sourceProjection.certificate.seed.nodeCount
    sourceProjection.certificate.seed.abox.concepts.length
  query_present : ∀ literal ∈ query.literals,
    (query.root, literal) ∈
      sourceProjection.certificate.seed.state.base.base.labels
  query_embedded : ∀ literal ∈ query.literals,
    bundleConceptEmbedding sourceProjection.sourceTargets sourceProjection.bundles
      (.inr (sourceProjection.sourceOf literal.concept)) = literal.concept

structure DecodedBundleNativeABoxCardinalityTaxonomyUnsat where
  taxonomy : DecodedNativeABoxCardinalityTaxonomyUnsat
  variable_ge_two : 2 ≤ taxonomy.initial.variableCount
  sourceConcepts : List String
  functions : List String
  sourceTargets : Fin sourceConcepts.length →
    Fin taxonomy.initial.abox.concepts.length
  direct : List (Clause (Fin taxonomy.initial.variableCount)
    (Fin sourceConcepts.length) (Fin taxonomy.initial.abox.roles.length))
  bundles : List (DecodedWireBundle (Fin taxonomy.initial.variableCount)
    (Fin sourceConcepts.length) (Fin taxonomy.initial.abox.roles.length)
    (Fin functions.length) (Fin taxonomy.initial.abox.concepts.length))
  domainExtras : List (IndexedBundleDomainSpec (Fin sourceConcepts.length)
    (Fin taxonomy.initial.abox.roles.length) bundles.length)
  nonemptyBundles : bundles ≠ []
  uniqueFunctions :
    (skolemPairFunctions (indexedBundlePairs (decodedBundleSpecs bundles))).Nodup
  embeddingInjective : Function.Injective
    (bundleConceptEmbedding sourceTargets bundles)
  rboxSource : Fin taxonomy.initial.variableCount
  rboxTarget : Fin taxonomy.initial.variableCount
  rboxDistinct : rboxSource ≠ rboxTarget
  pathPremises : ∀ spec ∈ domainExtras, ∀ clause ∈
    roleInclusionPathClauses
      (decodedBundleSpecs bundles spec.bundle).role spec.path rboxSource rboxTarget,
    clause ∈ direct
  domainPremises : ∀ spec ∈ domainExtras,
    roleDomainClause (spec.superRole (decodedBundleSpecs bundles)) spec.domain
      rboxSource rboxTarget ∈ direct
  sourceOf : Fin taxonomy.initial.abox.concepts.length → Fin sourceConcepts.length
  abox_embedded : ∀ individual concept,
    concept ∈ taxonomy.initial.abox.abox.proxies individual ++
      taxonomy.initial.abox.abox.assertions individual →
    bundleConceptEmbedding sourceTargets bundles (.inr (sourceOf concept)) = concept
  query_embedded : ∀ literal ∈ taxonomy.query.literals,
    bundleConceptEmbedding sourceTargets bundles (.inr (sourceOf literal.concept)) =
      literal.concept
  definitions : List (CardinalityDef (Fin sourceConcepts.length)
    (Fin taxonomy.initial.abox.roles.length))
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
      taxonomy.definitions
  exact_ontology :
    (renameOntology (bundleConceptEmbedding sourceTargets bundles)
      (indexedBundleOntology direct (decodedBundleSpecs bundles) ++
        indexedBundleDomainOntology (decodedBundleSpecs bundles) domainExtras) ++
      taxonomy.initial.abox.negativeRoleClausesAt taxonomy.initial.variableCount
        variable_ge_two).toFinset =
      taxonomy.initial.state.base.base.ontology.toFinset

def DecodedBundleNativeABoxCardinalityTaxonomyUnsat.semanticPairs
    (decoded : DecodedBundleNativeABoxCardinalityTaxonomyUnsat) :
    List (PairedCardinality (Fin decoded.sourceConcepts.length)
      (Fin decoded.taxonomy.initial.abox.roles.length)) :=
  decoded.cardinalityPairs.map IndexedComplementaryCardinalityPair.toPair

theorem DecodedBundleNativeABoxCardinalityTaxonomyUnsat.semanticPairs_mem
    (decoded : DecodedBundleNativeABoxCardinalityTaxonomyUnsat)
    (pair : PairedCardinality (Fin decoded.sourceConcepts.length)
      (Fin decoded.taxonomy.initial.abox.roles.length))
    (hpair : pair ∈ decoded.semanticPairs) :
    pair.maximum ∈ decoded.definitions ∧ pair.minimum ∈ decoded.definitions := by
  simp only [DecodedBundleNativeABoxCardinalityTaxonomyUnsat.semanticPairs,
    List.mem_map] at hpair
  rcases hpair with ⟨indexed, _, rfl⟩
  exact ⟨List.get_mem decoded.definitions indexed.maximum,
    List.get_mem decoded.definitions indexed.minimum⟩

inductive DecodedBundleNativeABoxCardinalityTaxonomyDecision where
  | sat (decoded : DecodedBundleNativeABoxCardinalityTaxonomySat)
  | unsat (decoded : DecodedBundleNativeABoxCardinalityTaxonomyUnsat)

structure WireBundleNativeABoxCardinalityTaxonomyDecision where
  version : Nat
  projection : WireBundleNativeABoxCardinalityTaxonomyProjection
  decision : WireNativeABoxCardinalityTaxonomyDecision
deriving FromJson, ToJson, Repr

def WireBundleNativeABoxCardinalityTaxonomyDecision.decode
    (wire : WireBundleNativeABoxCardinalityTaxonomyDecision) :
    Except String DecodedBundleNativeABoxCardinalityTaxonomyDecision := do
  if wire.version != 1 then
    throw s!"unsupported bundle native ABox cardinality taxonomy version {wire.version}"
  match wire.decision.evidence with
  | .sat certificateWire =>
      let sourceProjection ← ({
        source_concepts := wire.projection.source_concepts
        functions := wire.projection.functions
        direct := wire.projection.direct
        bundles := wire.projection.bundles
        domain_extras := wire.projection.domain_extras
        definitions := wire.projection.definitions
        exact_pairs := wire.projection.exact_pairs
        abox_source_map := wire.projection.abox_source_map
        certificate := certificateWire
      } : WireBundleNativeABoxCardinalitySatCertificate).decode
      let query ← wire.decision.query.decode
        sourceProjection.certificate.seed.nodeCount
        sourceProjection.certificate.seed.abox.concepts.length
      if hquery : query.labelsPresentB
          sourceProjection.certificate.seed.state.base.base.labels = true then
        let embedding := fun source => bundleConceptEmbedding
          sourceProjection.sourceTargets sourceProjection.bundles (.inr source)
        if hqueryEmbedded : queryConceptsEmbeddedB query.literals
            sourceProjection.sourceOf embedding = true then
          return .sat {
            sourceProjection
            query
            query_present := query.labelsPresentB_sound _ hquery
            query_embedded := queryConceptsEmbeddedB_sound _ _ _ hqueryEmbedded
          }
        else throw "bundle cardinality taxonomy query is not an embedded source concept"
      else throw "bundle cardinality taxonomy countermodel omits its query literals"
  | .unsat .. =>
      let taxonomy ← wire.decision.decode
      let taxonomy ← match taxonomy with
        | .unsat decoded => pure decoded
        | .sat _ => throw "internal bundle cardinality taxonomy evidence mismatch"
      let variableWitness ← requireAtLeastTwoVariables taxonomy.initial.variableCount
      let hvariables := variableWitness.proof
      if _hsourceConcepts : wire.projection.source_concepts.Nodup then
        if _hfunctions : wire.projection.functions.Nodup then
          let sourceTargets ← checkedNameEmbedding "source concept in target"
            wire.projection.source_concepts taxonomy.initial.abox.concepts
          let direct ← wire.projection.direct.mapM (WireDirectSourceClause.decode
            taxonomy.initial.variableCount wire.projection.source_concepts
            taxonomy.initial.abox.roles)
          let bundles ← wire.projection.bundles.mapM (WireSkolemBundle.decode
            taxonomy.initial.variableCount wire.projection.source_concepts
            taxonomy.initial.abox.concepts taxonomy.initial.abox.roles
            wire.projection.functions)
          if hnonempty : bundles ≠ [] then
            let rboxSource : Fin taxonomy.initial.variableCount :=
              ⟨0, lt_of_lt_of_le Nat.zero_lt_two hvariables⟩
            let rboxTarget : Fin taxonomy.initial.variableCount := ⟨1, hvariables⟩
            have hrboxDistinct : rboxSource ≠ rboxTarget := by
              intro hequal
              have hval := congrArg Fin.val hequal
              simp [rboxSource, rboxTarget] at hval
            let domainExtras ← wire.projection.domain_extras.mapM
              (WireBundleDomainExtra.decode wire.projection.source_concepts
                taxonomy.initial.abox.roles bundles.length)
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
                      wire.projection.source_concepts.length
                      taxonomy.initial.abox.concepts.length
                      wire.projection.abox_source_map
                    let embedding := fun source =>
                      bundleConceptEmbedding sourceTargets bundles (.inr source)
                    if haboxEmbedded : taxonomy.initial.abox.abox.conceptsEmbeddedB
                        sourceOf embedding = true then
                      if hqueryEmbedded : queryConceptsEmbeddedB taxonomy.query.literals
                          sourceOf embedding = true then
                        let definitions ← wire.projection.definitions.mapM
                          (WireProjectionCardinalityDef.decode
                            wire.projection.source_concepts.length
                            taxonomy.initial.abox.roles.length)
                        if hlength : wire.projection.definitions.length =
                            definitions.length then
                          if hdefinitionUnique : definitions.Nodup then
                            let cardinalityPairs ← wire.projection.exact_pairs.mapM
                              (WireComplementaryCardinalityPair.decode definitions)
                            if hpairs : (exactPairIndices cardinalityPairs).Nodup then
                              if hflags : ∀ index : Fin definitions.length,
                                  (wire.projection.definitions.get
                                    (hlength.symm ▸ index)).exact =
                                    decide (index.val ∈ exactPairIndices cardinalityPairs) then
                                if hdefinitions :
                                    ((definitions.map (renameCardinalityDef Sum.inr)).map
                                      (renameCardinalityDef
                                        (bundleConceptEmbedding sourceTargets bundles))) =
                                      taxonomy.definitions then
                                  if hequal :
                                      (renameOntology
                                        (bundleConceptEmbedding sourceTargets bundles)
                                        (indexedBundleOntology direct
                                            (decodedBundleSpecs bundles) ++
                                          indexedBundleDomainOntology
                                            (decodedBundleSpecs bundles) domainExtras) ++
                                        taxonomy.initial.abox.negativeRoleClausesAt
                                          taxonomy.initial.variableCount hvariables).toFinset =
                                        taxonomy.initial.state.base.base.ontology.toFinset then
                                    return .unsat {
                                      taxonomy
                                      variable_ge_two := hvariables
                                      sourceConcepts := wire.projection.source_concepts
                                      functions := wire.projection.functions
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
                                      abox_embedded :=
                                        taxonomy.initial.abox.abox.conceptsEmbeddedB_sound
                                          sourceOf embedding haboxEmbedded
                                      query_embedded := queryConceptsEmbeddedB_sound _ _ _
                                        hqueryEmbedded
                                      definitions
                                      definitionWires := wire.projection.definitions
                                      wireLength := hlength
                                      uniqueDefinitions := hdefinitionUnique
                                      cardinalityPairs
                                      uniquePairIndices := hpairs
                                      exactFlags := hflags
                                      definitions_equal := hdefinitions
                                      exact_ontology := hequal
                                    }
                                  else throw "bundle source conversion differs from the cardinality taxonomy refutation ontology"
                                else throw "bundle cardinality definitions differ from the taxonomy refutation"
                              else throw "cardinality exact flags differ from complementary-pair provenance"
                            else throw "an exact cardinality definition occurs in more than one pair"
                          else throw "bundle cardinality taxonomy contains duplicate definitions"
                        else throw "internal bundle cardinality taxonomy definition length mismatch"
                      else throw "bundle cardinality taxonomy query is not an embedded source concept"
                    else throw "native ABox concept is not an embedded bundle source concept"
                  else throw "bundle domain premise is absent from the source ontology"
                else throw "bundle role-inclusion path is absent from the source ontology"
              else throw "bundle definers collide with each other or source concepts"
            else throw "bundle cardinality taxonomy projection reuses a Skolem function"
          else throw "bundle cardinality taxonomy projection contains no bundles"
        else throw "bundle cardinality taxonomy function-name table contains duplicates"
      else throw "bundle cardinality taxonomy source concept-name table contains duplicates"

def WireBundleNativeABoxCardinalityTaxonomyDecision.check
    (wire : WireBundleNativeABoxCardinalityTaxonomyDecision) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedBundleNativeABoxCardinalityTaxonomySat.source_satisfiable
    (decoded : DecodedBundleNativeABoxCardinalityTaxonomySat) :
    NativeABox.SatisfiableWithBundleProjectedCardinalityQuery
      decoded.sourceProjection.certificate.seed.abox.abox
      decoded.sourceProjection.sourceOf decoded.sourceProjection.direct
      (decodedBundleSpecs decoded.sourceProjection.bundles)
      decoded.sourceProjection.definitions decoded.sourceProjection.semanticPairs
      (decoded.query.literals.map (renameLit decoded.sourceProjection.sourceOf)) := by
  let certificate := decoded.sourceProjection.certificate
  rcases certificate.canonical_model with
    ⟨value, hdomain, htarget, hdefinitions, habox⟩
  let J := certificate.seed.state.base.state.quotientCanonical
  let nodeValue : Fin certificate.seed.nodeCount →
      certificate.seed.state.base.state.QuotientDomain :=
    fun node => Quotient.mk certificate.seed.state.base.state.nodeSetoid node
  have hparts := certificate.cardinality
  simp only [FiniteEqCertificate.checkEqSatWithCardinality,
    Bool.and_eq_true] at hparts
  have hrealized : certificate.seed.state.base.state.RealizedBy J nodeValue :=
    certificate.seed.state.base.checkEqSat_realizes hparts.1
  have hquery : J.RealizesLiterals decoded.query.literals
      (nodeValue decoded.query.root) := by
    intro literal hliteral
    exact hrealized.1.1 decoded.query.root literal
      (decoded.query_present literal hliteral)
  let targetCore := renameOntology
    (bundleConceptEmbedding decoded.sourceProjection.sourceTargets
      decoded.sourceProjection.bundles)
    (indexedBundleOntology decoded.sourceProjection.direct
        (decodedBundleSpecs decoded.sourceProjection.bundles) ++
      indexedBundleDomainOntology (decodedBundleSpecs decoded.sourceProjection.bundles)
        decoded.sourceProjection.domainExtras)
  have happended : J.models (targetCore ++
      certificate.seed.abox.negativeRoleClausesAt certificate.seed.variableCount
        decoded.sourceProjection.variable_ge_two) :=
    (models_iff_of_toFinset_eq J _ _
      decoded.sourceProjection.exact_ontology).2 htarget
  have hcore : J.models targetCore := by
    intro clause hclause
    exact happended clause (List.mem_append_left _ hclause)
  let projection : DecodedBundleProjection := {
    variableCount := certificate.seed.variableCount
    sourceConcepts := decoded.sourceProjection.sourceConcepts
    concepts := certificate.seed.abox.concepts
    roles := certificate.seed.abox.roles
    functions := decoded.sourceProjection.functions
    sourceTargets := decoded.sourceProjection.sourceTargets
    direct := decoded.sourceProjection.direct
    bundles := decoded.sourceProjection.bundles
    domainExtras := decoded.sourceProjection.domainExtras
    target := targetCore
    nonemptyBundles := decoded.sourceProjection.nonemptyBundles
    uniqueFunctions := decoded.sourceProjection.uniqueFunctions
    embeddingInjective := decoded.sourceProjection.embeddingInjective
    rboxSource := decoded.sourceProjection.rboxSource
    rboxTarget := decoded.sourceProjection.rboxTarget
    rboxDistinct := decoded.sourceProjection.rboxDistinct
    pathPremises := decoded.sourceProjection.pathPremises
    domainPremises := decoded.sourceProjection.domainPremises
    exactProjection := rfl
  }
  have hexact := certificate.models_exact_definitions
  have htargetPairs : J.modelsPairedCardinalityTargets
      ((decoded.sourceProjection.definitions.map
          (renameCardinalityDef Sum.inr)).map
        (renameCardinalityDef (bundleConceptEmbedding
          decoded.sourceProjection.sourceTargets decoded.sourceProjection.bundles)))
      ((decoded.sourceProjection.semanticPairs.map
          (renamePairedCardinality Sum.inr)).map
        (renamePairedCardinality (bundleConceptEmbedding
          decoded.sourceProjection.sourceTargets decoded.sourceProjection.bundles))) := by
    refine ⟨?_, ?_⟩
    · rw [decoded.sourceProjection.definitions_equal]
      exact hdefinitions
    · intro pair hpair
      simp only [List.mem_map] at hpair
      rcases hpair with ⟨intermediate, hintermediate, rfl⟩
      rcases hintermediate with ⟨sourcePair, hsourcePair, rfl⟩
      exact ⟨hexact _
          (decoded.sourceProjection.exact_pair_coverage sourcePair hsourcePair).1,
        hexact _
          (decoded.sourceProjection.exact_pair_coverage sourcePair hsourcePair).2⟩
  have hroundtrip :
      (decoded.query.literals.map (renameLit decoded.sourceProjection.sourceOf)).map
          (renameLit projection.sourceQueryEmbedding) = decoded.query.literals :=
    map_source_query_roundtrip _ _ _ decoded.query_embedded
  have hqueryMapped : J.RealizesLiterals
      ((decoded.query.literals.map (renameLit decoded.sourceProjection.sourceOf)).map
        (renameLit projection.sourceQueryEmbedding)) (nodeValue decoded.query.root) := by
    rw [hroundtrip]
    exact hquery
  letI : Nonempty certificate.seed.state.base.state.QuotientDomain := hdomain
  let base : SkolemInterp certificate.seed.state.base.state.QuotientDomain
      (Fin decoded.sourceProjection.functions.length) :=
    ⟨fun _ _ => Classical.choice hdomain⟩
  rcases projection.target_model_to_source_model_preserving_nativeABox_cardinality_query
      certificate.seed.abox.abox decoded.sourceProjection.sourceOf
      decoded.sourceProjection.abox_embedded decoded.sourceProjection.definitions
      decoded.sourceProjection.semanticPairs
      (fun pair hpair => decoded.sourceProjection.semanticPairs_mem pair hpair)
      (decoded.query.literals.map (renameLit decoded.sourceProjection.sourceOf))
      J base value (nodeValue decoded.query.root) hcore habox htargetPairs hqueryMapped with
    ⟨I, functions, hdirect, hbundles, haboxSource, hcardinality, hquerySource⟩
  exact ⟨certificate.seed.state.base.state.QuotientDomain, I, functions, value,
    nodeValue decoded.query.root, hdomain, hdirect, hbundles, haboxSource,
    hcardinality, hquerySource⟩

theorem DecodedBundleNativeABoxCardinalityTaxonomyUnsat.source_unsatisfiable
    (decoded : DecodedBundleNativeABoxCardinalityTaxonomyUnsat) :
    ¬NativeABox.SatisfiableWithBundleProjectedCardinalityQuery
      decoded.taxonomy.initial.abox.abox decoded.sourceOf decoded.direct
      (decodedBundleSpecs decoded.bundles) decoded.definitions decoded.semanticPairs
      (decoded.taxonomy.query.literals.map (renameLit decoded.sourceOf)) := by
  rintro ⟨Domain, I, functions, value, element, hdomain, hdirect, hbundles,
    habox, hcardinality, hquery⟩
  let targetCore := renameOntology
    (bundleConceptEmbedding decoded.sourceTargets decoded.bundles)
    (indexedBundleOntology decoded.direct (decodedBundleSpecs decoded.bundles) ++
      indexedBundleDomainOntology (decodedBundleSpecs decoded.bundles)
        decoded.domainExtras)
  let projection : DecodedBundleProjection := {
    variableCount := decoded.taxonomy.initial.variableCount
    sourceConcepts := decoded.sourceConcepts
    concepts := decoded.taxonomy.initial.abox.concepts
    roles := decoded.taxonomy.initial.abox.roles
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
  obtain ⟨J, hcore, haboxTarget, htargetPairs, hqueryMapped⟩ :=
    projection.source_model_to_target_model_preserving_nativeABox_cardinality_query
      decoded.taxonomy.initial.abox.abox decoded.sourceOf decoded.abox_embedded
      decoded.definitions decoded.semanticPairs
      (fun pair hpair => decoded.semanticPairs_mem pair hpair)
      (decoded.taxonomy.query.literals.map (renameLit decoded.sourceOf))
      I functions value element hdirect hbundles habox hcardinality hquery
  have hroundtrip :
      (decoded.taxonomy.query.literals.map (renameLit decoded.sourceOf)).map
          (renameLit projection.sourceQueryEmbedding) =
        decoded.taxonomy.query.literals :=
    map_source_query_roundtrip _ _ _ decoded.query_embedded
  have hqueryTarget : J.RealizesLiterals decoded.taxonomy.query.literals element := by
    rw [← hroundtrip]
    exact hqueryMapped
  have happended : J.models (targetCore ++
      decoded.taxonomy.initial.abox.negativeRoleClausesAt
        decoded.taxonomy.initial.variableCount decoded.variable_ge_two) :=
    (decoded.taxonomy.initial.abox.models_append_negativeRoleClausesAt_iff
      J value haboxTarget.1 decoded.variable_ge_two targetCore).2
        ⟨hcore, haboxTarget.2.2.2.2⟩
  have htarget : J.models decoded.taxonomy.initial.state.base.base.ontology :=
    (models_iff_of_toFinset_eq J _ _ decoded.exact_ontology).1 happended
  have hdefinitions : J.modelsCardinalityDefs decoded.taxonomy.definitions := by
    rw [← decoded.definitions_equal]
    exact htargetPairs.1
  exact decoded.taxonomy.unsatisfiable
    ⟨Domain, J, value, element, hdomain, htarget, hdefinitions,
      haboxTarget, hqueryTarget⟩

def DecodedBundleNativeABoxCardinalityTaxonomyDecision.SemanticallyValid :
    DecodedBundleNativeABoxCardinalityTaxonomyDecision → Prop
  | .sat decoded =>
      NativeABox.SatisfiableWithBundleProjectedCardinalityQuery
        decoded.sourceProjection.certificate.seed.abox.abox
        decoded.sourceProjection.sourceOf decoded.sourceProjection.direct
        (decodedBundleSpecs decoded.sourceProjection.bundles)
        decoded.sourceProjection.definitions decoded.sourceProjection.semanticPairs
        (decoded.query.literals.map (renameLit decoded.sourceProjection.sourceOf))
  | .unsat decoded =>
      ¬NativeABox.SatisfiableWithBundleProjectedCardinalityQuery
        decoded.taxonomy.initial.abox.abox decoded.sourceOf decoded.direct
        (decodedBundleSpecs decoded.bundles) decoded.definitions decoded.semanticPairs
        (decoded.taxonomy.query.literals.map (renameLit decoded.sourceOf))

theorem DecodedBundleNativeABoxCardinalityTaxonomyDecision.semantic_valid
    (decoded : DecodedBundleNativeABoxCardinalityTaxonomyDecision) :
    decoded.SemanticallyValid := by
  cases decoded with
  | sat result => exact result.source_satisfiable
  | unsat result => exact result.source_unsatisfiable

def DecodedBundleNativeABoxCardinalityTaxonomyDecision.positive :
    DecodedBundleNativeABoxCardinalityTaxonomyDecision → Bool
  | .sat _ => false
  | .unsat _ => true

def DecodedBundleNativeABoxCardinalityTaxonomyDecision.QueryEntailed :
    DecodedBundleNativeABoxCardinalityTaxonomyDecision → Prop
  | .sat decoded =>
      ¬NativeABox.SatisfiableWithBundleProjectedCardinalityQuery
        decoded.sourceProjection.certificate.seed.abox.abox
        decoded.sourceProjection.sourceOf decoded.sourceProjection.direct
        (decodedBundleSpecs decoded.sourceProjection.bundles)
        decoded.sourceProjection.definitions decoded.sourceProjection.semanticPairs
        (decoded.query.literals.map (renameLit decoded.sourceProjection.sourceOf))
  | .unsat decoded =>
      ¬NativeABox.SatisfiableWithBundleProjectedCardinalityQuery
        decoded.taxonomy.initial.abox.abox decoded.sourceOf decoded.direct
        (decodedBundleSpecs decoded.bundles) decoded.definitions decoded.semanticPairs
        (decoded.taxonomy.query.literals.map (renameLit decoded.sourceOf))

theorem DecodedBundleNativeABoxCardinalityTaxonomyDecision.positive_eq_true_iff
    (decision : DecodedBundleNativeABoxCardinalityTaxonomyDecision) :
    decision.positive = true ↔ decision.QueryEntailed := by
  cases decision with
  | sat decoded =>
      have hsemantic := decoded.source_satisfiable
      change (false = true ↔
        ¬NativeABox.SatisfiableWithBundleProjectedCardinalityQuery
          decoded.sourceProjection.certificate.seed.abox.abox
          decoded.sourceProjection.sourceOf decoded.sourceProjection.direct
          (decodedBundleSpecs decoded.sourceProjection.bundles)
          decoded.sourceProjection.definitions decoded.sourceProjection.semanticPairs
          (decoded.query.literals.map (renameLit decoded.sourceProjection.sourceOf)))
      exact ⟨fun hfalse => by contradiction,
        fun hnot => False.elim (hnot hsemantic)⟩
  | unsat decoded =>
      have hsemantic := decoded.source_unsatisfiable
      change (true = true ↔
        ¬NativeABox.SatisfiableWithBundleProjectedCardinalityQuery
          decoded.taxonomy.initial.abox.abox decoded.sourceOf decoded.direct
          (decodedBundleSpecs decoded.bundles) decoded.definitions decoded.semanticPairs
          (decoded.taxonomy.query.literals.map (renameLit decoded.sourceOf)))
      exact ⟨fun _ => hsemantic, fun _ => rfl⟩

structure WireBundleNativeABoxCardinalityTaxonomyMatrix where
  version : Nat
  projection : WireBundleNativeABoxCardinalityTaxonomyProjection
  matrix : WireNativeABoxCardinalityTaxonomyMatrix
deriving FromJson, ToJson, Repr

structure DecodedBundleNativeABoxCardinalityTaxonomyMatrix where
  matrix : DecodedNativeABoxCardinalityTaxonomyMatrix
  concepts : List DecodedBundleNativeABoxCardinalityTaxonomyDecision
  subsumptions : List (List DecodedBundleNativeABoxCardinalityTaxonomyDecision)

def WireBundleNativeABoxCardinalityTaxonomyMatrix.decode
    (wire : WireBundleNativeABoxCardinalityTaxonomyMatrix) :
    Except String DecodedBundleNativeABoxCardinalityTaxonomyMatrix := do
  if wire.version != 1 then
    throw s!"unsupported bundle native ABox cardinality taxonomy matrix version {wire.version}"
  let matrix ← wire.matrix.decode
  let wrap := fun decision => ({
    version := 1
    projection := wire.projection
    decision
  } : WireBundleNativeABoxCardinalityTaxonomyDecision)
  let concepts ← wire.matrix.concepts.mapM fun decision => (wrap decision).decode
  let subsumptions ← wire.matrix.subsumptions.mapM fun row =>
    row.mapM fun decision => (wrap decision).decode
  return { matrix, concepts, subsumptions }

def WireBundleNativeABoxCardinalityTaxonomyMatrix.check
    (wire : WireBundleNativeABoxCardinalityTaxonomyMatrix) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedBundleNativeABoxCardinalityTaxonomyMatrix.allDecisions
    (decoded : DecodedBundleNativeABoxCardinalityTaxonomyMatrix) :
    List DecodedBundleNativeABoxCardinalityTaxonomyDecision :=
  decoded.concepts ++ decoded.subsumptions.flatten

def DecodedBundleNativeABoxCardinalityTaxonomyMatrix.SemanticallyValid
    (decoded : DecodedBundleNativeABoxCardinalityTaxonomyMatrix) : Prop :=
  decoded.matrix.wire.shapeB = true ∧ decoded.matrix.wire.queriesB = true ∧
  decoded.matrix.wire.sharedProblemB = true ∧
  ∀ decision ∈ decoded.allDecisions, decision.SemanticallyValid

theorem DecodedBundleNativeABoxCardinalityTaxonomyMatrix.semantic_valid
    (decoded : DecodedBundleNativeABoxCardinalityTaxonomyMatrix) :
    decoded.SemanticallyValid := by
  refine ⟨decoded.matrix.complete_shape, decoded.matrix.exact_queries,
    decoded.matrix.shared_problem, ?_⟩
  intro decision _
  exact decision.semantic_valid

#print axioms DecodedDirectNativeABoxCardinalityTaxonomyDecision.semantic_valid
#print axioms DecodedDirectNativeABoxCardinalityTaxonomyDecision.positive_eq_true_iff
#print axioms DecodedDirectNativeABoxCardinalityTaxonomyMatrix.semantic_valid
#print axioms DecodedMixedNativeABoxCardinalityTaxonomyDecision.semantic_valid
#print axioms DecodedMixedNativeABoxCardinalityTaxonomyDecision.positive_eq_true_iff
#print axioms DecodedMixedNativeABoxCardinalityTaxonomyMatrix.semantic_valid
#print axioms DecodedBundleNativeABoxCardinalityTaxonomyDecision.semantic_valid
#print axioms DecodedBundleNativeABoxCardinalityTaxonomyDecision.positive_eq_true_iff
#print axioms DecodedBundleNativeABoxCardinalityTaxonomyMatrix.semantic_valid

end ContextCalculus.Hypertableau
