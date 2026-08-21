import ContextCalculus.HypertableauNativeABoxTaxonomyMatrixWire
import ContextCalculus.HypertableauNativeABoxSourceDecisionWire

/-!
# Source-composed native-ABox taxonomy decisions

The direct source wrapper binds one taxonomy query to the exact source clauses
whose projection, together with checked negative-role guards, is the ontology
inside the finite model or refutation.  Query semantics are therefore proved
for the source problem rather than only for the normalized target.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireDirectNativeABoxTaxonomyDecision where
  version : Nat
  source : List WireDirectSourceClause
  decision : WireNativeABoxTaxonomyDecision
deriving FromJson, ToJson, Repr

structure DecodedDirectNativeABoxTaxonomySat where
  taxonomy : DecodedNativeABoxTaxonomySat
  variable_ge_two : 2 ≤ taxonomy.certificate.seed.variableCount
  source : List (Clause (Fin taxonomy.certificate.seed.variableCount)
    (Fin taxonomy.certificate.seed.abox.concepts.length)
    (Fin taxonomy.certificate.seed.abox.roles.length))
  exact_projection : source ++
      taxonomy.certificate.seed.abox.negativeRoleClausesAt
        taxonomy.certificate.seed.variableCount variable_ge_two =
      taxonomy.certificate.seed.state.base.base.ontology

structure DecodedDirectNativeABoxTaxonomyUnsat where
  taxonomy : DecodedNativeABoxTaxonomyUnsat
  variable_ge_two : 2 ≤ taxonomy.initial.variableCount
  source : List (Clause (Fin taxonomy.initial.variableCount)
    (Fin taxonomy.initial.abox.concepts.length)
    (Fin taxonomy.initial.abox.roles.length))
  exact_projection : source ++ taxonomy.initial.abox.negativeRoleClausesAt
      taxonomy.initial.variableCount variable_ge_two =
    taxonomy.initial.state.base.base.ontology

inductive DecodedDirectNativeABoxTaxonomyDecision where
  | sat (decoded : DecodedDirectNativeABoxTaxonomySat)
  | unsat (decoded : DecodedDirectNativeABoxTaxonomyUnsat)

def WireDirectNativeABoxTaxonomyDecision.decode
    (wire : WireDirectNativeABoxTaxonomyDecision) :
    Except String DecodedDirectNativeABoxTaxonomyDecision := do
  if wire.version != 1 then
    throw s!"unsupported direct native ABox taxonomy source version {wire.version}"
  match ← wire.decision.decode with
  | .sat taxonomy =>
      let variableWitness ← requireAtLeastTwoVariables
        taxonomy.certificate.seed.variableCount
      let hvariables := variableWitness.proof
      let source ← wire.source.mapM (WireDirectSourceClause.decode
        taxonomy.certificate.seed.variableCount
        taxonomy.certificate.seed.abox.concepts
        taxonomy.certificate.seed.abox.roles)
      if hequal : source ++ taxonomy.certificate.seed.abox.negativeRoleClausesAt
          taxonomy.certificate.seed.variableCount hvariables =
          taxonomy.certificate.seed.state.base.base.ontology then
        return .sat {
          taxonomy
          variable_ge_two := hvariables
          source
          exact_projection := hequal
        }
      else throw "direct source conversion differs from the native ABox taxonomy model"
  | .unsat taxonomy =>
      let variableWitness ← requireAtLeastTwoVariables taxonomy.initial.variableCount
      let hvariables := variableWitness.proof
      let source ← wire.source.mapM (WireDirectSourceClause.decode
        taxonomy.initial.variableCount taxonomy.initial.abox.concepts
        taxonomy.initial.abox.roles)
      if hequal : source ++ taxonomy.initial.abox.negativeRoleClausesAt
          taxonomy.initial.variableCount hvariables =
          taxonomy.initial.state.base.base.ontology then
        return .unsat {
          taxonomy
          variable_ge_two := hvariables
          source
          exact_projection := hequal
        }
      else throw "direct source conversion differs from the native ABox taxonomy refutation"

def WireDirectNativeABoxTaxonomyDecision.check
    (wire : WireDirectNativeABoxTaxonomyDecision) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedDirectNativeABoxTaxonomySat.source_satisfiable
    (decoded : DecodedDirectNativeABoxTaxonomySat) :
    decoded.taxonomy.certificate.seed.abox.abox.SatisfiableWithQuery
      decoded.source decoded.taxonomy.query.literals := by
  rcases decoded.taxonomy.certificate.satisfiable_with_query
      decoded.taxonomy.query.root decoded.taxonomy.query.literals
      decoded.taxonomy.query_present with
    ⟨Domain, I, value, element, hdomain, htarget, habox, hquery⟩
  have happended : I.models (decoded.source ++
      decoded.taxonomy.certificate.seed.abox.negativeRoleClausesAt
        decoded.taxonomy.certificate.seed.variableCount decoded.variable_ge_two) := by
    simpa only [decoded.exact_projection] using htarget
  have hsource : I.models decoded.source := by
    intro clause hclause
    exact happended clause (List.mem_append_left _ hclause)
  exact ⟨Domain, I, value, element, hdomain, hsource, habox, hquery⟩

theorem DecodedDirectNativeABoxTaxonomyUnsat.source_unsatisfiable
    (decoded : DecodedDirectNativeABoxTaxonomyUnsat) :
    ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithQuery
      decoded.source decoded.taxonomy.query.literals := by
  rintro ⟨Domain, I, value, element, hdomain, hsource, habox, hquery⟩
  apply decoded.taxonomy.unsatisfiable
  refine ⟨Domain, I, value, element, hdomain, ?_, habox, hquery⟩
  rw [← decoded.exact_projection]
  exact (decoded.taxonomy.initial.abox.models_append_negativeRoleClausesAt_iff
    I value habox.1 decoded.variable_ge_two decoded.source).2
      ⟨hsource, habox.2.2.2.2⟩

def DecodedDirectNativeABoxTaxonomyDecision.SemanticallyValid :
    DecodedDirectNativeABoxTaxonomyDecision → Prop
  | .sat decoded =>
      decoded.taxonomy.certificate.seed.abox.abox.SatisfiableWithQuery
        decoded.source decoded.taxonomy.query.literals
  | .unsat decoded =>
      ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithQuery
        decoded.source decoded.taxonomy.query.literals

theorem DecodedDirectNativeABoxTaxonomyDecision.semantic_valid
    (decoded : DecodedDirectNativeABoxTaxonomyDecision) :
    decoded.SemanticallyValid := by
  cases decoded with
  | sat result => exact result.source_satisfiable
  | unsat result => exact result.source_unsatisfiable

/-! ## Complete direct-source matrix -/

structure WireDirectNativeABoxTaxonomyMatrix where
  version : Nat
  source : List WireDirectSourceClause
  matrix : WireNativeABoxTaxonomyMatrix
deriving FromJson, ToJson, Repr

structure DecodedDirectNativeABoxTaxonomyMatrix where
  matrix : DecodedNativeABoxTaxonomyMatrix
  concepts : List DecodedDirectNativeABoxTaxonomyDecision
  subsumptions : List (List DecodedDirectNativeABoxTaxonomyDecision)

def WireDirectNativeABoxTaxonomyMatrix.decode
    (wire : WireDirectNativeABoxTaxonomyMatrix) :
    Except String DecodedDirectNativeABoxTaxonomyMatrix := do
  if wire.version != 1 then
    throw s!"unsupported direct native ABox taxonomy matrix version {wire.version}"
  let matrix ← wire.matrix.decode
  let wrap := fun decision => ({
    version := 1
    source := wire.source
    decision
  } : WireDirectNativeABoxTaxonomyDecision)
  let concepts ← wire.matrix.concepts.mapM fun decision => (wrap decision).decode
  let subsumptions ← wire.matrix.subsumptions.mapM fun row =>
    row.mapM fun decision => (wrap decision).decode
  return { matrix, concepts, subsumptions }

def WireDirectNativeABoxTaxonomyMatrix.check
    (wire : WireDirectNativeABoxTaxonomyMatrix) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedDirectNativeABoxTaxonomyMatrix.allDecisions
    (decoded : DecodedDirectNativeABoxTaxonomyMatrix) :
    List DecodedDirectNativeABoxTaxonomyDecision :=
  decoded.concepts ++ decoded.subsumptions.flatten

def DecodedDirectNativeABoxTaxonomyMatrix.SemanticallyValid
    (decoded : DecodedDirectNativeABoxTaxonomyMatrix) : Prop :=
  decoded.matrix.wire.shapeB = true ∧
  decoded.matrix.wire.queriesB = true ∧
  decoded.matrix.wire.sharedProblemB = true ∧
  ∀ decision ∈ decoded.allDecisions, decision.SemanticallyValid

theorem DecodedDirectNativeABoxTaxonomyMatrix.semantic_valid
    (decoded : DecodedDirectNativeABoxTaxonomyMatrix) :
    decoded.SemanticallyValid := by
  refine ⟨decoded.matrix.complete_shape, decoded.matrix.exact_queries,
    decoded.matrix.shared_problem, ?_⟩
  intro decision _
  exact decision.semantic_valid

#print axioms DecodedDirectNativeABoxTaxonomySat.source_satisfiable
#print axioms DecodedDirectNativeABoxTaxonomyUnsat.source_unsatisfiable
#print axioms DecodedDirectNativeABoxTaxonomyDecision.semantic_valid
#print axioms DecodedDirectNativeABoxTaxonomyMatrix.semantic_valid

end ContextCalculus.Hypertableau
