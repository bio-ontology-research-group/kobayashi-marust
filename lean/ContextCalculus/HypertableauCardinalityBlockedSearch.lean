import ContextCalculus.HypertableauCardinalityRuntimeSearch
import ContextCalculus.HypertableauCardinalityCertificate
import ContextCalculus.HypertableauCardinalitySearch

/-!
# Checked cardinality terminal outcomes

Runtime terminality is not a satisfiability verdict.  This module composes it
with the independent finite equality/cardinality model checker used at the
production boundary.  Rejected evidence and node exhaustion remain explicit
frontiers.
-/

namespace ContextCalculus.Hypertableau

def HasCheckedCardinalityModel
    (nodeCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Prop :=
  ∃ certificate : FiniteEqCertificate
      nodeCount conceptCount roleCount variableCount,
    0 < nodeCount ∧ certificate.base.ontology = ontology ∧
      certificate.checkEqSatWithCardinality definitions = true

theorem hasCardinalityModel_of_checked
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (hmodel : HasCheckedCardinalityModel (nodeCount := nodeCount)
      ontology definitions) :
    CardinalityHasNonemptyModel ontology definitions := by
  rcases hmodel with ⟨certificate, hpositive, hontology, hcheck⟩
  letI : Nonempty (Fin nodeCount) := ⟨⟨0, hpositive⟩⟩
  have hmodels := certificate.checkEqSatWithCardinality_models definitions hcheck
  refine ⟨certificate.state.QuotientDomain, certificate.state.quotientCanonical,
    ⟨Quotient.mk certificate.state.nodeSetoid (Classical.choice inferInstance)⟩, ?_,
    hmodels.2⟩
  simpa [hontology] using hmodels.1

/-- One bounded cardinality search reports checked closure, an independently
checked model, or an explicit inconclusive frontier. -/
inductive CardinalityBoundedOutcome
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (state : DistinctEqState
      (Fin nodeCount) (Fin conceptCount) (Fin roleCount)) : Type where
  | closed (proof : ClosedDistinctCardinalityRefutes
      (Fin nodeCount) ontology definitions state)
  | model (proof : HasCheckedCardinalityModel
      (nodeCount := nodeCount) ontology definitions)
  | frontier

theorem CardinalityBoundedOutcome.semantic_or_frontier
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    {state : DistinctEqState
      (Fin nodeCount) (Fin conceptCount) (Fin roleCount)}
    (outcome : CardinalityBoundedOutcome nodeCount conceptCount roleCount
      variableCount ontology definitions state) :
    ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions state ∨
      CardinalityHasNonemptyModel ontology definitions ∨ outcome = .frontier := by
  cases outcome with
  | closed proof => exact Or.inl proof
  | model proof => exact Or.inr (Or.inl (hasCardinalityModel_of_checked proof))
  | frontier => exact Or.inr (Or.inr rfl)

/-- A terminal state is semantically SAT only when the independent model
checker accepts its exact ontology and cardinality definitions. -/
theorem cardinality_terminal_checked_model
    [Fintype (Fin variableCount)] [DecidableEq (Fin variableCount)]
    [Fintype (Fin nodeCount)] [DecidableEq (Fin nodeCount)]
    [Fintype (Fin conceptCount)] [DecidableEq (Fin conceptCount)]
    [Fintype (Fin roleCount)] [DecidableEq (Fin roleCount)]
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (state : DistinctEqState
      (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (expanded : CardinalityDef (Fin conceptCount) (Fin roleCount) →
      Fin nodeCount → Prop)
    (_hterminal : state.CardinalityRuntimeTerminal ontology definitions
      parent ancestors expanded)
    (hmodel : HasCheckedCardinalityModel (nodeCount := nodeCount)
      ontology definitions) :
    CardinalityHasNonemptyModel ontology definitions :=
  hasCardinalityModel_of_checked hmodel

#print axioms hasCardinalityModel_of_checked
#print axioms CardinalityBoundedOutcome.semantic_or_frontier
#print axioms cardinality_terminal_checked_model

end ContextCalculus.Hypertableau
