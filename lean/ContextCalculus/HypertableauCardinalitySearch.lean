import ContextCalculus.HypertableauCardinalityDistinctCertificate

/-!
# Checked bounded cardinality-aware HT outcomes

The concrete distinct-cardinality refutation search reports checked closure,
an open finite branch, or exhaustion of its node budget.  Only checked closure
is currently conclusive.  This contract prevents the two inconclusive cases
from being collapsed into one control-flow result while equality-aware
blocking and model extraction remain to be certified.
-/

namespace ContextCalculus.Hypertableau

abbrev CardinalityHasNonemptyModel
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role),
    Nonempty Domain ∧ I.models ontology ∧ I.modelsCardinalityDefs definitions

inductive CheckedCardinalityRefutationOutcome
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Type where
  | closed
      {nodeCount depth : Nat}
      (certificate : FiniteDistinctEqCertificate
        nodeCount conceptCount roleCount variableCount)
      (tree : FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount depth)
      (hontology : certificate.base.base.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hempty : certificate.base.EmptyRoot)
      (hapart : certificate.apart = [])
      (hcheck : tree.check definitions certificate = true)
  | openBranch
  | frontier

def CheckedCardinalityRefutationOutcome.Semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedCardinalityRefutationOutcome
      conceptCount roleCount variableCount ontology definitions) : Prop :=
  match outcome with
  | .closed .. => ¬CardinalityHasNonemptyModel ontology definitions
  | .openBranch => False
  | .frontier => False

theorem CheckedCardinalityRefutationOutcome.closed_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    {nodeCount depth : Nat}
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (hontology : certificate.base.base.ontology = ontology)
    (hnonempty : 0 < nodeCount)
    (hempty : certificate.base.EmptyRoot)
    (hapart : certificate.apart = [])
    (hcheck : tree.check definitions certificate = true) :
    ¬CardinalityHasNonemptyModel ontology definitions := by
  letI : Nonempty (Fin nodeCount) := ⟨⟨0, hnonempty⟩⟩
  have hnot := tree.check_ontology_unsatisfiable
    definitions certificate hempty hapart hcheck
  simpa [CardinalityHasNonemptyModel, hontology] using hnot

theorem CheckedCardinalityRefutationOutcome.conclusive_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedCardinalityRefutationOutcome
      conceptCount roleCount variableCount ontology definitions) :
    (match outcome with | .closed .. => True | _ => False) →
      outcome.Semantics := by
  cases outcome with
  | closed certificate tree hontology hnonempty hempty hapart hcheck =>
      intro _
      exact CheckedCardinalityRefutationOutcome.closed_semantics
        certificate tree hontology hnonempty hempty hapart hcheck
  | openBranch => simp
  | frontier => simp

#print axioms CheckedCardinalityRefutationOutcome.closed_semantics
#print axioms CheckedCardinalityRefutationOutcome.conclusive_semantics

end ContextCalculus.Hypertableau
