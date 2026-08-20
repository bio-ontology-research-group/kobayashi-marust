import ContextCalculus.HypertableauEqualityCertificate

/-!
# Checked bounded equality-aware HT outcomes

KM's bounded equality-aware refutation search has three operational outcomes.
Only a checked closed tree is presently conclusive.  An open finite branch is
not yet a model certificate, and exhausting the node budget is a frontier.
Keeping those cases distinct prevents either inconclusive result from being
mistaken for a proof of satisfiability or unsatisfiability.
-/

namespace ContextCalculus.Hypertableau

abbrev EqualityHasNonemptyModel
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role),
    Nonempty Domain ∧ I.models ontology

inductive CheckedEqualityRefutationOutcome
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) : Type where
  | closed
      {nodeCount : Nat}
      (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
      (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
      (hontology : certificate.base.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hempty : certificate.EmptyRoot)
      (hcheck : tree.check certificate = true)
  | openBranch
  | frontier

def CheckedEqualityRefutationOutcome.Semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedEqualityRefutationOutcome
      conceptCount roleCount variableCount ontology) : Prop :=
  match outcome with
  | .closed .. => ¬EqualityHasNonemptyModel ontology
  | .openBranch => False
  | .frontier => False

theorem CheckedEqualityRefutationOutcome.closed_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {nodeCount : Nat}
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
    (hontology : certificate.base.ontology = ontology)
    (hnonempty : 0 < nodeCount)
    (hempty : certificate.EmptyRoot)
    (hcheck : tree.check certificate = true) :
    ¬EqualityHasNonemptyModel ontology := by
  letI : Nonempty (Fin nodeCount) := ⟨⟨0, hnonempty⟩⟩
  have hnot := tree.check_ontology_unsatisfiable certificate hempty hcheck
  simpa [EqualityHasNonemptyModel, hontology] using hnot

theorem CheckedEqualityRefutationOutcome.conclusive_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedEqualityRefutationOutcome
      conceptCount roleCount variableCount ontology) :
    (match outcome with | .closed .. => True | _ => False) →
      outcome.Semantics := by
  cases outcome with
  | closed certificate tree hontology hnonempty hempty hcheck =>
      intro _
      exact CheckedEqualityRefutationOutcome.closed_semantics
        certificate tree hontology hnonempty hempty hcheck
  | openBranch => simp
  | frontier => simp

#print axioms CheckedEqualityRefutationOutcome.closed_semantics
#print axioms CheckedEqualityRefutationOutcome.conclusive_semantics

end ContextCalculus.Hypertableau
