import ContextCalculus.HypertableauEqualityBlocking
import ContextCalculus.HypertableauEqualityCertificate
import ContextCalculus.HypertableauCardinalityCertificate

/-!
# Checked finite equality-quotient folds

The runtime may propose a pairwise blocker, but the blocker is not a trusted
semantic premise. This module materializes every outgoing edge visible at the
blocker's equality class at the blocked node and sends the resulting ordinary
equality certificate through `checkEqSat`.
-/

namespace ContextCalculus.Hypertableau

structure FiniteEqFoldCertificate
    (nodeCount conceptCount roleCount variableCount : Nat) where
  base : FiniteEqCertificate nodeCount conceptCount roleCount variableCount
  folds : List (Fin nodeCount × Fin nodeCount)

/-- Copy every raw edge whose source belongs to the blocker's supplied
representative class. Invalid representative maps are rejected by the ordinary
equality checker. -/
def FiniteEqFoldCertificate.foldedEdges
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    List (Fin roleCount × Fin nodeCount × Fin nodeCount) :=
  certificate.base.base.edges ++ certificate.folds.flatMap fun fold =>
    certificate.base.base.edges.filterMap fun edge =>
      if certificate.base.representative edge.2.1 =
          certificate.base.representative fold.2 then
        some (edge.1, fold.1, edge.2.2)
      else none

def FiniteEqFoldCertificate.materialize
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    FiniteEqCertificate nodeCount conceptCount roleCount variableCount := {
  certificate.base with
  base := { certificate.base.base with edges := certificate.foldedEdges }
}

@[simp] theorem FiniteEqFoldCertificate.materialize_ontology
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.base.ontology = certificate.base.base.ontology := rfl

@[simp] theorem FiniteEqFoldCertificate.materialize_equalities
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.equalities = certificate.base.equalities := rfl

@[simp] theorem FiniteEqFoldCertificate.materialize_representative
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.representative = certificate.base.representative := rfl

def FiniteEqFoldCertificate.check
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) : Bool :=
  certificate.materialize.checkEqSat

theorem FiniteEqFoldCertificate.check_eq_true_iff_materialize_valid
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.check = true ↔ certificate.materialize.Valid := by
  exact certificate.materialize.checkEqSat_eq_true_iff_valid

theorem FiniteEqFoldCertificate.check_complete
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.materialize.Valid) :
    certificate.check = true :=
  certificate.materialize.checkEqSat_complete hvalid

theorem FiniteEqFoldCertificate.check_complete_of
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hequality : certificate.base.equalityClosureValidB = true)
    (hguarded : ∀ clause ∈ certificate.base.base.ontology, clause.GuardedBody)
    (hclash : certificate.materialize.state.ClosedClashFree)
    (hwitness : certificate.materialize.state.ClosedWitnessComplete)
    (hsaturated : certificate.materialize.state.ClosedSaturatedFor
      certificate.base.base.ontology) :
    certificate.check = true := by
  apply certificate.check_complete
  exact ⟨hequality, hguarded, hclash, hwitness, hsaturated⟩

/-- Any accepted equality-aware fold is a model of the exact unchanged
ontology. The theorem assumes no correctness property of the proposed folds. -/
theorem FiniteEqFoldCertificate.check_satisfiable
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.check = true) :
    ∃ (Domain : Type) (I : Interp Domain (Fin conceptCount) (Fin roleCount)),
      I.models certificate.base.base.ontology := by
  simpa [FiniteEqFoldCertificate.check] using
    certificate.materialize.checkEqSat_satisfiable hcheck

def FiniteEqFoldCertificate.checkWithCardinality
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Bool :=
  certificate.materialize.checkEqSatWithCardinality definitions

theorem FiniteEqFoldCertificate.checkWithCardinality_eq_true_iff
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) :
    certificate.checkWithCardinality definitions = true ↔
      certificate.materialize.Valid ∧
        certificate.materialize.state.quotientCanonical.modelsCardinalityDefs
          definitions := by
  exact certificate.materialize.checkEqSatWithCardinality_eq_true_iff definitions

/-- The same untrusted fold boundary for cardinality-aware search. Acceptance
constructs one quotient interpretation satisfying both the exact ontology and
the exact minimum/maximum definitions. -/
theorem FiniteEqFoldCertificate.checkWithCardinality_models
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (hcheck : certificate.checkWithCardinality definitions = true) :
    ∃ (Domain : Type) (I : Interp Domain (Fin conceptCount) (Fin roleCount)),
      I.models certificate.base.base.ontology ∧
        I.modelsCardinalityDefs definitions := by
  have hmodels := certificate.materialize.checkEqSatWithCardinality_models
    definitions hcheck
  exact ⟨certificate.materialize.state.QuotientDomain,
    certificate.materialize.state.quotientCanonical, hmodels⟩

namespace EqFoldTests

private def cyclicBase : FiniteEqCertificate 3 1 1 1 where
  base := {
    ontology := [
      { body := [], head := [.concept (.pos 0) 0] },
      { body := [.concept (.pos 0) 0], head := [.exists_ 0 (.pos 0) 0] }
    ]
    labels := [(0, .pos 0), (1, .pos 0), (2, .pos 0)]
    edges := [(0, 0, 1), (0, 1, 2)]
    obligations := [(0, .pos 0, 0), (0, .pos 0, 1), (0, .pos 0, 2)]
  }
  equalities := []
  representative := id
  representativePath := fun _ => []

private def cyclicFold : FiniteEqFoldCertificate 3 1 1 1 where
  base := cyclicBase
  folds := [(2, 1)]

example : cyclicFold.materialize.base.edges =
    [(0, 0, 1), (0, 1, 2), (0, 2, 2)] := by native_decide

example : cyclicFold.check = true := by native_decide

end EqFoldTests

#print axioms FiniteEqFoldCertificate.check_satisfiable
#print axioms FiniteEqFoldCertificate.check_eq_true_iff_materialize_valid
#print axioms FiniteEqFoldCertificate.check_complete
#print axioms FiniteEqFoldCertificate.check_complete_of
#print axioms FiniteEqFoldCertificate.checkWithCardinality_eq_true_iff
#print axioms FiniteEqFoldCertificate.checkWithCardinality_models

end ContextCalculus.Hypertableau
