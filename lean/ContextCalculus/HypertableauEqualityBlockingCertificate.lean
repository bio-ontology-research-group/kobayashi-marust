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

@[simp] theorem FiniteEqFoldCertificate.materialize_labels
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.base.labels = certificate.base.base.labels := rfl

@[simp] theorem FiniteEqFoldCertificate.materialize_obligations
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.base.obligations =
      certificate.base.base.obligations := rfl

@[simp] theorem FiniteEqFoldCertificate.materialize_equalityClosureValidB
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.equalityClosureValidB =
      certificate.base.equalityClosureValidB := rfl

theorem FiniteEqFoldCertificate.base_edge_mem_foldedEdges
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (edge : Fin roleCount × Fin nodeCount × Fin nodeCount)
    (hedge : edge ∈ certificate.base.base.edges) :
    edge ∈ certificate.foldedEdges := by
  exact List.mem_append_left _ hedge

/-- Folding changes only the edge list, so equality-quotient clashes cannot be
introduced. -/
theorem FiniteEqFoldCertificate.closedClashFree_of_base
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hclash : certificate.base.state.ClosedClashFree) :
    certificate.materialize.state.ClosedClashFree := by
  intro positiveNode negativeNode concept hrelated hlabels
  exact hclash positiveNode negativeNode concept hrelated hlabels

/-- Existing witnesses remain witnesses because every base edge is retained by
the materialized fold. -/
theorem FiniteEqFoldCertificate.closedWitnessComplete_of_base
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hwitness : certificate.base.state.ClosedWitnessComplete) :
    certificate.materialize.state.ClosedWitnessComplete := by
  intro node role filler hobligation
  rcases hwitness node role filler hobligation with ⟨witness, hedge, hlabel⟩
  exact ⟨witness, certificate.base_edge_mem_foldedEdges _ hedge, hlabel⟩

/-- Body atoms unaffected by adding role edges. -/
def Atom.RoleFree : Atom Variable Concept Role → Prop
  | .role .. => False
  | _ => True

def Clause.RoleFreeBody (clause : Clause Variable Concept Role) : Prop :=
  ∀ atom ∈ clause.body, atom.RoleFree

/-- Every closed fact true before folding remains true afterwards. -/
theorem FiniteEqFoldCertificate.closedHoldsAtom_of_base
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount))
    (hholds : certificate.base.state.closedHoldsAtom assignment atom) :
    certificate.materialize.state.closedHoldsAtom assignment atom := by
  cases atom with
  | concept => exact hholds
  | role role source target =>
      rcases hholds with ⟨edgeSource, edgeTarget, hsource, htarget, hedge⟩
      exact ⟨edgeSource, edgeTarget, hsource, htarget,
        certificate.base_edge_mem_foldedEdges _ hedge⟩
  | exists_ => exact hholds
  | eq => exact hholds

/-- A role-free closed body fact cannot become newly true merely because a fold
adds role edges. -/
theorem FiniteEqFoldCertificate.closedHoldsAtom_base_of_roleFree
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount))
    (hroleFree : atom.RoleFree)
    (hholds : certificate.materialize.state.closedHoldsAtom assignment atom) :
    certificate.base.state.closedHoldsAtom assignment atom := by
  cases atom with
  | concept => exact hholds
  | role => contradiction
  | exists_ => exact hholds
  | eq => exact hholds

/-- Adding fold edges preserves saturation for the role-free-body portion of
the ontology. -/
theorem FiniteEqFoldCertificate.closedSaturatedFor_of_roleFree
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hroleFree : ∀ clause ∈ certificate.base.base.ontology, clause.RoleFreeBody)
    (hsaturated : certificate.base.state.ClosedSaturatedFor
      certificate.base.base.ontology) :
    certificate.materialize.state.ClosedSaturatedFor
      certificate.base.base.ontology := by
  intro clause hclause assignment hbody
  have hbaseBody : ∀ atom ∈ clause.body,
      certificate.base.state.closedHoldsAtom assignment atom := by
    intro atom hatom
    exact certificate.closedHoldsAtom_base_of_roleFree assignment atom
      (hroleFree clause hclause atom hatom) (hbody atom hatom)
  rcases hsaturated clause hclause assignment hbaseBody with ⟨atom, hatom, hholds⟩
  exact ⟨atom, hatom,
    certificate.closedHoldsAtom_of_base assignment atom hholds⟩

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

/-- Any fold over a valid equality endpoint is accepted when all clause bodies
are role-free. This closes the complete role-free portion of blocked search;
only clauses activated by newly copied role edges require pairwise reasoning. -/
theorem FiniteEqFoldCertificate.check_of_base_valid_roleFree
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.base.Valid)
    (hroleFree : ∀ clause ∈ certificate.base.base.ontology, clause.RoleFreeBody) :
    certificate.check = true := by
  apply certificate.check_complete_of hvalid.1 hvalid.2.1
  · exact certificate.closedClashFree_of_base hvalid.2.2.1
  · exact certificate.closedWitnessComplete_of_base hvalid.2.2.2.1
  · exact certificate.closedSaturatedFor_of_roleFree hroleFree hvalid.2.2.2.2

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
#print axioms FiniteEqFoldCertificate.closedClashFree_of_base
#print axioms FiniteEqFoldCertificate.closedWitnessComplete_of_base
#print axioms FiniteEqFoldCertificate.closedHoldsAtom_of_base
#print axioms FiniteEqFoldCertificate.closedHoldsAtom_base_of_roleFree
#print axioms FiniteEqFoldCertificate.closedSaturatedFor_of_roleFree
#print axioms FiniteEqFoldCertificate.check_eq_true_iff_materialize_valid
#print axioms FiniteEqFoldCertificate.check_complete
#print axioms FiniteEqFoldCertificate.check_complete_of
#print axioms FiniteEqFoldCertificate.check_of_base_valid_roleFree
#print axioms FiniteEqFoldCertificate.checkWithCardinality_eq_true_iff
#print axioms FiniteEqFoldCertificate.checkWithCardinality_models

end ContextCalculus.Hypertableau
