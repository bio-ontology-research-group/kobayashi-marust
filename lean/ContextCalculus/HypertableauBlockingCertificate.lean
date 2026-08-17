import ContextCalculus.HypertableauCertificate

/-!
# Checked finite-model folding for blocked hypertableau branches

A tableau blocker is a search device, not a trusted semantic premise.  This
module treats a finite fold plan as untrusted data, materializes the blocker's
outgoing edges at the blocked node, and then runs the existing exhaustive SAT
checker on the resulting ordinary finite graph.  Consequently, an incorrect
blocker choice can only make the checker reject; it cannot justify a verdict.
-/

namespace ContextCalculus.Hypertableau

/-- `(blocked, blocker)` pairs supplied by an untrusted finite-model producer. -/
structure FiniteFoldCertificate
    (nodeCount conceptCount roleCount variableCount : Nat) where
  base : FiniteSatCertificate nodeCount conceptCount roleCount variableCount
  folds : List (Fin nodeCount × Fin nodeCount)

/-- Copy every outgoing blocker edge to its blocked unfolding position. -/
def FiniteFoldCertificate.foldedEdges
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount) :
    List (Fin roleCount × Fin nodeCount × Fin nodeCount) :=
  certificate.base.edges ++ certificate.folds.flatMap fun fold =>
    certificate.base.edges.filterMap fun edge =>
      if edge.2.1 = fold.2 then some (edge.1, fold.1, edge.2.2) else none

/-- The ordinary finite SAT certificate obtained after materializing a fold. -/
def FiniteFoldCertificate.materialize
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount) :
    FiniteSatCertificate nodeCount conceptCount roleCount variableCount := {
  certificate.base with edges := certificate.foldedEdges
}

@[simp] theorem FiniteFoldCertificate.materialize_ontology
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.ontology = certificate.base.ontology := rfl

@[simp] theorem FiniteFoldCertificate.materialize_labels
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.labels = certificate.base.labels := rfl

@[simp] theorem FiniteFoldCertificate.materialize_obligations
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.obligations = certificate.base.obligations := rfl

theorem FiniteFoldCertificate.base_edge_mem_foldedEdges
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount)
    (edge : Fin roleCount × Fin nodeCount × Fin nodeCount)
    (hedge : edge ∈ certificate.base.edges) :
    edge ∈ certificate.foldedEdges := by
  exact List.mem_append_left _ hedge

/-- Executable acceptance condition for an untrusted finite fold. -/
def FiniteFoldCertificate.check
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount) : Bool :=
  certificate.materialize.checkSat

/-- A checked fold constructs a model of the exact, unchanged ontology.  No
property of `folds` occurs among the assumptions. -/
theorem FiniteFoldCertificate.check_satisfiable
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.check = true) :
    ∃ I : Interp (Fin nodeCount) (Fin conceptCount) (Fin roleCount),
      I.models certificate.base.ontology := by
  simpa [FiniteFoldCertificate.check] using
    certificate.materialize.checkSat_satisfiable hcheck

namespace FoldTests

private def cyclicBase : FiniteSatCertificate 3 2 1 1 where
  ontology := [
    { body := [], head := [.concept (.pos 0) 0] },
    { body := [.concept (.pos 0) 0], head := [.exists_ 0 (.pos 1) 0] }
  ]
  labels := [
    (0, .pos 0),
    (1, .pos 0), (1, .pos 1),
    (2, .pos 0), (2, .pos 1)
  ]
  edges := [(0, 0, 1), (0, 1, 2)]
  obligations := [(0, .pos 1, 0), (0, .pos 1, 1), (0, .pos 1, 2)]

example : cyclicBase.checkSat = false := by native_decide

private def cyclicFold : FiniteFoldCertificate 3 2 1 1 where
  base := cyclicBase
  folds := [(2, 1)]

example : cyclicFold.materialize.edges =
    [(0, 0, 1), (0, 1, 2), (0, 2, 2)] := by native_decide

example : cyclicFold.check = true := by native_decide

end FoldTests

#print axioms FiniteFoldCertificate.check_satisfiable

end ContextCalculus.Hypertableau
