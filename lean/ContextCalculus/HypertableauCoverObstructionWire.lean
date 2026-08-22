import ContextCalculus.HypertableauRegularWire

/-!
# Checked wire witnesses for regular-cover obstructions

The producer supplies a regular certificate, an index into its residual
clauses, and one finite assignment. Decoding checks every index. The Boolean
checker then establishes the exact semantic obstruction used by the regular
terminal selector; a successful witness consequently proves that the supplied
cover is not saturated.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireRegularCoverObstruction where
  version : Nat
  certificate : WireRegularCertificate
  clause : Nat
  assignment : List Nat
deriving FromJson, ToJson, Repr

structure DecodedRegularCoverObstruction where
  decoded : DecodedRegularCertificate
  clauseIndex : Fin decoded.certificate.residual.length
  assignment : Fin decoded.variableCount → Fin decoded.nodeCount

def DecodedRegularCoverObstruction.clause
    (witness : DecodedRegularCoverObstruction) :=
  witness.decoded.certificate.residual.get witness.clauseIndex

def WireRegularCoverObstruction.decode
    (wire : WireRegularCoverObstruction) :
    Except String DecodedRegularCoverObstruction := do
  if wire.version != 1 then
    throw s!"unsupported regular cover obstruction version {wire.version}"
  let decoded ← wire.certificate.decode
  let clauseIndex ← checkedFin "residual clause"
    decoded.certificate.residual.length wire.clause
  let assignment ← decodeAssignment decoded.nodeCount decoded.variableCount
    wire.assignment
  return { decoded, clauseIndex, assignment }

def DecodedRegularCoverObstruction.check
    (witness : DecodedRegularCoverObstruction) : Bool :=
  witness.decoded.certificate.coverObstructionB witness.clause
    witness.assignment

theorem DecodedRegularCoverObstruction.check_sound
    (witness : DecodedRegularCoverObstruction)
    (hcheck : witness.check = true) :
    witness.decoded.certificate.state.CoverObstruction
      witness.decoded.certificate.coverRelation witness.clause
      witness.assignment := by
  exact (witness.decoded.certificate.coverObstructionB_eq_true_iff
    witness.clause witness.assignment).mp hcheck

/-- A checked concrete witness forces rejection of the associated cover. -/
theorem DecodedRegularCoverObstruction.coverSaturatedB_eq_false
    (witness : DecodedRegularCoverObstruction)
    (hcheck : witness.check = true) :
    witness.decoded.certificate.coverSaturatedB = false := by
  apply witness.decoded.certificate.coverSaturatedB_eq_false_iff.mpr
  exact ⟨witness.clause, List.get_mem _ witness.clauseIndex,
    witness.assignment, witness.check_sound hcheck⟩

private def sampleCertificate : WireRegularCertificate where
  version := 1
  node_count := 1
  concept_count := 1
  role_count := 1
  variable_count := 1
  labels := []
  edges := []
  obligations := []
  redirect := [0]
  cover := []
  sub_roles := []
  inverse_roles := []
  chains := []
  reflexive_roles := []
  role_clauses := []
  residual := [{ body := [], head := [] }]

private def sampleWitness : WireRegularCoverObstruction where
  version := 1
  certificate := sampleCertificate
  clause := 0
  assignment := [0]

example : sampleWitness.decode.map (·.check) = .ok true := by native_decide

#print axioms DecodedRegularCoverObstruction.check_sound
#print axioms DecodedRegularCoverObstruction.coverSaturatedB_eq_false

end ContextCalculus.Hypertableau
