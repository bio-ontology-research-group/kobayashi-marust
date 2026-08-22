import ContextCalculus.HypertableauProductionBlockingWire
import ContextCalculus.HypertableauRegularWire

/-!
# Equality-free production SAT-terminal provenance

This wire joins the exact blocked production table, one selected Cartesian
fold assignment, and the regular-unravelling certificate published for that
assignment. Acceptance checks the blocker table, assignment membership, raw
state identity, exact redirect identity, ontology identity, and the complete
regular semantic certificate.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireRegularProductionTerminal where
  version : Nat
  table : WireProductionBlockingTable
  regular : WireRegularCertificate
  assignment : List WireNodePair
deriving FromJson, ToJson, Repr

structure DecodedRegularProductionTerminal where
  nodeCount : Nat
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  table : FiniteProductionBlockingTable
    nodeCount conceptCount roleCount variableCount
  regular : FiniteRegularCertificate
    nodeCount conceptCount roleCount variableCount
  assignmentList : List (Fin nodeCount × Fin nodeCount)

private def decodeRegularForBase
    (wire : WireRegularCertificate) (base : DecodedCertificate) :
    Except String (FiniteRegularCertificate base.nodeCount base.conceptCount
      base.roleCount base.variableCount) := do
  let decoded ← wire.decodeAt base.conceptCount base.roleCount base.variableCount
  if hnodes : decoded.nodeCount = base.nodeCount then
    match decoded with
    | ⟨_nodeCount, _positive, certificate⟩ =>
        return hnodes ▸ certificate
  else
    throw "regular terminal node count differs from blocked state"

def WireRegularProductionTerminal.decode
    (wire : WireRegularProductionTerminal) :
    Except String DecodedRegularProductionTerminal := do
  unless wire.version == 1 do
    throw s!"unsupported regular production terminal version {wire.version}"
  let decodedTable ← wire.table.decode
  let regular ← decodeRegularForBase wire.regular {
    nodeCount := decodedTable.nodeCount
    conceptCount := decodedTable.conceptCount
    roleCount := decodedTable.roleCount
    variableCount := decodedTable.variableCount
    certificate := decodedTable.table.base
  }
  let assignmentList ← wire.assignment.mapM fun pair => do
    return (← checkedFin "terminal fold source" decodedTable.nodeCount pair.source,
      ← checkedFin "terminal fold blocker" decodedTable.nodeCount pair.target)
  return {
    nodeCount := decodedTable.nodeCount
    conceptCount := decodedTable.conceptCount
    roleCount := decodedTable.roleCount
    variableCount := decodedTable.variableCount
    table := decodedTable.table
    regular
    assignmentList
  }

def WireRegularProductionTerminal.check
    (wire : WireRegularProductionTerminal) : Except String Bool := do
  let decoded ← wire.decode
  return decoded.table.computableCheck &&
    decide (decoded.assignmentList.toFinset ∈
      enumerateFoldAssignments decoded.table.options) &&
    decide decoded.assignmentList.Nodup &&
    decide (decoded.assignmentList.map Prod.fst).Nodup &&
    decoded.regular.matchesStateB decoded.table.base &&
    decoded.regular.redirectMatchesAssignmentB decoded.assignmentList &&
    decide (decoded.regular.ontology = decoded.table.base.ontology) &&
    decoded.regular.check

theorem WireRegularProductionTerminal.check_sound
    (wire : WireRegularProductionTerminal)
    (decoded : DecodedRegularProductionTerminal)
    (hdecode : wire.decode = .ok decoded)
    (hcheck : wire.check = .ok true) :
    decoded.table.ParentEarlier ∧
      decoded.table.options = decoded.table.expectedOptions ∧
      decoded.assignmentList.toFinset ∈
        enumerateFoldAssignments decoded.table.options ∧
      decoded.assignmentList.Nodup ∧
      (decoded.assignmentList.map Prod.fst).Nodup ∧
      decoded.regular.state = decoded.table.base.state ∧
      decoded.regular.redirect =
        redirectFromFoldList decoded.assignmentList ∧
      decoded.regular.ontology = decoded.table.base.ontology ∧
      decoded.regular.check = true := by
  have hbool : (
      decoded.table.computableCheck &&
        decide (decoded.assignmentList.toFinset ∈
          enumerateFoldAssignments decoded.table.options) &&
        decide decoded.assignmentList.Nodup &&
        decide (decoded.assignmentList.map Prod.fst).Nodup &&
        decoded.regular.matchesStateB decoded.table.base &&
        decoded.regular.redirectMatchesAssignmentB decoded.assignmentList &&
        decide (decoded.regular.ontology = decoded.table.base.ontology) &&
        decoded.regular.check) = true := by
    simpa [WireRegularProductionTerminal.check, hdecode] using hcheck
  have checks :
      decoded.table.computableCheck = true ∧
      decide (decoded.assignmentList.toFinset ∈
        enumerateFoldAssignments decoded.table.options) = true ∧
      decide decoded.assignmentList.Nodup = true ∧
      decide (decoded.assignmentList.map Prod.fst).Nodup = true ∧
      decoded.regular.matchesStateB decoded.table.base = true ∧
      decoded.regular.redirectMatchesAssignmentB decoded.assignmentList = true ∧
      decide (decoded.regular.ontology = decoded.table.base.ontology) = true ∧
      decoded.regular.check = true := by
    simpa only [Bool.and_eq_true, and_assoc] using hbool
  exact ⟨
    (decoded.table.computableCheck_eq_true_iff.mp checks.1).1,
    (decoded.table.computableCheck_eq_true_iff.mp checks.1).2,
    of_decide_eq_true checks.2.1,
    of_decide_eq_true checks.2.2.1,
    of_decide_eq_true checks.2.2.2.1,
    decoded.regular.matchesStateB_state decoded.table.base checks.2.2.2.2.1,
    decoded.regular.redirectMatchesAssignmentB_eq_true decoded.assignmentList
      checks.2.2.2.2.2.1,
    of_decide_eq_true checks.2.2.2.2.2.2.1,
    checks.2.2.2.2.2.2.2
  ⟩

#print axioms WireRegularProductionTerminal.check_sound

end ContextCalculus.Hypertableau
