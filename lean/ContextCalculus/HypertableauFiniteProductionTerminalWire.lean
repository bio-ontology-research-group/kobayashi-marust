import ContextCalculus.HypertableauProductionBlockingWire
import ContextCalculus.HypertableauRegularWire

/-!
# Equality-free finite production SAT-terminal provenance

This wire joins the exact blocked production table, one selected Cartesian
fold assignment, and the finite SAT certificate published for that assignment.
Acceptance reconstructs the fold materialization and checks that the published
certificate is exactly that materialization before running its semantic checker.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireFiniteProductionTerminal where
  version : Nat
  table : WireProductionBlockingTable
  finite : WireCertificate
  assignment : List WireNodePair
deriving FromJson, ToJson, Repr

structure DecodedFiniteProductionTerminal where
  nodeCount : Nat
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  table : FiniteProductionBlockingTable
    nodeCount conceptCount roleCount variableCount
  finite : FiniteSatCertificate
    nodeCount conceptCount roleCount variableCount
  assignmentList : List (Fin nodeCount × Fin nodeCount)

private def decodeFiniteForBase
    (wire : WireCertificate) (base : DecodedCertificate) :
    Except String (FiniteSatCertificate base.nodeCount base.conceptCount
      base.roleCount base.variableCount) := do
  let decoded ← wire.decodeBase
  if hnodes : decoded.nodeCount = base.nodeCount then
    if hconcepts : decoded.conceptCount = base.conceptCount then
      if hroles : decoded.roleCount = base.roleCount then
        if hvariables : decoded.variableCount = base.variableCount then
          match decoded with
          | ⟨_nodeCount, _conceptCount, _roleCount, _variableCount, certificate⟩ =>
              return hvariables ▸ hroles ▸ hconcepts ▸ hnodes ▸ certificate
        else throw "finite terminal variable count differs from blocked state"
      else throw "finite terminal role count differs from blocked state"
    else throw "finite terminal concept count differs from blocked state"
  else throw "finite terminal node count differs from blocked state"

def WireFiniteProductionTerminal.decode
    (wire : WireFiniteProductionTerminal) :
    Except String DecodedFiniteProductionTerminal := do
  unless wire.version == 1 do
    throw s!"unsupported finite production terminal version {wire.version}"
  let decodedTable ← wire.table.decode
  let finite ← decodeFiniteForBase wire.finite {
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
    finite
    assignmentList
  }

def FiniteSatCertificate.matchesB
    (left right : FiniteSatCertificate nodeCount conceptCount roleCount variableCount) : Bool :=
  decide (left.ontology = right.ontology) &&
    listMembershipEqB left.labels right.labels &&
    listMembershipEqB left.edges right.edges &&
    listMembershipEqB left.obligations right.obligations

theorem FiniteSatCertificate.matchesB_eq_true_iff
    (left right : FiniteSatCertificate nodeCount conceptCount roleCount variableCount) :
    left.matchesB right = true ↔
      left.ontology = right.ontology ∧ left.state = right.state := by
  simp only [FiniteSatCertificate.matchesB, Bool.and_eq_true,
    decide_eq_true_eq, listMembershipEqB_eq_true_iff]
  constructor
  · rintro ⟨⟨⟨hontology, hlabels⟩, hedges⟩, hobligations⟩
    refine ⟨hontology, ?_⟩
    apply State.ext
    · funext node literal
      exact propext (hlabels (node, literal))
    · funext role source target
      exact propext (hedges (role, source, target))
    · funext role filler node
      exact propext (hobligations (role, filler, node))
  · rintro ⟨hontology, hstate⟩
    refine ⟨⟨⟨hontology, ?_⟩, ?_⟩, ?_⟩
    · intro fact
      change left.state.label fact.1 fact.2 ↔ right.state.label fact.1 fact.2
      rw [hstate]
    · intro edge
      change left.state.edge edge.1 edge.2.1 edge.2.2 ↔
        right.state.edge edge.1 edge.2.1 edge.2.2
      rw [hstate]
    · intro obligation
      change left.state.obligation obligation.1 obligation.2.1 obligation.2.2 ↔
        right.state.obligation obligation.1 obligation.2.1 obligation.2.2
      rw [hstate]

def DecodedFiniteProductionTerminal.fold
    (decoded : DecodedFiniteProductionTerminal) :
    FiniteFoldCertificate decoded.nodeCount decoded.conceptCount
      decoded.roleCount decoded.variableCount := {
  base := decoded.table.base
  folds := decoded.assignmentList
}

def WireFiniteProductionTerminal.check
    (wire : WireFiniteProductionTerminal) : Except String Bool := do
  let decoded ← wire.decode
  return decoded.table.computableCheck &&
    decide (decoded.assignmentList.toFinset ∈
      enumerateFoldAssignments decoded.table.options) &&
    decide decoded.assignmentList.Nodup &&
    decide (decoded.assignmentList.map Prod.fst).Nodup &&
    decoded.finite.matchesB decoded.fold.materialize &&
    decoded.finite.checkSat

theorem WireFiniteProductionTerminal.check_sound
    (wire : WireFiniteProductionTerminal)
    (decoded : DecodedFiniteProductionTerminal)
    (hdecode : wire.decode = .ok decoded)
    (hcheck : wire.check = .ok true) :
    decoded.table.ParentEarlier ∧
      decoded.table.options = decoded.table.expectedOptions ∧
      decoded.assignmentList.toFinset ∈
        enumerateFoldAssignments decoded.table.options ∧
      decoded.assignmentList.Nodup ∧
      (decoded.assignmentList.map Prod.fst).Nodup ∧
      decoded.finite.ontology = decoded.fold.materialize.ontology ∧
      decoded.finite.state = decoded.fold.materialize.state ∧
      decoded.finite.checkSat = true := by
  have hbool : (
      decoded.table.computableCheck &&
        decide (decoded.assignmentList.toFinset ∈
          enumerateFoldAssignments decoded.table.options) &&
        decide decoded.assignmentList.Nodup &&
        decide (decoded.assignmentList.map Prod.fst).Nodup &&
        decoded.finite.matchesB decoded.fold.materialize &&
        decoded.finite.checkSat) = true := by
    simpa [WireFiniteProductionTerminal.check, hdecode] using hcheck
  have checks :
      decoded.table.computableCheck = true ∧
      decide (decoded.assignmentList.toFinset ∈
        enumerateFoldAssignments decoded.table.options) = true ∧
      decide decoded.assignmentList.Nodup = true ∧
      decide (decoded.assignmentList.map Prod.fst).Nodup = true ∧
      decoded.finite.matchesB decoded.fold.materialize = true ∧
      decoded.finite.checkSat = true := by
    simpa only [Bool.and_eq_true, and_assoc] using hbool
  exact ⟨
    (decoded.table.computableCheck_eq_true_iff.mp checks.1).1,
    (decoded.table.computableCheck_eq_true_iff.mp checks.1).2,
    of_decide_eq_true checks.2.1,
    of_decide_eq_true checks.2.2.1,
    of_decide_eq_true checks.2.2.2.1,
    (decoded.finite.matchesB_eq_true_iff decoded.fold.materialize).mp
      checks.2.2.2.2.1 |>.1,
    (decoded.finite.matchesB_eq_true_iff decoded.fold.materialize).mp
      checks.2.2.2.2.1 |>.2,
    checks.2.2.2.2.2
  ⟩

#print axioms WireFiniteProductionTerminal.check_sound

end ContextCalculus.Hypertableau
