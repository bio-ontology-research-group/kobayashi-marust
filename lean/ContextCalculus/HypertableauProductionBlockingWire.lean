import ContextCalculus.HypertableauRegularRouteProduction
import ContextCalculus.HypertableauWire
import Lean

/-!
# Bounded production-blocking control wire

This document is separate from SAT evidence. It lets Lean reconstruct the
complete equality-free blocker table from the exact finite leaf, predecessor
forest, and outer forbidden-pair set before Rust learns an exhausted option
union.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireNodePair where
  source : Nat
  target : Nat
deriving FromJson, ToJson, Repr

structure WireFoldOption where
  source : Nat
  blockers : List Nat
deriving FromJson, ToJson, Repr

structure WireProductionBlockingTable where
  version : Nat
  base : WireCertificate
  /-- `node_count` is the sentinel for no predecessor. -/
  parents : List Nat
  forbidden : List WireNodePair
  options : List WireFoldOption
  rejected : List (List WireNodePair)
deriving FromJson, ToJson, Repr

structure DecodedProductionBlockingTable where
  nodeCount : Nat
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  table : FiniteProductionBlockingTable
    nodeCount conceptCount roleCount variableCount
  rejected : Finset (FoldAssignment (Fin nodeCount))

/-! ## Executable finite signatures -/

/-- A concrete, duplicate-free enumeration of both polarities of every finite
concept.  Unlike the generic `Fintype (Lit Concept)` instance, this list is
usable by generated native code. -/
def finiteLiterals (conceptCount : Nat) : List (Lit (Fin conceptCount)) :=
  (List.finRange conceptCount).flatMap fun concept =>
    [.pos concept, .negated concept]

@[simp] theorem mem_finiteLiterals
    (literal : Lit (Fin conceptCount)) :
    literal ∈ finiteLiterals conceptCount := by
  rcases literal with ⟨concept, neg⟩
  cases neg <;> simp [finiteLiterals, Lit.pos, Lit.negated]

/-- Native-code counterpart of `State.localBlockingFacts`. -/
def State.computableLocalBlockingFacts
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    [DecidableState state] (node : Fin nodeCount) :
    LocalBlockingFacts (Fin conceptCount) (Fin roleCount) := by
  letI : ∀ node literal, Decidable (state.label node literal) :=
    DecidableState.label (state := state)
  letI : ∀ role filler node, Decidable (state.obligation role filler node) :=
    DecidableState.obligation (state := state)
  exact (((finiteLiterals conceptCount).filter fun literal =>
      decide (state.label node literal)).toFinset,
    (((List.finRange roleCount).flatMap fun role =>
      (finiteLiterals conceptCount).map fun literal => (role, literal)).filter fun obligation =>
      decide (state.obligation obligation.1 obligation.2 node)).toFinset)

theorem State.computableLocalBlockingFacts_eq
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    [DecidableState state] (node : Fin nodeCount) :
    state.computableLocalBlockingFacts node = state.localBlockingFacts node := by
  letI : ∀ node literal, Decidable (state.label node literal) :=
    DecidableState.label (state := state)
  letI : ∀ role filler node, Decidable (state.obligation role filler node) :=
    DecidableState.obligation (state := state)
  apply Prod.ext
  · ext literal
    simp [State.computableLocalBlockingFacts, State.localBlockingFacts]
  · ext obligation
    rcases obligation with ⟨role, literal⟩
    simp [State.computableLocalBlockingFacts, State.localBlockingFacts,
      State.obligationSet]

/-- Native-code counterpart of the complete pairwise blocking signature. -/
def State.computableRoleBlockingSignature
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    [DecidableState state]
    (parent : Fin nodeCount → Option (Fin nodeCount)) (node : Fin nodeCount) :
    RoleBlockingSignature (Fin conceptCount) (Fin roleCount) := by
  letI : ∀ role source target, Decidable (state.edge role source target) :=
    DecidableState.edge (state := state)
  exact (state.computableLocalBlockingFacts node, parent node |>.map fun predecessor =>
    (state.computableLocalBlockingFacts predecessor,
      ((List.finRange roleCount).filter fun role =>
        decide (state.edge role predecessor node)).toFinset,
      ((List.finRange roleCount).filter fun role =>
        decide (state.edge role node predecessor)).toFinset))

theorem State.computableRoleBlockingSignature_eq
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    [DecidableState state]
    (parent : Fin nodeCount → Option (Fin nodeCount)) (node : Fin nodeCount) :
    state.computableRoleBlockingSignature parent node =
      state.roleBlockingSignature parent node := by
  letI : ∀ role source target, Decidable (state.edge role source target) :=
    DecidableState.edge (state := state)
  unfold State.computableRoleBlockingSignature State.roleBlockingSignature
  rw [state.computableLocalBlockingFacts_eq]
  cases hparent : parent node with
  | none => simp
  | some predecessor =>
      simp only [Option.map_some]
      congr 3
      · exact state.computableLocalBlockingFacts_eq predecessor
      · apply Prod.ext
        · ext role
          simp [State.forwardParentRoles]
        · ext role
          simp [State.backwardParentRoles]

def State.hasWitnessB
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    [DecidableState state] (source : Fin nodeCount) (role : Fin roleCount)
    (filler : Lit (Fin conceptCount)) : Bool := by
  letI : ∀ node literal, Decidable (state.label node literal) :=
    DecidableState.label (state := state)
  letI : ∀ role source target, Decidable (state.edge role source target) :=
    DecidableState.edge (state := state)
  exact (List.finRange nodeCount).any fun witness =>
    decide (state.edge role source witness) && decide (state.label witness filler)

theorem State.hasWitnessB_eq_true_iff
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    [DecidableState state] (source : Fin nodeCount) (role : Fin roleCount)
    (filler : Lit (Fin conceptCount)) :
    state.hasWitnessB source role filler = true ↔
      ∃ witness, state.edge role source witness ∧ state.label witness filler := by
  letI : ∀ node literal, Decidable (state.label node literal) :=
    DecidableState.label (state := state)
  letI : ∀ role source target, Decidable (state.edge role source target) :=
    DecidableState.edge (state := state)
  simp [State.hasWitnessB, List.any_eq_true]

def State.unwitnessedB
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    [DecidableState state] (source : Fin nodeCount) : Bool := by
  letI : ∀ role filler node, Decidable (state.obligation role filler node) :=
    DecidableState.obligation (state := state)
  exact (List.finRange roleCount).any fun role =>
    (finiteLiterals conceptCount).any fun filler =>
      decide (state.obligation role filler source) &&
        !(state.hasWitnessB source role filler)

theorem State.unwitnessedB_eq_true_iff
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    [DecidableState state] (source : Fin nodeCount) :
    state.unwitnessedB source = true ↔
      ∃ role filler, state.obligation role filler source ∧
        ∀ witness, ¬(state.edge role source witness ∧ state.label witness filler) := by
  letI : ∀ role filler node, Decidable (state.obligation role filler node) :=
    DecidableState.obligation (state := state)
  simp only [State.unwitnessedB, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, List.mem_finRange, true_and,
    mem_finiteLiterals]
  constructor
  · rintro ⟨role, filler, hobligation, hnowitness⟩
    have hfalse : state.hasWitnessB source role filler = false := by
      simpa using hnowitness
    exact ⟨role, filler, hobligation, fun witness hwitness => by
      have htrue := (state.hasWitnessB_eq_true_iff source role filler).mpr
        ⟨witness, hwitness⟩
      simp [hfalse] at htrue⟩
  · rintro ⟨role, filler, hobligation, hnowitness⟩
    have hfalse : state.hasWitnessB source role filler = false :=
      Bool.eq_false_of_not_eq_true fun htrue =>
        let ⟨witness, hwitness⟩ :=
          (state.hasWitnessB_eq_true_iff source role filler).mp htrue
        hnowitness witness hwitness
    exact ⟨role, filler, hobligation, by simp [hfalse]⟩

def decidableEqOption [DecidableEq α] : DecidableEq (Option α)
  | none, none => isTrue rfl
  | none, some value => isFalse (by intro h; cases h)
  | some value, none => isFalse (by intro h; cases h)
  | some left, some right =>
      match decEq left right with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun heq => h (Option.some.inj heq)

def FiniteProductionBlockingTable.computableFoldB
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount)
    (source blocker : Fin nodeCount) : Bool := by
  letI : DecidableEq
      (Option (LocalBlockingFacts (Fin conceptCount) (Fin roleCount) ×
        Finset (Fin roleCount) × Finset (Fin roleCount))) := decidableEqOption
  letI : DecidableEq
      (RoleBlockingSignature (Fin conceptCount) (Fin roleCount)) := inferInstance
  exact decide (blocker ∈ ancestorChain table.parent nodeCount source) &&
    decide (table.base.state.computableRoleBlockingSignature table.parent blocker =
      table.base.state.computableRoleBlockingSignature table.parent source) &&
    decide ((source, blocker) ∉ table.forbidden)

theorem FiniteProductionBlockingTable.computableFoldB_eq_true_iff
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount)
    (source blocker : Fin nodeCount) :
    table.computableFoldB source blocker = true ↔
      table.base.state.productionFold table.parent
        (ancestorChain table.parent nodeCount) table.forbidden source blocker := by
  simp only [FiniteProductionBlockingTable.computableFoldB, Bool.and_eq_true,
    decide_eq_true_eq, State.productionFold]
  rw [table.base.state.computableRoleBlockingSignature_eq,
    table.base.state.computableRoleBlockingSignature_eq]
  tauto

def FiniteProductionBlockingTable.computableExpectedOptions
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount) :
    List (Fin nodeCount × List (Fin nodeCount)) :=
  ((List.finRange nodeCount).filter fun source =>
    table.base.state.unwitnessedB source).map fun source =>
      (source, (ancestorChain table.parent nodeCount source).filter fun blocker =>
        table.computableFoldB source blocker)

theorem FiniteProductionBlockingTable.computableExpectedOptions_eq
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount) :
    table.computableExpectedOptions = table.expectedOptions := by
  classical
  unfold FiniteProductionBlockingTable.computableExpectedOptions
    FiniteProductionBlockingTable.expectedOptions
  have hsources :
      List.filter (fun source => table.base.state.unwitnessedB source)
          (List.finRange nodeCount) =
        List.filter (fun source => decide
          (∃ role filler, table.base.state.obligation role filler source ∧
            ∀ witness, ¬(table.base.state.edge role source witness ∧
              table.base.state.label witness filler)))
          (List.finRange nodeCount) := by
    apply List.filter_congr
    intro source _
    rw [Bool.eq_iff_iff]
    simp [State.unwitnessedB_eq_true_iff]
  rw [hsources]
  apply List.map_congr_left
  intro source _
  congr 1
  apply List.filter_congr
  intro blocker _
  rw [Bool.eq_iff_iff]
  simp [FiniteProductionBlockingTable.computableFoldB_eq_true_iff]

def FiniteProductionBlockingTable.computableCheck
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount) :
    Bool :=
  ((List.finRange nodeCount).all fun node =>
    match table.parent node with
    | none => true
    | some predecessor => decide (predecessor.val < node.val)) &&
  decide (table.options = table.computableExpectedOptions)

theorem FiniteProductionBlockingTable.computableCheck_eq_true_iff
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount) :
    table.computableCheck = true ↔
      table.ParentEarlier ∧ table.options = table.expectedOptions := by
  rw [← table.computableExpectedOptions_eq]
  simp only [FiniteProductionBlockingTable.computableCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_finRange, true_implies]
  constructor
  · rintro ⟨hall, hoptions⟩
    exact ⟨fun node predecessor hparent => by
      have hnode := hall node
      rw [hparent] at hnode
      simpa using hnode, hoptions⟩
  · rintro ⟨hearlier, hoptions⟩
    exact ⟨fun node => by
      cases hparent : table.parent node with
      | none => simp
      | some predecessor => simpa using hearlier node predecessor hparent,
      hoptions⟩

def DecodedProductionBlockingTable.assignmentsExhausted
    (decoded : DecodedProductionBlockingTable) : Bool :=
  (enumerateFoldAssignments decoded.table.options).all fun assignment =>
    decide (assignment ∈ decoded.rejected)

theorem DecodedProductionBlockingTable.assignmentsExhausted_eq_true_iff
    (decoded : DecodedProductionBlockingTable) :
    decoded.assignmentsExhausted = true ↔
      ∀ assignment ∈ enumerateFoldAssignments decoded.table.options,
        assignment ∈ decoded.rejected := by
  simp [DecodedProductionBlockingTable.assignmentsExhausted]

def DecodedProductionBlockingTable.optionsNonempty
    (decoded : DecodedProductionBlockingTable) : Bool :=
  decoded.table.options.all fun option => !option.2.isEmpty

theorem DecodedProductionBlockingTable.optionsNonempty_eq_true_iff
    (decoded : DecodedProductionBlockingTable) :
    decoded.optionsNonempty = true ↔
      ∀ option ∈ decoded.table.options, option.2 ≠ [] := by
  simp [DecodedProductionBlockingTable.optionsNonempty]

def decodeProductionParent (nodeCount : Nat) (value : Nat) :
    Except String (Option (Fin nodeCount)) :=
  if value = nodeCount then
    return none
  else
    return some (← checkedFin "production predecessor" nodeCount value)

def decodeProductionParents (nodeCount : Nat) (values : List Nat) :
    Except String (Fin nodeCount → Option (Fin nodeCount)) := do
  let decoded ← values.mapM (decodeProductionParent nodeCount)
  if h : decoded.length = nodeCount then
    return fun node => decoded.get (h.symm ▸ node)
  else
    throw s!"production parent table has {decoded.length} entries, expected {nodeCount}"

def WireProductionBlockingTable.decode
    (wire : WireProductionBlockingTable) :
    Except String DecodedProductionBlockingTable := do
  if wire.version != 2 then
    throw s!"unsupported production blocker table version {wire.version}"
  let decodedBase ← wire.base.decodeBase
  let parent ← decodeProductionParents decodedBase.nodeCount wire.parents
  let forbidden ← wire.forbidden.mapM fun pair => do
    return (← checkedFin "forbidden source" decodedBase.nodeCount pair.source,
      ← checkedFin "forbidden blocker" decodedBase.nodeCount pair.target)
  let options ← wire.options.mapM fun option => do
    let source ← checkedFin "option source" decodedBase.nodeCount option.source
    let blockers ← option.blockers.mapM
      (checkedFin "option blocker" decodedBase.nodeCount)
    return (source, blockers)
  let rejected ← wire.rejected.mapM fun assignment => do
    let pairs ← assignment.mapM fun pair => do
      return (← checkedFin "rejected source" decodedBase.nodeCount pair.source,
        ← checkedFin "rejected blocker" decodedBase.nodeCount pair.target)
    return pairs.toFinset
  return {
    nodeCount := decodedBase.nodeCount
    conceptCount := decodedBase.conceptCount
    roleCount := decodedBase.roleCount
    variableCount := decodedBase.variableCount
    table := {
      base := decodedBase.certificate
      parent := parent
      forbidden := forbidden.toFinset
      options := options
    }
    rejected := rejected.toFinset
  }

def WireProductionBlockingTable.check
    (wire : WireProductionBlockingTable) : Except String Bool := do
  let decoded ← wire.decode
  return decoded.table.computableCheck && decoded.assignmentsExhausted &&
    decoded.optionsNonempty

theorem WireProductionBlockingTable.check_sound
    (wire : WireProductionBlockingTable)
    (decoded : DecodedProductionBlockingTable)
    (hdecode : wire.decode = .ok decoded)
    (hcheck : wire.check = .ok true) :
    decoded.table.ParentEarlier ∧
      decoded.table.options = decoded.table.expectedOptions ∧
      (∀ assignment ∈ enumerateFoldAssignments decoded.table.options,
        assignment ∈ decoded.rejected) ∧
      (∀ option ∈ decoded.table.options, option.2 ≠ []) := by
  simp only [WireProductionBlockingTable.check, hdecode] at hcheck
  have hbool : (decoded.table.computableCheck &&
      decoded.assignmentsExhausted && decoded.optionsNonempty) = true := by
    simpa using hcheck
  have checks : decoded.table.computableCheck = true ∧
      decoded.assignmentsExhausted = true ∧
      decoded.optionsNonempty = true := by
    simpa only [Bool.and_eq_true, and_assoc] using hbool
  exact ⟨(decoded.table.computableCheck_eq_true_iff.mp checks.1).1,
    (decoded.table.computableCheck_eq_true_iff.mp checks.1).2,
    decoded.assignmentsExhausted_eq_true_iff.mp checks.2.1,
    decoded.optionsNonempty_eq_true_iff.mp checks.2.2⟩

theorem WireProductionBlockingTable.checked_sourceExpansionControlled
    (wire : WireProductionBlockingTable)
    (decoded : DecodedProductionBlockingTable)
    (hdecode : wire.decode = .ok decoded)
    (hcheck : wire.check = .ok true)
    {source blockers}
    (hoption : (source, blockers) ∈ decoded.table.options) :
    SourceExpansionControlled decoded.rejected source blockers := by
  have checked := wire.check_sound decoded hdecode hcheck
  exact sourceExpansionControlled_of_assignment_exhaustion checked.2.2.2
    decoded.rejected checked.2.2.1 hoption

#print axioms WireProductionBlockingTable.check_sound
#print axioms FiniteProductionBlockingTable.computableExpectedOptions_eq
#print axioms FiniteProductionBlockingTable.computableCheck_eq_true_iff
#print axioms DecodedProductionBlockingTable.assignmentsExhausted_eq_true_iff
#print axioms DecodedProductionBlockingTable.optionsNonempty_eq_true_iff
#print axioms WireProductionBlockingTable.checked_sourceExpansionControlled

end ContextCalculus.Hypertableau
