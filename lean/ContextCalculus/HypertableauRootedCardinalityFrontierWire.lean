import ContextCalculus.HypertableauCardinalityFrontierWire

/-!
# Multi-root tagged frontiers for native-ABox cardinality search

Native ABoxes have one finite root per named individual in addition to the
query root. Their addresses must retain root identity; a path alone is not an
injective address when several roots have empty paths.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireRootedCardinalityAddress where
  root : Nat
  steps : List WireCardinalityWitnessStep
deriving FromJson, ToJson, Repr

structure WireRootedCardinalityAddressFrontier where
  version : Nat
  node_count : Nat
  root_count : Nat
  concept_count : Nat
  role_count : Nat
  definition_count : Nat
  max_width : Nat
  addresses : List WireRootedCardinalityAddress
deriving FromJson, ToJson, Repr

def WireRootedCardinalityAddress.decode
    (conceptCount roleCount definitionCount maxWidth rootCount : Nat)
    (wire : WireRootedCardinalityAddress) : Except String
      (RootedRoleBlockedAddress (Fin rootCount)
        (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
          definitionCount maxWidth)
        (Fin conceptCount) (Fin roleCount)) := do
  let root ← checkedFin "native-ABox root" rootCount wire.root
  let decoded ← wire.steps.mapM
    (WireCardinalityWitnessStep.decode conceptCount roleCount definitionCount maxWidth)
  if hdepth : decoded.length ≤ roleBlockingSignatureCard conceptCount roleCount then
    return (root, ⟨decoded, by
      rw [card_roleBlockingSignature_fin]
      exact hdepth⟩)
  else
    throw s!"rooted cardinality address depth {decoded.length} exceeds the full-signature bound"

def WireRootedCardinalityAddress.encode
    (address : RootedRoleBlockedAddress (Fin rootCount)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitionCount maxWidth)
      (Fin conceptCount) (Fin roleCount)) : WireRootedCardinalityAddress where
  root := address.1.val
  steps := address.2.1.map WireCardinalityWitnessStep.encode

private theorem mapM_decode_encoded_rooted_cardinality_steps
    (steps : List (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
      definitionCount maxWidth)) :
    (steps.map WireCardinalityWitnessStep.encode).mapM
      (WireCardinalityWitnessStep.decode conceptCount roleCount
        definitionCount maxWidth) = .ok steps := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
      simp only [List.map_cons, List.mapM_cons,
        WireCardinalityWitnessStep.decode_encode, ih]
      rfl

@[simp] theorem WireRootedCardinalityAddress.decode_encode
    (address : RootedRoleBlockedAddress (Fin rootCount)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitionCount maxWidth)
      (Fin conceptCount) (Fin roleCount)) :
    (WireRootedCardinalityAddress.encode address).decode conceptCount roleCount
      definitionCount maxWidth rootCount = .ok address := by
  unfold WireRootedCardinalityAddress.decode WireRootedCardinalityAddress.encode
  rw [checkedFin_value, mapM_decode_encoded_rooted_cardinality_steps]
  have hdepth : address.2.1.length ≤
      roleBlockingSignatureCard conceptCount roleCount := by
    rw [← card_roleBlockingSignature_fin]
    exact address.2.2
  change Except.bind (Except.ok address.1) _ = Except.ok address
  rw [Except.bind]
  change Except.bind (Except.ok address.2.1) _ = Except.ok address
  rw [Except.bind]
  rw [dif_pos hdepth]
  apply congrArg (Except.ok (ε := String))
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    rfl

structure DecodedRootedCardinalityAddressFrontier
    (nodeCount rootCount conceptCount roleCount definitionCount maxWidth : Nat) where
  address : Fin nodeCount → RootedRoleBlockedAddress (Fin rootCount)
    (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
      definitionCount maxWidth)
    (Fin conceptCount) (Fin roleCount)
  injective : Function.Injective address

def WireRootedCardinalityAddressFrontier.decode
    (document : WireRootedCardinalityAddressFrontier) : Except String
      (DecodedRootedCardinalityAddressFrontier document.node_count
        document.root_count document.concept_count document.role_count
        document.definition_count document.max_width) := do
  if document.version != 1 then
    throw s!"unsupported rooted cardinality frontier version {document.version}"
  let decoded ← document.addresses.mapM fun address =>
    address.decode document.concept_count document.role_count
      document.definition_count document.max_width document.root_count
  if hlength : decoded.length = document.node_count then
    if hnodup : decoded.Nodup then
      let address := fun node : Fin document.node_count =>
        decoded.get (Fin.cast hlength.symm node)
      return {
        address := address
        injective := by
          intro left right hequal
          have hcast : Fin.cast hlength.symm left = Fin.cast hlength.symm right :=
            hnodup.injective_get hequal
          apply Fin.ext
          simpa using congrArg (fun node => node.val) hcast
      }
    else throw "rooted cardinality frontier contains duplicate addresses"
  else throw "rooted cardinality frontier address count differs from node count"

def WireRootedCardinalityAddressFrontier.check
    (document : WireRootedCardinalityAddressFrontier) : Bool :=
  document.decode.isOk

def WireRootedCardinalityAddressFrontier.checkScheduled
    (document : WireRootedCardinalityAddressFrontier)
    (budget rootCount maxWidth : Nat) : Bool :=
  document.check &&
    decide (document.node_count = 8 * 2 ^ budget) &&
    decide (document.root_count = rootCount) &&
    decide (document.max_width = maxWidth)

def WireRootedCardinalityAddressFrontier.ofAddress
    (address : Fin nodeCount → RootedRoleBlockedAddress (Fin rootCount)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitionCount maxWidth)
      (Fin conceptCount) (Fin roleCount)) :
    WireRootedCardinalityAddressFrontier where
  version := 1
  node_count := nodeCount
  root_count := rootCount
  concept_count := conceptCount
  role_count := roleCount
  definition_count := definitionCount
  max_width := maxWidth
  addresses := (List.finRange nodeCount).map
    (WireRootedCardinalityAddress.encode ∘ address)

private theorem mapM_decode_encoded_rooted_cardinality_address_function
    (nodes : List (Fin nodeCount))
    (address : Fin nodeCount → RootedRoleBlockedAddress (Fin rootCount)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitionCount maxWidth)
      (Fin conceptCount) (Fin roleCount)) :
    nodes.mapM (WireRootedCardinalityAddress.decode conceptCount roleCount
      definitionCount maxWidth rootCount ∘
        WireRootedCardinalityAddress.encode ∘ address) =
      .ok (nodes.map address) := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
      simp only [List.mapM_cons, List.map_cons, Function.comp_apply,
        WireRootedCardinalityAddress.decode_encode, ih]
      rfl

theorem WireRootedCardinalityAddressFrontier.ofAddress_checkScheduled
    (address : Fin nodeCount → RootedRoleBlockedAddress (Fin rootCount)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitionCount maxWidth)
      (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address)
    (hnodes : nodeCount = 8 * 2 ^ budget) :
    (WireRootedCardinalityAddressFrontier.ofAddress address).checkScheduled
      budget rootCount maxWidth = true := by
  classical
  have hnodup : ((List.finRange nodeCount).map address).Nodup :=
    (List.nodup_finRange nodeCount).map hinjective
  simp only [WireRootedCardinalityAddressFrontier.checkScheduled,
    WireRootedCardinalityAddressFrontier.check,
    WireRootedCardinalityAddressFrontier.ofAddress]
  unfold WireRootedCardinalityAddressFrontier.decode
  simp [mapM_decode_encoded_rooted_cardinality_address_function]
  constructor
  · change (Except.bind (Except.ok ((List.finRange nodeCount).map address)) _).isOk = true
    rw [Except.bind]
    simp [hnodup]
    rfl
  · exact hnodes

theorem WireRootedCardinalityAddressFrontier.checkScheduled_check
    (document : WireRootedCardinalityAddressFrontier)
    (budget rootCount maxWidth : Nat)
    (hcheck : document.checkScheduled budget rootCount maxWidth = true) :
    document.check = true := by
  simp only [WireRootedCardinalityAddressFrontier.checkScheduled,
    Bool.and_eq_true] at hcheck
  exact hcheck.1.1.1

theorem WireRootedCardinalityAddressFrontier.checkScheduled_node_count
    (document : WireRootedCardinalityAddressFrontier)
    (budget rootCount maxWidth : Nat)
    (hcheck : document.checkScheduled budget rootCount maxWidth = true) :
    document.node_count = 8 * 2 ^ budget := by
  simp only [WireRootedCardinalityAddressFrontier.checkScheduled,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact hcheck.1.1.2

theorem WireRootedCardinalityAddressFrontier.checkScheduled_root_count
    (document : WireRootedCardinalityAddressFrontier)
    (budget rootCount maxWidth : Nat)
    (hcheck : document.checkScheduled budget rootCount maxWidth = true) :
    document.root_count = rootCount := by
  simp only [WireRootedCardinalityAddressFrontier.checkScheduled,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact hcheck.1.2

theorem WireRootedCardinalityAddressFrontier.checkScheduled_max_width
    (document : WireRootedCardinalityAddressFrontier)
    (budget rootCount maxWidth : Nat)
    (hcheck : document.checkScheduled budget rootCount maxWidth = true) :
    document.max_width = maxWidth := by
  simp only [WireRootedCardinalityAddressFrontier.checkScheduled,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact hcheck.2

theorem WireRootedCardinalityAddressFrontier.check_refines
    (document : WireRootedCardinalityAddressFrontier)
    (hcheck : document.check = true) :
    ∃ address : Fin document.node_count → RootedRoleBlockedAddress
        (Fin document.root_count)
        (CardinalityWitnessSlot (Fin document.concept_count)
          (Fin document.role_count) document.definition_count document.max_width)
        (Fin document.concept_count) (Fin document.role_count),
      Function.Injective address := by
  unfold WireRootedCardinalityAddressFrontier.check at hcheck
  generalize hdecode : document.decode = result at hcheck
  cases result with
  | error error => exact Bool.noConfusion hcheck
  | ok decoded => exact ⟨decoded.address, decoded.injective⟩

private theorem transportRootedCardinalityAddressInjection
    {nodeCount rootCount conceptCount roleCount definitionCount maxWidth
      targetNodeCount targetRootCount targetConceptCount targetRoleCount
      targetDefinitionCount targetMaxWidth : Nat}
    (hnodes : nodeCount = targetNodeCount)
    (hroots : rootCount = targetRootCount)
    (hconcepts : conceptCount = targetConceptCount)
    (hroles : roleCount = targetRoleCount)
    (hdefinitions : definitionCount = targetDefinitionCount)
    (hwidth : maxWidth = targetMaxWidth)
    (address : Fin nodeCount → RootedRoleBlockedAddress (Fin rootCount)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitionCount maxWidth)
      (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    ∃ transported : Fin targetNodeCount → RootedRoleBlockedAddress
        (Fin targetRootCount)
        (CardinalityWitnessSlot (Fin targetConceptCount) (Fin targetRoleCount)
          targetDefinitionCount targetMaxWidth)
        (Fin targetConceptCount) (Fin targetRoleCount),
      Function.Injective transported := by
  subst targetNodeCount
  subst targetRootCount
  subst targetConceptCount
  subst targetRoleCount
  subst targetDefinitionCount
  subst targetMaxWidth
  exact ⟨address, hinjective⟩

/-- Fixed multi-root cardinality vocabularies cannot fill every doubling
budget with distinct rooted addresses. -/
theorem rooted_cardinality_doubling_eventually_rejects_checked_frontier
    (frontier : Nat → WireRootedCardinalityAddressFrontier)
    (rootCount conceptCount roleCount definitionCount maxWidth : Nat)
    (hnodes : ∀ round, (frontier round).node_count = 8 * 2 ^ round)
    (hroots : ∀ round, (frontier round).root_count = rootCount)
    (hconcepts : ∀ round, (frontier round).concept_count = conceptCount)
    (hroles : ∀ round, (frontier round).role_count = roleCount)
    (hdefinitions : ∀ round, (frontier round).definition_count = definitionCount)
    (hwidth : ∀ round, (frontier round).max_width = maxWidth) :
    ∃ round, (frontier round).check ≠ true := by
  apply role_blocked_doubling_eventually_not_frontier
    (Root := Fin rootCount)
    (Slot := CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
      definitionCount maxWidth)
    (Concept := Fin conceptCount) (Role := Fin roleCount)
    (frontier := fun round => (frontier round).check = true)
  intro round hcheck
  obtain ⟨address, hinjective⟩ := (frontier round).check_refines hcheck
  exact transportRootedCardinalityAddressInjection
    (hnodes round) (hroots round) (hconcepts round) (hroles round)
    (hdefinitions round) (hwidth round) address hinjective

#print axioms WireRootedCardinalityAddress.decode_encode
#print axioms WireRootedCardinalityAddressFrontier.ofAddress_checkScheduled
#print axioms WireRootedCardinalityAddressFrontier.checkScheduled_check
#print axioms WireRootedCardinalityAddressFrontier.checkScheduled_node_count
#print axioms WireRootedCardinalityAddressFrontier.checkScheduled_root_count
#print axioms WireRootedCardinalityAddressFrontier.checkScheduled_max_width
#print axioms WireRootedCardinalityAddressFrontier.check_refines
#print axioms rooted_cardinality_doubling_eventually_rejects_checked_frontier

end ContextCalculus.Hypertableau
