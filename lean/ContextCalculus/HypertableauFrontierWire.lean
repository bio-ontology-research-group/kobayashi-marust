import ContextCalculus.HypertableauRoleBlocking
import ContextCalculus.HypertableauWire
import Mathlib.Data.List.Nodup

/-!
# Checked wire refinement for equality-free HT frontiers

The Rust producer reports bounded-search frontiers using ordinary natural
number identifiers and lists of `(role, filler)` witness steps.  This module
decodes that untrusted representation into Lean's finite, depth-bounded rooted
witness addresses.  Acceptance therefore supplies the injective address map
required by the iterative-deepening termination theorem.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireWitnessStep where
  role : Nat
  filler : WireLit
deriving FromJson, ToJson, Repr

structure WireAddressFrontier where
  version : Nat
  node_count : Nat
  concept_count : Nat
  role_count : Nat
  addresses : List (List WireWitnessStep)
deriving FromJson, ToJson, Repr

structure DecodedAddressFrontier
    (nodeCount conceptCount roleCount : Nat) where
  address : Fin nodeCount → WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount)
  injective : Function.Injective address

/-- Executable cardinality of the full signed pairwise signature over finite
concept and role identifiers. -/
def roleBlockingSignatureCard (conceptCount roleCount : Nat) : Nat :=
  let localFactBits := 2 * conceptCount + roleCount * (2 * conceptCount)
  2 ^ localFactBits * (1 + 2 ^ (localFactBits + 2 * roleCount))

theorem card_lit_fin (count : Nat) :
    Fintype.card (Lit (Fin count)) = 2 * count := by
  rw [Fintype.card_congr (litEquiv (Fin count))]
  simp [Nat.mul_comm]

theorem card_roleBlockingSignature_fin (conceptCount roleCount : Nat) :
    Fintype.card (RoleBlockingSignature (Fin conceptCount) (Fin roleCount)) =
      roleBlockingSignatureCard conceptCount roleCount := by
  simp only [RoleBlockingSignature, LocalBlockingFacts, Fintype.card_prod, Fintype.card_finset,
    Fintype.card_option, Fintype.card_fin, card_lit_fin]
  simp only [roleBlockingSignatureCard, pow_add, Nat.mul_comm]
  ring

def WireWitnessStep.decode (conceptCount roleCount : Nat)
    (step : WireWitnessStep) :
    Except String (WitnessSlot (Fin conceptCount) (Fin roleCount)) := do
  return (← checkedFin "role" roleCount step.role,
    ← step.filler.decode conceptCount)

def WireWitnessStep.encode
    (step : WitnessSlot (Fin conceptCount) (Fin roleCount)) : WireWitnessStep where
  role := step.1.val
  filler := WireLit.encode step.2

@[simp] theorem WireWitnessStep.decode_encode
    (step : WitnessSlot (Fin conceptCount) (Fin roleCount)) :
    (WireWitnessStep.encode step).decode conceptCount roleCount = .ok step := by
  rcases step with ⟨role, literal⟩
  simp only [WireWitnessStep.encode, WireWitnessStep.decode,
    checkedFin_value, WireLit.decode_encode]
  rfl

def encodeWireWitnessAddress
    (address : WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount)) :
    List WireWitnessStep :=
  address.2.1.map WireWitnessStep.encode

private theorem mapM_decode_encoded_steps
    (steps : List (WitnessSlot (Fin conceptCount) (Fin roleCount))) :
    (steps.map WireWitnessStep.encode).mapM
      (WireWitnessStep.decode conceptCount roleCount) = .ok steps := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
      simp only [List.map_cons, List.mapM_cons,
        WireWitnessStep.decode_encode, ih]
      rfl

def decodeWireWitnessAddress (conceptCount roleCount : Nat)
    (steps : List WireWitnessStep) :
    Except String (WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount)) := do
  let decoded ← steps.mapM (WireWitnessStep.decode conceptCount roleCount)
  if hdepth : decoded.length ≤ roleBlockingSignatureCard conceptCount roleCount then
    return (0, ⟨decoded, by
      rw [card_roleBlockingSignature_fin]
      exact hdepth⟩)
  else
    throw s!"witness address depth {decoded.length} exceeds the full-signature bound"

@[simp] theorem decodeWireWitnessAddress_encode
    (address : WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount)) :
    decodeWireWitnessAddress conceptCount roleCount
      (encodeWireWitnessAddress address) = .ok address := by
  unfold decodeWireWitnessAddress encodeWireWitnessAddress
  rw [mapM_decode_encoded_steps]
  have hdepth : address.2.1.length ≤
      roleBlockingSignatureCard conceptCount roleCount := by
    rw [← card_roleBlockingSignature_fin]
    exact address.2.2
  change Except.bind (Except.ok address.2.1) _ = Except.ok address
  rw [Except.bind]
  rw [dif_pos hdepth]
  apply congrArg (Except.ok (ε := String))
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · apply Subtype.ext
    rfl

private theorem mapM_decode_encoded_addresses
    (addresses : List
      (WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount))) :
    (addresses.map encodeWireWitnessAddress).mapM
      (decodeWireWitnessAddress conceptCount roleCount) = .ok addresses := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
      simp only [List.map_cons, List.mapM_cons,
        decodeWireWitnessAddress_encode, ih]
      rfl

private theorem mapM_decode_encoded_address_function
    (nodes : List (Fin nodeCount))
    (address : Fin nodeCount →
      WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount)) :
    nodes.mapM (decodeWireWitnessAddress conceptCount roleCount ∘
      encodeWireWitnessAddress ∘ address) =
        .ok (nodes.map address) := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
      simp only [List.mapM_cons, List.map_cons, Function.comp_apply,
        decodeWireWitnessAddress_encode, ih]
      rfl

/-- Canonical wire document for a complete finite rooted-address map. -/
def WireAddressFrontier.ofAddress
    (address : Fin nodeCount →
      WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount)) :
    WireAddressFrontier where
  version := 1
  node_count := nodeCount
  concept_count := conceptCount
  role_count := roleCount
  addresses := (List.finRange nodeCount).map
    (encodeWireWitnessAddress ∘ address)

def WireAddressFrontier.decode (document : WireAddressFrontier) :
    Except String (DecodedAddressFrontier document.node_count
      document.concept_count document.role_count) := do
  if document.version != 1 then
    throw s!"unsupported HT frontier wire version {document.version}"
  let decoded ← document.addresses.mapM
    (decodeWireWitnessAddress document.concept_count document.role_count)
  if hlength : decoded.length = document.node_count then
    if hnodup : decoded.Nodup then
      let address : Fin document.node_count →
          WitnessAddress (Fin 1) (Fin document.concept_count) (Fin document.role_count) :=
        fun node => decoded.get (Fin.cast hlength.symm node)
      return {
        address := address
        injective := by
          intro left right hequal
          have hcast : Fin.cast hlength.symm left = Fin.cast hlength.symm right :=
            hnodup.injective_get hequal
          have hval := congrArg (fun node => node.val) hcast
          apply Fin.ext
          simpa using hval
      }
    else
      throw "HT frontier contains duplicate rooted witness addresses"
  else
    throw s!"HT frontier has {decoded.length} addresses for {document.node_count} nodes"

def WireAddressFrontier.check (document : WireAddressFrontier) : Bool :=
  document.decode.isOk

/-- Check both the untrusted address frontier and the exact production budget
encoded by its node count. The retry number is intentionally absent: retries
at one budget share the same finite node universe. -/
def WireAddressFrontier.checkScheduled
    (document : WireAddressFrontier) (budget : Nat) : Bool :=
  document.check && decide (document.node_count = 8 * 2 ^ budget)

/-- Every injective complete rooted-address map has a checker-accepted wire
representation at its exact production budget. This is frontier serializer
completeness, not merely checker soundness. -/
theorem WireAddressFrontier.ofAddress_checkScheduled
    (address : Fin nodeCount →
      WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address)
    (hnodes : nodeCount = 8 * 2 ^ budget) :
    (WireAddressFrontier.ofAddress address).checkScheduled budget = true := by
  classical
  have hnodup : ((List.finRange nodeCount).map address).Nodup :=
    (List.nodup_finRange nodeCount).map hinjective
  simp only [WireAddressFrontier.checkScheduled, WireAddressFrontier.check,
    WireAddressFrontier.ofAddress]
  unfold WireAddressFrontier.decode
  simp [mapM_decode_encoded_address_function]
  constructor
  · change (Except.bind (Except.ok ((List.finRange nodeCount).map address)) _).isOk = true
    rw [Except.bind]
    simp [hnodup]
    rfl
  · exact hnodes

theorem WireAddressFrontier.checkScheduled_check
    (document : WireAddressFrontier) (budget : Nat)
    (hcheck : document.checkScheduled budget = true) :
    document.check = true := by
  simp only [WireAddressFrontier.checkScheduled, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  exact hcheck.1

/-- Acceptance of the scheduled wire payload supplies the former abstract
frontier-dimension premise directly. -/
theorem WireAddressFrontier.checkScheduled_node_count
    (document : WireAddressFrontier) (budget : Nat)
    (hcheck : document.checkScheduled budget = true) :
    document.node_count = 8 * 2 ^ budget := by
  simp only [WireAddressFrontier.checkScheduled, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  exact hcheck.2

/-- Checker acceptance is the exact concrete refinement premise consumed by
the outer iterative-deepening theorem. -/
theorem WireAddressFrontier.check_refines (document : WireAddressFrontier)
    (hcheck : document.check = true) :
    ∃ address : Fin document.node_count →
        WitnessAddress (Fin 1) (Fin document.concept_count) (Fin document.role_count),
      Function.Injective address := by
  unfold WireAddressFrontier.check at hcheck
  generalize hdecode : document.decode = result at hcheck
  cases result with
  | error error => exact Bool.noConfusion hcheck
  | ok decoded => exact ⟨decoded.address, decoded.injective⟩

private theorem transportWitnessAddressInjection
    {nodeCount conceptCount roleCount
      targetNodeCount targetConceptCount targetRoleCount : Nat}
    (hnodes : nodeCount = targetNodeCount)
    (hconcepts : conceptCount = targetConceptCount)
    (hroles : roleCount = targetRoleCount)
    (address : Fin nodeCount →
      WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    ∃ transported : Fin targetNodeCount →
        WitnessAddress (Fin 1) (Fin targetConceptCount) (Fin targetRoleCount),
      Function.Injective transported := by
  subst targetNodeCount
  subst targetConceptCount
  subst targetRoleCount
  exact ⟨address, hinjective⟩

/-- A fixed-vocabulary sequence of full doubling frontiers cannot all pass the
wire refinement checker. This composes untrusted Rust JSON directly with the
finite-address termination theorem. -/
theorem mode6_doubling_eventually_rejects_checked_frontier
    (frontier : Nat → WireAddressFrontier)
    (conceptCount roleCount : Nat)
    (hnodes : ∀ round, (frontier round).node_count = 8 * 2 ^ round)
    (hconcepts : ∀ round, (frontier round).concept_count = conceptCount)
    (hroles : ∀ round, (frontier round).role_count = roleCount) :
    ∃ round, (frontier round).check ≠ true := by
  apply mode6_doubling_eventually_not_frontier
    (Root := Fin 1) (Concept := Fin conceptCount) (Role := Fin roleCount)
    (frontier := fun round => (frontier round).check = true)
  intro round hcheck
  obtain ⟨address, hinjective⟩ :=
    (frontier round).check_refines hcheck
  exact transportWitnessAddressInjection
    (hnodes round) (hconcepts round) (hroles round) address hinjective

#print axioms WireAddressFrontier.check_refines
#print axioms decodeWireWitnessAddress_encode
#print axioms WireAddressFrontier.ofAddress_checkScheduled
#print axioms WireAddressFrontier.checkScheduled_check
#print axioms WireAddressFrontier.checkScheduled_node_count
#print axioms mode6_doubling_eventually_rejects_checked_frontier

end ContextCalculus.Hypertableau
