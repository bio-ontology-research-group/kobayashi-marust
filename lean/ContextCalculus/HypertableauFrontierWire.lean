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
  2 ^ (2 * conceptCount) * (1 + 2 ^ (2 * conceptCount + 2 * roleCount))

theorem card_lit_fin (count : Nat) :
    Fintype.card (Lit (Fin count)) = 2 * count := by
  rw [Fintype.card_congr (litEquiv (Fin count))]
  simp [Nat.mul_comm]

theorem card_roleBlockingSignature_fin (conceptCount roleCount : Nat) :
    Fintype.card (RoleBlockingSignature (Fin conceptCount) (Fin roleCount)) =
      roleBlockingSignatureCard conceptCount roleCount := by
  simp only [RoleBlockingSignature, Fintype.card_prod, Fintype.card_finset,
    Fintype.card_option, Fintype.card_fin, card_lit_fin]
  simp only [roleBlockingSignatureCard, pow_add]
  ring

def WireWitnessStep.decode (conceptCount roleCount : Nat)
    (step : WireWitnessStep) :
    Except String (WitnessSlot (Fin conceptCount) (Fin roleCount)) := do
  return (← checkedFin "role" roleCount step.role,
    ← step.filler.decode conceptCount)

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
#print axioms mode6_doubling_eventually_rejects_checked_frontier

end ContextCalculus.Hypertableau
