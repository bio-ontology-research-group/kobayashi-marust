import ContextCalculus.HypertableauFrontierWire

/-!
# Checked tagged frontiers for cardinality-aware HT search

Minimum restrictions may create several children with the same role and
filler. Their rooted addresses therefore use a tagged finite slot vocabulary:
ordinary existential slots, or a minimum-definition and child-index slot.
-/

namespace ContextCalculus.Hypertableau

open Lean

abbrev CardinalityWitnessSlot
    (Concept Role : Type) (DefinitionCount MaxWidth : Nat) :=
  (Role × Lit Concept) ⊕ (Fin DefinitionCount × Fin MaxWidth)

structure WireCardinalityWitnessStep where
  kind : Nat
  role : Nat
  filler : WireLit
  definition : Nat
  index : Nat
deriving FromJson, ToJson, Repr

structure WireCardinalityAddressFrontier where
  version : Nat
  node_count : Nat
  concept_count : Nat
  role_count : Nat
  definition_count : Nat
  max_width : Nat
  addresses : List (List WireCardinalityWitnessStep)
deriving FromJson, ToJson, Repr

def WireCardinalityWitnessStep.decode
    (conceptCount roleCount definitionCount maxWidth : Nat)
    (step : WireCardinalityWitnessStep) : Except String
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitionCount maxWidth) := do
  match step.kind with
  | 0 =>
      return .inl (← checkedFin "role" roleCount step.role,
        ← step.filler.decode conceptCount)
  | 1 =>
      return .inr (← checkedFin "minimum definition" definitionCount step.definition,
        ← checkedFin "minimum child index" maxWidth step.index)
  | kind => throw s!"unsupported cardinality witness-step kind {kind}"

def decodeWireCardinalityAddress
    (conceptCount roleCount definitionCount maxWidth : Nat)
    (steps : List WireCardinalityWitnessStep) : Except String
      (RootedRoleBlockedAddress (Fin 1)
        (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
          definitionCount maxWidth)
        (Fin conceptCount) (Fin roleCount)) := do
  let decoded ← steps.mapM
    (WireCardinalityWitnessStep.decode conceptCount roleCount definitionCount maxWidth)
  if hdepth : decoded.length ≤ roleBlockingSignatureCard conceptCount roleCount then
    return (0, ⟨decoded, by
      rw [card_roleBlockingSignature_fin]
      exact hdepth⟩)
  else
    throw s!"cardinality witness address depth {decoded.length} exceeds the full-signature bound"

structure DecodedCardinalityAddressFrontier
    (nodeCount conceptCount roleCount definitionCount maxWidth : Nat) where
  address : Fin nodeCount → RootedRoleBlockedAddress (Fin 1)
    (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
      definitionCount maxWidth)
    (Fin conceptCount) (Fin roleCount)
  injective : Function.Injective address

def WireCardinalityAddressFrontier.decode
    (document : WireCardinalityAddressFrontier) : Except String
      (DecodedCardinalityAddressFrontier document.node_count
        document.concept_count document.role_count document.definition_count
        document.max_width) := do
  if document.version != 1 then
    throw s!"unsupported cardinality frontier wire version {document.version}"
  let decoded ← document.addresses.mapM
    (decodeWireCardinalityAddress document.concept_count document.role_count
      document.definition_count document.max_width)
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
    else throw "cardinality frontier contains duplicate rooted witness addresses"
  else
    throw s!"cardinality frontier has {decoded.length} addresses for {document.node_count} nodes"

def WireCardinalityAddressFrontier.check
    (document : WireCardinalityAddressFrontier) : Bool := document.decode.isOk

theorem WireCardinalityAddressFrontier.check_refines
    (document : WireCardinalityAddressFrontier)
    (hcheck : document.check = true) :
    ∃ address : Fin document.node_count → RootedRoleBlockedAddress (Fin 1)
        (CardinalityWitnessSlot (Fin document.concept_count) (Fin document.role_count)
          document.definition_count document.max_width)
        (Fin document.concept_count) (Fin document.role_count),
      Function.Injective address := by
  unfold WireCardinalityAddressFrontier.check at hcheck
  generalize hdecode : document.decode = result at hcheck
  cases result with
  | error error => exact Bool.noConfusion hcheck
  | ok decoded => exact ⟨decoded.address, decoded.injective⟩

private theorem transportCardinalityAddressInjection
    {nodeCount conceptCount roleCount definitionCount maxWidth
      targetNodeCount targetConceptCount targetRoleCount
      targetDefinitionCount targetMaxWidth : Nat}
    (hnodes : nodeCount = targetNodeCount)
    (hconcepts : conceptCount = targetConceptCount)
    (hroles : roleCount = targetRoleCount)
    (hdefinitions : definitionCount = targetDefinitionCount)
    (hwidth : maxWidth = targetMaxWidth)
    (address : Fin nodeCount → RootedRoleBlockedAddress (Fin 1)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitionCount maxWidth)
      (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    ∃ transported : Fin targetNodeCount → RootedRoleBlockedAddress (Fin 1)
        (CardinalityWitnessSlot (Fin targetConceptCount) (Fin targetRoleCount)
          targetDefinitionCount targetMaxWidth)
        (Fin targetConceptCount) (Fin targetRoleCount),
      Function.Injective transported := by
  subst targetNodeCount
  subst targetConceptCount
  subst targetRoleCount
  subst targetDefinitionCount
  subst targetMaxWidth
  exact ⟨address, hinjective⟩

/-- A fixed cardinality vocabulary cannot produce checked full frontiers at
every budget in the doubling schedule. -/
theorem cardinality_doubling_eventually_rejects_checked_frontier
    (frontier : Nat → WireCardinalityAddressFrontier)
    (conceptCount roleCount definitionCount maxWidth : Nat)
    (hnodes : ∀ round, (frontier round).node_count = 8 * 2 ^ round)
    (hconcepts : ∀ round, (frontier round).concept_count = conceptCount)
    (hroles : ∀ round, (frontier round).role_count = roleCount)
    (hdefinitions : ∀ round, (frontier round).definition_count = definitionCount)
    (hwidth : ∀ round, (frontier round).max_width = maxWidth) :
    ∃ round, (frontier round).check ≠ true := by
  apply role_blocked_doubling_eventually_not_frontier
    (Root := Fin 1)
    (Slot := CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
      definitionCount maxWidth)
    (Concept := Fin conceptCount) (Role := Fin roleCount)
    (frontier := fun round => (frontier round).check = true)
  intro round hcheck
  obtain ⟨address, hinjective⟩ := (frontier round).check_refines hcheck
  exact transportCardinalityAddressInjection
    (hnodes round) (hconcepts round) (hroles round)
    (hdefinitions round) (hwidth round) address hinjective

#print axioms WireCardinalityAddressFrontier.check_refines
#print axioms cardinality_doubling_eventually_rejects_checked_frontier

end ContextCalculus.Hypertableau
