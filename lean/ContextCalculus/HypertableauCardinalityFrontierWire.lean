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

def WireCardinalityWitnessStep.encode
    (step : CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
      definitionCount maxWidth) : WireCardinalityWitnessStep :=
  match step with
  | .inl (role, filler) => {
      kind := 0
      role := role.val
      filler := WireLit.encode filler
      definition := 0
      index := 0 }
  | .inr (definition, index) => {
      kind := 1
      role := 0
      filler := { concept := 0, neg := false }
      definition := definition.val
      index := index.val }

@[simp] theorem WireCardinalityWitnessStep.decode_encode
    (step : CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
      definitionCount maxWidth) :
    (WireCardinalityWitnessStep.encode step).decode conceptCount roleCount
      definitionCount maxWidth = .ok step := by
  rcases step with ⟨role, filler⟩ | ⟨definition, index⟩
  · simp only [WireCardinalityWitnessStep.encode,
      WireCardinalityWitnessStep.decode, checkedFin_value,
      WireLit.decode_encode]
    rfl
  · simp only [WireCardinalityWitnessStep.encode,
      WireCardinalityWitnessStep.decode, checkedFin_value]
    rfl

def encodeWireCardinalityAddress
    (address : RootedRoleBlockedAddress (Fin 1)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitionCount maxWidth)
      (Fin conceptCount) (Fin roleCount)) :
    List WireCardinalityWitnessStep :=
  address.2.1.map WireCardinalityWitnessStep.encode

private theorem mapM_decode_encoded_cardinality_steps
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

@[simp] theorem decodeWireCardinalityAddress_encode
    (address : RootedRoleBlockedAddress (Fin 1)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitionCount maxWidth)
      (Fin conceptCount) (Fin roleCount)) :
    decodeWireCardinalityAddress conceptCount roleCount definitionCount maxWidth
      (encodeWireCardinalityAddress address) = .ok address := by
  unfold decodeWireCardinalityAddress encodeWireCardinalityAddress
  rw [mapM_decode_encoded_cardinality_steps]
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

private theorem mapM_decode_encoded_cardinality_address_function
    (nodes : List (Fin nodeCount))
    (address : Fin nodeCount → RootedRoleBlockedAddress (Fin 1)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitionCount maxWidth)
      (Fin conceptCount) (Fin roleCount)) :
    nodes.mapM (decodeWireCardinalityAddress conceptCount roleCount
      definitionCount maxWidth ∘ encodeWireCardinalityAddress ∘ address) =
        .ok (nodes.map address) := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
      simp only [List.mapM_cons, List.map_cons, Function.comp_apply,
        decodeWireCardinalityAddress_encode, ih]
      rfl

structure DecodedCardinalityAddressFrontier
    (nodeCount conceptCount roleCount definitionCount maxWidth : Nat) where
  address : Fin nodeCount → RootedRoleBlockedAddress (Fin 1)
    (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
      definitionCount maxWidth)
    (Fin conceptCount) (Fin roleCount)
  injective : Function.Injective address

/-- Canonical cardinality-frontier document for a complete tagged address
map. -/
def WireCardinalityAddressFrontier.ofAddress
    (address : Fin nodeCount → RootedRoleBlockedAddress (Fin 1)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitionCount maxWidth)
      (Fin conceptCount) (Fin roleCount)) :
    WireCardinalityAddressFrontier where
  version := 1
  node_count := nodeCount
  concept_count := conceptCount
  role_count := roleCount
  definition_count := definitionCount
  max_width := maxWidth
  addresses := (List.finRange nodeCount).map
    (encodeWireCardinalityAddress ∘ address)

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

/-- Check the serialized cardinality frontier together with both dimensions
that vary in the production termination argument. -/
def WireCardinalityAddressFrontier.checkScheduled
    (document : WireCardinalityAddressFrontier)
    (budget maxWidth : Nat) : Bool :=
  document.check &&
    decide (document.node_count = 8 * 2 ^ budget) &&
    decide (document.max_width = maxWidth)

/-- Every injective complete tagged address map is accepted at its exact node
and width schedule. -/
theorem WireCardinalityAddressFrontier.ofAddress_checkScheduled
    (address : Fin nodeCount → RootedRoleBlockedAddress (Fin 1)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitionCount maxWidth)
      (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address)
    (hnodes : nodeCount = 8 * 2 ^ budget) :
    (WireCardinalityAddressFrontier.ofAddress address).checkScheduled
      budget maxWidth = true := by
  classical
  have hnodup : ((List.finRange nodeCount).map address).Nodup :=
    (List.nodup_finRange nodeCount).map hinjective
  simp only [WireCardinalityAddressFrontier.checkScheduled,
    WireCardinalityAddressFrontier.check,
    WireCardinalityAddressFrontier.ofAddress]
  unfold WireCardinalityAddressFrontier.decode
  simp [mapM_decode_encoded_cardinality_address_function]
  constructor
  · change (Except.bind (Except.ok ((List.finRange nodeCount).map address)) _).isOk = true
    rw [Except.bind]
    simp [hnodup]
    rfl
  · exact hnodes

theorem WireCardinalityAddressFrontier.checkScheduled_check
    (document : WireCardinalityAddressFrontier) (budget maxWidth : Nat)
    (hcheck : document.checkScheduled budget maxWidth = true) :
    document.check = true := by
  simp only [WireCardinalityAddressFrontier.checkScheduled, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  exact hcheck.1.1

theorem WireCardinalityAddressFrontier.checkScheduled_node_count
    (document : WireCardinalityAddressFrontier) (budget maxWidth : Nat)
    (hcheck : document.checkScheduled budget maxWidth = true) :
    document.node_count = 8 * 2 ^ budget := by
  simp only [WireCardinalityAddressFrontier.checkScheduled, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  exact hcheck.1.2

theorem WireCardinalityAddressFrontier.checkScheduled_max_width
    (document : WireCardinalityAddressFrontier) (budget maxWidth : Nat)
    (hcheck : document.checkScheduled budget maxWidth = true) :
    document.max_width = maxWidth := by
  simp only [WireCardinalityAddressFrontier.checkScheduled, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  exact hcheck.2

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
#print axioms decodeWireCardinalityAddress_encode
#print axioms WireCardinalityAddressFrontier.ofAddress_checkScheduled
#print axioms WireCardinalityAddressFrontier.checkScheduled_check
#print axioms WireCardinalityAddressFrontier.checkScheduled_node_count
#print axioms WireCardinalityAddressFrontier.checkScheduled_max_width
#print axioms cardinality_doubling_eventually_rejects_checked_frontier

end ContextCalculus.Hypertableau
