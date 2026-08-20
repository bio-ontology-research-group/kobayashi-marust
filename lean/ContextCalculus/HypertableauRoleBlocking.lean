import ContextCalculus.HypertableauSearch
import Mathlib.Data.Fintype.Option

/-!
# Finite role-sensitive hypertableau blocking signatures

Label equality alone does not retain the predecessor context inspected by role
and inverse-role bodies. This module defines the full pairwise signature used by
sound double blocking: the signed node label, signed predecessor label, and the
sets of roles connecting predecessor and node in both directions. All fields
range over finite types, so sufficiently long predecessor paths repeat a full
signature.
-/

namespace ContextCalculus.Hypertableau

abbrev RoleBlockingSignature (Concept Role : Type) :=
  Finset (Lit Concept) ×
    Option (Finset (Lit Concept) × Finset Role × Finset Role)

noncomputable def State.forwardParentRoles
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) (parent node : Node) : Finset Role := by
  classical
  exact Finset.univ.filter fun role => state.edge role parent node

noncomputable def State.backwardParentRoles
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) (parent node : Node) : Finset Role := by
  classical
  exact Finset.univ.filter fun role => state.edge role node parent

/-- Full signed bidirectional pairwise signature. This is the mathematical
counterpart of Rust's `i3_signature_full`, with `none` reserved for roots. -/
noncomputable def State.roleBlockingSignature
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) (parent : Node → Option Node) (node : Node) :
    RoleBlockingSignature Concept Role :=
  (state.labelSet node, parent node |>.map fun predecessor =>
    (state.labelSet predecessor,
      state.forwardParentRoles predecessor node,
      state.backwardParentRoles predecessor node))

theorem State.roleBlockingSignature_label
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) (parent : Node → Option Node)
    {left right : Node}
    (hequal : state.roleBlockingSignature parent left =
      state.roleBlockingSignature parent right) :
    state.labelSet left = state.labelSet right := by
  exact congrArg Prod.fst hequal

theorem State.roleBlockingSignature_blocks
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) (parent : Node → Option Node)
    {blocker blocked : Node}
    (hequal : state.roleBlockingSignature parent blocker =
      state.roleBlockingSignature parent blocked) :
    state.Blocks blocker blocked :=
  state.blocks_of_labelSet_eq (state.roleBlockingSignature_label parent hequal)

/-- Equal non-root signatures retain the complete predecessor and connecting
role context in addition to the blocked node label. -/
theorem State.roleBlockingSignature_parent_context
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) (parent : Node → Option Node)
    {blocker blocked blockerParent blockedParent : Node}
    (hblockerParent : parent blocker = some blockerParent)
    (hblockedParent : parent blocked = some blockedParent)
    (hequal : state.roleBlockingSignature parent blocker =
      state.roleBlockingSignature parent blocked) :
    state.labelSet blockerParent = state.labelSet blockedParent ∧
      state.forwardParentRoles blockerParent blocker =
        state.forwardParentRoles blockedParent blocked ∧
      state.backwardParentRoles blockerParent blocker =
        state.backwardParentRoles blockedParent blocked := by
  have hsecond := congrArg Prod.snd hequal
  have hcontext :
      (state.labelSet blockerParent,
        state.forwardParentRoles blockerParent blocker,
        state.backwardParentRoles blockerParent blocker) =
      (state.labelSet blockedParent,
        state.forwardParentRoles blockedParent blocked,
        state.backwardParentRoles blockedParent blocked) := by
    simpa [State.roleBlockingSignature, hblockerParent, hblockedParent] using hsecond
  exact ⟨congrArg Prod.fst hcontext,
    congrArg (fun context => context.2.1) hcontext,
    congrArg (fun context => context.2.2) hcontext⟩

/-- Every path longer than the finite full-signature vocabulary has an earlier
node with the same signed pairwise role signature. -/
theorem State.exists_role_blocker_on_long_path
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) (parent : Node → Option Node)
    (path : Fin (Fintype.card (RoleBlockingSignature Concept Role) + 1) → Node) :
    ∃ earlier later,
      earlier < later ∧
      state.roleBlockingSignature parent (path earlier) =
        state.roleBlockingSignature parent (path later) := by
  classical
  let positions :
      Finset (Fin (Fintype.card (RoleBlockingSignature Concept Role) + 1)) :=
    Finset.univ
  let signatures : Finset (RoleBlockingSignature Concept Role) := Finset.univ
  have hcard : signatures.card < positions.card := by
    simp [positions, signatures]
  obtain ⟨left, _, right, _, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun position => state.roleBlockingSignature parent (path position))
      (fun _ _ => by simp [signatures])
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨left, right, hlt, heq⟩
  · exact ⟨right, left, hgt, heq.symm⟩

/-! A finite branching vocabulary turns the signature depth bound into a finite
node-address universe. A slot identifies one of the finitely many successor
obligations available at a node. Blocking prevents an address from being longer
than the number of pairwise signatures. -/

def RoleBlockedAddress (Slot Concept Role : Type)
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role] :=
  {address : List Slot //
    address.length ≤ Fintype.card (RoleBlockingSignature Concept Role)}

noncomputable instance roleBlockedAddressFintype
    (Slot Concept Role : Type)
    [Fintype Slot]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role] :
    Fintype (RoleBlockedAddress Slot Concept Role) :=
  (List.finite_length_le Slot
    (Fintype.card (RoleBlockingSignature Concept Role))).fintype

def RoleBlockedAddress.extend
    {Slot Concept Role : Type}
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (address : RoleBlockedAddress Slot Concept Role) (slot : Slot)
    (hdepth : address.1.length <
      Fintype.card (RoleBlockingSignature Concept Role)) :
    RoleBlockedAddress Slot Concept Role :=
  ⟨address.1 ++ [slot], by simpa using Nat.succ_le_of_lt hdepth⟩

@[simp] theorem RoleBlockedAddress.extend_length
    {Slot Concept Role : Type}
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (address : RoleBlockedAddress Slot Concept Role) (slot : Slot)
    (hdepth : address.1.length <
      Fintype.card (RoleBlockingSignature Concept Role)) :
    (address.extend slot hdepth).1.length = address.1.length + 1 := by
  simp [RoleBlockedAddress.extend]

/-- An obligation-specific child address below the blocking depth is a valid
fresh witness whenever that exact address is not already active. -/
theorem State.fresh_extended_roleBlockedAddress
    {Slot Concept Role : Type}
    [Fintype Slot] [DecidableEq Slot]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State (RoleBlockedAddress Slot Concept Role) Concept Role)
    (address : RoleBlockedAddress Slot Concept Role) (slot : Slot)
    (hdepth : address.1.length <
      Fintype.card (RoleBlockingSignature Concept Role))
    (hunused : ¬state.NodeUsed (address.extend slot hdepth)) :
    state.Fresh (address.extend slot hdepth) := by
  refine ⟨?_, ?_, ?_⟩
  · intro literal hlabel
    exact hunused (Or.inl ⟨literal, hlabel⟩)
  · intro candidateRole node
    exact ⟨fun hedge => hunused
        (Or.inr (Or.inl ⟨candidateRole, node, Or.inl hedge⟩)),
      fun hedge => hunused
        (Or.inr (Or.inl ⟨candidateRole, node, Or.inr hedge⟩))⟩
  · intro candidateRole filler hobligation
    exact hunused (Or.inr (Or.inr ⟨candidateRole, filler, hobligation⟩))

/-! Equality-free existential expansion assigns one canonical child slot to
each role-and-filler obligation. The invariant below states the exact runtime
condition needed by finite search: the canonical child is either unused or it
already realizes that obligation. -/

abbrev WitnessSlot (Concept Role : Type) := Role × Lit Concept

abbrev RootedRoleBlockedAddress (Root Slot Concept Role : Type)
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role] :=
  Root × RoleBlockedAddress Slot Concept Role

def RootedRoleBlockedAddress.extend
    {Root Slot Concept Role : Type}
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (address : RootedRoleBlockedAddress Root Slot Concept Role) (slot : Slot)
    (hdepth : address.2.1.length <
      Fintype.card (RoleBlockingSignature Concept Role)) :
    RootedRoleBlockedAddress Root Slot Concept Role :=
  (address.1, address.2.extend slot hdepth)

abbrev WitnessAddress (Root Concept Role : Type)
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role] :=
  RootedRoleBlockedAddress Root (WitnessSlot Concept Role) Concept Role

/-- Extending one rooted path preserves its root identity and gives a fresh
node whenever that exact rooted address is not active. -/
theorem State.fresh_extended_rootedRoleBlockedAddress
    {Root Slot Concept Role : Type}
    [Fintype Root] [DecidableEq Root]
    [Fintype Slot] [DecidableEq Slot]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State (RootedRoleBlockedAddress Root Slot Concept Role) Concept Role)
    (address : RootedRoleBlockedAddress Root Slot Concept Role) (slot : Slot)
    (hdepth : address.2.1.length <
      Fintype.card (RoleBlockingSignature Concept Role))
    (hunused : ¬state.NodeUsed (address.extend slot hdepth)) :
    state.Fresh (address.extend slot hdepth) := by
  refine ⟨?_, ?_, ?_⟩
  · intro literal hlabel
    exact hunused (Or.inl ⟨literal, hlabel⟩)
  · intro candidateRole node
    exact ⟨fun hedge => hunused
        (Or.inr (Or.inl ⟨candidateRole, node, Or.inl hedge⟩)),
      fun hedge => hunused
        (Or.inr (Or.inl ⟨candidateRole, node, Or.inr hedge⟩))⟩
  · intro candidateRole filler hobligation
    exact hunused (Or.inr (Or.inr ⟨candidateRole, filler, hobligation⟩))

def State.ObligationAddressInvariant
    {Root : Type} [Fintype Root] [DecidableEq Root]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State (WitnessAddress Root Concept Role) Concept Role) : Prop :=
  ∀ source role filler, state.obligation role filler source →
    ∃ hdepth : source.2.1.length <
        Fintype.card (RoleBlockingSignature Concept Role),
      let target := source.extend (role, filler) hdepth
      ¬state.NodeUsed target ∨
        (state.edge role source target ∧ state.label target filler)

/-- Under canonical obligation addressing, every unwitnessed existential has
an unused, and therefore fresh, finite role-blocked child address. -/
theorem State.exists_fresh_of_unwitnessed_of_obligationAddressInvariant
    {Root : Type} [Fintype Root] [DecidableEq Root]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State (WitnessAddress Root Concept Role) Concept Role)
    (hinvariant : state.ObligationAddressInvariant)
    (hunwitnessed : state.HasUnwitnessed) :
    ∃ target, state.Fresh target := by
  rcases hunwitnessed with
    ⟨source, role, filler, hobligation, hnowitness⟩
  obtain ⟨hdepth, hunused | hwitness⟩ :=
    hinvariant source role filler hobligation
  · let target := source.extend (role, filler) hdepth
    exact ⟨target,
      state.fresh_extended_rootedRoleBlockedAddress source (role, filler) hdepth
        (by simpa [target] using hunused)⟩
  · exact False.elim (hnowitness _ hwitness)

/-- The address invariant discharges the abstract fresh-supply premise of the
exact equality-free HT transition theorem. -/
theorem State.obstruction_has_addressed_exhaustive_step
    {Root : Type} [Fintype Root] [DecidableEq Root]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (state : State (WitnessAddress Root Concept Role) Concept Role)
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom)
    (hinvariant : state.ObligationAddressInvariant)
    (hobstruction : state.HasUnwitnessed ∨ state.HasUndischarged ontology) :
    ∃ children, ExhaustiveStep ontology state children := by
  apply obstruction_has_exhaustive_step ontology state hheads _ hobstruction
  exact state.exists_fresh_of_unwitnessed_of_obligationAddressInvariant hinvariant

/-- Finite successor choice together with role-sensitive blocking yields a
finite node universe, not only finite individual predecessor paths. -/
theorem role_blocked_node_universe_finite
    (Slot Concept Role : Type)
    [Fintype Slot]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role] :
    Set.Finite (Set.univ : Set (RoleBlockedAddress Slot Concept Role)) := by
  exact Set.toFinite _

/-- Runtime mode 6 assigns children strictly increasing node identifiers and
never expands a node if an earlier node has the same full pairwise signature.
Under exactly those two refinement invariants, no path consisting entirely of
expanded nodes can exceed the finite signature vocabulary. -/
theorem State.no_overlong_mode6_expansion
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Nat Concept Role) (parent : Nat → Option Nat)
    (expanded : Nat → Prop)
    (hsafe : ∀ {blocker blocked}, blocker < blocked → expanded blocked →
      state.roleBlockingSignature parent blocker ≠
        state.roleBlockingSignature parent blocked)
    (path : Fin (Fintype.card (RoleBlockingSignature Concept Role) + 1) → Nat)
    (hcreation : StrictMono path)
    (hexpanded : ∀ position, expanded (path position)) : False := by
  obtain ⟨earlier, later, hposition, hsignature⟩ :=
    state.exists_role_blocker_on_long_path parent path
  exact hsafe (hcreation hposition) (hexpanded later) hsignature

#print axioms State.roleBlockingSignature_blocks
#print axioms State.roleBlockingSignature_parent_context
#print axioms State.exists_role_blocker_on_long_path
#print axioms role_blocked_node_universe_finite
#print axioms State.fresh_extended_roleBlockedAddress
#print axioms State.fresh_extended_rootedRoleBlockedAddress
#print axioms State.exists_fresh_of_unwitnessed_of_obligationAddressInvariant
#print axioms State.obstruction_has_addressed_exhaustive_step
#print axioms State.no_overlong_mode6_expansion

end ContextCalculus.Hypertableau
