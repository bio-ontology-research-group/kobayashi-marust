import ContextCalculus.HypertableauTerminal
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

#print axioms State.roleBlockingSignature_blocks
#print axioms State.roleBlockingSignature_parent_context
#print axioms State.exists_role_blocker_on_long_path

end ContextCalculus.Hypertableau
