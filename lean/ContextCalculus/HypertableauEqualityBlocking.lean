import ContextCalculus.HypertableauEqualityModel
import ContextCalculus.HypertableauRoleBlocking

/-!
# Finite equality-quotient blocking signatures

Equality-aware search must compare branch facts modulo the complete node
equivalence relation. This module defines the corresponding signed pairwise
signature and proves its finite repetition and path-depth bounds. These are the
combinatorial termination bounds needed by a concrete quotient-aware blocker;
the sound fold refinement remains a separate obligation.
-/

namespace ContextCalculus.Hypertableau

noncomputable def EqState.closedLabelSet
    [Fintype Concept] [DecidableEq Concept]
    (state : EqState Node Concept Role) (node : Node) : Finset (Lit Concept) := by
  classical
  exact Finset.univ.filter fun literal => state.closedLabel node literal

@[simp] theorem EqState.mem_closedLabelSet
    [Fintype Concept] [DecidableEq Concept]
    (state : EqState Node Concept Role) (node : Node) (lit : Lit Concept) :
    lit ∈ state.closedLabelSet node ↔ state.closedLabel node lit := by
  classical
  simp [EqState.closedLabelSet]

noncomputable def EqState.closedForwardParentRoles
    [Fintype Role] [DecidableEq Role]
    (state : EqState Node Concept Role) (parent node : Node) : Finset Role := by
  classical
  exact Finset.univ.filter fun role => state.closedEdge role parent node

noncomputable def EqState.closedBackwardParentRoles
    [Fintype Role] [DecidableEq Role]
    (state : EqState Node Concept Role) (parent node : Node) : Finset Role := by
  classical
  exact Finset.univ.filter fun role => state.closedEdge role node parent

/-- Full pairwise blocking signature read on equality classes. Roots use
`none`; non-roots retain the closed labels of both positions and every closed
role in both predecessor directions. -/
noncomputable def EqState.quotientRoleBlockingSignature
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : EqState Node Concept Role) (parent : Node → Option Node) (node : Node) :
    RoleBlockingSignature Concept Role :=
  (state.closedLabelSet node, parent node |>.map fun predecessor =>
    (state.closedLabelSet predecessor,
      state.closedForwardParentRoles predecessor node,
      state.closedBackwardParentRoles predecessor node))

theorem EqState.quotientRoleBlockingSignature_label
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : EqState Node Concept Role) (parent : Node → Option Node)
    {left right : Node}
    (hequal : state.quotientRoleBlockingSignature parent left =
      state.quotientRoleBlockingSignature parent right) :
    state.closedLabelSet left = state.closedLabelSet right := by
  exact congrArg Prod.fst hequal

theorem EqState.quotientRoleBlockingSignature_parent_context
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : EqState Node Concept Role) (parent : Node → Option Node)
    {blocker blocked blockerParent blockedParent : Node}
    (hblockerParent : parent blocker = some blockerParent)
    (hblockedParent : parent blocked = some blockedParent)
    (hequal : state.quotientRoleBlockingSignature parent blocker =
      state.quotientRoleBlockingSignature parent blocked) :
    state.closedLabelSet blockerParent = state.closedLabelSet blockedParent ∧
      state.closedForwardParentRoles blockerParent blocker =
        state.closedForwardParentRoles blockedParent blocked ∧
      state.closedBackwardParentRoles blockerParent blocker =
        state.closedBackwardParentRoles blockedParent blocked := by
  have hsecond := congrArg Prod.snd hequal
  have hcontext :
      (state.closedLabelSet blockerParent,
        state.closedForwardParentRoles blockerParent blocker,
        state.closedBackwardParentRoles blockerParent blocker) =
      (state.closedLabelSet blockedParent,
        state.closedForwardParentRoles blockedParent blocked,
        state.closedBackwardParentRoles blockedParent blocked) := by
    simpa [EqState.quotientRoleBlockingSignature,
      hblockerParent, hblockedParent] using hsecond
  exact ⟨congrArg Prod.fst hcontext,
    congrArg (fun context => context.2.1) hcontext,
    congrArg (fun context => context.2.2) hcontext⟩

/-- Every equality-aware predecessor path longer than the finite quotient
signature vocabulary repeats a full signed pairwise signature. -/
theorem EqState.exists_quotient_role_blocker_on_long_path
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : EqState Node Concept Role) (parent : Node → Option Node)
    (path : Fin (Fintype.card (RoleBlockingSignature Concept Role) + 1) → Node) :
    ∃ earlier later, earlier < later ∧
      state.quotientRoleBlockingSignature parent (path earlier) =
        state.quotientRoleBlockingSignature parent (path later) := by
  classical
  let positions :
      Finset (Fin (Fintype.card (RoleBlockingSignature Concept Role) + 1)) :=
    Finset.univ
  let signatures : Finset (RoleBlockingSignature Concept Role) := Finset.univ
  have hcard : signatures.card < positions.card := by
    simp [positions, signatures]
  obtain ⟨left, _, right, _, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun position => state.quotientRoleBlockingSignature parent (path position))
      (fun _ _ => by simp [signatures])
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨left, right, hlt, heq⟩
  · exact ⟨right, left, hgt, heq.symm⟩

/-- Pairwise-distinct equality-quotient signatures bound predecessor depth by
the same finite signature type used for equality-free full pairwise blocking. -/
theorem EqState.quotientRoleBlockingDepth_lt_of_signature_injective
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : EqState Node Concept Role) (parent : Node → Option Node)
    (depth : Nat) (path : Fin (depth + 1) → Node)
    (hinjective : Function.Injective
      (fun position => state.quotientRoleBlockingSignature parent (path position))) :
    depth < Fintype.card (RoleBlockingSignature Concept Role) := by
  have hcard : Fintype.card (Fin (depth + 1)) ≤
      Fintype.card (RoleBlockingSignature Concept Role) :=
    Fintype.card_le_of_injective _ hinjective
  simpa using hcard

/-- A runtime that allocates children with increasing identifiers and refuses
to expand a node after an earlier equal quotient signature cannot contain an
overlong path of expanded equality-aware nodes. -/
theorem EqState.no_overlong_quotient_blocking_expansion
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : EqState Nat Concept Role) (parent : Nat → Option Nat)
    (expanded : Nat → Prop)
    (hsafe : ∀ {blocker blocked}, blocker < blocked → expanded blocked →
      state.quotientRoleBlockingSignature parent blocker ≠
        state.quotientRoleBlockingSignature parent blocked)
    (path : Fin (Fintype.card (RoleBlockingSignature Concept Role) + 1) → Nat)
    (hcreation : StrictMono path)
    (hexpanded : ∀ position, expanded (path position)) : False := by
  obtain ⟨earlier, later, hposition, hsignature⟩ :=
    state.exists_quotient_role_blocker_on_long_path parent path
  exact hsafe (hcreation hposition) (hexpanded later) hsignature

#print axioms EqState.quotientRoleBlockingSignature_label
#print axioms EqState.quotientRoleBlockingSignature_parent_context
#print axioms EqState.exists_quotient_role_blocker_on_long_path
#print axioms EqState.quotientRoleBlockingDepth_lt_of_signature_injective
#print axioms EqState.no_overlong_quotient_blocking_expansion

end ContextCalculus.Hypertableau
