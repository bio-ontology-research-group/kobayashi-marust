import ContextCalculus.Hypertableau

/-!
# Regular path unravelling for blocked hypertableau endpoints

A blocked completion graph is not itself the semantic model in expressive
description logics.  Its model is obtained by unravelling successor steps into
paths.  Reusing a finite graph node at a later path position creates a new
domain value, and a natural-number slot keeps distinct cardinality witnesses
separate even when they reuse the same finite node.

This module defines the path domain independently of a particular blocking
policy.  `redirect` chooses the finite node whose outgoing witness edges are
used at a path endpoint; a concrete pairwise blocker will later instantiate and
justify that map.  The first endpoint theorem proves that witness completion at
redirected nodes gives a genuine, distinct path witness.
-/

namespace ContextCalculus.Hypertableau

universe u v w

variable {Node : Type u} {Concept : Type v} {Role : Type w}

inductive UnravellingPath
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node) :
    Node → Type (max u w) where
  | root : UnravellingPath state redirect slotAllowed root root
  | step {source target : Node}
      (parent : UnravellingPath state redirect slotAllowed root source)
      (slot : Nat) (role : Role)
      (edge : state.edge role (redirect source) target)
      (allowed : slotAllowed source role target slot) :
      UnravellingPath state redirect slotAllowed root target

namespace UnravellingPath

def depth {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root endpoint : Node} :
    UnravellingPath state redirect slotAllowed root endpoint → Nat
  | .root => 0
  | .step parent _ _ _ _ => parent.depth + 1

def lastSlot {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root endpoint : Node} :
    UnravellingPath state redirect slotAllowed root endpoint → Option Nat
  | .root => none
  | .step _ slot _ _ _ => some slot

@[simp] theorem depth_root
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node) :
    (UnravellingPath.root :
      UnravellingPath state redirect slotAllowed root root).depth = 0 := rfl

@[simp] theorem depth_step
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root source target : Node}
    (parent : UnravellingPath state redirect slotAllowed root source)
    (slot : Nat) (role : Role) (edge : state.edge role (redirect source) target)
    (allowed : slotAllowed source role target slot) :
    (UnravellingPath.step parent slot role edge allowed).depth = parent.depth + 1 := rfl

end UnravellingPath

abbrev UnravellingDomain
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node) :=
  Σ endpoint, UnravellingPath state redirect slotAllowed root endpoint

def UnravellingDomain.depth
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root : Node}
    (value : UnravellingDomain state redirect slotAllowed root) : Nat :=
  value.2.depth

def UnravellingDomain.lastSlot
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root : Node}
    (value : UnravellingDomain state redirect slotAllowed root) : Option Nat :=
  value.2.lastSlot

inductive UnravellingDirectRole
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node) (role : Role) :
    UnravellingDomain state redirect slotAllowed root →
      UnravellingDomain state redirect slotAllowed root → Prop where
  | step {source target : Node}
      (parent : UnravellingPath state redirect slotAllowed root source)
      (slot : Nat) (edge : state.edge role (redirect source) target)
      (allowed : slotAllowed source role target slot) :
      UnravellingDirectRole state redirect slotAllowed root role
        ⟨source, parent⟩
        ⟨target, UnravellingPath.step parent slot role edge allowed⟩

def State.unravelling
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node) :
    Interp (UnravellingDomain state redirect slotAllowed root) Concept Role where
  concept concept value := state.label value.1 (.pos concept)
  role := UnravellingDirectRole state redirect slotAllowed root

theorem UnravellingDirectRole.target_depth
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root : Node}
    {role : Role}
    {source target : UnravellingDomain state redirect slotAllowed root}
    (hedge : UnravellingDirectRole state redirect slotAllowed root role source target) :
    target.depth = source.depth + 1 := by
  cases hedge
  rfl

theorem UnravellingDirectRole.ne
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root : Node}
    {role : Role}
    {source target : UnravellingDomain state redirect slotAllowed root}
    (hedge : UnravellingDirectRole state redirect slotAllowed root role source target) :
    target ≠ source := by
  intro hequal
  have hdepth := hedge.target_depth
  rw [hequal] at hdepth
  omega

theorem State.unravelling_sat_label
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (hclash : state.ClashFree)
    (value : UnravellingDomain state redirect slotAllowed root) (lit : Lit Concept)
    (hlabel : state.label value.1 lit) :
    (state.unravelling redirect slotAllowed root).satLit lit value := by
  rcases lit with ⟨concept, neg⟩
  cases neg with
  | false => exact hlabel
  | true =>
      intro hpositive
      exact hclash value.1 concept ⟨hpositive, hlabel⟩

/-- A redirected completion-graph witness becomes a genuinely new path-domain
value.  The finite target node may repeat; path depth still distinguishes the
semantic witness from its predecessor. -/
theorem State.unravelling_obligation_witness
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (hclash : state.ClashFree)
    (hwitness : state.WitnessComplete)
    (hobligationRedirect : ∀ node role filler,
      state.obligation role filler node →
        state.obligation role filler (redirect node))
    (source : UnravellingDomain state redirect slotAllowed root)
    (role : Role) (filler : Lit Concept)
    (hslot : ∀ target, state.edge role (redirect source.1) target →
      slotAllowed source.1 role target 0)
    (hobligation : state.obligation role filler source.1) :
    ∃ target,
      (state.unravelling redirect slotAllowed root).role role source target ∧
      (state.unravelling redirect slotAllowed root).satLit filler target ∧
      target ≠ source := by
  obtain ⟨targetNode, hedge, hlabel⟩ :=
    hwitness (redirect source.1) role filler
      (hobligationRedirect source.1 role filler hobligation)
  let target : UnravellingDomain state redirect slotAllowed root :=
    ⟨targetNode, UnravellingPath.step source.2 0 role hedge (hslot targetNode hedge)⟩
  have hrole : (state.unravelling redirect slotAllowed root).role
      role source target := by
    exact UnravellingDirectRole.step source.2 0 hedge (hslot targetNode hedge)
  exact ⟨target, hrole,
    state.unravelling_sat_label redirect slotAllowed root hclash target filler hlabel,
    hrole.ne⟩

/-- Distinct witness slots denote distinct path-domain values, even if their
finite completion-graph targets coincide. -/
theorem State.unravelling_minimum_witnesses
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (hclash : state.ClashFree)
    (source : UnravellingDomain state redirect slotAllowed root)
    (role : Role) (filler : Lit Concept) (count : Nat)
    (witness : Fin count → Node)
    (hedge : ∀ index,
      state.edge role (redirect source.1) (witness index))
    (hslot : ∀ index,
      slotAllowed source.1 role (witness index) index.1)
    (hlabel : ∀ index, state.label (witness index) filler) :
    ∃ target : Fin count → UnravellingDomain state redirect slotAllowed root,
      Function.Injective target ∧
      ∀ index,
        (state.unravelling redirect slotAllowed root).role role source (target index) ∧
        (state.unravelling redirect slotAllowed root).satLit filler (target index) := by
  let target (index : Fin count) :
      UnravellingDomain state redirect slotAllowed root :=
    ⟨witness index,
      UnravellingPath.step source.2 index.1 role (hedge index) (hslot index)⟩
  refine ⟨target, ?_, ?_⟩
  · intro left right hequal
    have hslot := congrArg UnravellingDomain.lastSlot hequal
    simp [target, UnravellingDomain.lastSlot, UnravellingPath.lastSlot] at hslot
    exact Fin.ext hslot
  · intro index
    refine ⟨?_, state.unravelling_sat_label redirect slotAllowed root hclash
      (target index) filler (hlabel index)⟩
    exact UnravellingDirectRole.step source.2 index.1 (hedge index) (hslot index)

abbrev UnravellingDirectSuccessor
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (source : UnravellingDomain state redirect slotAllowed root) (role : Role) :=
  {target // UnravellingDirectRole state redirect slotAllowed root role source target}

def UnravellingDirectSuccessor.key
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root : Node}
    {source : UnravellingDomain state redirect slotAllowed root} {role : Role}
    (successor : UnravellingDirectSuccessor
      state redirect slotAllowed root source role) : Node × Nat := by
  exact (successor.1.1, successor.1.lastSlot.getD 0)

/-- Direct semantic successors inject into their authorized finite
`(target-node, slot)` keys. Consequently an at-most checker only needs to bound
that finite key set; unravelling itself introduces no additional direct
successors. -/
theorem UnravellingDirectSuccessor.key_injective
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root : Node}
    {source : UnravellingDomain state redirect slotAllowed root} {role : Role} :
    Function.Injective
      (UnravellingDirectSuccessor.key (Node := Node)
        (Concept := Concept) (Role := Role) :
        UnravellingDirectSuccessor state redirect slotAllowed root source role →
          Node × Nat) := by
  rintro ⟨left, hleft⟩ ⟨right, hright⟩ hkey
  cases hleft
  cases hright
  simp only [UnravellingDirectSuccessor.key, UnravellingDomain.lastSlot,
    UnravellingPath.lastSlot, Option.getD_some, Prod.mk.injEq] at hkey
  rcases hkey with ⟨rfl, rfl⟩
  rfl

#print axioms UnravellingDirectRole.target_depth
#print axioms UnravellingDirectRole.ne
#print axioms State.unravelling_sat_label
#print axioms State.unravelling_obligation_witness
#print axioms State.unravelling_minimum_witnesses
#print axioms UnravellingDirectSuccessor.key_injective

end ContextCalculus.Hypertableau
