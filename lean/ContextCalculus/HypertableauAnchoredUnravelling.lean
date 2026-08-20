import ContextCalculus.Hypertableau

/-!
# Canonical roots for nominal-aware regular unravellings

Ordinary path unravelling creates a fresh domain value for every path. That is
correct for anonymous blocked witnesses, but it is not correct for nominals:
all paths reaching one nominal representative must denote one domain value.

This module defines the rooted-forest domain used by the equality-aware regular
model. Anonymous endpoints retain their full path identity. A designated anchor
endpoint is represented only by its canonical root. The central theorem
`AnchoredForestDomain.eq_root_of_anchor` states the singleton invariant without
assuming decidable equality of paths or quotienting proof terms.
-/

namespace ContextCalculus.Hypertableau

universe u v w

variable {Node : Type u} {Concept : Type v} {Role : Type w}

/-- A forest path may start at any finite root. Successor steps still read
outgoing edges from the redirected finite endpoint. -/
inductive ForestPath
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) : Node → Type (max u w) where
  | root (node : Node) : ForestPath state redirect slotAllowed node
  | step {source target : Node}
      (parent : ForestPath state redirect slotAllowed source)
      (slot : Nat) (role : Role)
      (edge : state.edge role (redirect source) target)
      (allowed : slotAllowed source role target slot) :
      ForestPath state redirect slotAllowed target

abbrev ForestDomain
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) :=
  Σ endpoint, ForestPath state redirect slotAllowed endpoint

/-- Canonical values retain arbitrary paths only for anonymous endpoints.
Every anchored endpoint must carry the root path. -/
def AnchoredForestDomain
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop) :=
  { value : ForestDomain state redirect slotAllowed //
      anchor value.1 → value.2 = ForestPath.root value.1 }

namespace AnchoredForestDomain

def endpoint
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {anchor : Node → Prop}
    (value : AnchoredForestDomain state redirect slotAllowed anchor) : Node :=
  value.1.1

def root
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    (node : Node) : AnchoredForestDomain state redirect slotAllowed anchor :=
  ⟨⟨node, ForestPath.root node⟩, fun _ => rfl⟩

/-- Every value whose endpoint is anchored is the unique canonical root for
that endpoint. This is the semantic singleton property required for nominals. -/
theorem eq_root_of_anchor
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {anchor : Node → Prop}
    (value : AnchoredForestDomain state redirect slotAllowed anchor)
    (hanchor : anchor value.endpoint) :
    value = root state redirect slotAllowed anchor value.endpoint := by
  rcases value with ⟨⟨endpoint, path⟩, canonical⟩
  have hpath : path = ForestPath.root endpoint := canonical hanchor
  subst path
  rfl

theorem eq_of_same_anchored_endpoint
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {anchor : Node → Prop}
    (left right : AnchoredForestDomain state redirect slotAllowed anchor)
    (hleft : anchor left.endpoint) (hendpoint : left.endpoint = right.endpoint) :
    left = right := by
  calc
    left = root state redirect slotAllowed anchor left.endpoint :=
      left.eq_root_of_anchor hleft
    _ = root state redirect slotAllowed anchor right.endpoint := by rw [hendpoint]
    _ = right := (right.eq_root_of_anchor (hendpoint ▸ hleft)).symm

/-- Extend an anonymous path normally, but redirect every edge into an anchor
to that anchor's canonical root. -/
def successor
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor]
    (source : AnchoredForestDomain state redirect slotAllowed anchor)
    (slot : Nat) (role : Role) (target : Node)
    (edge : state.edge role (redirect source.endpoint) target)
    (allowed : slotAllowed source.endpoint role target slot) :
    AnchoredForestDomain state redirect slotAllowed anchor :=
  if hanchor : anchor target then
    root state redirect slotAllowed anchor target
  else
    ⟨⟨target, ForestPath.step source.1.2 slot role edge allowed⟩,
      fun h => (hanchor h).elim⟩

@[simp] theorem endpoint_root
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    (node : Node) :
    (root state redirect slotAllowed anchor node).endpoint = node := rfl

@[simp] theorem endpoint_successor
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor]
    (source : AnchoredForestDomain state redirect slotAllowed anchor)
    (slot : Nat) (role : Role) (target : Node)
    (edge : state.edge role (redirect source.endpoint) target)
    (allowed : slotAllowed source.endpoint role target slot) :
    (successor state redirect slotAllowed anchor source slot role target edge allowed).endpoint =
      target := by
  simp only [successor, endpoint]
  split <;> rfl

theorem successor_eq_root_of_anchor
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor]
    (source : AnchoredForestDomain state redirect slotAllowed anchor)
    (slot : Nat) (role : Role) (target : Node)
    (edge : state.edge role (redirect source.endpoint) target)
    (allowed : slotAllowed source.endpoint role target slot)
    (hanchor : anchor target) :
    successor state redirect slotAllowed anchor source slot role target edge allowed =
      root state redirect slotAllowed anchor target := by
  simp [successor, hanchor]

/-- Concept interpretation for the future nominal-aware regular model.
Ordinary concepts are read from endpoint labels. A concept selected as a
nominal denotes exactly its selected canonical root. -/
def concept
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    (nominalRoot : Concept → Option Node) (name : Concept)
    (value : AnchoredForestDomain state redirect slotAllowed anchor) : Prop :=
  match nominalRoot name with
  | none => state.label value.endpoint (.pos name)
  | some node => value = root state redirect slotAllowed anchor node

theorem concept_nominal_iff
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    (nominalRoot : Concept → Option Node) (name : Concept) (node : Node)
    (hnominal : nominalRoot name = some node)
    (value : AnchoredForestDomain state redirect slotAllowed anchor) :
    concept state redirect slotAllowed anchor nominalRoot name value ↔
      value = root state redirect slotAllowed anchor node := by
  simp [concept, hnominal]

/-- Every selected nominal concept has a singleton extension, witnessed by its
canonical root. -/
theorem concept_nominal_singleton
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    (nominalRoot : Concept → Option Node) (name : Concept) (node : Node)
    (hnominal : nominalRoot name = some node) :
    ∃ unique : AnchoredForestDomain state redirect slotAllowed anchor,
      ∀ value, concept state redirect slotAllowed anchor nominalRoot name value ↔
        value = unique := by
  exact ⟨root state redirect slotAllowed anchor node,
    fun value => concept_nominal_iff state redirect slotAllowed anchor
      nominalRoot name node hnominal value⟩

#print axioms eq_root_of_anchor
#print axioms eq_of_same_anchored_endpoint
#print axioms successor_eq_root_of_anchor
#print axioms concept_nominal_singleton

end AnchoredForestDomain

end ContextCalculus.Hypertableau
