/-!
# Inactive Horn deltas preserve query closures

This proves the abstract dependency argument used by experimental incremental
activation. It does not establish OWL source lowering or the Rust bit matrix.
A caller must supply a bound closed under both rule sets and show that changed
rules cannot fire inside that bound. A distinguished atom can represent a clash.
-/
namespace ContextCalculus.IncrementalHornActivation

structure Rule where
  body : List Nat
  head : Nat
  deriving DecidableEq

inductive Derives (rules : List Rule) (seed : Nat → Prop) : Nat → Prop where
  | initial {atom} : seed atom → Derives rules seed atom
  | fire (rule : Rule) : rule ∈ rules →
      (∀ atom, atom ∈ rule.body → Derives rules seed atom) →
      Derives rules seed rule.head

/-- The abstraction bounds every finite Horn derivation. -/
theorem derives_bounded {rules : List Rule} {seed bound : Nat → Prop}
    (initial : ∀ atom, seed atom → bound atom)
    (closed : ∀ rule, rule ∈ rules →
      (∀ atom, atom ∈ rule.body → bound atom) → bound rule.head)
    {atom : Nat} (proof : Derives rules seed atom) : bound atom := by
  induction proof with
  | initial h => exact initial _ h
  | fire rule member _ ih => exact closed rule member ih

/-- Removing inactive rules preserves every existing derivation. -/
theorem transfer_inactive_removed {old newer : List Rule} {seed bound : Nat → Prop}
    (initial : ∀ atom, seed atom → bound atom)
    (closed : ∀ rule, rule ∈ old →
      (∀ atom, atom ∈ rule.body → bound atom) → bound rule.head)
    (inactive : ∀ rule, rule ∈ old → rule ∉ newer →
      ¬ (∀ atom, atom ∈ rule.body → bound atom))
    {atom : Nat} (proof : Derives old seed atom) : Derives newer seed atom := by
  classical
  induction proof with
  | initial h => exact Derives.initial h
  | fire rule member premises ih =>
    by_cases kept : rule ∈ newer
    · exact Derives.fire rule kept ih
    · exact False.elim (inactive rule member kept
        (fun atom inBody => derives_bounded initial closed (premises atom inBody)))

/-- A shared closed bound and inactive symmetric difference preserve every
consequence, including a designated clash atom. -/
theorem inactive_delta_preserves_closure
    {old newer : List Rule} {seed bound : Nat → Prop}
    (initial : ∀ atom, seed atom → bound atom)
    (closed : ∀ rule, rule ∈ old ∨ rule ∈ newer →
      (∀ atom, atom ∈ rule.body → bound atom) → bound rule.head)
    (removed : ∀ rule, rule ∈ old → rule ∉ newer →
      ¬ (∀ atom, atom ∈ rule.body → bound atom))
    (added : ∀ rule, rule ∈ newer → rule ∉ old →
      ¬ (∀ atom, atom ∈ rule.body → bound atom))
    (atom : Nat) : Derives old seed atom ↔ Derives newer seed atom := by
  constructor
  · exact transfer_inactive_removed initial
      (fun rule member => closed rule (Or.inl member)) removed
  · exact transfer_inactive_removed initial
      (fun rule member => closed rule (Or.inr member)) added

/-- Positive Horn consequence in every model of the seeds and rules. -/
def Entails (rules : List Rule) (seed : Nat → Prop) (atom : Nat) : Prop :=
  ∀ model : Nat → Prop,
    (∀ fact, seed fact → model fact) →
    (∀ rule, rule ∈ rules →
      (∀ premise, premise ∈ rule.body → model premise) → model rule.head) →
    model atom

/-- The derivable facts themselves form the least Horn model. -/
theorem entails_iff_derives {rules : List Rule} {seed : Nat → Prop} {atom : Nat} :
    Entails rules seed atom ↔ Derives rules seed atom := by
  constructor
  · intro entails
    exact entails (Derives rules seed)
      (fun _ h => Derives.initial h)
      (fun rule member premises => Derives.fire rule member premises)
  · intro proof model initial closed
    exact derives_bounded initial closed proof

theorem inactive_delta_preserves_entailment
    {old newer : List Rule} {seed bound : Nat → Prop}
    (initial : ∀ atom, seed atom → bound atom)
    (closed : ∀ rule, rule ∈ old ∨ rule ∈ newer →
      (∀ atom, atom ∈ rule.body → bound atom) → bound rule.head)
    (removed : ∀ rule, rule ∈ old → rule ∉ newer →
      ¬ (∀ atom, atom ∈ rule.body → bound atom))
    (added : ∀ rule, rule ∈ newer → rule ∉ old →
      ¬ (∀ atom, atom ∈ rule.body → bound atom))
    (atom : Nat) : Entails old seed atom ↔ Entails newer seed atom := by
  rw [entails_iff_derives, entails_iff_derives]
  exact inactive_delta_preserves_closure initial closed removed added atom

#print axioms derives_bounded
#print axioms transfer_inactive_removed
#print axioms inactive_delta_preserves_closure
#print axioms entails_iff_derives
#print axioms inactive_delta_preserves_entailment

end ContextCalculus.IncrementalHornActivation
