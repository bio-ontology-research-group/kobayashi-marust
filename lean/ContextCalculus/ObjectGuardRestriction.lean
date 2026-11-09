import Mathlib.Tactic

/-! Object guard for the native bridge (`engine/src/frontend/object_guard.rs`,
docs/NOMINALS-CB.md, "Object guard for the native bridge").

The rewrite adds a fresh class `G` to the left side of class inclusions and
asserts `A ⊑ G` for every named class, `G(a)` for every individual, and
`⊤ ⊑ ∀r.G` for every object role (an inverse role is the forward role read
backwards, so its edges also end in `G` by the domain axiom `∃r.⊤ ⊑ G`).

This module proves the semantic core: restricting a model of the rewritten
ontology to `G` gives a model of the original ontology with the same truth
values at `G` elements, and every model of the original ontology is a model of
the rewritten one with `G := ⊤`.

Roles are role symbols (an inverse is its own symbol whose edges the model
fixes); the restriction only needs every edge to end in `G`. Data restrictions
are atoms `data d` read from the element's own data edges, which the object
restriction does not change (two-sorted semantics: data values are not
objects). Nominals denote individuals, which the rewrite puts into `G`. -/
namespace ContextCalculus.ObjectGuardRestriction

inductive Concept (Class Role Data Ind : Type) where
  | top | bottom
  | atom (name : Class)
  | data (restriction : Data)
  | nominal (individual : Ind)
  | neg (inner : Concept Class Role Data Ind)
  | and (left right : Concept Class Role Data Ind)
  | or (left right : Concept Class Role Data Ind)
  | some (role : Role) (filler : Concept Class Role Data Ind)
  | all (role : Role) (filler : Concept Class Role Data Ind)
  | min (n : Nat) (role : Role) (filler : Concept Class Role Data Ind)
  | max (n : Nat) (role : Role) (filler : Concept Class Role Data Ind)

structure Model (Class Role Data Ind Object : Type) where
  concept : Class → Object → Prop
  role : Role → Object → Object → Prop
  data : Data → Object → Prop
  ind : Ind → Object

def count {Object : Type} (predicate : Object → Prop) (n : Nat) : Prop :=
  ∃ witnesses : Fin n → Object, Function.Injective witnesses ∧ ∀ i, predicate (witnesses i)

def holds {Class Role Data Ind Object : Type} (model : Model Class Role Data Ind Object)
    : Concept Class Role Data Ind → Object → Prop
  | .top, _ => True
  | .bottom, _ => False
  | .atom name, x => model.concept name x
  | .data restriction, x => model.data restriction x
  | .nominal individual, x => x = model.ind individual
  | .neg inner, x => ¬holds model inner x
  | .and left right, x => holds model left x ∧ holds model right x
  | .or left right, x => holds model left x ∨ holds model right x
  | .some role filler, x => ∃ y, model.role role x y ∧ holds model filler y
  | .all role filler, x => ∀ y, model.role role x y → holds model filler y
  | .min n role filler, x => count (fun y => model.role role x y ∧ holds model filler y) n
  | .max n role filler, x => ¬count (fun y => model.role role x y ∧ holds model filler y) (n + 1)

/-- The hypotheses the guard axioms establish in a model of the rewritten
ontology: every role edge ends in `G`, every individual is in `G`. -/
structure Guarded {Class Role Data Ind Object : Type}
    (model : Model Class Role Data Ind Object) (G : Object → Prop) : Prop where
  edge_target : ∀ role x y, model.role role x y → G y
  individual : ∀ individual, G (model.ind individual)

/-- The model restricted to the guard. -/
def restrict {Class Role Data Ind Object : Type} (model : Model Class Role Data Ind Object)
    (G : Object → Prop) (guarded : Guarded model G) :
    Model Class Role Data Ind {x // G x} where
  concept := fun name x => model.concept name x.val
  role := fun role x y => model.role role x.val y.val
  data := fun restriction x => model.data restriction x.val
  ind := fun individual => ⟨model.ind individual, guarded.individual individual⟩

theorem count_transport {Object Target : Type} (embed : Object → Target)
    (injective : Function.Injective embed) (predicate : Object → Prop)
    (targetPredicate : Target → Prop)
    (preserved : ∀ x, targetPredicate (embed x) ↔ predicate x)
    (supported : ∀ y, targetPredicate y → ∃ x, embed x = y) (n : Nat) :
    count targetPredicate n ↔ count predicate n := by
  classical
  constructor
  · rintro ⟨witnesses, distinct, matched⟩
    have supportedWitness : ∀ i, ∃ x, embed x = witnesses i := fun i => supported _ (matched i)
    let oldWitness := fun i => Classical.choose (supportedWitness i)
    have mapped : ∀ i, embed (oldWitness i) = witnesses i :=
      fun i => Classical.choose_spec (supportedWitness i)
    refine ⟨oldWitness, ?_, ?_⟩
    · intro i j equal
      apply distinct
      rw [←mapped i, ←mapped j, equal]
    · intro i
      apply (preserved (oldWitness i)).mp
      rw [mapped i]
      exact matched i
  · rintro ⟨witnesses, distinct, matched⟩
    exact ⟨embed ∘ witnesses, injective.comp distinct, fun i => (preserved _).mpr (matched i)⟩

/-- Every concept has the same truth value at a `G` element before and after
the restriction. -/
theorem restrict_holds {Class Role Data Ind Object : Type}
    (model : Model Class Role Data Ind Object) (G : Object → Prop) (guarded : Guarded model G)
    (concept : Concept Class Role Data Ind) (x : {x // G x}) :
    holds (restrict model G guarded) concept x ↔ holds model concept x.val := by
  induction concept generalizing x with
  | top | bottom | atom | data => rfl
  | nominal individual =>
    show x = ⟨model.ind individual, _⟩ ↔ x.val = model.ind individual
    exact Subtype.ext_iff
  | neg inner ih => exact not_congr (ih x)
  | and left right ihLeft ihRight => exact and_congr (ihLeft x) (ihRight x)
  | or left right ihLeft ihRight => exact or_congr (ihLeft x) (ihRight x)
  | some role filler ih =>
    constructor
    · rintro ⟨y, edge, matched⟩
      exact ⟨y.val, edge, (ih y).mp matched⟩
    · rintro ⟨y, edge, matched⟩
      exact ⟨⟨y, guarded.edge_target role _ _ edge⟩, edge, (ih _).mpr matched⟩
  | all role filler ih =>
    constructor
    · intro matched y edge
      exact (ih ⟨y, guarded.edge_target role _ _ edge⟩).mp (matched _ edge)
    · intro matched y edge
      exact (ih y).mpr (matched y.val edge)
  | min n role filler ih =>
    exact (count_transport Subtype.val Subtype.val_injective
      (fun y => (restrict model G guarded).role role x y ∧ holds (restrict model G guarded) filler y)
      (fun y => model.role role x.val y ∧ holds model filler y)
      (fun y => and_congr Iff.rfl (ih y).symm)
      (fun y matched => ⟨⟨y, guarded.edge_target role _ _ matched.1⟩, rfl⟩) n).symm
  | max n role filler ih =>
    exact not_congr (count_transport Subtype.val Subtype.val_injective
      (fun y => (restrict model G guarded).role role x y ∧ holds (restrict model G guarded) filler y)
      (fun y => model.role role x.val y ∧ holds model filler y)
      (fun y => and_congr Iff.rfl (ih y).symm)
      (fun y matched => ⟨⟨y, guarded.edge_target role _ _ matched.1⟩, rfl⟩) (n + 1)).symm

/-- A guarded inclusion `G ⊓ C ⊑ D` of the rewritten ontology gives the
original `C ⊑ D` in the restriction. -/
theorem guarded_inclusion_restricted {Class Role Data Ind Object : Type}
    (model : Model Class Role Data Ind Object) (G : Object → Prop) (guarded : Guarded model G)
    (left right : Concept Class Role Data Ind)
    (valid : ∀ x, G x → holds model left x → holds model right x) :
    ∀ x, holds (restrict model G guarded) left x → holds (restrict model G guarded) right x := by
  intro x matched
  exact (restrict_holds model G guarded right x).mpr
    (valid x.val x.property ((restrict_holds model G guarded left x).mp matched))

/-- An unguarded inclusion holds in the restriction as well. -/
theorem inclusion_restricted {Class Role Data Ind Object : Type}
    (model : Model Class Role Data Ind Object) (G : Object → Prop) (guarded : Guarded model G)
    (left right : Concept Class Role Data Ind)
    (valid : ∀ x, holds model left x → holds model right x) :
    ∀ x, holds (restrict model G guarded) left x → holds (restrict model G guarded) right x :=
  guarded_inclusion_restricted model G guarded left right (fun x _ => valid x)

/-- A class assertion `C(a)`, or its nominal form `{a} ⊑ C`, carries over. -/
theorem assertion_restricted {Class Role Data Ind Object : Type}
    (model : Model Class Role Data Ind Object) (G : Object → Prop) (guarded : Guarded model G)
    (concept : Concept Class Role Data Ind) (individual : Ind)
    (valid : holds model concept (model.ind individual)) :
    holds (restrict model G guarded) concept ((restrict model G guarded).ind individual) :=
  (restrict_holds model G guarded concept _).mpr valid

/-- A role assertion carries over. -/
theorem role_assertion_restricted {Class Role Data Ind Object : Type}
    (model : Model Class Role Data Ind Object) (G : Object → Prop) (guarded : Guarded model G)
    (role : Role) (a b : Ind) (valid : model.role role (model.ind a) (model.ind b)) :
    (restrict model G guarded).role role ((restrict model G guarded).ind a)
      ((restrict model G guarded).ind b) :=
  valid

/-- Role axioms that are universal Horn conditions on edges (inclusion,
transitivity, functionality) carry over, since the restriction keeps exactly
the edges between `G` elements. -/
theorem functionality_restricted {Class Role Data Ind Object : Type}
    (model : Model Class Role Data Ind Object) (G : Object → Prop) (guarded : Guarded model G)
    (role : Role) (valid : ∀ x y z, model.role role x y → model.role role x z → y = z) :
    ∀ x y z, (restrict model G guarded).role role x y → (restrict model G guarded).role role x z →
      y = z := by
  intro x y z first second
  exact Subtype.ext (valid _ _ _ first second)

theorem role_inclusion_restricted {Class Role Data Ind Object : Type}
    (model : Model Class Role Data Ind Object) (G : Object → Prop) (guarded : Guarded model G)
    (left right : Role) (valid : ∀ x y, model.role left x y → model.role right x y) :
    ∀ x y, (restrict model G guarded).role left x y → (restrict model G guarded).role right x y :=
  fun x y edge => valid x.val y.val edge

theorem transitivity_restricted {Class Role Data Ind Object : Type}
    (model : Model Class Role Data Ind Object) (G : Object → Prop) (guarded : Guarded model G)
    (role : Role) (valid : ∀ x y z, model.role role x y → model.role role y z → model.role role x z) :
    ∀ x y z, (restrict model G guarded).role role x y → (restrict model G guarded).role role y z →
      (restrict model G guarded).role role x z :=
  fun x y z first second => valid x.val y.val z.val first second

/-- A witness of a named class `A` with `A ⊑ G` survives the restriction:
satisfiability of a source concept at a `G` element is preserved, so the
rewritten ontology and the original agree on unsatisfiable classes and on
subsumptions (a refutation witness of `A ⊓ ¬B` is an `A` element). -/
theorem witness_restricted {Class Role Data Ind Object : Type}
    (model : Model Class Role Data Ind Object) (G : Object → Prop) (guarded : Guarded model G)
    (concept : Concept Class Role Data Ind) (x : Object) (inGuard : G x)
    (matched : holds model concept x) :
    ∃ y, holds (restrict model G guarded) concept y :=
  ⟨⟨x, inGuard⟩, (restrict_holds model G guarded concept ⟨x, inGuard⟩).mpr matched⟩

/-- The other direction: with `G := ⊤` every original inclusion gives its
guarded form, and every guard axiom holds. -/
theorem original_model_is_guarded {Class Role Data Ind Object : Type}
    (model : Model Class Role Data Ind Object) :
    Guarded model (fun _ => True) :=
  ⟨fun _ _ _ _ => trivial, fun _ => trivial⟩

end ContextCalculus.ObjectGuardRestriction
