/-!
# Positive source fragments with an empty public taxonomy

This module states the semantic contract implemented by KM's one-pass source
recognizer. A TBox axiom has a named class on the left and a positive leaf on
the right. A leaf is an existential, or an intersection made only of leaves;
its fillers may contain arbitrary nested positive expressions. The ABox
contains only positive class assertions.

For two distinct public classes, a two-point interpretation separates them at
the query point and makes every class true at a witness point. Every role is
universal. The witness point realizes every positive expression, while every
leaf is true even at the query point. This simultaneously supplies a model of
the complete source and a countermodel to every proper named subsumption.
-/

namespace ContextCalculus.PositiveEmptySource

inductive Expr (Concept Role : Type)
  | named : Concept → Expr Concept Role
  | some : Role → Expr Concept Role → Expr Concept Role
  | inter : Expr Concept Role → Expr Concept Role → Expr Concept Role

def Expr.eval (concept : Concept → Domain → Prop)
    (role : Role → Domain → Domain → Prop) : Expr Concept Role → Domain → Prop
  | .named name, value => concept name value
  | .some name filler, value =>
      ∃ witness, role name value witness ∧ filler.eval concept role witness
  | .inter left right, value =>
      left.eval concept role value ∧ right.eval concept role value

/-- Expressions admitted at the top level of a subclass conclusion. Named
conjuncts may occur only below an existential. -/
def Leaf : Expr Concept Role → Prop
  | .named _ => False
  | .some _ _ => True
  | .inter left right => Leaf left ∧ Leaf right

def ModelsTBox (concept : Concept → Domain → Prop)
    (role : Role → Domain → Domain → Prop)
    (tbox : List (Concept × Expr Concept Role)) : Prop :=
  ∀ pair ∈ tbox, ∀ value,
    concept pair.1 value → pair.2.eval concept role value

def ModelsABox (concept : Concept → Domain → Prop)
    (role : Role → Domain → Domain → Prop)
    (abox : List (Expr Concept Role)) : Prop :=
  ∀ assertion ∈ abox, ∃ value, assertion.eval concept role value

def LeafTBox (tbox : List (Concept × Expr Concept Role)) : Prop :=
  ∀ pair ∈ tbox, Leaf pair.2

def EntailsSubWith (tbox : List (Concept × Expr Concept Role))
    (abox : List (Expr Concept Role)) (source target : Concept) : Prop :=
  ∀ (Domain : Type) [Nonempty Domain]
      (concept : Concept → Domain → Prop)
      (role : Role → Domain → Domain → Prop),
    ModelsTBox concept role tbox → ModelsABox concept role abox →
      ∀ value, concept source value → concept target value

private def separatingConcept [DecidableEq Concept]
    (target : Concept) (name : Concept) (value : Bool) : Prop :=
  value = true ∨ name ≠ target

private def universalRole (_ : Role) (_ _ : Bool) : Prop := True

private def fullConcept (_ : Concept) (_ : Unit) : Prop := True

private def fullRole (_ : Role) (_ _ : Unit) : Prop := True

private theorem unit_realizes_every_expression
    (expr : Expr Concept Role) : expr.eval fullConcept fullRole () := by
  induction expr with
  | named name => trivial
  | some role filler ih => exact ⟨(), trivial, ih⟩
  | inter left right left_ih right_ih => exact ⟨left_ih, right_ih⟩

private theorem witness_realizes_every_expression [DecidableEq Concept]
    (target : Concept) (expr : Expr Concept Role) :
    expr.eval (separatingConcept target) universalRole true := by
  induction expr with
  | named name => exact Or.inl rfl
  | some role filler ih => exact ⟨true, trivial, ih⟩
  | inter left right left_ih right_ih => exact ⟨left_ih, right_ih⟩

private theorem leaf_holds_everywhere [DecidableEq Concept]
    (target : Concept) {expr : Expr Concept Role} (leaf : Leaf expr)
    (value : Bool) :
    expr.eval (separatingConcept target) universalRole value := by
  induction expr with
  | named name => simp [Leaf] at leaf
  | some role filler filler_ih =>
      exact ⟨true, trivial, witness_realizes_every_expression target filler⟩
  | inter left right left_ih right_ih =>
      exact ⟨left_ih leaf.1, right_ih leaf.2⟩

private theorem separating_models_tbox [DecidableEq Concept]
    (target : Concept) {tbox : List (Concept × Expr Concept Role)}
    (leaf_tbox : LeafTBox tbox) :
    ModelsTBox (separatingConcept target) universalRole tbox := by
  intro pair member value _
  exact leaf_holds_everywhere target (leaf_tbox pair member) value

private theorem separating_models_abox [DecidableEq Concept]
    (target : Concept) (abox : List (Expr Concept Role)) :
    ModelsABox (separatingConcept target) universalRole abox := by
  intro assertion member
  exact ⟨true, witness_realizes_every_expression target assertion⟩

/-- The accepted positive source has exactly the reflexive public taxonomy,
even after all accepted positive class assertions are included. -/
theorem entailsSubWith_iff_eq [DecidableEq Concept]
    {tbox : List (Concept × Expr Concept Role)} (leaf_tbox : LeafTBox tbox)
    (abox : List (Expr Concept Role)) (source target : Concept) :
    EntailsSubWith tbox abox source target ↔ source = target := by
  constructor
  · intro entails
    by_cases equality : source = target
    · exact equality
    have separated := entails Bool (separatingConcept target) universalRole
      (separating_models_tbox target leaf_tbox)
      (separating_models_abox target abox) false
      (Or.inr equality)
    simp [separatingConcept] at separated
  · intro equality
    subst target
    intro Domain _ concept role tbox_model abox_model value source_holds
    exact source_holds

/-- Every accepted positive source is satisfiable. -/
theorem has_model
    (tbox : List (Concept × Expr Concept Role))
    (abox : List (Expr Concept Role)) :
    ∃ (Domain : Type) (_ : Nonempty Domain)
        (concept : Concept → Domain → Prop)
        (role : Role → Domain → Domain → Prop),
      ModelsTBox concept role tbox ∧ ModelsABox concept role abox := by
  refine ⟨Unit, inferInstance, fullConcept, fullRole, ?_, ?_⟩
  · intro pair member value _
    exact unit_realizes_every_expression pair.2
  · intro assertion member
    exact ⟨(), unit_realizes_every_expression assertion⟩

#print axioms entailsSubWith_iff_eq
#print axioms has_model

end ContextCalculus.PositiveEmptySource
