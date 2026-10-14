import ContextCalculus.IsolatedObjectModelExtension

/-! Disjoint extension by isolated elements that all carry one fixed named
label. This generalizes `IsolatedObjectModelExtension.extend` (the empty
label). It justifies the native bridge's data successors: every data value is
represented by a completion node that the object axioms also constrain. If an
isolated element labelled `label` satisfies every inclusion (`shellWith`),
then every model of the source ontology extends to one in which the data
values also carry that label, so no named subsumption or satisfiability verdict
changes. The converse direction is immediate, because the represented theory
only adds constraints. -/
namespace ContextCalculus.LabelledIsolatedExtension

open ContextCalculus.IsolatedObjectModelExtension

def extendLabelled {Class Role Object Fresh : Type} (model : Model Class Role Object)
    (label : Class → Prop) : Model Class Role (Sum Object Fresh) where
  concept := fun name x => match x with | .inl old => model.concept name old | .inr _ => label name
  role := fun role x y => match x, y with
    | .inl old, .inl target => model.role role old target
    | _, _ => False

/-- Exact truth at an isolated element carrying `label`. -/
def shellWith {Class Role : Type} (label : Class → Prop) : Concept Class Role → Prop
  | .top => True
  | .bottom | .some _ _ | .self _ => False
  | .atom name => label name
  | .neg inner => ¬shellWith label inner
  | .and left right => shellWith label left ∧ shellWith label right
  | .or left right => shellWith label left ∨ shellWith label right
  | .all _ _ | .max _ _ _ => True
  | .min n _ _ => n = 0

theorem labelled_old_concepts_preserved {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (label : Class → Prop)
    (concept : Concept Class Role) (x : Object) :
    holds (extendLabelled (Fresh := Fresh) model label) concept (.inl x) ↔
      holds model concept x := by
  induction concept generalizing x with
  | top | bottom | atom | self => rfl
  | neg inner ih => exact not_congr (ih x)
  | and left right ihLeft ihRight => exact and_congr (ihLeft x) (ihRight x)
  | or left right ihLeft ihRight => exact or_congr (ihLeft x) (ihRight x)
  | some role filler ih =>
    constructor
    · rintro ⟨y, edge, matched⟩
      cases y with
      | inl old => exact ⟨old, edge, (ih old).mp matched⟩
      | inr fresh => exact False.elim edge
    · rintro ⟨y, edge, matched⟩
      exact ⟨.inl y, edge, (ih y).mpr matched⟩
  | all role filler ih =>
    constructor
    · intro matched y edge
      exact (ih y).mp (matched (.inl y) edge)
    · intro matched y edge
      cases y with
      | inl old => exact (ih old).mpr (matched old edge)
      | inr fresh => exact False.elim edge
  | min n role filler ih =>
    apply count_transport Sum.inl Sum.inl_injective
    · intro y
      exact and_congr Iff.rfl (ih y)
    · intro y edge
      cases y with
      | inl old => exact ⟨old, rfl⟩
      | inr fresh => exact False.elim edge.1
  | max n role filler ih =>
    apply not_congr
    apply count_transport Sum.inl Sum.inl_injective
    · intro y
      exact and_congr Iff.rfl (ih y)
    · intro y edge
      cases y with
      | inl old => exact ⟨old, rfl⟩
      | inr fresh => exact False.elim edge.1

theorem labelled_fresh_concepts_shell {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (label : Class → Prop)
    (concept : Concept Class Role) (fresh : Fresh) :
    holds (extendLabelled model label) concept (.inr fresh) ↔ shellWith label concept := by
  induction concept with
  | top | bottom | atom | self => rfl
  | neg inner ih => exact not_congr ih
  | and left right ihLeft ihRight => exact and_congr ihLeft ihRight
  | or left right ihLeft ihRight => exact or_congr ihLeft ihRight
  | some role filler _ => simp [holds, extendLabelled, shellWith]
  | all role filler _ => simp [holds, extendLabelled, shellWith]
  | min n role filler _ =>
    apply count_empty
    intro y matched
    simpa [extendLabelled] using matched.1
  | max n role filler _ =>
    change (¬count (fun y => (extendLabelled model label).role role (.inr fresh) y ∧
      holds (extendLabelled model label) filler y) (n + 1)) ↔ True
    have empty : ∀ y, ¬((extendLabelled model label).role role (.inr fresh) y ∧
        holds (extendLabelled model label) filler y) := by
      intro y matched
      simpa [extendLabelled] using matched.1
    rw [count_empty _ empty]
    simp

/-- The empty label is the original shell. -/
theorem shellWith_empty {Class Role : Type} (concept : Concept Class Role) :
    shellWith (fun _ => False) concept ↔ shell concept := by
  induction concept with
  | top | bottom | atom | self | some | all | min | max => simp [shellWith, shell]
  | neg inner ih => exact not_congr ih
  | and left right ihLeft ihRight => exact and_congr ihLeft ihRight
  | or left right ihLeft ihRight => exact or_congr ihLeft ihRight

theorem labelled_inclusion_extended {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (label : Class → Prop) (left right : Concept Class Role)
    (base : ∀ x, holds model left x → holds model right x)
    (witness : shellWith label left → shellWith label right) :
    ∀ x : Sum Object Fresh, holds (extendLabelled model label) left x →
      holds (extendLabelled model label) right x := by
  intro x matched
  cases x with
  | inl old =>
    exact (labelled_old_concepts_preserved model label right old).mpr
      (base old ((labelled_old_concepts_preserved model label left old).mp matched))
  | inr fresh =>
    exact (labelled_fresh_concepts_shell model label right fresh).mpr
      (witness ((labelled_fresh_concepts_shell model label left fresh).mp matched))

theorem labelled_role_inclusion_extended {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (label : Class → Prop) (left right : Role)
    (base : ∀ x y, model.role left x y → model.role right x y) :
    ∀ x y : Sum Object Fresh, (extendLabelled model label).role left x y →
      (extendLabelled model label).role right x y := by
  intro x y edge
  cases x <;> cases y <;> simp_all [extendLabelled]

theorem labelled_functionality_extended {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (label : Class → Prop) (role : Role)
    (base : ∀ x y z, model.role role x y → model.role role x z → y = z) :
    ∀ x y z : Sum Object Fresh, (extendLabelled model label).role role x y →
      (extendLabelled model label).role role x z → y = z := by
  intro x y z first second
  cases x <;> cases y <;> cases z <;> simp_all [extendLabelled]
  all_goals exact base _ _ _ first second

theorem labelled_transitivity_extended {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (label : Class → Prop) (role : Role)
    (base : ∀ x y z, model.role role x y → model.role role y z → model.role role x z) :
    ∀ x y z : Sum Object Fresh, (extendLabelled model label).role role x y →
      (extendLabelled model label).role role y z → (extendLabelled model label).role role x z := by
  intro x y z first second
  cases x <;> cases y <;> cases z <;> simp_all [extendLabelled]
  all_goals exact base _ _ _ first second

theorem labelled_inverse_roles_extended {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (label : Class → Prop) (left right : Role)
    (base : ∀ x y, model.role left x y ↔ model.role right y x) :
    ∀ x y : Sum Object Fresh, (extendLabelled model label).role left x y ↔
      (extendLabelled model label).role right y x := by
  intro x y
  cases x <;> cases y <;> simp_all [extendLabelled]

/-- A countermodel of `A ⊑ B` on an old element survives the labelled
extension, which satisfies every inclusion the witness label satisfies. -/
theorem labelled_countermodel_preserved {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (label : Class → Prop)
    (inclusions : List (Concept Class Role × Concept Class Role))
    (base : ∀ pair ∈ inclusions, ∀ x, holds model pair.1 x → holds model pair.2 x)
    (witness : ∀ pair ∈ inclusions, shellWith label pair.1 → shellWith label pair.2)
    (sub super : Concept Class Role) (x : Object)
    (inSub : holds model sub x) (notSuper : ¬holds model super x) :
    (∀ pair ∈ inclusions, ∀ y : Sum Object Fresh,
        holds (extendLabelled model label) pair.1 y →
          holds (extendLabelled model label) pair.2 y) ∧
      holds (extendLabelled (Fresh := Fresh) model label) sub (.inl x) ∧
      ¬holds (extendLabelled (Fresh := Fresh) model label) super (.inl x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro pair member
    exact labelled_inclusion_extended model label pair.1 pair.2
      (base pair member) (witness pair member)
  · exact (labelled_old_concepts_preserved model label sub x).mpr inSub
  · intro matched
    exact notSuper ((labelled_old_concepts_preserved model label super x).mp matched)

end ContextCalculus.LabelledIsolatedExtension
