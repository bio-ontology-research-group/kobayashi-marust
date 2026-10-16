import ContextCalculus.IncrementalDataModuleReuse

/-!
# Deletion rows supported by surviving global role facts

The executable shortcut checks OLD and NEW against the augmented object/data
envelope, admits NEW independently, and uses only NEW named reflexivity,
named role inclusions, and named domain/range statements to seed Told proofs.
Every seed holds at every object in every actual NEW model. No assertion edge
establishes reflexivity, and no union domain is split into its operands.

The seed-aware Told graph is only a proof search aid. It does not change the
source passed to classification, and its seeds are not saved across revisions.
All old rows start potentially affected after a global locality refusal; only
satisfiable rows whose complete published contents have these proofs survive.
The remaining rows are classified against the complete actual NEW source.
The fixed data domain, range interpretation, and literal map remain unchanged.
-/

namespace ContextCalculus.IncrementalGlobalTold

open IncrementalModuleReuse IncrementalDataModuleReuse

inductive ReflexiveFrom (O : AugAx → Prop) : Role → Prop
  | direct {r} : O (.object (.refl r)) → ReflexiveFrom O r
  | super {r s} : ReflexiveFrom O r →
      O (.object (.roleSub r [] s)) → ReflexiveFrom O s

inductive GlobalClass (O : AugAx → Prop) : Nat → Prop
  | domain {r n} : ReflexiveFrom O r →
      O (.object (.sub (.some r .top) (.atom n))) → GlobalClass O n
  | range {r n} : ReflexiveFrom O r →
      O (.object (.sub .top (.all r (.atom n)))) → GlobalClass O n

variable {D W : Type} {ranges : Nat → D → Prop} {literal : Nat → D}
  {O O' : AugAx → Prop} {i : DataInterp W D}

theorem reflexive_sound {r : Role} (h : ReflexiveFrom O r)
    (model : IncrementalDataModuleReuse.Models ranges literal O i) :
    ∀ x, i.obj.role r x x := by
  induction h with
  | direct ha => exact model _ ha
  | super _ ha ih =>
      intro x
      exact model _ ha x x ⟨x, ih x, rfl⟩

theorem global_class_sound {n : Nat} (h : GlobalClass O n)
    (model : IncrementalDataModuleReuse.Models ranges literal O i) :
    ∀ x, i.obj.cls n x := by
  cases h with
  | domain hr ha =>
      intro x
      exact model _ ha x ⟨x, reflexive_sound hr model x, trivial⟩
  | range hr ha =>
      intro x
      exact model _ ha x trivial x (reflexive_sound hr model x)

/-- An analysis-only extension by independently justified universal classes. -/
def ToldTheory (O : AugAx → Prop) (a : Axiom) : Prop :=
  O (.object a) ∨ ∃ n, a = .sub .top (.atom n) ∧ GlobalClass O n

theorem told_theory_model
    (model : IncrementalDataModuleReuse.Models ranges literal O i) :
    ∀ a, ToldTheory O a → sat i.obj a := by
  intro a ha
  rcases ha with ha | ⟨n, rfl, hn⟩
  · exact model _ ha
  · intro x _
    exact global_class_sound hn model x

theorem told_global_sound {c d : Concept} (proof : Told (ToldTheory O) c d) :
    IncrementalDataModuleReuse.Entails ranges literal O (c, d) := by
  intro U model satisfies
  exact told_sound proof U model.obj (told_theory_model satisfies)

/-- Exact OLD rows plus NEW-supported proofs suffice after deletion, even
when a removed axiom was in the global locality core. -/
theorem deletion_row_exact {c : Concept} {row : Concept → Prop}
    (subset : ∀ a, O' a → O a)
    (oldExact : ∀ d, IncrementalDataModuleReuse.Entails ranges literal O (c, d) ↔ row d)
    (supported : ∀ d, row d → Told (ToldTheory O') c d) :
    ∀ d, IncrementalDataModuleReuse.Entails ranges literal O' (c, d) ↔ row d := by
  intro d
  constructor
  · intro entailed
    apply (oldExact d).mp
    intro U model satisfies
    exact entailed U model (fun a ha => satisfies a (subset a ha))
  · intro kept
    exact told_global_sound (supported d kept)

theorem deletion_consistent (subset : ∀ a, O' a → O a)
    (consistent : IncrementalDataModuleReuse.Consistent ranges literal O) :
    IncrementalDataModuleReuse.Consistent ranges literal O' := by
  rcases consistent with ⟨U, model, satisfies⟩
  exact ⟨U, model, fun a ha => satisfies a (subset a ha)⟩

/-- Old satisfiable subjects remain satisfiable; old unsatisfiable subjects
are explicitly excluded from retained rows by the executable shortcut. -/
theorem deletion_satisfiable {c : Concept} (subset : ∀ a, O' a → O a)
    (witness : ∃ (U : Type) (model : DataInterp U D),
      IncrementalDataModuleReuse.Models ranges literal O model ∧
      ∃ x, eval model.obj c x) :
    ∃ (U : Type) (model : DataInterp U D),
      IncrementalDataModuleReuse.Models ranges literal O' model ∧
      ∃ x, eval model.obj c x := by
  rcases witness with ⟨U, model, satisfies, x, hx⟩
  exact ⟨U, model, (fun a ha => satisfies a (subset a ha)), x, hx⟩

#print axioms reflexive_sound
#print axioms global_class_sound
#print axioms told_theory_model
#print axioms told_global_sound
#print axioms deletion_row_exact
#print axioms deletion_consistent
#print axioms deletion_satisfiable

end ContextCalculus.IncrementalGlobalTold
