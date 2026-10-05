import ContextCalculus.HypertableauCardinality

/-! Symbolic complementary cardinality definitions over arbitrary object
domains. These theorems justify the semantic side channel, not its Rust
serialization, frontend source coverage, or a taxonomy publication. -/
namespace ContextCalculus.NativeCardinalityNormalization
open ContextCalculus.Hypertableau

theorem maximum_complement_recognition {Object : Type} (n : Nat)
    (predicate : Object → Prop) (marker complement : Prop)
    (split : marker ∨ complement)
    (maximumBound : marker → HasAtMost n predicate)
    (minimumBound : complement → HasAtLeast (n + 1) predicate) :
    marker ↔ HasAtMost n predicate := by
  constructor
  · exact maximumBound
  · intro bound
    rcases split with positive | negative
    · exact positive
    · exact False.elim (bound (minimumBound negative))

theorem minimum_definition_extension_iff {Object Root : Type} (n : Nat)
    (predicate : Root → Object → Prop) (marker : Root → Prop) :
    (∀ root, marker root ↔ HasAtLeast (n + 1) (predicate root)) ↔
    ∃ complement : Root → Prop,
      (∀ root, marker root ∨ complement root) ∧
      (∀ root, ¬(marker root ∧ complement root)) ∧
      (∀ root, marker root → HasAtLeast (n + 1) (predicate root)) ∧
      (∀ root, complement root → HasAtMost n (predicate root)) := by
  classical
  constructor
  · intro exact
    refine ⟨fun root => ¬marker root, ?_, ?_, ?_, ?_⟩
    · intro root
      exact Classical.em (marker root)
    · intro root contradictory
      exact contradictory.2 contradictory.1
    · intro root
      exact (exact root).mp
    · intro root negative witnesses
      exact negative ((exact root).mpr witnesses)
  · rintro ⟨complement, split, _, lower, upper⟩ root
    exact minimum_complement_recognition n (predicate root)
      (marker root) (complement root) (split root) (lower root) (upper root)

theorem maximum_definition_extension_iff {Object Root : Type} (n : Nat)
    (predicate : Root → Object → Prop) (marker : Root → Prop) :
    (∀ root, marker root ↔ HasAtMost n (predicate root)) ↔
    ∃ complement : Root → Prop,
      (∀ root, marker root ∨ complement root) ∧
      (∀ root, ¬(marker root ∧ complement root)) ∧
      (∀ root, marker root → HasAtMost n (predicate root)) ∧
      (∀ root, complement root → HasAtLeast (n + 1) (predicate root)) := by
  classical
  constructor
  · intro exact
    refine ⟨fun root => ¬marker root, ?_, ?_, ?_, ?_⟩
    · intro root
      exact Classical.em (marker root)
    · intro root contradictory
      exact contradictory.2 contradictory.1
    · intro root
      exact (exact root).mp
    · intro root negative
      by_contra absent
      exact negative ((exact root).mpr absent)
  · rintro ⟨complement, split, _, upper, lower⟩ root
    exact maximum_complement_recognition n (predicate root)
      (marker root) (complement root) (split root) (upper root) (lower root)

#print axioms maximum_complement_recognition
#print axioms minimum_definition_extension_iff
#print axioms maximum_definition_extension_iff
end ContextCalculus.NativeCardinalityNormalization
