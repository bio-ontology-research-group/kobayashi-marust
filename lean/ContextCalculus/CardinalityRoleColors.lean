import ContextCalculus.HypertableauCardinality
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-! Parent-indexed fresh role labels. A successor shared by different parents
may receive different labels. No unique-name or global-color assumption occurs.
This boundary proves the encoding semantics; it is not a Rust extraction. -/
namespace ContextCalculus.CardinalityRoleColors
open ContextCalculus.Hypertableau

theorem finite_bit_code_injective {n k : Nat} (bound : n ≤ 2 ^ k) :
    Function.Injective (fun i : Fin n => fun bit : Fin k => i.val.testBit bit.val) := by
  intro i j equal
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases low : bit < k
  · exact congrFun equal ⟨bit, low⟩
  · have power : 2 ^ k ≤ 2 ^ bit := Nat.pow_le_pow_right (by decide) (by omega)
    have hi : i.val < 2 ^ bit := lt_of_lt_of_le (lt_of_lt_of_le i.isLt bound) power
    have hj : j.val < 2 ^ bit := lt_of_lt_of_le (lt_of_lt_of_le j.isLt bound) power
    rw [Nat.testBit_eq_false_of_lt hi, Nat.testBit_eq_false_of_lt hj]

theorem disjoint_labels_force_distinct {Root Object Index Bit : Type}
    (code : Index → Bit → Bool) (codeInjective : Function.Injective code)
    (guard : Root → Prop) (witness : Root → Index → Object)
    (zero one : Bit → Root → Object → Prop)
    (zeroLabels : ∀ root, guard root → ∀ index bit,
      code index bit = false → zero bit root (witness root index))
    (oneLabels : ∀ root, guard root → ∀ index bit,
      code index bit = true → one bit root (witness root index))
    (disjoint : ∀ bit root object, zero bit root object → one bit root object → False) :
    ∀ root, guard root → Function.Injective (witness root) := by
  intro root guarded i j same
  apply codeInjective
  funext bit
  cases hi : code i bit <;> cases hj : code j bit
  · rfl
  · exact False.elim (disjoint bit root (witness root j)
      (by simpa [same] using zeroLabels root guarded i bit hi)
      (oneLabels root guarded j bit hj))
  · exact False.elim (disjoint bit root (witness root j)
      (zeroLabels root guarded j bit hj)
      (by simpa [same] using oneLabels root guarded i bit hi))
  · rfl

theorem distinct_witnesses_admit_labels {Root Object Index Bit : Type}
    (code : Index → Bit → Bool) (guard : Root → Prop)
    (witness : Root → Index → Object)
    (distinct : ∀ root, guard root → Function.Injective (witness root)) :
    ∃ zero one : Bit → Root → Object → Prop,
      (∀ root, guard root → ∀ index bit, code index bit = false →
        zero bit root (witness root index)) ∧
      (∀ root, guard root → ∀ index bit, code index bit = true →
        one bit root (witness root index)) ∧
      (∀ bit root object, zero bit root object → one bit root object → False) := by
  let zero := fun bit root object =>
    ∃ index, guard root ∧ witness root index = object ∧ code index bit = false
  let one := fun bit root object =>
    ∃ index, guard root ∧ witness root index = object ∧ code index bit = true
  refine ⟨zero, one, ?_, ?_, ?_⟩
  · intro root guarded index bit encoded
    exact ⟨index, guarded, rfl, encoded⟩
  · intro root guarded index bit encoded
    exact ⟨index, guarded, rfl, encoded⟩
  · rintro bit root object ⟨i, guarded, hi, ci⟩ ⟨j, _, hj, cj⟩
    have same := distinct root guarded (hi.trans hj.symm)
    subst j
    rw [ci] at cj
    cases cj

theorem maximum_admits_finite_buckets {Object : Type} {n : Nat}
    (predicate : Object → Prop) (bound : HasAtMost n predicate) :
    Nonempty ({object // predicate object} ↪ Fin n) := by
  classical
  let Successor := {object // predicate object}
  by_cases finite : Nonempty (Fintype Successor)
  · letI : Fintype Successor := Classical.choice finite
    have cardBound : Fintype.card Successor ≤ n := by
      by_contra tooMany
      have count : Fintype.card (Fin (n + 1)) ≤ Fintype.card Successor := by
        simp only [Fintype.card_fin]
        omega
      obtain ⟨embed⟩ := Function.Embedding.nonempty_of_card_le count
      exact bound ⟨fun index => (embed index).val,
        Subtype.val_injective.comp embed.injective, fun index => (embed index).property⟩
    exact Function.Embedding.nonempty_of_card_le (by simpa using cardBound)
  · letI : Infinite Successor := Infinite.of_not_fintype (fun inst => finite ⟨inst⟩)
    let embed := Infinite.natEmbedding Successor
    exact False.elim (bound ⟨fun index => (embed index.val).val,
      Subtype.val_injective.comp (embed.injective.comp Fin.val_injective),
      fun index => (embed index.val).property⟩)

theorem functional_bucket_cover_bounds {Object : Type} {n : Nat}
    (predicate : Object → Prop) (bucket : Fin n → Object → Prop)
    (cover : ∀ object, predicate object → ∃ index, bucket index object)
    (functional : ∀ index left right, bucket index left → bucket index right → left = right) :
    HasAtMost n predicate := by
  classical
  rintro ⟨witness, distinct, matched⟩
  choose color colored using fun index => cover (witness index) (matched index)
  have injective : Function.Injective color := by
    intro i j same
    apply distinct
    exact functional (color i) (witness i) (witness j) (colored i) (by simpa [same] using colored j)
  have count := Fintype.card_le_of_injective color injective
  simp only [Fintype.card_fin] at count
  omega

theorem embedding_supplies_functional_cover {Object : Type} {n : Nat}
    (predicate : Object → Prop) (color : {object // predicate object} ↪ Fin n) :
    ∃ bucket : Fin n → Object → Prop,
      (∀ object, predicate object → ∃ index, bucket index object) ∧
      (∀ index left right, bucket index left → bucket index right → left = right) := by
  let bucket := fun index object => ∃ h : predicate object, color ⟨object, h⟩ = index
  refine ⟨bucket, ?_, ?_⟩
  · intro object matched
    exact ⟨color ⟨object, matched⟩, matched, rfl⟩
  · rintro index left right ⟨hl, cl⟩ ⟨hr, cr⟩
    exact congrArg Subtype.val (color.injective (cl.trans cr.symm))

theorem maximum_bucket_encoding_iff {Object : Type} {n : Nat}
    (predicate : Object → Prop) :
    HasAtMost n predicate ↔ ∃ bucket : Fin n → Object → Prop,
      (∀ object, predicate object → ∃ index, bucket index object) ∧
      (∀ index left right, bucket index left → bucket index right → left = right) := by
  constructor
  · intro bound
    obtain ⟨color⟩ := maximum_admits_finite_buckets predicate bound
    exact embedding_supplies_functional_cover predicate color
  · rintro ⟨bucket, cover, functional⟩
    exact functional_bucket_cover_bounds predicate bucket cover functional

#print axioms maximum_bucket_encoding_iff
#print axioms finite_bit_code_injective
#print axioms disjoint_labels_force_distinct
#print axioms distinct_witnesses_admit_labels
#print axioms maximum_admits_finite_buckets
#print axioms functional_bucket_cover_bounds
#print axioms embedding_supplies_functional_cover
end ContextCalculus.CardinalityRoleColors
