import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace ContextCalculus.IntegerProfileCover

/-- Endpoints and their integer neighbours cover every comparison profile.
The Rust generator includes these candidates before deduplicating profiles. -/
theorem cut_cover (cuts : Finset Int) (x : Int) :
    ∃ r : Int,
      (r = 0 ∨ ∃ c ∈ cuts, r = c ∨ r = c - 1 ∨ r = c + 1) ∧
      ∀ c ∈ cuts, (x < c ↔ r < c) ∧ (x ≤ c ↔ r ≤ c) ∧ (x = c ↔ r = c) := by
  classical
  let lower := cuts.filter (fun c => c ≤ x)
  by_cases hl : lower.Nonempty
  · let l := lower.max' hl
    have hmem : l ∈ lower := Finset.max'_mem lower hl
    have hlc : l ∈ cuts := (Finset.mem_filter.mp hmem).1
    have hlx : l ≤ x := (Finset.mem_filter.mp hmem).2
    by_cases equal : l = x
    · refine ⟨x, Or.inr ⟨l, hlc, Or.inl equal.symm⟩, ?_⟩
      intro c _
      exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩
    · refine ⟨l + 1, Or.inr ⟨l, hlc, Or.inr (Or.inr rfl)⟩, ?_⟩
      intro c hc
      by_cases hcx : c ≤ x
      · have hcl : c ≤ l := Finset.le_max' lower c (Finset.mem_filter.mpr ⟨hc, hcx⟩)
        omega
      · omega
  · by_cases hc : cuts.Nonempty
    · let c := cuts.min' hc
      have hcmem : c ∈ cuts := Finset.min'_mem cuts hc
      refine ⟨c - 1, Or.inr ⟨c, hcmem, Or.inr (Or.inl rfl)⟩, ?_⟩
      intro d hd
      have hcd : c ≤ d := Finset.min'_le cuts d hd
      have hxd : x < d := by
        by_contra h
        have : d ∈ lower := Finset.mem_filter.mpr ⟨hd, by omega⟩
        exact hl ⟨d, this⟩
      omega
    · refine ⟨0, Or.inl rfl, ?_⟩
      intro c hm
      exact False.elim (hc ⟨c, hm⟩)

inductive Predicate where
  | lt : Int → Predicate
  | le : Int → Predicate
  | eq : Int → Predicate
  | neg : Predicate → Predicate
  | conj : Predicate → Predicate → Predicate
  | disj : Predicate → Predicate → Predicate

def endpoints : Predicate → Finset Int
  | .lt c | .le c | .eq c => {c}
  | .neg p => endpoints p
  | .conj p q | .disj p q => endpoints p ∪ endpoints q

def holds : Predicate → Int → Prop
  | .lt c, x => x < c
  | .le c, x => x ≤ c
  | .eq c, x => x = c
  | .neg p, x => ¬ holds p x
  | .conj p q, x => holds p x ∧ holds q x
  | .disj p q, x => holds p x ∨ holds q x

theorem same_profile (p : Predicate) (x r : Int)
    (h : ∀ c ∈ endpoints p,
      (x < c ↔ r < c) ∧ (x ≤ c ↔ r ≤ c) ∧ (x = c ↔ r = c)) :
    holds p x ↔ holds p r := by
  induction p with
  | lt c => exact (h c (by simp [endpoints])).1
  | le c => exact (h c (by simp [endpoints])).2.1
  | eq c => exact (h c (by simp [endpoints])).2.2
  | neg p ih => exact not_congr (ih h)
  | conj p q ihp ihq =>
      exact and_congr
        (ihp (fun c hc => h c (Finset.mem_union_left _ hc)))
        (ihq (fun c hc => h c (Finset.mem_union_right _ hc)))
  | disj p q ihp ihq =>
      exact or_congr
        (ihp (fun c hc => h c (Finset.mem_union_left _ hc)))
        (ihq (fun c hc => h c (Finset.mem_union_right _ hc)))

/-- A common endpoint set gives one representative for all collected predicates,
including literal equality tests, rather than a different representative per test. -/
theorem predicate_family_cover (cuts : Finset Int) (predicates : List Predicate)
    (complete : ∀ p ∈ predicates, ∀ c ∈ endpoints p, c ∈ cuts) (x : Int) :
    ∃ r : Int,
      (r = 0 ∨ ∃ c ∈ cuts, r = c ∨ r = c - 1 ∨ r = c + 1) ∧
      ∀ p ∈ predicates, holds p x ↔ holds p r := by
  obtain ⟨r, candidate, profile⟩ := cut_cover cuts x
  refine ⟨r, candidate, ?_⟩
  intro p hp
  exact same_profile p x r (fun c hc => profile c (complete p hp c hc))

/-- Discarding duplicate profiles preserves coverage as long as each generated
candidate has a retained representative with the same complete signature. -/
theorem deduplicated_family_cover (cuts : Finset Int) (predicates : List Predicate)
    (kept : Finset Int)
    (complete : ∀ p ∈ predicates, ∀ c ∈ endpoints p, c ∈ cuts)
    (retained : ∀ r : Int,
      (r = 0 ∨ ∃ c ∈ cuts, r = c ∨ r = c - 1 ∨ r = c + 1) →
      ∃ k ∈ kept, ∀ p ∈ predicates, holds p r ↔ holds p k) (x : Int) :
    ∃ k ∈ kept, ∀ p ∈ predicates, holds p x ↔ holds p k := by
  obtain ⟨r, candidate, profile⟩ := predicate_family_cover cuts predicates complete x
  obtain ⟨k, hk, same⟩ := retained r candidate
  exact ⟨k, hk, fun p hp => (profile p hp).trans (same p hp)⟩

/-- For a bounded discrete ordered family, include both endpoints as cuts.
The selected representative then remains inside the representable interval.
This is the ordered-domain ingredient for float rank coverage; the IEEE rank
mapping, signed zeros and NaN require separate refinement evidence. -/
theorem bounded_cut_cover (cuts : Finset Int) (lo hi x : Int)
    (hlo : lo ∈ cuts) (hhi : hi ∈ cuts) (hxlo : lo ≤ x) (hxhi : x ≤ hi) :
    ∃ r : Int,
      (r = 0 ∨ ∃ c ∈ cuts, r = c ∨ r = c - 1 ∨ r = c + 1) ∧
      lo ≤ r ∧ r ≤ hi ∧
      ∀ c ∈ cuts, (x < c ↔ r < c) ∧ (x ≤ c ↔ r ≤ c) ∧ (x = c ↔ r = c) := by
  obtain ⟨r, candidate, profile⟩ := cut_cover cuts x
  have lower := (profile lo hlo).1
  have upper := (profile hi hhi).2.1
  exact ⟨r, candidate, by omega, upper.mp hxhi, profile⟩

#print axioms bounded_cut_cover
#print axioms deduplicated_family_cover
#print axioms same_profile
#print axioms predicate_family_cover
#print axioms cut_cover
end ContextCalculus.IntegerProfileCover
