/-!
# Linear encoding of data-value relations

`frontend::datatypes::linear_value_relation_clauses` replaces the pairwise
value clauses of a large literal vocabulary by helper concepts:

* index bits: identity class `i` implies `bit k (i k)` for every position `k`,
  and `bit k false ⊓ bit k true ⊑ ⊥`;
* membership profiles: every value with membership vector `π` implies
  `prof π`, and `prof π ⊑ R` (resp. `prof π ⊓ R ⊑ ⊥`) when `π` says the
  value is in `R` (resp. not in `R`).

This file proves, for one arbitrary interpretation of the value concepts over
an arbitrary domain, that the helper clauses (1) entail the pairwise clauses
they replace, and (2) are satisfiable on top of every interpretation that
satisfies the pairwise clauses, by reading each helper as the union of the
values that imply it. Together: the linear clause set is a conservative
extension of the pairwise one over the source vocabulary.

Scope. This is a statement about the clause sets as sets of first-order
sentences. It does not cover the Rust generator (that it emits exactly these
clauses), the datatype oracle's decisions (`val_eq`, `val_in_range`), or the
bridge admission that checks the emitted helper clauses; those are tested,
not proved.
-/

namespace ContextCalculus.LinearValueEncoding
universe u v w

variable {Δ : Type u} {V : Type v} {K : Type w}

/-- Pairwise value distinctness: values with different identity keys never
share an element. -/
def PairwiseDistinct (key : V → K) (ext : V → Δ → Prop) : Prop :=
  ∀ a b x, key a ≠ key b → ext a x → ext b x → False

/-- The index-bit clauses for an index `idx : K → Nat → Bool` over the
positions `p < n`. -/
def BitClauses (n : Nat) (key : V → K) (idx : K → Nat → Bool)
    (ext : V → Δ → Prop) (bit : Nat → Bool → Δ → Prop) : Prop :=
  (∀ a x p, p < n → ext a x → bit p (idx (key a) p) x) ∧
  (∀ p x, p < n → bit p false x → bit p true x → False)

/-- The index separates keys on the first `n` positions. -/
def Separating (n : Nat) (idx : K → Nat → Bool) : Prop :=
  ∀ k l, k ≠ l → ∃ p, p < n ∧ idx k p ≠ idx l p

theorem bits_entail_pairwise (n : Nat) (key : V → K) (idx : K → Nat → Bool)
    (ext : V → Δ → Prop) (bit : Nat → Bool → Δ → Prop)
    (sep : Separating n idx) (h : BitClauses n key idx ext bit) :
    PairwiseDistinct key ext := by
  intro a b x hne ha hb
  obtain ⟨p, hp, hdiff⟩ := sep (key a) (key b) hne
  have ba := h.1 a x p hp ha
  have bb := h.1 b x p hp hb
  cases hia : idx (key a) p <;> cases hib : idx (key b) p
  · exact hdiff (hia.trans hib.symm)
  · rw [hia] at ba; rw [hib] at bb; exact h.2 p x hp ba bb
  · rw [hia] at ba; rw [hib] at bb; exact h.2 p x hp bb ba
  · exact hdiff (hia.trans hib.symm)

/-- The canonical interpretation of a bit helper: the union of the values
whose index has that bit. -/
def canonicalBit (key : V → K) (idx : K → Nat → Bool) (ext : V → Δ → Prop) :
    Nat → Bool → Δ → Prop :=
  fun p c x => ∃ a, ext a x ∧ idx (key a) p = c

theorem pairwise_admits_bits (n : Nat) (key : V → K) (idx : K → Nat → Bool)
    (ext : V → Δ → Prop) (h : PairwiseDistinct key ext) :
    BitClauses n key idx ext (canonicalBit key idx ext) := by
  constructor
  · intro a x p _ ha
    exact ⟨a, ha, rfl⟩
  · intro p x _ ⟨a, ha, hpa⟩ ⟨b, hb, hpb⟩
    by_cases hk : key a = key b
    · rw [hk] at hpa
      rw [hpa] at hpb
      exact Bool.false_ne_true hpb
    · exact h a b x hk ha hb

/-- Membership of the values in the ranges, as the pairwise form states it:
`member a r = some true` gives `a ⊑ r`, `some false` gives `a ⊓ r ⊑ ⊥`. -/
def PairwiseMembership {R : Type w} (member : V → R → Option Bool)
    (ext : V → Δ → Prop) (range : R → Δ → Prop) : Prop :=
  ∀ a r x, ext a x →
    (member a r = some true → range r x) ∧ (member a r = some false → range r x → False)

/-- The profile clauses: every value implies the helper of its membership
vector, which carries the membership clauses. -/
def ProfileClauses {R : Type w} (member : V → R → Option Bool)
    (ext : V → Δ → Prop) (range : R → Δ → Prop)
    (prof : (R → Option Bool) → Δ → Prop) : Prop :=
  (∀ a x, ext a x → prof (member a) x) ∧
  (∀ π r x, prof π x → (π r = some true → range r x) ∧ (π r = some false → range r x → False))

theorem profiles_entail_membership {R : Type w} (member : V → R → Option Bool)
    (ext : V → Δ → Prop) (range : R → Δ → Prop) (prof : (R → Option Bool) → Δ → Prop)
    (h : ProfileClauses member ext range prof) : PairwiseMembership member ext range := by
  intro a r x ha
  exact h.2 (member a) r x (h.1 a x ha)

theorem membership_admits_profiles {R : Type w} (member : V → R → Option Bool)
    (ext : V → Δ → Prop) (range : R → Δ → Prop) (h : PairwiseMembership member ext range) :
    ProfileClauses member ext range (fun π x => ∃ a, ext a x ∧ member a = π) := by
  constructor
  · intro a x ha
    exact ⟨a, ha, rfl⟩
  · intro π r x ⟨a, ha, hπ⟩
    subst hπ
    exact h a r x ha

/-- The standard binary index of the identity classes `0 … m-1` separates them
on `n` positions when `m ≤ 2^n`. -/
def binaryIndex (i : Nat) (p : Nat) : Bool := (i / 2 ^ p) % 2 == 1

theorem binaryIndex_separating (n : Nat) :
    ∀ i j, i < 2 ^ n → j < 2 ^ n → i ≠ j → ∃ p, p < n ∧ binaryIndex i p ≠ binaryIndex j p := by
  induction n with
  | zero =>
    intro i j hi hj hne
    simp at hi hj
    omega
  | succ n ih =>
    intro i j hi hj hne
    by_cases hlow : i % 2 = j % 2
    · have hi' : i / 2 < 2 ^ n := by rw [Nat.pow_succ] at hi; omega
      have hj' : j / 2 < 2 ^ n := by rw [Nat.pow_succ] at hj; omega
      have hne' : i / 2 ≠ j / 2 := by
        have := Nat.div_add_mod i 2
        have := Nat.div_add_mod j 2
        omega
      obtain ⟨p, hp, hd⟩ := ih (i / 2) (j / 2) hi' hj' hne'
      refine ⟨p + 1, by omega, ?_⟩
      unfold binaryIndex at hd ⊢
      rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      exact hd
    · refine ⟨0, by omega, ?_⟩
      unfold binaryIndex
      simp only [Nat.pow_zero, Nat.div_one]
      have hi2 : i % 2 < 2 := Nat.mod_lt i (by decide)
      have hj2 : j % 2 < 2 := Nat.mod_lt j (by decide)
      intro heq
      apply hlow
      cases hx : i % 2 with
      | zero =>
        cases hy : j % 2 with
        | zero => rfl
        | succ m => rw [hx, hy] at heq; simp at heq; omega
      | succ m =>
        cases hy : j % 2 with
        | zero => rw [hx, hy] at heq; simp at heq; omega
        | succ k => omega

end ContextCalculus.LinearValueEncoding
