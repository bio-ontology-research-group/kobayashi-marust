import ContextCalculus.SRIQD.NormalForm
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Oracles from cell decompositions (stage C4)

A generic way to prove `OracleSpec` for a data theory with one fixed
reading of its "map" atoms and `s` free atoms (datatypes outside the map,
read freely).

The values `Val` are cut into *cells* (`key : Val → K`, every key in the
list `cells`). Each cell has a size: `size c = some k` if exactly `k`
values lie in it, `none` if infinitely many do (`CellSpec`). An atom of
the theory holds at a value as a function `E p c g` of the value's cell
`c` and of the free atoms `g : Fin s → Bool` that hold at it. The theory
(`cellTheory`) has one admissible pair per reading `fr` of the free atoms.

The oracle `cellCard` adds the sizes of the cells, once per reading of
the free atoms that gives the value type `τ`. It satisfies `OracleSpec`
(`oracleSpec_cell`) if there are no free atoms or if every value type
with a finite count has count `0` (`FreeOK`; `freeCheck` decides a
sufficient condition: every value type of a finite nonempty cell also
comes from an infinite cell). Without that condition the lower half
fails: a cell of one value read with and without a free atom `F` gives
two value types of one value each, which no single reading realises
together.
-/

namespace ContextCalculus.SRIQD

set_option linter.unusedSectionVars false

/-! ## Sums of optional counts -/

/-- `none` (infinite) absorbs. -/
def oaddN : Option Nat → Option Nat → Option Nat
  | some a, some b => some (a + b)
  | _, _ => none

/-- The sum of a list of optional counts. -/
def osum (l : List (Option Nat)) : Option Nat := l.foldr oaddN (some 0)

/-- An optional count as an extended natural number. -/
def toE : Option Nat → ℕ∞
  | none => ⊤
  | some k => k

theorem toE_osum (l : List (Option Nat)) : toE (osum l) = (l.map toE).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [osum, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih]
    cases a <;> cases h : List.foldr oaddN (some 0) l <;> simp [oaddN, toE]

theorem toE_eq_coe {o : Option Nat} {k : Nat} : toE o = k ↔ o = some k := by
  cases o <;> simp [toE]

theorem osum_eq_none {l : List (Option Nat)} : osum l = none ↔ none ∈ l := by
  induction l with
  | nil => simp [osum]
  | cons a l ih =>
    simp only [osum, List.foldr_cons, List.mem_cons] at ih ⊢
    rw [← ih]
    cases a <;> cases h : List.foldr oaddN (some 0) l <;> simp [oaddN]

/-! ## All readings of the free atoms -/

/-- Every function `Fin s → Bool`. -/
def allG : (s : Nat) → List (Fin s → Bool)
  | 0 => [fun j => j.elim0]
  | s + 1 => (allG s).flatMap fun g => [Fin.cons false g, Fin.cons true g]

theorem mem_allG : ∀ {s : Nat} (g : Fin s → Bool), g ∈ allG s
  | 0, g => by
    simp only [allG, List.mem_singleton]
    funext j
    exact j.elim0
  | s + 1, g => by
    simp only [allG, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨Fin.tail g, mem_allG _, ?_⟩
    cases h : g 0
    · left
      rw [← h]
      exact (Fin.cons_self_tail g).symm
    · right
      rw [← h]
      exact (Fin.cons_self_tail g).symm

/-! ## The theory and its oracle -/

variable {Val K : Type} [DecidableEq K] {q s : Nat}

/-- The data theory: one admissible pair per reading `fr` of the free
atoms, up to a bijection with `Val`. -/
def cellTheory (key : Val → K) (E : Fin q → K → (Fin s → Bool) → Bool) : DataTheory (Fin q) :=
  fun V atom => ∃ (e : V ≃ Val) (fr : Fin s → Val → Bool),
    ∀ p v, atom p v ↔ E p (key (e v)) (fun j => fr j (e v)) = true

/-- The value type of a cell under a reading of the free atoms. -/
def vtc (E : Fin q → K → (Fin s → Bool) → Bool) (c : K) (g : Fin s → Bool) : Finset (Fin q) :=
  Finset.univ.filter fun p => E p c g = true

/-- The terms of the oracle sum for `τ`. -/
def cardTerms (cells : List K) (size : K → Option Nat) (E : Fin q → K → (Fin s → Bool) → Bool)
    (τ : Finset (Fin q)) : List (Option Nat) :=
  cells.flatMap fun c => (allG s).map fun g => if vtc E c g = τ then size c else some 0

/-- **The oracle**: the sizes of the cells, once per reading of the free
atoms that gives `τ`. -/
def cellCard (cells : List K) (size : K → Option Nat) (E : Fin q → K → (Fin s → Bool) → Bool)
    (τ : Finset (Fin q)) : Option Nat :=
  osum (cardTerms cells size E τ)

/-- The cells are exact. -/
structure CellSpec (key : Val → K) (cells : List K) (size : K → Option Nat) : Prop where
  mem : ∀ v, key v ∈ cells
  nodup : cells.Nodup
  size : ∀ c ∈ cells, {v | key v = c}.encard = toE (size c)

/-- No free atoms, or every value type with a finite count has count `0`. -/
def FreeOK (cells : List K) (size : K → Option Nat) (E : Fin q → K → (Fin s → Bool) → Bool) : Prop :=
  s = 0 ∨ ∀ τ k, cellCard cells size E τ = some k → k = 0

/-- A decidable condition for `FreeOK`: no free atoms, or every value type
of a finite nonempty cell also comes from an infinite cell. -/
def freeCheck (cells : List K) (size : K → Option Nat) (E : Fin q → K → (Fin s → Bool) → Bool) :
    Bool :=
  s == 0 || cells.all fun c => (allG s).all fun g =>
    match size c with
    | some (_ + 1) => cells.any fun c' => (allG s).any fun g' =>
        size c' == none && decide (vtc E c' g' = vtc E c g)
    | _ => true

section Proofs

variable {key : Val → K} {cells : List K} {size : K → Option Nat}
  {E : Fin q → K → (Fin s → Bool) → Bool}

theorem length_le_encard {α : Type} {L : List α} (hL : L.Nodup) {S : Set α} (h : ∀ x ∈ L, x ∈ S) :
    (L.length : ℕ∞) ≤ S.encard := by
  classical
  have : ((L.toFinset : Finset α) : Set α) ⊆ S := fun x hx => h x (List.mem_toFinset.1 hx)
  have h2 := Set.encard_le_encard this
  rw [Set.encard_coe_eq_coe_finsetCard, List.toFinset_card_of_nodup hL] at h2
  exact h2

/-- A nodup list whose keys lie in a nodup list `D` has length the sum of
the counts per key. -/
theorem length_eq_sum_count {α : Type} (f : α → K) (L : List α) {D : List K} (hD : D.Nodup)
    (hcov : ∀ x ∈ L, f x ∈ D) :
    L.length = (D.map fun c => L.countP fun x => f x = c).sum := by
  induction D generalizing L with
  | nil =>
    cases L with
    | nil => rfl
    | cons x L => exact absurd (hcov x List.mem_cons_self) (List.not_mem_nil)
  | cons c D ih =>
    rw [List.map_cons, List.sum_cons]
    have hsplit := List.length_eq_countP_add_countP (fun x => decide (f x = c)) (l := L)
    rw [hsplit]
    congr 1
    · have hD' := (List.nodup_cons.1 hD)
      have h := ih (L.filter fun x => ¬ decide (f x = c)) hD'.2 (by
        intro x hx
        obtain ⟨hxL, hne⟩ := List.mem_filter.1 hx
        rcases List.mem_cons.1 (hcov x hxL) with h | h
        · simp [h] at hne
        · exact h)
      rw [List.countP_eq_length_filter, h]
      congr 1
      refine List.map_congr_left fun c' hc' => ?_
      rw [List.countP_filter]
      refine List.countP_congr fun x _ => ?_
      constructor
      · intro hx
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
        exact hx.1
      · intro hx
        simp only [decide_eq_true_eq] at hx
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨hx, ?_⟩
        rw [hx]
        exact fun h => hD'.1 (h ▸ hc')

theorem sum_map_mono {D : List K} {f g : K → ℕ∞} (h : ∀ c ∈ D, f c ≤ g c) :
    (D.map f).sum ≤ (D.map g).sum := by
  induction D with
  | nil => simp
  | cons c D ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h c List.mem_cons_self) (ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

/-- Each term of the sum is at most the whole sum. -/
theorem le_sum_of_mem {l : List ℕ∞} {a : ℕ∞} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_self_add
    · exact (ih h).trans le_add_self

/-- A sum over a sublist of distinct entries is at most a sum over a
superlist, for `ℕ∞` (every entry nonnegative). -/
theorem sum_map_le_of_sub {D L : List K} (hD : D.Nodup) (hsub : ∀ c ∈ D, c ∈ L) (w : K → ℕ∞)
    (t : K → List ℕ∞) (ht : ∀ c, w c ≤ (t c).sum) :
    (D.map w).sum ≤ (L.flatMap t).sum := by
  induction D generalizing L with
  | nil => simp
  | cons c D ih =>
    obtain ⟨hcD, hDn⟩ := List.nodup_cons.1 hD
    have hcL := hsub c List.mem_cons_self
    obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hcL
    rw [List.map_cons, List.sum_cons, List.flatMap_append, List.flatMap_cons, List.sum_append,
      List.sum_append]
    have h2 : (D.map w).sum ≤ ((L1 ++ L2).flatMap t).sum := ih hDn fun c' hc' => by
      have := hsub c' (List.mem_cons_of_mem _ hc')
      rcases List.mem_append.1 this with h | h
      · exact List.mem_append_left _ h
      · rcases List.mem_cons.1 h with h | h
        · exact absurd (h ▸ hc') hcD
        · exact List.mem_append_right _ h
    rw [List.flatMap_append, List.sum_append] at h2
    calc w c + (D.map w).sum ≤ (t c).sum + ((L1.flatMap t).sum + (L2.flatMap t).sum) :=
          add_le_add (ht c) h2
      _ = (L1.flatMap t).sum + ((t c).sum + (L2.flatMap t).sum) := by
          rw [← add_assoc, ← add_assoc, add_comm (t c).sum]

theorem vt_cell {V : Type} {atom : Fin q → V → Prop} {e : V ≃ Val} {fr : Fin s → Val → Bool}
    (h : ∀ p v, atom p v ↔ E p (key (e v)) (fun j => fr j (e v)) = true) (v : V) :
    vt atom v = vtc E (key (e v)) (fun j => fr j (e v)) := by
  ext p
  rw [mem_vt, h]
  simp [vtc]

/-- **Upper half.** -/
theorem upper_cell (hc : CellSpec key cells size) :
    ∀ (V : Type) (atom : Fin q → V → Prop), cellTheory key E V atom → ∀ τ k,
      cellCard cells size E τ = some k →
      ∀ l : List V, l.Nodup → (∀ v ∈ l, vt atom v = τ) → l.length ≤ k := by
  classical
  rintro V atom ⟨e, fr, h⟩ τ k hk l hl hvt
  let L := l.map e
  have hL : L.Nodup := hl.map e.injective
  let D := cells.filter fun c => (allG s).any fun g => decide (vtc E c g = τ)
  have hDn : D.Nodup := hc.nodup.filter _
  have hcov : ∀ w ∈ L, key w ∈ D := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    refine List.mem_filter.2 ⟨hc.mem _, List.any_eq_true.2 ⟨fun j => fr j (e v), mem_allG _, ?_⟩⟩
    rw [← vt_cell h, hvt v hv]
    simp
  have hlen := length_eq_sum_count key L hDn hcov
  have hcnt : ∀ c ∈ D, ((L.countP fun w => key w = c : Nat) : ℕ∞) ≤ toE (size c) := by
    intro c hcD
    rw [← hc.size c (List.mem_filter.1 hcD).1, List.countP_eq_length_filter]
    exact length_le_encard (hL.filter _) fun w hw => by simpa using (List.mem_filter.1 hw).2
  have hterm : ∀ c, (if c ∈ D then toE (size c) else 0) ≤
      (((allG s).map fun g => if vtc E c g = τ then size c else some 0).map toE).sum := by
    intro c
    split_ifs with hcD
    · obtain ⟨g, hg, hgt⟩ := List.any_eq_true.1 (List.mem_filter.1 hcD).2
      refine le_sum_of_mem (List.mem_map.2 ⟨_, List.mem_map.2 ⟨g, hg, rfl⟩, ?_⟩)
      simp only [decide_eq_true_eq] at hgt
      simp [hgt]
    · exact zero_le _
  have hsum : (((L.length : Nat)) : ℕ∞) ≤ toE (cellCard cells size E τ) := by
    rw [hlen, Nat.cast_list_sum, List.map_map, cellCard, toE_osum, cardTerms, List.map_flatMap]
    calc ((D.map ((Nat.cast : Nat → ℕ∞) ∘ fun c => L.countP fun w => key w = c))).sum
        ≤ (D.map fun c => toE (size c)).sum := by
          refine sum_map_mono fun c hcD => ?_
          simpa using hcnt c hcD
      _ = (D.map fun c => if c ∈ D then toE (size c) else 0).sum := by
          congr 1
          exact List.map_congr_left fun c hcD => by rw [if_pos hcD]
      _ ≤ (cells.flatMap fun c => ((allG s).map fun g =>
            if vtc E c g = τ then size c else some 0).map toE).sum :=
          sum_map_le_of_sub hDn (fun c hc' => (List.mem_filter.1 hc').1) _ _ hterm
  rw [hk] at hsum
  have : L.length = l.length := List.length_map _
  rw [← this]
  simpa [toE] using hsum

theorem sum_flatMap' {α : Type} (L : List α) (t : α → List ℕ∞) :
    (L.flatMap t).sum = (L.map fun c => (t c).sum).sum := by
  induction L with
  | nil => rfl
  | cons c L ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem sum_map_ite_filter (L : List K) (P : K → Prop) [DecidablePred P] (w : K → ℕ∞) :
    (L.map fun c => if P c then w c else 0).sum = ((L.filter fun c => decide (P c)).map w).sum := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    by_cases h : P c
    · simp [h, ih]
    · simp [h, ih]

/-- The values whose keys lie in a nodup list of cells. -/
theorem encard_keys (hc : CellSpec key cells size) {D : List K} (hD : D.Nodup)
    (hsub : ∀ c ∈ D, c ∈ cells) :
    {v | key v ∈ D}.encard = (D.map fun c => toE (size c)).sum := by
  induction D with
  | nil => simp
  | cons c D ih =>
    obtain ⟨hcD, hDn⟩ := List.nodup_cons.1 hD
    have hset : {v | key v ∈ c :: D} = {v | key v = c} ∪ {v | key v ∈ D} := by
      ext v
      simp
    rw [hset, Set.encard_union_eq, hc.size c (hsub c List.mem_cons_self),
      ih hDn fun c' hc' => hsub c' (List.mem_cons_of_mem _ hc')]
    · simp
    · rw [Set.disjoint_left]
      intro v h1 h2
      simp only [Set.mem_setOf_eq] at h1 h2
      exact hcD (h1 ▸ h2)

/-- A set with at least `n` elements holds a nodup list of length `n`. -/
theorem exists_list_of_encard {α : Type} {S : Set α} {n : Nat} (h : (n : ℕ∞) ≤ S.encard) :
    ∃ l : List α, l.Nodup ∧ l.length = n ∧ ∀ x ∈ l, x ∈ S := by
  classical
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq h
  have hfin : t.Finite := Set.finite_of_encard_eq_coe htc
  refine ⟨hfin.toFinset.toList, Finset.nodup_toList _, ?_, fun x hx => hts ?_⟩
  · rw [Finset.length_toList]
    have := hfin.encard_eq_coe_toFinset_card
    rw [htc] at this
    exact_mod_cast this.symm
  · simpa using hx

/-- In the theory of one reading, the value types of the cells. -/
def oneAtom (key : Val → K) (E : Fin q → K → (Fin s → Bool) → Bool) (fr : Fin s → Val → Bool) :
    Fin q → Val → Prop :=
  fun p v => E p (key v) (fun j => fr j v) = true

theorem oneAtom_theory (fr : Fin s → Val → Bool) : cellTheory key E Val (oneAtom key E fr) :=
  ⟨Equiv.refl _, fr, fun _ _ => Iff.rfl⟩

/-- **Lower half without free atoms.** -/
theorem lower_cell_zero (hc : CellSpec key cells size) {E : Fin q → K → (Fin 0 → Bool) → Bool} :
    ∀ need : Finset (Fin q) → Nat, (∀ τ k, cellCard cells size E τ = some k → need τ ≤ k) →
      ∃ (V : Type) (atom : Fin q → V → Prop), cellTheory key E V atom ∧
        ∀ τ, ∃ l : List V, l.Nodup ∧ l.length = need τ ∧ ∀ v ∈ l, vt atom v = τ := by
  classical
  intro need hneed
  let g0 : Fin 0 → Bool := fun j => j.elim0
  let fr : Fin 0 → Val → Bool := fun j _ => j.elim0
  refine ⟨Val, oneAtom key E fr, oneAtom_theory fr, fun τ => ?_⟩
  let D := cells.filter fun c => decide (vtc E c g0 = τ)
  have hDn : D.Nodup := hc.nodup.filter _
  have hS : {v | key v ∈ D} = {v | vt (oneAtom key E fr) v = τ} := by
    ext v
    have hv : vt (oneAtom key E fr) v = vtc E (key v) g0 := by
      ext p
      rw [mem_vt]
      simp only [oneAtom, vtc, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show (fun j => fr j v) = g0 from funext fun j => j.elim0]
    simp only [Set.mem_setOf_eq, D, List.mem_filter, decide_eq_true_eq, hv]
    exact ⟨fun h => h.2, fun h => ⟨hc.mem v, h⟩⟩
  have hcard : toE (cellCard cells size E τ) = (D.map fun c => toE (size c)).sum := by
    rw [cellCard, toE_osum, cardTerms, List.map_flatMap]
    have : ∀ c, (((allG 0).map fun g => if vtc E c g = τ then size c else some 0).map toE).sum =
        if vtc E c g0 = τ then toE (size c) else 0 := by
      intro c
      simp only [allG, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      split_ifs <;> rfl
    rw [sum_flatMap', show (cells.map fun c => (((allG 0).map fun g =>
        if vtc E c g = τ then size c else some 0).map toE).sum) =
        cells.map fun c => if vtc E c g0 = τ then toE (size c) else 0 from
        List.map_congr_left fun c _ => this c, sum_map_ite_filter]
  have hle : (need τ : ℕ∞) ≤ {v | key v ∈ D}.encard := by
    rw [encard_keys hc hDn fun c hc' => (List.mem_filter.1 hc').1, ← hcard]
    cases h : cellCard cells size E τ with
    | none => simp [toE]
    | some k => simpa [toE] using hneed τ k h
  obtain ⟨l, hl, hlen, hmem⟩ := exists_list_of_encard hle
  refine ⟨l, hl, hlen, fun v hv => ?_⟩
  have := hmem v hv
  rw [hS] at this
  exact this

/-- With every cell empty or infinite, a value type with a finite count
has count `0`. -/
theorem cellCard_some_zero (hinf : ∀ c ∈ cells, size c = none ∨ size c = some 0)
    {τ : Finset (Fin q)} {k : Nat} (hk : cellCard cells size E τ = some k) : k = 0 := by
  have h1 : none ∉ cardTerms cells size E τ := fun h => by
    rw [cellCard, (osum_eq_none).2 h] at hk
    cases hk
  have h2 : ∀ t ∈ cardTerms cells size E τ, t = some 0 := by
    intro t ht
    obtain ⟨c, hc, ht⟩ := List.mem_flatMap.1 ht
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 ht
    split_ifs with hτ
    · rcases hinf c hc with h | h
      · exact absurd (by
          refine List.mem_flatMap.2 ⟨c, hc, List.mem_map.2 ⟨g, mem_allG g, ?_⟩⟩
          rw [if_pos hτ, h]) h1
      · exact h
    · rfl
  have h3 : toE (cellCard cells size E τ) = 0 := by
    rw [cellCard, toE_osum]
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    rw [h2 t ht]
    rfl
  rw [hk] at h3
  simpa [toE] using h3

/-- A value type with an infinite count comes from an infinite cell. -/
theorem exists_inf_cell {τ : Finset (Fin q)} (h : cellCard cells size E τ = none) :
    ∃ c ∈ cells, ∃ g : Fin s → Bool, vtc E c g = τ ∧ size c = none := by
  rw [cellCard, osum_eq_none] at h
  obtain ⟨c, hc, ht⟩ := List.mem_flatMap.1 h
  obtain ⟨g, -, hg⟩ := List.mem_map.1 ht
  split_ifs at hg with hτ
  · exact ⟨c, hc, g, hτ, hg⟩

/-- **Lower half when finite counts are `0`.** -/
theorem lower_cell_inf (hc : CellSpec key cells size)
    (hz : ∀ τ k, cellCard cells size E τ = some k → k = 0) :
    ∀ need : Finset (Fin q) → Nat, (∀ τ k, cellCard cells size E τ = some k → need τ ≤ k) →
      ∃ (V : Type) (atom : Fin q → V → Prop), cellTheory key E V atom ∧
        ∀ τ, ∃ l : List V, l.Nodup ∧ l.length = need τ ∧ ∀ v ∈ l, vt atom v = τ := by
  classical
  intro need hneed
  -- a demanded value type comes from an infinite cell
  have hpos : ∀ τ, 0 < need τ → ∃ c ∈ cells, ∃ g : Fin s → Bool, vtc E c g = τ ∧ size c = none := by
    intro τ hτ
    cases h : cellCard cells size E τ with
    | none => exact exists_inf_cell h
    | some k =>
      have := hneed τ k h
      rw [hz τ k h] at this
      omega
  -- an injection of `ℕ` into each infinite cell
  have hInf : ∀ c ∈ cells, size c = none → {v | key v = c}.Infinite := by
    intro c hc' hs
    have := hc.size c hc'
    rw [hs] at this
    exact Set.encard_eq_top_iff.1 this
  let H : (c : K) → {v | key v = c}.Infinite → ℕ → Val := fun c h n =>
    (@Infinite.natEmbedding _ h.to_subtype n).1
  have hHkey : ∀ c h n, key (H c h n) = c := fun c h n => (@Infinite.natEmbedding _ h.to_subtype n).2
  have hHinj : ∀ c h, Function.Injective (H c h) := fun c h a b hab =>
    (@Infinite.natEmbedding _ h.to_subtype).injective (Subtype.ext hab)
  let enc : Finset (Fin q) → ℕ := fun τ => (Fintype.equivFin (Finset (Fin q)) τ).val
  have henc : Function.Injective enc := fun a b h =>
    (Fintype.equivFin (Finset (Fin q))).injective (Fin.ext h)
  -- the chosen cell and reading of each demanded value type
  let cg : (τ : Finset (Fin q)) → 0 < need τ → K × (Fin s → Bool) := fun τ h =>
    ((hpos τ h).choose, (hpos τ h).choose_spec.2.choose)
  have hcg : ∀ τ h, (cg τ h).1 ∈ cells ∧ vtc E (cg τ h).1 (cg τ h).2 = τ ∧ size (cg τ h).1 = none :=
    fun τ h => ⟨(hpos τ h).choose_spec.1, (hpos τ h).choose_spec.2.choose_spec⟩
  let w : (τ : Finset (Fin q)) → 0 < need τ → ℕ → Val := fun τ h i =>
    H (cg τ h).1 (hInf _ (hcg τ h).1 (hcg τ h).2.2) (Nat.pair (enc τ) i)
  have hwkey : ∀ τ h i, key (w τ h i) = (cg τ h).1 := fun τ h i =>
    hHkey _ (hInf _ (hcg τ h).1 (hcg τ h).2.2) _
  have hwinj : ∀ τ h i τ' h' i', w τ h i = w τ' h' i' → τ = τ' ∧ i = i' := by
    intro τ h i τ' h' i' he
    have hk : (cg τ h).1 = (cg τ' h').1 := by rw [← hwkey τ h i, ← hwkey τ' h' i', he]
    simp only [w] at he
    revert he
    generalize hInf _ (hcg τ h).1 (hcg τ h).2.2 = p1
    generalize hInf _ (hcg τ' h').1 (hcg τ' h').2.2 = p2
    revert p1 p2
    rw [hk]
    intro p1 p2 he
    have := hHinj _ p2 he
    have hp := Nat.pair_eq_pair.1 this
    exact ⟨henc hp.1, hp.2⟩
  let fr : Fin s → Val → Bool := fun j v =>
    decide (∃ τ, ∃ h : 0 < need τ, ∃ i, v = w τ h i ∧ (cg τ h).2 j = true)
  have hfr : ∀ τ h i, (fun j => fr j (w τ h i)) = (cg τ h).2 := by
    intro τ h i
    funext j
    simp only [fr]
    by_cases hj : (cg τ h).2 j = true
    · rw [hj, decide_eq_true_iff]
      exact ⟨τ, h, i, rfl, hj⟩
    · rw [Bool.not_eq_true] at hj
      rw [hj, decide_eq_false_iff_not]
      rintro ⟨τ', h', i', he, hj'⟩
      obtain ⟨rfl, rfl⟩ := hwinj τ h i τ' h' i' he
      rw [hj] at hj'
      cases hj'
  refine ⟨Val, oneAtom key E fr, oneAtom_theory fr, fun τ => ?_⟩
  by_cases h : 0 < need τ
  · refine ⟨(List.range (need τ)).map (w τ h), ?_, by simp, ?_⟩
    · refine (List.nodup_range).map ?_
      intro i i' he
      exact (hwinj τ h i τ h i' he).2
    · intro v hv
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv
      have hvt : vt (oneAtom key E fr) (w τ h i) = vtc E (key (w τ h i)) (fun j => fr j (w τ h i)) := by
        ext p
        rw [mem_vt]
        simp [oneAtom, vtc]
      rw [hvt, hfr τ h i, hwkey τ h i]
      exact (hcg τ h).2.1
  · exact ⟨[], List.nodup_nil, by simp at h ⊢; omega, by simp⟩

/-- **The cell oracle.** -/
theorem oracleSpec_cell (hc : CellSpec key cells size) (hf : FreeOK cells size E) :
    OracleSpec (cellTheory key E) (cellCard cells size E) := by
  refine ⟨upper_cell hc, ?_⟩
  rcases hf with rfl | hz
  · exact lower_cell_zero hc
  · exact lower_cell_inf hc hz

/-- The decidable check gives `FreeOK`. -/
theorem freeOK_of_check (h : freeCheck cells size E = true) : FreeOK cells size E := by
  unfold freeCheck at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact Or.inl (by simpa using h)
  · right
    intro τ k hk
    by_contra hk0
    -- a positive finite term
    have hnone : none ∉ cardTerms cells size E τ := fun hn => by
      rw [cellCard, (osum_eq_none).2 hn] at hk
      cases hk
    have hpos : ∃ t ∈ cardTerms cells size E τ, t ≠ some 0 := by
      by_contra hall
      push Not at hall
      have : toE (cellCard cells size E τ) = 0 := by
        rw [cellCard, toE_osum]
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
        rw [hall t ht]; rfl
      rw [hk] at this
      exact hk0 (by simpa [toE] using this)
    obtain ⟨t, ht, ht0⟩ := hpos
    obtain ⟨c, hcc, ht⟩ := List.mem_flatMap.1 ht
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 ht
    split_ifs at ht0 with hτ
    · cases hs : size c with
      | none => exact hnone (List.mem_flatMap.2 ⟨c, hcc, List.mem_map.2 ⟨g, mem_allG g, by
          rw [if_pos hτ, hs]⟩⟩)
      | some j =>
        cases j with
        | zero => exact ht0 hs
        | succ j =>
          have := List.all_eq_true.1 (List.all_eq_true.1 h c hcc) g (mem_allG g)
          rw [hs] at this
          obtain ⟨c', hc', hg'⟩ := List.any_eq_true.1 this
          obtain ⟨g', -, hg''⟩ := List.any_eq_true.1 hg'
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg''
          exact hnone (List.mem_flatMap.2 ⟨c', hc', List.mem_map.2 ⟨g', mem_allG g', by
            rw [if_pos (hg''.2.trans hτ), hg''.1]⟩⟩)
    · exact ht0 rfl

end Proofs

end ContextCalculus.SRIQD

#print axioms ContextCalculus.SRIQD.upper_cell
#print axioms ContextCalculus.SRIQD.oracleSpec_cell
#print axioms ContextCalculus.SRIQD.freeOK_of_check
