import ContextCalculus.SRIQD.CellOracle
import ContextCalculus.SRIQD.OracleB

/-!
# Splitting a cell theory by the readings of its free atoms (stage C4)

A cell theory (`SRIQD/CellOracle.lean`) with free atoms has no oracle when
a finite cell can be read in several ways (`OWL/Datatypes/OracleObstacle.lean`).
The repair: split the theory into *parts*. A part `n` fixes, for every
*small* cell (`size c = some k` with `k ≤ L`), how many of its values get
each reading `g` of the free atoms (`n c g`, summing to `k`, `ValidPart`).
Cells with more than `L` values, and infinite cells, stay unconstrained.

* `partTheory L n ⊆ cellTheory` and every admissible pair of the cell theory
  lies in the part of its own counts (`cellTheory_iff_part`), so a
  subsumption holds in the cell theory iff it holds in every part.
* Each part has a bounded oracle (`oracleSpecB_part`): `partCard L n` counts
  `n c g` for small cells and the size for the others, and for
  `L = B · 2^s` it supplies up to `B` values of every value type.
-/

namespace ContextCalculus.SRIQD

set_option linter.unusedSectionVars false

/-! ## Readings -/

theorem allG_nodup : ∀ s : Nat, (allG s).Nodup
  | 0 => by simp [allG]
  | s + 1 => by
    rw [allG, List.nodup_flatMap]
    refine ⟨fun g _ => ?_, ?_⟩
    · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_true]
      intro h
      have := congrFun h 0
      simp at this
    · refine (allG_nodup s).imp fun {g g'} hne => ?_
      rw [Function.onFun, List.disjoint_left]
      intro x hx hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hx'
      apply hne
      have h1 : Fin.tail x = g := by rcases hx with rfl | rfl <;> simp
      have h2 : Fin.tail x = g' := by rcases hx' with rfl | rfl <;> simp
      rw [← h1, ← h2]

/-! ## Encard of fibres -/

theorem encard_sum_fibers {α β : Type} [DecidableEq β] (f : α → β) (S : Set α) :
    ∀ {D : List β}, D.Nodup → (∀ v ∈ S, f v ∈ D) →
      S.encard = (D.map fun d => {v | v ∈ S ∧ f v = d}.encard).sum
  | [], _, hcov => by
    simp only [List.map_nil, List.sum_nil, Set.encard_eq_zero]
    ext v
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hv
    exact absurd (hcov v hv) (List.not_mem_nil)
  | d :: D, hD, hcov => by
    obtain ⟨hdD, hDn⟩ := List.nodup_cons.1 hD
    have hS : S = {v | v ∈ S ∧ f v = d} ∪ {v | v ∈ S ∧ f v ≠ d} := by
      ext v; by_cases h : f v = d <;> simp [h]
    have hdis : Disjoint {v | v ∈ S ∧ f v = d} {v | v ∈ S ∧ f v ≠ d} := by
      rw [Set.disjoint_left]; intro v h1 h2; exact h2.2 h1.2
    have ih := encard_sum_fibers f {v | v ∈ S ∧ f v ≠ d} hDn (fun v hv => by
      rcases List.mem_cons.1 (hcov v hv.1) with h | h
      · exact absurd h hv.2
      · exact h)
    conv_lhs => rw [hS]
    rw [Set.encard_union_eq hdis, ih, List.map_cons, List.sum_cons]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun d' hd' => ?_)
    congr 1
    ext v
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, fun h => hdD (by rw [← h, h2]; exact hd')⟩, h2⟩

/-- A finite set with `Σ m g` elements can be coloured with exactly `m g`
elements of colour `g`. -/
theorem exists_colouring {α β : Type} [DecidableEq β] [Inhabited β] :
    ∀ (D : List β), D.Nodup → ∀ (m : β → Nat) (T : Set α),
      T.encard = ((D.map m).sum : ℕ∞) →
      ∃ f : α → β, (∀ v ∈ T, f v ∈ D) ∧ ∀ d ∈ D, {v | v ∈ T ∧ f v = d}.encard = m d
  | [], _, m, T, hT => by
    refine ⟨fun _ => default, fun v hv => ?_, fun d hd => absurd hd List.not_mem_nil⟩
    simp only [List.map_nil, List.sum_nil, Nat.cast_zero, Set.encard_eq_zero] at hT
    rw [hT] at hv; exact absurd hv (Set.notMem_empty v)
  | d :: D, hD, m, T, hT => by
    obtain ⟨hdD, hDn⟩ := List.nodup_cons.1 hD
    rw [List.map_cons, List.sum_cons, Nat.cast_add] at hT
    obtain ⟨T1, hT1, hc1⟩ := Set.exists_subset_encard_eq (s := T) (k := (m d : ℕ∞))
      (by rw [hT]; exact le_self_add)
    have hfin : T.Finite := Set.finite_of_encard_eq_coe hT
    have hT2 : (T \ T1).encard = ((D.map m).sum : ℕ∞) := by
      have := Set.encard_diff_add_encard_of_subset hT1
      rw [hT, hc1] at this
      have h2 : (T \ T1).encard ≠ ⊤ := (hfin.diff).encard_lt_top.ne
      obtain ⟨x, hx⟩ := ENat.ne_top_iff_exists.1 h2
      rw [← hx] at this ⊢
      have : x + m d = m d + (D.map m).sum := by exact_mod_cast this
      congr 1; omega
    obtain ⟨f', hf'D, hf'⟩ := exists_colouring D hDn m (T \ T1) hT2
    classical
    refine ⟨fun v => if v ∈ T1 then d else f' v, fun v hv => ?_, fun d' hd' => ?_⟩
    · by_cases h1 : v ∈ T1
      · simp [h1]
      · simp only [h1, if_false]; exact List.mem_cons_of_mem _ (hf'D v ⟨hv, h1⟩)
    · rcases List.mem_cons.1 hd' with rfl | hd'
      · have : {v | v ∈ T ∧ (if v ∈ T1 then d' else f' v) = d'} = T1 := by
          ext v
          simp only [Set.mem_setOf_eq]
          constructor
          · rintro ⟨hv, he⟩
            by_contra h1
            rw [if_neg h1] at he
            exact hdD (he ▸ hf'D v ⟨hv, h1⟩)
          · intro h1; exact ⟨hT1 h1, by simp [h1]⟩
        rw [this, hc1]
      · have hne : d' ≠ d := fun h => hdD (h ▸ hd')
        have : {v | v ∈ T ∧ (if v ∈ T1 then d else f' v) = d'} = {v | v ∈ T \ T1 ∧ f' v = d'} := by
          ext v
          simp only [Set.mem_setOf_eq, Set.mem_diff]
          constructor
          · rintro ⟨hv, he⟩
            by_cases h1 : v ∈ T1
            · rw [if_pos h1] at he; exact absurd he.symm hne
            · rw [if_neg h1] at he; exact ⟨⟨hv, h1⟩, he⟩
          · rintro ⟨⟨hv, h1⟩, he⟩; exact ⟨hv, by rw [if_neg h1]; exact he⟩
        rw [this, hf' d' hd']

/-! ## Parts -/

variable {Val K : Type} [DecidableEq K] {q s : Nat}
  {key : Val → K} {cells : List K} {size : K → Option Nat}
  {E : Fin q → K → (Fin s → Bool) → Bool}

/-- A cell is small: finite with at most `L` values. -/
def small (size : K → Option Nat) (L : Nat) (c : K) : Bool :=
  match size c with
  | some k => decide (k ≤ L)
  | none => false

/-- The reading of the free atoms at a value. -/
def readOf (fr : Fin s → Val → Bool) (v : Val) : Fin s → Bool := fun j => fr j v

/-- `fr` gives the small cells the counts `n`. -/
def InPart (key : Val → K) (cells : List K) (size : K → Option Nat) (L : Nat)
    (n : K → (Fin s → Bool) → Nat) (fr : Fin s → Val → Bool) : Prop :=
  ∀ c ∈ cells, small size L c = true → ∀ g,
    {v | key v = c ∧ readOf fr v = g}.encard = n c g

/-- The counts of a small cell add up to its size. -/
def ValidPart (cells : List K) (size : K → Option Nat) (L : Nat) (n : K → (Fin s → Bool) → Nat) :
    Prop :=
  ∀ c ∈ cells, small size L c = true → size c = some (((allG s).map (n c)).sum)

/-- The part `n` of the cell theory. -/
def partTheory (key : Val → K) (cells : List K) (size : K → Option Nat) (L : Nat)
    (E : Fin q → K → (Fin s → Bool) → Bool) (n : K → (Fin s → Bool) → Nat) :
    DataTheory (Fin q) :=
  fun V atom => ∃ (e : V ≃ Val) (fr : Fin s → Val → Bool), InPart key cells size L n fr ∧
    ∀ p v, atom p v ↔ E p (key (e v)) (readOf fr (e v)) = true

/-- The pairs (cell, reading). -/
def pairs (cells : List K) (s : Nat) : List (K × (Fin s → Bool)) :=
  cells.flatMap fun c => (allG s).map fun g => (c, g)

/-- The bound of a pair: its count for a small cell, the cell size otherwise. -/
def pairBound (size : K → Option Nat) (L : Nat) (n : K → (Fin s → Bool) → Nat)
    (cg : K × (Fin s → Bool)) : Option Nat :=
  if small size L cg.1 then some (n cg.1 cg.2) else size cg.1

/-- **The oracle of a part.** -/
def partCard (cells : List K) (size : K → Option Nat) (L : Nat)
    (E : Fin q → K → (Fin s → Bool) → Bool) (n : K → (Fin s → Bool) → Nat)
    (τ : Finset (Fin q)) : Option Nat :=
  osum ((pairs cells s).map fun cg =>
    if vtc E cg.1 cg.2 = τ then pairBound size L n cg else some 0)

theorem mem_pairs {cg : K × (Fin s → Bool)} : cg ∈ pairs cells s ↔ cg.1 ∈ cells := by
  obtain ⟨c, g⟩ := cg
  simp [pairs, mem_allG]

theorem pairs_nodup (hc : cells.Nodup) : (pairs cells s).Nodup := by
  unfold pairs
  rw [List.nodup_flatMap]
  refine ⟨fun c _ => (allG_nodup s).map fun g g' h => by simpa using h, ?_⟩
  refine hc.imp fun {c c'} hne => ?_
  rw [Function.onFun, List.disjoint_left]
  intro x hx hx'
  obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨g', -, he⟩ := List.mem_map.1 hx'
  exact hne (congrArg Prod.fst he).symm

theorem small_size {L : Nat} {c : K} (h : small size L c = true) : ∃ k, size c = some k ∧ k ≤ L := by
  unfold small at h
  split at h
  · rename_i k hk; exact ⟨k, hk, of_decide_eq_true h⟩
  · cases h

theorem not_small_size {L : Nat} {c : K} (h : small size L c = false) :
    size c = none ∨ ∃ k, size c = some k ∧ L < k := by
  unfold small at h
  split at h
  · rename_i k hk
    right; exact ⟨k, hk, by simpa using h⟩
  · rename_i hk
    left; exact hk

/-! ## The cell theory is the union of its parts -/

theorem cellTheory_of_part {L : Nat} {n : K → (Fin s → Bool) → Nat} {V : Type}
    {atom : Fin q → V → Prop} (h : partTheory key cells size L E n V atom) :
    cellTheory key E V atom := by
  obtain ⟨e, fr, -, hat⟩ := h
  exact ⟨e, fr, hat⟩

/-- The counts of a reading. -/
noncomputable def countsOf (key : Val → K) (fr : Fin s → Val → Bool) (c : K) (g : Fin s → Bool) :
    Nat := ({v | key v = c ∧ readOf fr v = g}.encard).toNat

theorem part_of_cellTheory (hc : CellSpec key cells size) (L : Nat) {V : Type}
    {atom : Fin q → V → Prop} (h : cellTheory key E V atom) :
    ∃ fr : Fin s → Val → Bool, ValidPart cells size L (countsOf key fr) ∧
      partTheory key cells size L E (countsOf key fr) V atom := by
  classical
  obtain ⟨e, fr, hat⟩ := h
  have hfib : ∀ c ∈ cells, small size L c = true → ∀ g,
      ({v | key v = c ∧ readOf fr v = g}.encard) = (countsOf key fr c g : ℕ∞) := by
    intro c hc' hs g
    obtain ⟨k, hk, -⟩ := small_size hs
    have hfin : {v | key v = c}.Finite := by
      apply Set.finite_of_encard_eq_coe (k := k)
      rw [hc.size c hc', hk]; rfl
    have : {v | key v = c ∧ readOf fr v = g}.Finite := hfin.subset fun v hv => hv.1
    unfold countsOf
    exact (ENat.coe_toNat this.encard_lt_top.ne).symm
  refine ⟨fr, fun c hc' hs => ?_, e, fr, fun c hc' hs g => hfib c hc' hs g, hat⟩
  obtain ⟨k, hk, -⟩ := small_size hs
  have hsum := encard_sum_fibers (readOf fr) {v | key v = c} (allG_nodup s)
    (fun v _ => mem_allG _)
  rw [hc.size c hc', hk] at hsum
  rw [hk]
  congr 1
  have : ((allG s).map fun g => {v | v ∈ {v | key v = c} ∧ readOf fr v = g}.encard) =
      ((allG s).map (countsOf key fr c)).map (Nat.cast : Nat → ℕ∞) := by
    rw [List.map_map]
    exact List.map_congr_left fun g _ => hfib c hc' hs g
  rw [this, ← Nat.cast_list_sum] at hsum
  simp only [toE] at hsum
  exact_mod_cast hsum

/-! ## Each part has a bounded oracle -/

theorem sum_map_ite_filter' {β : Type} (L : List β) (P : β → Prop) [DecidablePred P]
    (w : β → ℕ∞) :
    (L.map fun c => if P c then w c else 0).sum = ((L.filter fun c => decide (P c)).map w).sum := by
  induction L with
  | nil => rfl
  | cons c L ih => by_cases h : P c <;> simp [h, ih]

theorem toE_partCard {L : Nat} {n : K → (Fin s → Bool) → Nat} (τ : Finset (Fin q)) :
    toE (partCard cells size L E n τ) = (((pairs cells s).filter fun cg =>
      decide (vtc E cg.1 cg.2 = τ)).map fun cg => toE (pairBound size L n cg)).sum := by
  rw [partCard, toE_osum, List.map_map, ← sum_map_ite_filter']
  congr 1
  refine List.map_congr_left fun cg _ => ?_
  simp only [Function.comp]
  split_ifs <;> rfl

theorem vt_part {V : Type} {atom : Fin q → V → Prop} {e : V ≃ Val} {fr : Fin s → Val → Bool}
    (hat : ∀ p v, atom p v ↔ E p (key (e v)) (readOf fr (e v)) = true) (v : V) :
    vt atom v = vtc E (key (e v)) (readOf fr (e v)) := by
  ext p
  rw [mem_vt, hat]
  simp [vtc]

/-- **Each part has a bounded oracle.** -/
theorem oracleSpecB_part (hc : CellSpec key cells size) {B L : Nat}
    (hL : B * (allG s).length ≤ L) {n : K → (Fin s → Bool) → Nat}
    (hv : ValidPart cells size L n) :
    OracleSpecB (partTheory key cells size L E n) (partCard cells size L E n) B := by
  classical
  constructor
  · rintro V atom ⟨e, fr, hin, hat⟩ τ k hk l hl hvt
    let κ : Val → K × (Fin s → Bool) := fun w => (key w, readOf fr w)
    let Lv := l.map e
    have hLv : Lv.Nodup := hl.map e.injective
    let D := (pairs cells s).filter fun cg => decide (vtc E cg.1 cg.2 = τ)
    have hDn : D.Nodup := (pairs_nodup hc.nodup).filter _
    have hcov : ∀ w ∈ Lv, κ w ∈ D := by
      intro w hw
      obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hw
      refine List.mem_filter.2 ⟨mem_pairs.2 (hc.mem _), ?_⟩
      rw [← vt_part hat, hvt v hv']
      simp
    have hlen := length_eq_sum_count κ Lv hDn hcov
    have hcnt : ∀ cg ∈ D, ((Lv.countP fun w => κ w = cg : Nat) : ℕ∞) ≤
        toE (pairBound size L n cg) := by
      intro cg hcg
      have h1 : ((Lv.countP fun w => κ w = cg : Nat) : ℕ∞) ≤ {w | κ w = cg}.encard := by
        rw [List.countP_eq_length_filter]
        exact length_le_encard (hLv.filter _) fun w hw => by simpa using (List.mem_filter.1 hw).2
      refine h1.trans ?_
      obtain ⟨c, g⟩ := cg
      have hcc : c ∈ cells := mem_pairs.1 (List.mem_filter.1 hcg).1
      unfold pairBound
      split_ifs with hs
      · have := hin c hcc hs g
        simp only [toE]
        rw [← this]
        exact le_of_eq (congrArg Set.encard (by ext w; simp [κ]))
      · rw [← hc.size c hcc]
        exact Set.encard_le_encard fun w hw => by
          simp only [Set.mem_setOf_eq, κ, Prod.mk.injEq] at hw ⊢; exact hw.1
    have hsum : ((l.length : Nat) : ℕ∞) ≤ toE (partCard cells size L E n τ) := by
      rw [show l.length = Lv.length from (List.length_map _).symm, hlen, Nat.cast_list_sum,
        List.map_map, toE_partCard]
      exact sum_map_mono fun cg hcg => by simpa using hcnt cg hcg
    rw [hk] at hsum
    simpa [toE] using hsum
  · intro need hB hneed
    -- a colouring of every cell
    have hcol : ∀ c : K, ∃ F : Val → (Fin s → Bool),
        (c ∈ cells → small size L c = true → ∀ g, {v | key v = c ∧ F v = g}.encard = n c g) ∧
        (c ∈ cells → small size L c = false → ∀ g, (B : ℕ∞) ≤ {v | key v = c ∧ F v = g}.encard) := by
      intro c
      by_cases hcc : c ∈ cells
      · cases hs : small size L c
        · -- a large or infinite cell: colour `B · |readings|` of its values
          have hbig : ((B * (allG s).length : Nat) : ℕ∞) ≤ {v | key v = c}.encard := by
            rw [hc.size c hcc]
            rcases not_small_size hs with h | ⟨k, hk, hk'⟩
            · rw [h]; exact le_top
            · rw [hk]; simp only [toE]; exact_mod_cast (hL.trans hk'.le)
          obtain ⟨T, hT, hTc⟩ := Set.exists_subset_encard_eq hbig
          have hsum : T.encard = (((allG s).map fun _ => B).sum : ℕ∞) := by
            rw [hTc]; simp [List.map_const', List.sum_replicate, mul_comm]
          obtain ⟨F, -, hF⟩ := exists_colouring (allG s) (allG_nodup s) (fun _ => B) T hsum
          refine ⟨F, fun _ h => absurd h (by simp), fun _ _ g => ?_⟩
          rw [← hF g (mem_allG g)]
          exact Set.encard_le_encard fun v hv => ⟨hT hv.1, hv.2⟩
        · obtain ⟨k, hk, -⟩ := small_size hs
          have hsum : {v | key v = c}.encard = (((allG s).map (n c)).sum : ℕ∞) := by
            rw [hc.size c hcc, hv c hcc hs]; rfl
          obtain ⟨F, -, hF⟩ := exists_colouring (allG s) (allG_nodup s) (n c) _ hsum
          exact ⟨F, fun _ _ g => hF g (mem_allG g), fun _ h => absurd h (by simp)⟩
      · exact ⟨fun _ => fun _ => false, fun h => absurd h hcc, fun h => absurd h hcc⟩
    choose F hF using hcol
    let fr : Fin s → Val → Bool := fun j v => F (key v) v j
    have hread : ∀ v, readOf fr v = F (key v) v := fun v => rfl
    have hfib : ∀ c g, {v | key v = c ∧ readOf fr v = g} = {v | key v = c ∧ F c v = g} := by
      intro c g; ext v
      simp only [Set.mem_setOf_eq, hread]
      constructor
      · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
      · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
    have hin : InPart key cells size L n fr := fun c hcc hs g => by
      rw [hfib]; exact (hF c).1 hcc hs g
    let atom : Fin q → Val → Prop := fun p v => E p (key v) (readOf fr v) = true
    refine ⟨Val, atom, ⟨Equiv.refl _, fr, hin, fun _ _ => Iff.rfl⟩, fun τ => ?_⟩
    have hvtv : ∀ v, vt atom v = vtc E (key v) (readOf fr v) := fun v =>
      vt_part (e := Equiv.refl Val) (fun _ _ => Iff.rfl) v
    let S := {v | vtc E (key v) (readOf fr v) = τ}
    have hneedE : (need τ : ℕ∞) ≤ toE (partCard cells size L E n τ) := by
      cases h : partCard cells size L E n τ with
      | none => exact le_top
      | some k => simp only [toE]; exact_mod_cast hneed τ k h
    have hle : (need τ : ℕ∞) ≤ S.encard := by
      let D := (pairs cells s).filter fun cg => decide (vtc E cg.1 cg.2 = τ)
      by_cases hall : ∀ cg ∈ D, small size L cg.1 = true
      · have hS := encard_sum_fibers (fun v => (key v, readOf fr v)) S (D := D)
          ((pairs_nodup hc.nodup).filter _) (fun v hv =>
            List.mem_filter.2 ⟨mem_pairs.2 (hc.mem v), decide_eq_true hv⟩)
        have hS' : S.encard = toE (partCard cells size L E n τ) := by
          rw [hS, toE_partCard]
          congr 1
          refine List.map_congr_left fun cg hcg => ?_
          obtain ⟨c, g⟩ := cg
          have hcc : c ∈ cells := mem_pairs.1 (List.mem_filter.1 hcg).1
          have hτ : vtc E c g = τ := by simpa using (List.mem_filter.1 hcg).2
          have hs := hall _ hcg
          simp only [pairBound, hs, if_true, toE]
          rw [← hin c hcc hs g]
          congr 1
          ext v
          simp only [Set.mem_setOf_eq, S, Prod.mk.injEq]
          constructor
          · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨by rw [h1, h2]; exact hτ, h1, h2⟩
        rw [hS']; exact hneedE
      · push Not at hall
        obtain ⟨⟨c, g⟩, hcg, hs⟩ := hall
        have hcc : c ∈ cells := mem_pairs.1 (List.mem_filter.1 hcg).1
        have hτ : vtc E c g = τ := by simpa using (List.mem_filter.1 hcg).2
        have h1 := (hF c).2 hcc (by simpa using hs) g
        refine le_trans (by exact_mod_cast hB τ) (h1.trans (Set.encard_le_encard ?_))
        rintro v ⟨hkv, hfv⟩
        show vtc E (key v) (readOf fr v) = τ
        rw [hread, hkv, hfv, hτ]
    obtain ⟨l, hl, hlen, hmem⟩ := exists_list_of_encard hle
    exact ⟨l, hl, hlen, fun v hv => by rw [hvtv]; exact hmem v hv⟩

end ContextCalculus.SRIQD

#print axioms ContextCalculus.SRIQD.part_of_cellTheory
#print axioms ContextCalculus.SRIQD.oracleSpecB_part
