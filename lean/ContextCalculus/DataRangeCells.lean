import Mathlib.Data.Set.Card
import ContextCalculus.DataValueSingletonElision
import ContextCalculus.DataRangeBoolean
import ContextCalculus.DataRangeStrings

/-!
# Cell realizability (`docs/DATATYPES.md`, "Boolean data ranges and ordered cells")

In a role group with overlapping ordered ranges (decimal tower, one IEEE
width) `frontend/datatypes/vocabulary.rs` cuts the partition into cells
(point cells, integer and kind bands of the decimal tower, IEEE rank
segments) and emits, for every cell `c` and atomic range `R` of the group,
`c → R` or `c ∧ R → ⊥` (`cell_member`), the cover `R → ⋁{c ⊆ R}`, and
`c ∧ c' → ⊥` for distinct cells. Cells are ordinary range names: the
relation generator relates them to the values, and the exhaustion test
gives a finite cell `c` its enumerated cover `c → v₁ ∨ … ∨ vₘ` whenever its
values can be exhausted by the vocabulary values inside it plus the count
bound `N`, that is when `|c| ≤ |V ∩ c| + N`; a cell it cannot enumerate is
reported (`DROPPED`).

All of these clauses have the shape of the oracle's pairwise decision
clauses (`DecisionClauses` of `DataValueSingletonElision`: `dec c d = some
true` emits `c → d`, `some false` emits `c ∧ d → ⊥`), so one decision function
`dec` covers the value relations and the cell relations, and
`DecisionSound den dec` is the oracle's soundness (`cell_member`,
`val_in_range`, the cell disjointness).

The size of a cell is the oracle's arithmetic (`Cell::size`: `1` for a
point, the integer count of an integer band, the rank difference of an
IEEE segment, infinite for a non-integer band of a nonempty open interval).
We state it abstractly as `size : DN → ℕ∞` with the single property the
proof needs, `(den c).encard = size c`, and assume it.

Theorems (labels of one data node are `L : DN → Prop`, as in
`DataRangeBoolean`; `voc` lists the names that can label the node):

* `fresh_values`: a cell with more than `|V ∩ c| + k` values has `k`
  distinct values outside every vocabulary value (pigeonhole);
* `fresh_realizes` / `value_realizes`: a value of the cell outside the
  vocabulary values realizes every label set that carries the cell and no
  value; a fully decided value realizes every label set that carries it;
* `cell_node_realizable`: every label set closed under the clauses that
  carries a cell is realized, either by one of its values or by `N + 1`
  distinct fresh values (the cover handles the small cells);
* `undecidedRealizable_of_cells`: when every data successor of a clause
  model carries a cell and `voc` is the whole vocabulary, this discharges
  the hypothesis `UndecidedRealizable` of `singleton_elision_sound`;
* `laminar_realizable`: the partitions that get no cells (ranges decided
  pairwise nested or disjoint, each with a large residue) are realizable
  too.
-/

namespace ContextCalculus.DataRangeCells
open ContextCalculus.TwoSortedDL ContextCalculus.DataValueSingletonElision
  ContextCalculus.DataRangeBoolean

variable {DN Val : Type}

/-- The decision clauses at one node. -/
def DecisionClausesAt (L : DN → Prop) (dec : DN → DN → Option Bool) : Prop :=
  ∀ v d, L v → (dec v d = some true → L d) ∧ (dec v d = some false → ¬ L d)

theorem decisionClauses_at {Cls OR DR Ind Obj N : Type} (J : Interp Cls OR DR Ind DN Obj N)
    (dec : DN → DN → Option Bool) (h : DecisionClauses J dec) (n : N) :
    DecisionClausesAt (fun d => J.dcon d n) dec :=
  fun v d hv => h v d n hv

/-- Every value denotes exactly its literal. -/
def ValuesSingleton (den : DN → Val → Prop) (isValue : DN → Bool) (lit : DN → Val) : Prop :=
  ∀ v, isValue v = true → ∀ y, den v y → y = lit v

/-- The vocabulary values the oracle places inside `c` (`V ∩ c`). -/
def valuesIn (voc : List DN) (isValue : DN → Bool) (dec : DN → DN → Option Bool) (c : DN) :
    List DN :=
  voc.filter (fun v => isValue v && dec v c == some true)

/-- `y` is none of the vocabulary values. -/
def Fresh (den : DN → Val → Prop) (voc : List DN) (isValue : DN → Bool) (y : Val) : Prop :=
  ∀ v ∈ voc, isValue v = true → ¬ den v y

section Fresh
variable (den : DN → Val → Prop) (voc : List DN) (isValue : DN → Bool) (lit : DN → Val)
  (dec : DN → DN → Option Bool)

theorem encard_lits_le (vs : List DN) :
    {y | ∃ v ∈ vs, y = lit v}.encard ≤ vs.length := by
  have : {y | ∃ v ∈ vs, y = lit v} = (fun i : Fin vs.length => lit (vs.get i)) '' Set.univ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.image_univ, Set.mem_range]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hv
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, List.get_mem _ _, rfl⟩
  rw [this]
  refine (Set.encard_image_le _ _).trans ?_
  rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]

/-- `k ≤ |S|` gives `k` distinct elements of `S`. -/
theorem atLeast_of_encard {S : Set Val} {k : Nat} (h : (k : ℕ∞) ≤ S.encard) :
    AtLeast k (fun y => y ∈ S) := by
  cases k with
  | zero => exact AtLeast.zero _
  | succ k =>
    obtain ⟨t, hts, htk⟩ := Set.exists_subset_encard_eq h
    have hne : t.Nonempty := by
      rw [← Set.encard_pos, htk]; exact_mod_cast Nat.succ_pos k
    obtain ⟨y₀, _⟩ := hne
    haveI : Nonempty Val := ⟨y₀⟩
    obtain ⟨f, hf, hinj⟩ := (Set.finite_univ (α := Fin (k + 1))).exists_injOn_of_encard_le
      (t := t) (by rw [htk, Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin])
    exact ⟨f, fun i j hij => hinj (Set.mem_univ _) (Set.mem_univ _) hij,
      fun i => hts (hf (Set.mem_univ i))⟩

/-- Pigeonhole: if every vocabulary value that meets `S` is in the list
`vs`, and `S` has at least `|vs| + k` elements, then `S` has `k` distinct
elements that are none of the vocabulary values. -/
theorem fresh_of_encard (hsing : ValuesSingleton den isValue lit) (S : Set Val) (vs : List DN)
    (hvs : ∀ v ∈ voc, isValue v = true → ∀ y ∈ S, den v y → v ∈ vs)
    (k : Nat) (hbig : (vs.length + k : ℕ∞) ≤ S.encard) :
    AtLeast k (fun y => y ∈ S ∧ Fresh den voc isValue y) := by
  let Tset : Set Val := {y | ∃ v ∈ vs, y = lit v}
  have hT : Tset.encard ≤ vs.length := encard_lits_le lit vs
  have hk : (k : ℕ∞) ≤ (S \ Tset).encard := by
    have h1 := Set.encard_le_encard_diff_add_encard S Tset
    have h2 : ((vs.length : ℕ∞) + k) ≤ (S \ Tset).encard + vs.length :=
      hbig.trans (h1.trans (add_le_add le_rfl hT))
    rw [add_comm] at h2
    exact (ENat.add_le_add_iff_right (ENat.coe_ne_top _)).1 h2
  refine AtLeast.mono ?_ (atLeast_of_encard hk)
  intro y ⟨hS, hnT⟩
  exact ⟨hS, fun v hv hval hvy => hnT ⟨v, hvs v hv hval y hS hvy, hsing v hval y hvy⟩⟩

/-- **Fresh values.** If the cell `c` has at least `|V ∩ c| + k` values, then
it has `k` distinct values that are none of the vocabulary values. -/
theorem fresh_values (hsound : DecisionSound den dec) (hsing : ValuesSingleton den isValue lit)
    (c : DN) (hvdec : ∀ v ∈ voc, isValue v = true → (dec v c).isSome)
    (k : Nat) (hbig : ((valuesIn voc isValue dec c).length + k : ℕ∞) ≤ {y | den c y}.encard) :
    AtLeast k (fun y => den c y ∧ Fresh den voc isValue y) := by
  refine fresh_of_encard den voc isValue lit hsing {y | den c y} _ ?_ k hbig
  intro v hv hval y hc hvy
  cases hd : dec v c with
  | none => have := hvdec v hv hval; rw [hd] at this; exact absurd this (by decide)
  | some b =>
    cases b with
    | true => simp [valuesIn, List.mem_filter, hv, hval, hd]
    | false => exact absurd hc ((hsound v c y hvy).2 hd)

end Fresh

/-! ## Realizing one label set -/

section Realize
variable (den : DN → Val → Prop) (voc : List DN) (isValue : DN → Bool) (lit : DN → Val)
  (dec : DN → DN → Option Bool) (defs : DN → Option (BDef DN))

/-- A fresh value of the cell realizes the atomic labels of every label set
that carries the cell and no vocabulary value. -/
theorem fresh_realizes (hsound : DecisionSound den dec) (c : DN)
    (hcdec : ∀ d ∈ voc, defs d = none → isValue d = false → d = c ∨ (dec c d).isSome)
    (L : DN → Prop) (hLd : DecisionClausesAt L dec) (hLc : L c)
    (hnoval : ∀ v ∈ voc, isValue v = true → ¬ L v)
    (y : Val) (hyc : den c y) (hyf : Fresh den voc isValue y) :
    ∀ d ∈ voc, defs d = none → (L d ↔ den d y) := by
  intro d hd hdef
  cases hval : isValue d with
  | true => exact ⟨fun h => absurd h (hnoval d hd hval), fun h => absurd h (hyf d hd hval)⟩
  | false =>
    rcases hcdec d hd hdef hval with rfl | hs
    · exact ⟨fun _ => hyc, fun _ => hLc⟩
    · cases hb : dec c d with
      | none => rw [hb] at hs; exact absurd hs (by decide)
      | some b =>
        cases b with
        | true => exact ⟨fun _ => (hsound c d y hyc).1 hb, fun _ => (hLd c d hLc).1 hb⟩
        | false =>
          exact ⟨fun h => absurd h ((hLd c d hLc).2 hb), fun h => absurd h ((hsound c d y hyc).2 hb)⟩

/-- A value decided against every atomic name realizes the atomic labels of
every label set that carries it. -/
theorem value_realizes (hsound : DecisionSound den dec) (hlit : ValuesDenote den isValue lit)
    (v : DN) (hval : isValue v = true)
    (hvdec : ∀ d ∈ voc, defs d = none → d = v ∨ (dec v d).isSome)
    (L : DN → Prop) (hLd : DecisionClausesAt L dec) (hLv : L v) :
    ∀ d ∈ voc, defs d = none → (L d ↔ den d (lit v)) := by
  intro d hd hdef
  have hden := hlit v hval
  rcases hvdec d hd hdef with rfl | hs
  · exact ⟨fun _ => hden, fun _ => hLv⟩
  · cases hb : dec v d with
    | none => rw [hb] at hs; exact absurd hs (by decide)
    | some b =>
      cases b with
      | true => exact ⟨fun _ => (hsound v d _ hden).1 hb, fun _ => (hLd v d hLv).1 hb⟩
      | false =>
        exact ⟨fun h => absurd h ((hLd v d hLv).2 hb), fun h => absurd h ((hsound v d _ hden).2 hb)⟩

/-- Atomic realization extends to the Boolean names of a vocabulary closed
under operands (`DataRangeBoolean.labels_agree`). -/
theorem realize_boolean (rank : DN → Nat) (hr : Ranked defs rank)
    (hden : ∀ y, DefSatAt defs (fun d => den d y))
    (hclosed : ∀ d b, d ∈ voc → defs d = some b → ∀ a ∈ b.names, a ∈ voc)
    (L : DN → Prop) (hL : ClausesAt defs L) (y : Val)
    (hatom : ∀ d ∈ voc, defs d = none → (L d ↔ den d y)) : ∀ d ∈ voc, L d ↔ den d y :=
  labels_agree defs rank hr (· ∈ voc) hclosed ((clausesAt_iff defs L).1 hL) (hden y) hatom

/-- What the frontend guarantees of a cell `c` (with the oracle's
arithmetic `size` and enumerated cover `enum c`). -/
structure CellSpec (size : DN → ℕ∞) (enum : DN → List DN) (c : DN) : Prop where
  mem : c ∈ voc
  atomic : defs c = none
  /-- `cell_member` decides the cell against every atomic name that can label
  the node (the group's ranges, the other cells, the other partitions). -/
  decided : ∀ d ∈ voc, defs d = none → isValue d = false → d = c ∨ (dec c d).isSome
  /-- The oracle's arithmetic (assumed). -/
  size_eq : {y | den c y}.encard = size c
  /-- The enumerated cover lists vocabulary values. -/
  enum_vals : ∀ v ∈ enum c, v ∈ voc ∧ isValue v = true

/-- The enumerated cover clause `c → ⋁ enum c` at a node, emitted when the
cell can be exhausted (`|c| ≤ |V ∩ c| + N`). -/
def CoverAt (size : DN → ℕ∞) (enum : DN → List DN) (N : Nat) (c : DN) (L : DN → Prop) : Prop :=
  L c → size c ≤ ((valuesIn voc isValue dec c).length + N : ℕ∞) → ∃ v ∈ enum c, L v

/-- **Cell realizability.** A label set closed under the clauses that
carries a cell is realized: if it carries a value, by that value; otherwise
by `N + 1` distinct values that are none of the vocabulary values (the cover
has excluded the small cells). Values are decided against every atomic name
of the vocabulary (the decided fragment). -/
theorem cell_node_realizable (rank : DN → Nat) (hr : Ranked defs rank)
    (hden : ∀ y, DefSatAt defs (fun d => den d y))
    (hclosed : ∀ d b, d ∈ voc → defs d = some b → ∀ a ∈ b.names, a ∈ voc)
    (hsound : DecisionSound den dec) (hlit : ValuesDenote den isValue lit)
    (hsing : ValuesSingleton den isValue lit)
    (hvdec : ∀ v ∈ voc, isValue v = true → ∀ d ∈ voc, defs d = none → d = v ∨ (dec v d).isSome)
    (size : DN → ℕ∞) (enum : DN → List DN) (N : Nat) (c : DN)
    (hc : CellSpec den voc isValue dec defs size enum c)
    (L : DN → Prop) (hL : ClausesAt defs L) (hLd : DecisionClausesAt L dec) (hLc : L c)
    (hcover : CoverAt voc isValue dec size enum N c L) :
    (∃ v ∈ voc, isValue v = true ∧ L v ∧ ∀ d ∈ voc, L d ↔ den d (lit v)) ∨
    ((∀ v ∈ voc, isValue v = true → ¬ L v) ∧
      AtLeast (N + 1) (fun y => (∀ d ∈ voc, L d ↔ den d y) ∧ Fresh den voc isValue y)) := by
  by_cases hv : ∃ v ∈ voc, isValue v = true ∧ L v
  · obtain ⟨v, hvv, hval, hLv⟩ := hv
    refine Or.inl ⟨v, hvv, hval, hLv, ?_⟩
    exact realize_boolean den voc defs rank hr hden hclosed L hL (lit v)
      (value_realizes den voc isValue lit dec defs hsound hlit v hval (hvdec v hvv hval) L hLd hLv)
  · have hnoval : ∀ v ∈ voc, isValue v = true → ¬ L v := fun v hvv hval hLv => hv ⟨v, hvv, hval, hLv⟩
    have hcv : isValue c = false := by
      cases h : isValue c with
      | false => rfl
      | true => exact absurd hLc (hnoval c hc.mem h)
    have hlarge : ((valuesIn voc isValue dec c).length + N : ℕ∞) < size c := by
      refine lt_of_not_ge fun hle => ?_
      obtain ⟨v, hve, hLv⟩ := hcover hLc hle
      exact hnoval v (hc.enum_vals v hve).1 (hc.enum_vals v hve).2 hLv
    have hbig : ((valuesIn voc isValue dec c).length + (N + 1 : Nat) : ℕ∞) ≤ {y | den c y}.encard := by
      rw [hc.size_eq, Nat.cast_add, Nat.cast_one, ← add_assoc]
      exact (ENat.add_one_le_iff (by rw [← Nat.cast_add]; exact ENat.coe_ne_top _)).2 hlarge
    have hcvdec : ∀ v ∈ voc, isValue v = true → (dec v c).isSome := by
      intro v hvv hval
      rcases hvdec v hvv hval c hc.mem hc.atomic with rfl | h
      · rw [hval] at hcv; exact absurd hcv (by decide)
      · exact h
    refine Or.inr ⟨hnoval, AtLeast.mono ?_ (fresh_values den voc isValue lit dec hsound hsing c
      hcvdec (N + 1) hbig)⟩
    intro y ⟨hyc, hyf⟩
    exact ⟨realize_boolean den voc defs rank hr hden hclosed L hL y
      (fresh_realizes den voc isValue dec defs hsound c hc.decided L hLd hLc hnoval y hyc hyf), hyf⟩

end Realize

/-! ## Partitions without cells (`laminar_with_large_residues`)

`partition_cells` emits no cells for a partition whose ranges `rs` the
oracle decides pairwise nested or disjoint and in which every range `R` has
a large cell (`≥ 2^62` values) inside `R` and outside every range strictly
inside it. We state the residue abstractly as a set and its size as a bound
on `encard`. -/

section Laminar
variable (den : DN → Val → Prop) (voc : List DN) (isValue : DN → Bool) (lit : DN → Val)
  (dec : DN → DN → Option Bool) (defs : DN → Option (BDef DN))

/-- The residue of `R`: values of `R` outside every range of `rs` strictly
inside `R` (`decided(inner, outer) && !decided(outer, inner)`). -/
def residue (rs : List DN) (R : DN) : Set Val :=
  {y | den R y ∧ ∀ R' ∈ rs, dec R' R = some true → dec R R' ≠ some true → ¬ den R' y}

/-- Among the ranges of a label set whose members are pairwise nested,
one is contained in all of them. -/
theorem exists_least (hsound : DecisionSound den dec) (L : DN → Prop) :
    ∀ (rs : List DN), (∀ a ∈ rs, ∀ b ∈ rs, L a → L b → dec a b = some true ∨ dec b a = some true) →
    (∃ R ∈ rs, L R) →
    ∃ R ∈ rs, L R ∧ ∀ R' ∈ rs, L R' → ∀ y, den R y → den R' y
  | [], _, ⟨_, h, _⟩ => absurd h (by simp)
  | a :: rs, hpair, hex => by
    by_cases hrest : ∃ R ∈ rs, L R
    · obtain ⟨R, hR, hLR, hmin⟩ := exists_least hsound L rs
        (fun x hx y hy => hpair x (by simp [hx]) y (by simp [hy])) hrest
      by_cases hLa : L a
      · rcases hpair a (by simp) R (by simp [hR]) hLa hLR with h | h
        · refine ⟨a, by simp, hLa, fun R' hR' hLR' y hy => ?_⟩
          have hyR := (hsound a R y hy).1 h
          rcases List.mem_cons.1 hR' with rfl | hR'
          · exact hy
          · exact hmin R' hR' hLR' y hyR
        · refine ⟨R, by simp [hR], hLR, fun R' hR' hLR' y hy => ?_⟩
          rcases List.mem_cons.1 hR' with rfl | hR'
          · exact (hsound R R' y hy).1 h
          · exact hmin R' hR' hLR' y hy
      · refine ⟨R, by simp [hR], hLR, fun R' hR' hLR' y hy => ?_⟩
        rcases List.mem_cons.1 hR' with rfl | hR'
        · exact absurd hLR' hLa
        · exact hmin R' hR' hLR' y hy
    · obtain ⟨R, hR, hLR⟩ := hex
      have hRa : R = a := by
        rcases List.mem_cons.1 hR with h | h
        · exact h
        · exact absurd ⟨R, h, hLR⟩ hrest
      subst hRa
      refine ⟨R, by simp, hLR, fun R' hR' hLR' y hy => ?_⟩
      rcases List.mem_cons.1 hR' with rfl | hR'
      · exact hy
      · exact absurd ⟨R', hR', hLR'⟩ hrest

/-- **Laminar partitions are realizable.** Let the ranges `rs` of the
partition be decided pairwise nested or disjoint, every range decided
against the atomic non-value names outside `rs`, and every residue hold at
least `|V| + k` values. Then a label set closed under the clauses that
carries a range of `rs` and no value has `k` distinct fresh realizers. -/
theorem laminar_realizable (rank : DN → Nat) (hr : Ranked defs rank)
    (hden : ∀ y, DefSatAt defs (fun d => den d y))
    (hclosed : ∀ d b, d ∈ voc → defs d = some b → ∀ a ∈ b.names, a ∈ voc)
    (hsound : DecisionSound den dec) (hsing : ValuesSingleton den isValue lit)
    (rs : List DN)
    (hpair : ∀ a ∈ rs, ∀ b ∈ rs, dec a b = some true ∨ dec b a = some true ∨ dec a b = some false)
    (hout : ∀ R ∈ rs, ∀ d ∈ voc, defs d = none → isValue d = false → d ∉ rs → (dec R d).isSome)
    (k : Nat)
    (hres : ∀ R ∈ rs, ((voc.filter isValue).length + k : ℕ∞) ≤ (residue den dec rs R).encard)
    (L : DN → Prop) (hL : ClausesAt defs L) (hLd : DecisionClausesAt L dec)
    (hrange : ∃ R ∈ rs, L R) (hnoval : ∀ v ∈ voc, isValue v = true → ¬ L v) :
    AtLeast k (fun y => (∀ d ∈ voc, L d ↔ den d y) ∧ Fresh den voc isValue y) := by
  have hnested : ∀ a ∈ rs, ∀ b ∈ rs, L a → L b → dec a b = some true ∨ dec b a = some true := by
    intro a ha b hb hLa hLb
    rcases hpair a ha b hb with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd hLb ((hLd a b hLa).2 h)
  obtain ⟨R, hR, hLR, hmin⟩ := exists_least den dec hsound L rs hnested hrange
  have hfresh := fresh_of_encard den voc isValue lit hsing (residue den dec rs R)
    (voc.filter isValue) (fun v hv hval _ _ _ => List.mem_filter.2 ⟨hv, hval⟩) k (hres R hR)
  refine AtLeast.mono ?_ hfresh
  intro y ⟨⟨hyR, hyin⟩, hyf⟩
  refine ⟨realize_boolean den voc defs rank hr hden hclosed L hL y ?_, hyf⟩
  intro d hd hdef
  cases hval : isValue d with
  | true => exact ⟨fun h => absurd h (hnoval d hd hval), fun h => absurd h (hyf d hd hval)⟩
  | false =>
    by_cases hdrs : d ∈ rs
    · by_cases hLd' : L d
      · exact ⟨fun _ => hmin d hdrs hLd' y hyR, fun _ => hLd'⟩
      · refine ⟨fun h => absurd h hLd', fun hyd => ?_⟩
        rcases hpair R hR d hdrs with h | h | h
        · exact absurd ((hLd R d hLR).1 h) hLd'
        · by_cases h' : dec R d = some true
          · exact absurd ((hLd R d hLR).1 h') hLd'
          · exact absurd hyd (hyin d hdrs h h')
        · exact absurd hyd ((hsound R d y hyR).2 h)
    · have hs := hout R hR d hd hdef hval hdrs
      cases hb : dec R d with
      | none => rw [hb] at hs; exact absurd hs (by decide)
      | some b =>
        cases b with
        | true => exact ⟨fun _ => (hsound R d y hyR).1 hb, fun _ => (hLd R d hLR).1 hb⟩
        | false =>
          exact ⟨fun h => absurd h ((hLd R d hLR).2 hb), fun h => absurd h ((hsound R d y hyR).2 hb)⟩

end Laminar

/-! ## Discharging `UndecidedRealizable` -/

/-- **`UndecidedRealizable` for cell vocabularies.** Let `voc` be the whole
vocabulary, every value fully decided (`fullyDecided`, the decided
fragment), and every data successor of the clause model `J` carry a cell
(the range covers put one on every node with a range of the partition).
Then the undecided successors are realizable, as `singleton_elision_sound`
assumes. -/
theorem undecidedRealizable_of_cells [DecidableEq DN] [Nonempty Val]
    {Cls OR DR Ind Obj N : Type} (J : Interp Cls OR DR Ind DN Obj N)
    (den : DN → Val → Prop) (voc : List DN) (hvoc : ∀ d, d ∈ voc) (isValue : DN → Bool)
    (lit : DN → Val) (dec : DN → DN → Option Bool) (defs : DN → Option (BDef DN))
    (rank : DN → Nat) (hr : Ranked defs rank) (hden : ∀ y, DefSatAt defs (fun d => den d y))
    (hsound : DecisionSound den dec) (hlit : ValuesDenote den isValue lit)
    (hsing : ValuesSingleton den isValue lit)
    (hvals : ∀ v, isValue v = true → fullyDecided voc isValue dec v = true)
    (size : DN → ℕ∞) (enum : DN → List DN) (Nb : Nat)
    (hJdef : ∀ n, ClausesAt defs (fun d => J.dcon d n)) (hJdec : DecisionClauses J dec)
    (hcells : ∀ u x n, J.drole u x n → ∃ c, CellSpec den voc isValue dec defs size enum c ∧
      J.dcon c n ∧ CoverAt voc isValue dec size enum Nb c (fun d => J.dcon d n)) :
    ∃ ρ₀ : N → Val, UndecidedRealizable J den voc isValue dec ρ₀ := by
  classical
  refine ⟨fun n => if h : ∃ y, ∀ d, J.dcon d n ↔ den d y then Classical.choose h
    else Classical.arbitrary Val, ?_⟩
  intro u x n hn hund
  have hex : ∃ y, ∀ d, J.dcon d n ↔ den d y := by
    obtain ⟨c, hc, hcn, hcov⟩ := hcells u x n hn
    have hvdec : ∀ v ∈ voc, isValue v = true → ∀ d ∈ voc, defs d = none →
        d = v ∨ (dec v d).isSome := by
      intro v _ hval d _ _
      rcases (fullyDecided_spec hvoc (hvals v hval)).2 d with h | ⟨b, hb⟩
      · exact Or.inl h
      · exact Or.inr (by rw [hb]; rfl)
    rcases cell_node_realizable den voc isValue lit dec defs rank hr hden
        (fun _ _ _ _ a _ => hvoc a) hsound hlit hsing hvdec size enum Nb c hc
        (fun d => J.dcon d n) (hJdef n) (decisionClauses_at J dec hJdec n) hcn hcov with
      ⟨v, _, hval, hLv, _⟩ | ⟨_, hat⟩
    · exact absurd ⟨v, hvals v hval, hLv⟩ hund
    · obtain ⟨f, _, hp⟩ := hat
      exact ⟨f 0, fun d => (hp 0).1 d (hvoc d)⟩
  intro d
  simp only [dif_pos hex]
  exact Classical.choose_spec hex d

/-- **Composition.** `UndecidedRealizable` holds as soon as every undecided
data successor has some value with exactly its labels; the per-node
theorems (`cell_node_realizable` for nodes with a cell, `laminar_realizable`
with `string_residue_infinite` for the string chain and the other laminar
partitions, `value_realizes` for nodes with a value) supply such values, so
a vocabulary that mixes families is covered node by node. -/
theorem undecidedRealizable_of_realizers [DecidableEq DN] [Nonempty Val]
    {Cls OR DR Ind Obj N : Type} (J : Interp Cls OR DR Ind DN Obj N)
    (den : DN → Val → Prop) (voc : List DN) (isValue : DN → Bool) (dec : DN → DN → Option Bool)
    (h : ∀ u x n, J.drole u x n → Undecided J voc isValue dec n →
      ∃ y, ∀ d, J.dcon d n ↔ den d y) :
    ∃ ρ₀ : N → Val, UndecidedRealizable J den voc isValue dec ρ₀ := by
  classical
  refine ⟨fun n => if h : ∃ y, ∀ d, J.dcon d n ↔ den d y then Classical.choose h
    else Classical.arbitrary Val, ?_⟩
  intro u x n hn hund d
  have hex := h u x n hn hund
  simp only [dif_pos hex]
  exact Classical.choose_spec hex d

/-! ## The OWL reading satisfies the cell clauses -/

/-- **`O ⇒ S` for the cell clauses.** With the oracle's covers sound (every
value of a range lies in one of its cells, every value of an enumerated
cell is one of the listed values), the datatype map satisfies at every value
the decision clauses (cell membership, cell disjointness, value relations),
the range covers and the enumerated covers. -/
theorem owl_satisfies_cell_clauses (den : DN → Val → Prop) (voc : List DN) (isValue : DN → Bool)
    (dec : DN → DN → Option Bool) (hsound : DecisionSound den dec)
    (cover : DN → List DN) (hcover : ∀ R y, den R y → ∃ c ∈ cover R, den c y)
    (size : DN → ℕ∞) (enum : DN → List DN) (N : Nat)
    (henum : ∀ c, size c ≤ ((valuesIn voc isValue dec c).length + N : ℕ∞) →
      ∀ y, den c y → ∃ v ∈ enum c, den v y) (y : Val) :
    DecisionClausesAt (fun d => den d y) dec ∧
    (∀ R, den R y → ∃ c ∈ cover R, den c y) ∧
    (∀ c, CoverAt voc isValue dec size enum N c (fun d => den d y)) :=
  ⟨fun v d hv => hsound v d y hv, fun R h => hcover R y h, fun c hc hs => henum c hs y hc⟩

/-! ## The string chain is a laminar partition with infinite residues -/

/-- **String residues are infinite.** For every type `a` of the string chain
and any list `rs` of the twelve datatypes, the residue of `a` (values of `a`
outside every type the oracle places strictly inside `a`) is infinite, so
the hypothesis `hres` of `laminar_realizable` holds for every finite
vocabulary and count bound. The pairwise hypothesis `hpair` holds because
`oracleDec` decides every pair of chain types nested. -/
theorem string_residue_infinite {T : Type} (rs : List DataRangeStrings.SName)
    (a : DataRangeStrings.SName) (ha : (DataRangeStrings.chainRank a).isSome = true) :
    (residue (DataRangeStrings.den (T := T)) DataRangeStrings.oracleDec rs a).encard = ⊤ := by
  refine Set.Infinite.encard_eq (Set.infinite_of_injective_forall_mem
    (DataRangeStrings.stepVal_injective (T := T) a) fun n => ?_)
  exact ⟨(DataRangeStrings.step_family a ha n).1, fun b _ hba hab =>
    DataRangeStrings.step_avoids_inner a b ha hba hab n⟩

theorem string_chain_pairwise (a b : DataRangeStrings.SName)
    (ha : (DataRangeStrings.chainRank a).isSome = true)
    (hb : (DataRangeStrings.chainRank b).isSome = true) :
    DataRangeStrings.oracleDec a b = some true ∨ DataRangeStrings.oracleDec b a = some true := by
  cases a <;> cases b <;> simp [DataRangeStrings.chainRank, DataRangeStrings.oracleDec] at ha hb ⊢

end ContextCalculus.DataRangeCells
