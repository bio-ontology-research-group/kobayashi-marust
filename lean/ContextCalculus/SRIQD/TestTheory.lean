import ContextCalculus.SRIQD.NormalForm
import Mathlib.Logic.Equiv.Defs

/-!
# A small concrete data theory for tests (stage C4, step 5)

Values are integers, booleans and strings (`Val`). An atom is one of
`int`, `intR lo hi` (the integers between the optional bounds, both
inclusive: a facet restriction of `xsd:integer`, and with `lo = hi` an
integer literal), `bool`, `boolV b` (a boolean literal) and `str`
(strings, without facets or literals). An ontology fixes its atoms by
`spec : Fin q → ASpec`, and `theory spec` admits the value types
isomorphic to `Val` with this reading.

The oracle `card spec` counts per kind and adds:

* integers: all bounds of the atoms lie strictly between `lowZ` and
  `highZ`, so every integer at or below `lowZ` has the value type of
  `lowZ`, and every integer at or above `highZ` that of `highZ`
  (`vtV_low`, `vtV_high`). A value type is unbounded if it is one of
  these two, and otherwise counted in the window between them;
* booleans: counted;
* strings: all strings have one value type, which is unbounded.

`oracleSpec_test`: `card spec` satisfies `OracleSpec` for
`theory spec`.
-/

namespace ContextCalculus.SRIQD.TestTheory

open ContextCalculus.SRIQD

/-- The values. -/
inductive Val where
  | int (z : Int)
  | bool (b : Bool)
  | str (s : String)
deriving DecidableEq, Repr

/-- The atoms. -/
inductive ASpec where
  | int
  | intR (lo hi : Option Int)
  | bool
  | boolV (b : Bool)
  | str
deriving DecidableEq, Repr

/-- The lower bound holds. -/
def geB : Option Int → Int → Bool
  | none, _ => true
  | some l, z => decide (l ≤ z)

/-- The upper bound holds. -/
def leB : Option Int → Int → Bool
  | none, _ => true
  | some h, z => decide (z ≤ h)

/-- The reading of an atom. -/
def semB : ASpec → Val → Bool
  | .int, .int _ => true
  | .intR lo hi, .int z => geB lo z && leB hi z
  | .bool, .bool _ => true
  | .boolV b, .bool b' => b == b'
  | .str, .str _ => true
  | _, _ => false

variable {q : Nat} (spec : Fin q → ASpec)

/-- The value type of a value. -/
def vtV (w : Val) : Finset (Fin q) :=
  Finset.univ.filter fun p => semB (spec p) w = true

/-- The theory: value types isomorphic to `Val` with the reading `semB`. -/
def theory : DataTheory (Fin q) :=
  fun V atom => ∃ e : V ≃ Val, ∀ p v, atom p v ↔ semB (spec p) (e v) = true

/-- All integer bounds of the atoms. -/
def bounds : List Int :=
  (List.finRange q).flatMap fun p => match spec p with
    | .intR lo hi => lo.toList ++ hi.toList
    | _ => []

def lowZ : Int := (bounds spec).foldr min 0 - 1

def highZ : Int := (bounds spec).foldr max 0 + 1

/-- The integers strictly between `lowZ` and `highZ`. -/
def window : List Int :=
  List.map (fun i : Nat => lowZ spec + 1 + (i : Int)) (List.range (highZ spec - lowZ spec - 1).toNat)

def oadd : Option Nat → Option Nat → Option Nat
  | some a, some b => some (a + b)
  | _, _ => none

def cardInt (τ : Finset (Fin q)) : Option Nat :=
  if vtV spec (.int (lowZ spec)) = τ ∨ vtV spec (.int (highZ spec)) = τ then none
  else some ((window spec).filter fun z => decide (vtV spec (.int z) = τ)).length

def cardBool (τ : Finset (Fin q)) : Option Nat :=
  some (([true, false].filter fun b => decide (vtV spec (.bool b) = τ)).length)

def cardStr (τ : Finset (Fin q)) : Option Nat :=
  if vtV spec (.str "") = τ then none else some 0

/-- **The oracle.** -/
def card (τ : Finset (Fin q)) : Option Nat :=
  oadd (oadd (cardInt spec τ) (cardBool spec τ)) (cardStr spec τ)

/-! ## The window -/

theorem foldr_min_le : ∀ (l : List Int), ∀ b ∈ l, l.foldr min 0 ≤ b
  | [], b, h => by simp at h
  | a :: l, b, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (foldr_min_le l b h)

theorem le_foldr_max : ∀ (l : List Int), ∀ b ∈ l, b ≤ l.foldr max 0
  | [], b, h => by simp at h
  | a :: l, b, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (le_foldr_max l b h) (le_max_right _ _)

theorem mem_bounds {p : Fin q} {lo hi : Option Int} (hp : spec p = .intR lo hi) :
    (∀ l ∈ lo, l ∈ bounds spec) ∧ ∀ h ∈ hi, h ∈ bounds spec := by
  refine ⟨fun l hl => ?_, fun h hh => ?_⟩ <;>
    refine List.mem_flatMap.2 ⟨p, List.mem_finRange _, ?_⟩ <;> rw [hp]
  · simp [Option.mem_def.1 hl]
  · simp [Option.mem_def.1 hh]

theorem lowZ_lt {b : Int} (hb : b ∈ bounds spec) : lowZ spec < b := by
  have := foldr_min_le _ b hb
  unfold lowZ
  omega

theorem lt_highZ {b : Int} (hb : b ∈ bounds spec) : b < highZ spec := by
  have := le_foldr_max _ b hb
  unfold highZ
  omega

theorem vtV_low {z : Int} (hz : z ≤ lowZ spec) : vtV spec (.int z) = vtV spec (.int (lowZ spec)) := by
  ext p
  simp only [vtV, Finset.mem_filter, Finset.mem_univ, true_and]
  cases hp : spec p with
  | intR lo hi =>
    obtain ⟨hlo, hhi⟩ := mem_bounds spec hp
    simp only [semB]
    have h1 : geB lo z = geB lo (lowZ spec) := by
      cases lo with
      | none => rfl
      | some l =>
        have := lowZ_lt spec (hlo l rfl)
        simp only [geB, decide_eq_decide]
        omega
    have h2 : leB hi z = leB hi (lowZ spec) := by
      cases hi with
      | none => rfl
      | some h =>
        have := lowZ_lt spec (hhi h rfl)
        simp only [leB, decide_eq_decide]
        omega
    rw [h1, h2]
  | _ => rfl

theorem vtV_high {z : Int} (hz : highZ spec ≤ z) :
    vtV spec (.int z) = vtV spec (.int (highZ spec)) := by
  ext p
  simp only [vtV, Finset.mem_filter, Finset.mem_univ, true_and]
  cases hp : spec p with
  | intR lo hi =>
    obtain ⟨hlo, hhi⟩ := mem_bounds spec hp
    simp only [semB]
    have h1 : geB lo z = geB lo (highZ spec) := by
      cases lo with
      | none => rfl
      | some l =>
        have := lt_highZ spec (hlo l rfl)
        simp only [geB, decide_eq_decide]
        omega
    have h2 : leB hi z = leB hi (highZ spec) := by
      cases hi with
      | none => rfl
      | some h =>
        have := lt_highZ spec (hhi h rfl)
        simp only [leB, decide_eq_decide]
        omega
    rw [h1, h2]
  | _ => rfl

theorem vtV_str (s : String) : vtV spec (.str s) = vtV spec (.str "") := by
  ext p
  simp only [vtV, Finset.mem_filter, Finset.mem_univ, true_and]
  cases spec p <;> rfl

theorem mem_window {z : Int} : z ∈ window spec ↔ lowZ spec < z ∧ z < highZ spec := by
  simp only [window, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro h
    exact ⟨(z - lowZ spec - 1).toNat, by omega, by omega⟩

theorem window_nodup : (window spec).Nodup :=
  (List.nodup_range).map fun i j h => by omega

/-! ## Exact counts -/

theorem oadd_eq_some {a b : Option Nat} {k : Nat} :
    oadd a b = some k ↔ ∃ x y, a = some x ∧ b = some y ∧ k = x + y := by
  cases a <;> cases b <;> simp [oadd, eq_comm]

theorem oadd_eq_none {a b : Option Nat} : oadd a b = none ↔ a = none ∨ b = none := by
  cases a <;> cases b <;> simp [oadd]

/-- A finite count lists exactly the values of the value type. -/
theorem exact_card {τ : Finset (Fin q)} {k : Nat} (h : card spec τ = some k) :
    ∃ L : List Val, L.Nodup ∧ L.length = k ∧ ∀ w, w ∈ L ↔ vtV spec w = τ := by
  obtain ⟨x, ks, hx, h3, rfl⟩ := oadd_eq_some.1 h
  obtain ⟨ki, kb, h1, h2, rfl⟩ := oadd_eq_some.1 hx
  clear hx h
  unfold cardInt at h1
  split_ifs at h1 with hlh
  try simp only [Option.some.injEq] at h1
  unfold cardStr at h3
  split_ifs at h3 with hs
  try simp only [Option.some.injEq] at h3
  simp only [cardBool, Option.some.injEq] at h2
  subst h1 h2 h3
  refine ⟨((window spec).filter fun z => decide (vtV spec (.int z) = τ)).map Val.int ++
    ([true, false].filter fun b => decide (vtV spec (.bool b) = τ)).map Val.bool, ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨((window_nodup spec).filter _).map fun _ _ h => by cases h; rfl,
      (by decide : [true, false].Nodup).filter _ |>.map fun _ _ h => by cases h; rfl, ?_⟩
    intro u hu v hv huv
    subst huv
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hu
    obtain ⟨b, -, hb⟩ := List.mem_map.1 hv
    cases hb
  · simp
  · intro w
    cases w with
    | int z =>
      simp only [List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq,
        Val.int.injEq, reduceCtorEq, and_false, exists_false, or_false]
      constructor
      · rintro ⟨z', ⟨-, h⟩, rfl⟩
        exact h
      · intro hz
        refine ⟨z, ⟨(mem_window spec).2 ⟨?_, ?_⟩, hz⟩, rfl⟩
        · by_contra hle
          exact hlh (Or.inl (by rw [← vtV_low spec (z := z) (by omega)]; exact hz))
        · by_contra hle
          exact hlh (Or.inr (by rw [← vtV_high spec (z := z) (by omega)]; exact hz))
    | bool b =>
      cases b <;> simp
    | str s =>
      simp only [List.mem_append, List.mem_map, reduceCtorEq, and_false, exists_false, or_self,
        false_iff]
      rw [vtV_str]
      exact hs

theorem replicate_inj {i j : Nat}
    (h : String.ofList (List.replicate i 'a') = String.ofList (List.replicate j 'a')) : i = j := by
  have := congrArg String.toList h
  simpa using this

/-- Enough values of the value type, below its count. -/
theorem exists_list (τ : Finset (Fin q)) (N : Nat) (hN : ∀ k, card spec τ = some k → N ≤ k) :
    ∃ L : List Val, L.Nodup ∧ L.length = N ∧ ∀ w ∈ L, vtV spec w = τ := by
  cases hc : card spec τ with
  | some k =>
    obtain ⟨L, hnd, hlen, hmem⟩ := exact_card spec hc
    refine ⟨L.take N, hnd.sublist (List.take_sublist _ _), ?_, fun w hw =>
      (hmem w).1 (List.mem_of_mem_take hw)⟩
    rw [List.length_take, hlen]
    have := hN k hc
    omega
  | none =>
    rcases oadd_eq_none.1 hc with h | h
    · rcases oadd_eq_none.1 h with h | h
      · unfold cardInt at h
        split_ifs at h with hlh
        rcases hlh with hl | hh
        · refine ⟨List.map (fun i : Nat => Val.int (lowZ spec - (i : Int))) (List.range N), List.nodup_range.map
            fun i j h => by simp only [Val.int.injEq] at h; omega, by simp, fun w hw => ?_⟩
          obtain ⟨i, -, rfl⟩ := List.mem_map.1 hw
          rw [vtV_low spec (by omega)]
          exact hl
        · refine ⟨List.map (fun i : Nat => Val.int (highZ spec + (i : Int))) (List.range N), List.nodup_range.map
            fun i j h => by simp only [Val.int.injEq] at h; omega, by simp, fun w hw => ?_⟩
          obtain ⟨i, -, rfl⟩ := List.mem_map.1 hw
          rw [vtV_high spec (by omega)]
          exact hh
      · simp [cardBool] at h
    · unfold cardStr at h
      split_ifs at h with hs
      refine ⟨List.map (fun i : Nat => Val.str (String.ofList (List.replicate i 'a'))) (List.range N),
        List.nodup_range.map fun i j h => replicate_inj (by simpa using h), by simp,
        fun w hw => ?_⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hw
      rw [vtV_str]
      exact hs

/-- **The oracle of the test theory satisfies `OracleSpec`.** -/
theorem oracleSpec_test : OracleSpec (theory spec) (card spec) := by
  constructor
  · rintro V atom ⟨e, he⟩ τ k hk l hl hvt
    obtain ⟨L, -, hlen, hmem⟩ := exact_card spec hk
    have hv : ∀ v, vt atom v = vtV spec (e v) := by
      intro v
      ext p
      rw [mem_vt, he]
      simp [vtV]
    have hsub : l.map e ⊆ L := by
      intro w hw
      obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hw
      exact (hmem _).2 ((hv v) ▸ hvt v hv')
    have := ((hl.map e.injective).subperm hsub).length_le
    rw [List.length_map] at this
    omega
  · intro need hneed
    refine ⟨Val, fun p w => semB (spec p) w = true, ⟨Equiv.refl _, fun _ _ => Iff.rfl⟩,
      fun τ => ?_⟩
    obtain ⟨L, hnd, hlen, hL⟩ := exists_list spec τ (need τ) (hneed τ)
    refine ⟨L, hnd, hlen, fun w hw => ?_⟩
    rw [← hL w hw]
    ext p
    rw [mem_vt]
    simp [vtV]

end ContextCalculus.SRIQD.TestTheory

#print axioms ContextCalculus.SRIQD.TestTheory.oracleSpec_test
