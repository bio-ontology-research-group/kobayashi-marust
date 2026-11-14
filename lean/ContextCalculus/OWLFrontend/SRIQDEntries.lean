import ContextCalculus.OWLFrontend.SRIQDTranslateCorrect

/-!
# The data clauses of one table entry (v1.7.0 stage C4, part D)

`posK e d a` is what the clause on `F_e` asserts at an element with the
data relation `d` and the atom `a` of the entry; `negK e d a` is what the
clause on `W_e` asserts (`entry_dLocal`). Read through a bijection of value
types, `posK` is the OWL extension of the data expression
(`posK_iff_ext`) and `negK` its negation (`negK_iff_not`).
-/

namespace ContextCalculus.OWLFrontend.SHIQD

open ContextCalculus.OWL
open ContextCalculus.SRIQD (dLocal rngSem litSem)

/-- The assertion of the clause on `F_e`. -/
def posK {V : Type} (e : DExpr) (d a : V → Prop) : Prop :=
  match e.kind with
  | 0 => ∃ v, d v ∧ a v
  | 1 => ∀ v, d v → a v
  | 2 => AtLeast e.n fun v => d v ∧ a v
  | _ => AtMost e.n fun v => d v ∧ a v

/-- The assertion of the clause on `W_e`. -/
def negK {V : Type} (e : DExpr) (d a : V → Prop) : Prop :=
  match e.kind with
  | 0 => ∀ v, d v → ¬ a v
  | 1 => ∃ v, d v ∧ ¬ a v
  | 2 => AtMost (e.n - 1) fun v => d v ∧ a v
  | _ => AtLeast (e.n + 1) fun v => d v ∧ a v

variable {V CName Role DProp DAtom : Type}

theorem rngSem_single (atom : DAtom → V → Prop) (j : DAtom) (v : V) :
    rngSem atom [j] [] v ↔ atom j v := by
  simp [rngSem]

theorem rngSem_neg (atom : DAtom → V → Prop) (j : DAtom) (v : V) :
    rngSem atom [] [j] v ↔ ¬ atom j v := by
  simp [rngSem]

/-- The two data clauses of an entry, read at one element. -/
theorem entry_dLocal (atom : DAtom → V → Prop) (c : CName → Prop) (d : DProp → V → Prop)
    (e : DExpr) (F W : CName) (u : DProp) (j : DAtom) :
    (∀ cl ∈ ([] : List (ContextCalculus.SRIQD.Clause CName Role DProp DAtom)) ++
        (match e.kind with
          | 0 => [.dEx F u [j] [], .dAll W u [(j, false)]]
          | 1 => [.dAll F u [(j, true)], .dEx W u [] [j]]
          | 2 => [.dAtLeast F e.n u [j] [], .dAtMost W (e.n - 1) u [j] []]
          | _ => [.dAtMost F e.n u [j] [], .dAtLeast W (e.n + 1) u [j] []]),
        dLocal atom c d cl) ↔
      (c F → posK e (d u) (atom j)) ∧ (c W → negK e (d u) (atom j)) := by
  rcases e with ⟨k, n, p, R⟩
  simp only [List.nil_append]
  match k with
  | 0 =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, dLocal,
      posK, negK, rngSem_single, litSem]
    simp
  | 1 =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, dLocal,
      posK, negK, rngSem_neg, litSem]
    simp
  | 2 =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, dLocal,
      posK, negK, rngSem_single]
    rfl
  | 3 =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, dLocal,
      posK, negK, rngSem_single]
    rfl

theorem entryClauses_dLocal {n m p q : Nat} (atom : Fin q → V → Prop) (c : Fin n → Prop)
    (d : Fin p → V → Prop) (e : DExpr) (F W : Fin n) (u : Fin p) (j : Fin q) :
    (∀ cl ∈ entryClauses (m := m) e F W u j, dLocal atom c d cl) ↔
      (c F → posK e (d u) (atom j)) ∧ (c W → negK e (d u) (atom j)) := by
  have := entry_dLocal (Role := Fin m) atom c d e F W u j
  simp only [List.nil_append] at this
  rw [← this]
  rfl

/-! ## Transport along a bijection -/

theorem atLeast_equiv {W : Type} (e : V ≃ W) (P : W → Prop) (n : Nat) :
    AtLeast n (fun v => P (e v)) ↔ AtLeast n P := by
  constructor
  · rintro ⟨l, hl, hlen, hP⟩
    refine ⟨l.map e, hl.map e.injective, by simp [hlen], fun w hw => ?_⟩
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    exact hP v hv
  · rintro ⟨l, hl, hlen, hP⟩
    refine ⟨l.map e.symm, hl.map e.symm.injective, by simp [hlen], fun v hv => ?_⟩
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
    simpa using hP w hw

theorem atMost_equiv {W : Type} (e : V ≃ W) (P : W → Prop) (n : Nat) :
    AtMost n (fun v => P (e v)) ↔ AtMost n P := by
  constructor
  · intro h l hl hP
    have := h (l.map e.symm) (hl.map e.symm.injective) (fun v hv => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
      simpa using hP w hw)
    simpa using this
  · intro h l hl hP
    have := h (l.map e) (hl.map e.injective) (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
      exact hP v hv)
    simpa using this

/-- `posK` read through a bijection is the OWL extension of the data
expression. -/
theorem posK_iff_ext {DM : DatatypeMap} {D : Type} (I : Interp DM D) (e : DExpr) (x : D)
    (eq : V ≃ DM.Val) (dK aK : V → Prop) (hd : ∀ v, dK v ↔ I.dprop e.p x (eq v))
    (ha : ∀ v, aK v ↔ I.drExt e.R (eq v)) :
    posK e dK aK ↔ I.ext e.toCE x := by
  rcases e with ⟨k, n, p, R⟩
  match k with
  | 0 =>
    simp only [posK, DExpr.toCE, Interp.ext, Interp.dp, hd, ha]
    exact ⟨fun ⟨v, h⟩ => ⟨eq v, h⟩, fun ⟨w, h⟩ => ⟨eq.symm w, by simpa using h⟩⟩
  | 1 =>
    simp only [posK, DExpr.toCE, Interp.ext, Interp.dp, hd, ha]
    exact ⟨fun h w hw => by simpa using h (eq.symm w) (by simpa using hw), fun h v hv => h _ hv⟩
  | 2 =>
    simp only [posK, DExpr.toCE, Interp.ext, Interp.dp, hd, ha]
    exact atLeast_equiv eq (fun w => I.dprop p x w ∧ I.drExt R w) n
  | 3 =>
    simp only [posK, DExpr.toCE, Interp.ext, Interp.dp, hd, ha]
    exact atMost_equiv eq (fun w => I.dprop p x w ∧ I.drExt R w) n

/-- `negK` is the negation of `posK` (for `≥n` with `n ≥ 1`). -/
theorem negK_iff_not (e : DExpr) (he : e.kind = 2 → 1 ≤ e.n) (d a : V → Prop) :
    negK e d a ↔ ¬ posK e d a := by
  rcases e with ⟨k, n, p, R⟩
  match k with
  | 0 => simp only [negK, posK]; constructor
         · rintro h ⟨v, hv, ha⟩; exact h v hv ha
         · intro h v hv ha; exact h ⟨v, hv, ha⟩
  | 1 => simp only [negK, posK]; push Not; exact Iff.rfl
  | 2 =>
    simp only [negK, posK]
    have hn : 1 ≤ n := he rfl
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    constructor
    · intro h h'
      obtain ⟨l, hl, hlen, hP⟩ := h'
      have := h l hl hP
      omega
    · exact SRIQT.atMost_of_not_atLeast
  | 3 =>
    simp only [negK, posK]
    constructor
    · intro h h'
      obtain ⟨l, hl, hlen, hP⟩ := h
      have := h' l hl hP
      omega
    · exact SRIQT.atLeast_of_not_atMost

end ContextCalculus.OWLFrontend.SHIQD
