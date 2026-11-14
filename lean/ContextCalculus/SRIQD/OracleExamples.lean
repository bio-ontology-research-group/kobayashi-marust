import ContextCalculus.SRIQD.Stars
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases

/-!
# Both halves of `OracleSpec` are needed (stage C4)

`entailsSub_iff_dstar` assumes `OracleSpec`: (upper) and (lower) with
one admissible pair for all value types at once. Two small theories show
that dropping either half breaks the characterisation. Names are `Fin 3`
(`A = 0`, `T = 1`, `X = 2`), one role, one data property `u = 0`.

* `thA` admits three values, all booleans (one atom `b = 0`), while
  `cardA` says two. (lower) holds (`lower_thA`), (upper) does not.
  `A ⊑ ≥3 u.b` has a model, so `A ⊑ X` fails, but no good root record
  contains `A` (`not_iff_A`).
* `thB` admits two values of value type `{p₀}` or two of value type
  `{p₁}`, never both kinds; `cardB` says two for each. (upper) holds
  (`upper_thB`), and (lower) holds for one value type at a time
  (`lower_one_thB`), but not for two at once. `A ⊑ ∃u.p₀`,
  `A ⊑ ∃u.p₁` make `A` unsatisfiable, so `A ⊑ X`, but a good root record
  contains `A` and not `X` (`not_iff_B`).
-/

namespace ContextCalculus.SRIQD.OracleExamples

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQD

/-! ## Without (upper) -/

/-- Three values, all satisfying the one atom. -/
def thA : DataTheory (Fin 1) := fun V atom => ∃ _ : V ≃ Fin 3, ∀ p v, atom p v

/-- Two values of value type `{b}`, none of the empty one. -/
def cardA (τ : Finset (Fin 1)) : Option Nat := if τ = Finset.univ then some 2 else some 0

/-- `⊤ ⊑ T`, `A ⊑ ≥3 u.b`. -/
def OA : Ontology (Fin 3) (Fin 1) (Fin 1) (Fin 1) := [.obj (.gci [] [1]), .dAtLeast 0 3 0 [0] []]

theorem lower_thA : ∀ need : Finset (Fin 1) → Nat, (∀ τ k, cardA τ = some k → need τ ≤ k) →
    ∃ (V : Type) (atom : Fin 1 → V → Prop), thA V atom ∧
      ∀ τ, ∃ l : List V, l.Nodup ∧ l.length = need τ ∧ ∀ v ∈ l, vt atom v = τ := by
  intro need hneed
  refine ⟨Fin 3, fun _ _ => True, ⟨Equiv.refl _, fun _ _ => trivial⟩, fun τ => ?_⟩
  have hvt : ∀ v : Fin 3, vt (fun (_ : Fin 1) (_ : Fin 3) => True) v = Finset.univ := by
    intro v; ext p; rw [mem_vt]; exact iff_of_true trivial (Finset.mem_univ p)
  by_cases hτ : τ = Finset.univ
  · subst hτ
    have h2 := hneed Finset.univ 2 (by simp [cardA])
    refine ⟨(List.finRange 3).take (need Finset.univ),
      (List.nodup_finRange 3).sublist (List.take_sublist _ _), ?_, fun v _ => hvt v⟩
    simp only [List.length_take, List.length_finRange]
    omega
  · have h0 := hneed τ 0 (by rw [cardA, if_neg hτ])
    exact ⟨[], List.nodup_nil, by rw [List.length_nil]; omega, by simp⟩

/-- **(upper) is needed.** -/
theorem not_iff_A : ¬ (EntailsSub thA OA 0 2 ↔ ∀ t, DGood OA cardA (t, none) → 0 ∈ t → 2 ∈ t) := by
  intro h
  have hR : ∀ t, DGood OA cardA (t, none) → (0 : Fin 3) ∈ t → (2 : Fin 3) ∈ t := by
    rintro t ⟨G, hG, hS⟩ h0
    obtain ⟨C, Dn, ⟨-, hok⟩, -⟩ := hS _ hG
    have h3 := hok.atLeast 0 3 0 [0] [] (by simp [OA]) h0
    have h2 := hok.card Finset.univ 2 (by simp [cardA])
    have hle : dcnt Dn 0 [0] [] ≤ tcnt Dn Finset.univ := by
      unfold dcnt tcnt
      refine List.countP_mono_left fun e _ he => ?_
      have := (of_decide_eq_true he).2.1 0 List.mem_cons_self
      refine decide_eq_true (Finset.eq_univ_of_forall fun p => ?_)
      rwa [Subsingleton.elim p 0]
    omega
  have hE := h.2 hR
  let I : DInterp Unit (Fin 3) (Fin 3) (Fin 1) (Fin 1) :=
    { c := fun a _ => a ≠ 2, r := fun _ _ _ => False, d := fun _ _ _ => True }
  have hm : models (fun _ _ => True) I OA := by
    intro cl hcl
    simp only [OA, List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl
    · intro x _
      exact ⟨1, by simp, by simp [I]⟩
    · intro x _
      exact ⟨[0, 1, 2], by decide, rfl, fun v _ => ⟨trivial, fun _ _ => trivial, by simp⟩⟩
  have := hE Unit (Fin 3) (fun _ _ => True) ⟨Equiv.refl _, fun _ _ => trivial⟩ I hm () (by simp [I])
  exact this rfl

/-! ## Without (lower) for all value types at once -/

/-- Two values, all of value type `{p₀}` or all of value type `{p₁}`. -/
def thB : DataTheory (Fin 2) := fun V atom => ∃ _ : V ≃ Fin 2,
  (∀ v, atom 0 v ∧ ¬ atom 1 v) ∨ (∀ v, ¬ atom 0 v ∧ atom 1 v)

def cardB (τ : Finset (Fin 2)) : Option Nat := if τ = {0} ∨ τ = {1} then some 2 else some 0

/-- `⊤ ⊑ T`, `A ⊑ ∃u.p₀`, `A ⊑ ∃u.p₁`. -/
def OB : Ontology (Fin 3) (Fin 1) (Fin 1) (Fin 2) :=
  [.obj (.gci [] [1]), .dEx 0 0 [0] [], .dEx 0 0 [1] []]

theorem vt_thB {V : Type} {atom : Fin 2 → V → Prop}
    (h : (∀ v, atom 0 v ∧ ¬ atom 1 v) ∨ (∀ v, ¬ atom 0 v ∧ atom 1 v)) (v : V) :
    vt atom v = {0} ∨ vt atom v = {1} := by
  rcases h with h | h
  · left
    ext p
    rw [mem_vt]
    fin_cases p <;> simp [h v]
  · right
    ext p
    rw [mem_vt]
    fin_cases p <;> simp [h v]

theorem upper_thB : ∀ (V : Type) (atom : Fin 2 → V → Prop), thB V atom → ∀ τ k, cardB τ = some k →
    ∀ l : List V, l.Nodup → (∀ v ∈ l, vt atom v = τ) → l.length ≤ k := by
  rintro V atom ⟨e, he⟩ τ k hk l hl hvt
  letI : Fintype V := Fintype.ofEquiv _ e.symm
  unfold cardB at hk
  split_ifs at hk with hτ
  · simp only [Option.some.injEq] at hk
    subst hk
    have := hl.length_le_card
    rwa [Fintype.card_congr e, Fintype.card_fin] at this
  · simp only [Option.some.injEq] at hk
    subst hk
    cases l with
    | nil => exact le_refl _
    | cons v l =>
      have := vt_thB he v
      rw [hvt v List.mem_cons_self] at this
      exact absurd this hτ

/-- (lower) for one value type at a time. -/
theorem lower_one_thB (τ : Finset (Fin 2)) (N : Nat) (hN : ∀ k, cardB τ = some k → N ≤ k) :
    ∃ (V : Type) (atom : Fin 2 → V → Prop), thB V atom ∧
      ∃ l : List V, l.Nodup ∧ l.length = N ∧ ∀ v ∈ l, vt atom v = τ := by
  by_cases hτ : τ = {0} ∨ τ = {1}
  · have h2 := hN 2 (by simp [cardB, hτ])
    rcases hτ with rfl | rfl
    · refine ⟨Fin 2, fun p _ => p = 0, ⟨Equiv.refl _, Or.inl fun v => by simp⟩,
        (List.finRange 2).take N, (List.nodup_finRange 2).sublist (List.take_sublist _ _),
        by simp; omega, fun v _ => ?_⟩
      ext p; rw [mem_vt]; fin_cases p <;> simp
    · refine ⟨Fin 2, fun p _ => p = 1, ⟨Equiv.refl _, Or.inr fun v => by simp⟩,
        (List.finRange 2).take N, (List.nodup_finRange 2).sublist (List.take_sublist _ _),
        by simp; omega, fun v _ => ?_⟩
      ext p; rw [mem_vt]; fin_cases p <;> simp
  · have h0 := hN 0 (by rw [cardB, if_neg hτ])
    exact ⟨Fin 2, fun p _ => p = 0, ⟨Equiv.refl _, Or.inl fun v => by simp⟩, [], List.nodup_nil,
      by rw [List.length_nil]; omega, by simp⟩

/-- **(lower) for all value types at once is needed.** -/
theorem not_iff_B : ¬ (EntailsSub thB OB 0 2 ↔ ∀ t, DGood OB cardB (t, none) → 0 ∈ t → 2 ∈ t) := by
  intro h
  have hE : EntailsSub thB OB 0 2 := by
    rintro D V _ atom ⟨-, hat⟩ I hI x hx
    obtain ⟨v0, -, h0⟩ := (hI _ (by simp [OB]) : satClause atom I (.dEx 0 0 [0] [])) x hx
    obtain ⟨v1, -, h1⟩ := (hI _ (by simp [OB]) : satClause atom I (.dEx 0 0 [1] [])) x hx
    rcases hat with hat | hat
    · exact absurd (h1.1 1 (by simp)) (hat v1).2
    · exact absurd (h0.1 0 (by simp)) (hat v0).1
  have hR := h.1 hE
  let t : Finset (Fin 3) := {0, 1}
  have hS : DSelfSupp OB cardB {(t, none)} := by
    rintro ρ hρ
    rw [Set.mem_singleton_iff] at hρ
    subst hρ
    refine ⟨[], [({0}, {0}), ({0}, {1})], ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, by simp⟩
    · rw [SRIQ.closed_iff]
      intro body head hcl _
      simp only [mem_objPart, OB, List.mem_cons, Clause.obj.injEq, SRIQ.Clause.gci.injEq,
        reduceCtorEq, List.not_mem_nil, or_false] at hcl
      obtain ⟨-, rfl⟩ := hcl
      exact ⟨1, by simp, by simp [t]⟩
    · simp
    · intro a R b hcl
      simp [mem_objPart, OB] at hcl
    · intro a k R b hcl
      simp [mem_objPart, OB] at hcl
    · intro a k R b hcl
      simp [mem_objPart, OB] at hcl
    · intro e _ u w hcl
      simp [OB] at hcl
    · intro τ k hk
      unfold cardB at hk
      split_ifs at hk with hτ
      · simp only [Option.some.injEq] at hk
        subst hk
        rcases hτ with rfl | rfl <;> decide
      · simp only [Option.some.injEq] at hk
        subst hk
        simp only [tcnt, List.countP_cons, List.countP_nil]
        push Not at hτ
        simp [Ne.symm hτ.1, Ne.symm hτ.2]
    · intro a u head hcl
      simp [OB] at hcl
    · intro a u pos neg hcl _
      simp only [OB, List.mem_cons, Clause.dEx.injEq, reduceCtorEq, List.not_mem_nil,
        or_false, false_or] at hcl
      rcases hcl with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ <;> decide
    · intro a k u pos neg hcl
      simp [OB] at hcl
    · intro a k u pos neg hcl
      simp [OB] at hcl
  have := hR t ⟨{(t, none)}, Set.mem_singleton _, hS⟩ (by simp [t])
  simp [t] at this

end ContextCalculus.SRIQD.OracleExamples

#print axioms ContextCalculus.SRIQD.OracleExamples.lower_thA
#print axioms ContextCalculus.SRIQD.OracleExamples.not_iff_A
#print axioms ContextCalculus.SRIQD.OracleExamples.upper_thB
#print axioms ContextCalculus.SRIQD.OracleExamples.lower_one_thB
#print axioms ContextCalculus.SRIQD.OracleExamples.not_iff_B
