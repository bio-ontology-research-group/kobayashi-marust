/-
  ContextCalculus/Checker.lean
  ============================
  **A Lean-verified certificate checker for the Rust reasoner's verdicts.**

  Proving the Rust source itself in Lean is out of scope; instead we *validate
  every run*.  The reasoner emits, for each subsumption / inconsistency it
  reports, a **resolution certificate**: an ordered derivation of the verdict
  clause from the genuine premises (the ontology clauses and the context core),
  using only resolution and tautology axioms — the rules `Basic.lean` already
  proved sound (`resolution_sound`).  Engine-derived clauses are *never* taken as
  axioms; each must be re-justified from the premises.

  This file gives a **decidable** checker `checkCert` and proves
  `checkCert_sound : checkCert P cert target = true → entailed P target`.  So if
  `checkCert` accepts (verifiable by the kernel via `decide`/`native_decide` on a
  concrete certificate), the verdict is a genuine logical consequence.  The
  generated per-benchmark theorems (`certifies_subsumption`, `certifies_unsat`)
  are therefore machine-checked validations of the actual reasoner's output.

  Clauses are compared up to **atom-set equivalence** (`clEquiv`): the engine
  works with sets, so resolvents match its clauses up to order/duplication, which
  `sat` does not see.
-/
import ContextCalculus.Basic

namespace ContextCalculus.Checker

open ContextCalculus

abbrev CL := Clause Lit

/-- `c` is a logical consequence of the premises `P`. -/
def entailed (P : List CL) (c : CL) : Prop :=
  ∀ I : Model Lit, (∀ d ∈ P, sat I d) → sat I c

theorem entailed_premise {P : List CL} {c : CL} (h : c ∈ P) : entailed P c :=
  fun _ hI => hI c h

/-- A clause with an atom in both body and head is a tautology, valid everywhere. -/
theorem entailed_taut {P : List CL} {c : CL} (h : ∃ a ∈ c.body, a ∈ c.head) :
    entailed P c := by
  intro I _ hbody
  obtain ⟨a, hb, hh⟩ := h
  exact ⟨a, hh, hbody a hb⟩

/-- Two clauses are equivalent when they have the same body- and head-atom sets. -/
def clEquiv (c d : CL) : Prop :=
  c.body ⊆ d.body ∧ d.body ⊆ c.body ∧ c.head ⊆ d.head ∧ d.head ⊆ c.head

instance (c d : CL) : Decidable (clEquiv c d) := by unfold clEquiv; infer_instance

/-- Equivalent clauses have the same models, so entailment transfers. -/
theorem sat_of_clEquiv {I : Model Lit} {c d : CL} (h : clEquiv c d) (hd : sat I d) :
    sat I c := by
  intro hbody
  have hbd : ∀ a ∈ d.body, I a := fun a ha => hbody a (h.2.1 ha)
  obtain ⟨a, ha, hIa⟩ := hd hbd
  exact ⟨a, h.2.2.2 ha, hIa⟩

theorem entailed_clEquiv {P : List CL} {c d : CL} (hd : entailed P d) (h : clEquiv c d) :
    entailed P c :=
  fun I hI => sat_of_clEquiv h (hd I hI)

/-- The resolvent of two entailed clauses (on a head/body atom) is entailed. -/
theorem entailed_res {P : List CL} {c1 c2 : CL} {a : Lit}
    (h1 : entailed P c1) (h2 : entailed P c2) (ha1 : a ∈ c1.head) (ha2 : a ∈ c2.body) :
    entailed P (resolvent c1 c2 a) :=
  fun I hI => resolution_sound I c1 c2 a (h1 I hI) (h2 I hI) ha1 ha2

/-! ### The checker -/

/-- A justification for a derivation entry. -/
inductive Justif where
  | ax                            -- a premise of `P`, or a tautology
  | res (i j : Nat) (a : Lit)     -- equivalent to the resolvent of entries `i`, `j` on `a`
deriving Repr

/-- Check that clause `c` with justification `j` is valid given the earlier
    (already-validated) entries `done`. -/
def stepOk (P done : List CL) (c : CL) : Justif → Bool
  | .ax => decide (c ∈ P) || decide (∃ a ∈ c.body, a ∈ c.head)
  | .res i j a =>
      match done[i]?, done[j]? with
      | some c1, some c2 =>
          decide (a ∈ c1.head) && decide (a ∈ c2.body) && decide (clEquiv c (resolvent c1 c2 a))
      | _, _ => false

/-- Every step that passes `stepOk`, given that the earlier entries are entailed,
    yields an entailed clause. -/
theorem stepOk_sound {P done : List CL} (hdone : ∀ d ∈ done, entailed P d)
    {c : CL} {j : Justif} (h : stepOk P done c j = true) : entailed P c := by
  cases j with
  | ax =>
    simp only [stepOk, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact entailed_premise h
    · exact entailed_taut h
  | res i j a =>
    simp only [stepOk] at h
    rcases hi : done[i]? with _ | c1
    · rw [hi] at h; simp at h
    · rcases hj : done[j]? with _ | c2
      · rw [hi, hj] at h; simp at h
      · rw [hi, hj] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨ha1, ha2⟩, heq⟩ := h
        have hc1 : entailed P c1 := hdone c1 (List.mem_of_getElem? hi)
        have hc2 : entailed P c2 := hdone c2 (List.mem_of_getElem? hj)
        exact entailed_clEquiv (entailed_res hc1 hc2 ha1 ha2) heq

/-- Validate a whole derivation, threading the list of already-validated clauses. -/
def checkFold (P : List CL) : List CL → List (CL × Justif) → Option (List CL)
  | done, [] => some done
  | done, (c, j) :: rest =>
      if stepOk P done c j then checkFold P (done ++ [c]) rest else none

theorem checkFold_sound {P : List CL} :
    ∀ {done : List CL} {cert : List (CL × Justif)} {final : List CL},
      (∀ d ∈ done, entailed P d) → checkFold P done cert = some final →
      ∀ d ∈ final, entailed P d := by
  intro done cert
  induction cert generalizing done with
  | nil =>
    intro final hdone hf
    simp only [checkFold, Option.some.injEq] at hf
    subst hf; exact hdone
  | cons hd rest ih =>
    intro final hdone hf
    obtain ⟨c, j⟩ := hd
    simp only [checkFold] at hf
    by_cases hstep : stepOk P done c j
    · rw [if_pos hstep] at hf
      have hc : entailed P c := stepOk_sound hdone hstep
      have hdone' : ∀ d ∈ done ++ [c], entailed P d := by
        intro d hd'
        rcases List.mem_append.mp hd' with h | h
        · exact hdone d h
        · simp only [List.mem_singleton] at h; subst h; exact hc
      exact ih hdone' hf
    · rw [if_neg hstep] at hf; simp at hf

/-- The checker: validate `cert`, then confirm the target appears. -/
def checkCert (P : List CL) (cert : List (CL × Justif)) (target : CL) : Bool :=
  match checkFold P [] cert with
  | some final => decide (target ∈ final)
  | none => false

/-- **Checker soundness.**  Acceptance certifies that the target is entailed. -/
theorem checkCert_sound {P : List CL} {cert : List (CL × Justif)} {target : CL}
    (h : checkCert P cert target = true) : entailed P target := by
  unfold checkCert at h
  rcases hf : checkFold P [] cert with _ | final
  · rw [hf] at h; simp at h
  · rw [hf] at h
    simp only [decide_eq_true_eq] at h
    exact checkFold_sound (by intro d hd; cases hd) hf target h

/-! ### Verdict wrappers: turning a checked certificate into a soundness statement -/

/-- **Validated subsumption.**  If the certificate (over premises `O` plus the
    core `→ A(x)`) derives `→ B(x)`, then `O ⊨ A ⊑ B`. -/
theorem certifies_subsumption (O : List CL) (A B : Nat)
    (cert : List (CL × Justif))
    (h : checkCert (O ++ [coreClause A]) cert ⟨[], [Lit.P (Pred.concept B Term.x)]⟩ = true)
    (I : Model Lit) (hO : ∀ c ∈ O, sat I c)
    (hA : I (Lit.P (Pred.concept A Term.x))) :
    I (Lit.P (Pred.concept B Term.x)) := by
  have hP : ∀ d ∈ O ++ [coreClause A], sat I d := by
    intro d hd
    rcases List.mem_append.mp hd with h' | h'
    · exact hO d h'
    · simp only [List.mem_singleton] at h'; subst h'; exact (sat_coreClause I A).mpr hA
  have he := checkCert_sound h I hP
  obtain ⟨a, ha, hIa⟩ := he (by intro a ha; cases ha)
  simp only [List.mem_singleton] at ha; subst ha; exact hIa

/-- **Validated inconsistency.**  If the certificate derives the empty clause in
    the context of `A`, then `O ⊨ A ⊑ ⊥` (no model makes `A(x)` true). -/
theorem certifies_unsat (O : List CL) (A : Nat)
    (cert : List (CL × Justif))
    (h : checkCert (O ++ [coreClause A]) cert ⟨[], []⟩ = true)
    (I : Model Lit) (hO : ∀ c ∈ O, sat I c) :
    ¬ I (Lit.P (Pred.concept A Term.x)) := by
  intro hA
  have hP : ∀ d ∈ O ++ [coreClause A], sat I d := by
    intro d hd
    rcases List.mem_append.mp hd with h' | h'
    · exact hO d h'
    · simp only [List.mem_singleton] at h'; subst h'; exact (sat_coreClause I A).mpr hA
  exact sat_empty I (checkCert_sound h I hP)

end ContextCalculus.Checker
