/-
  ContextCalculus/CheckerTerm.lean
  ================================
  **A first-order certificate checker over a proper term algebra.**

  `CheckerFO.lean` encodes a successor as a *one-level* term `fₖ(x)` (a positive
  integer id read as `fn_k` applied to the central variable).  That suffices for
  verdicts whose derivation stays within a single successor context, but not for
  those that build a successor *of* a successor — `f(g(x))` — as transitive-role
  and successor-chain subsumptions do (e.g. `trans_test`'s `A ⊑ D`, the nested
  `kinship` subsumptions).  Those stayed validated only empirically.

  This file removes that limitation by replacing the integer term code with a
  genuine **term algebra** `FTerm` (`var i` for variables and neighbours,
  `const i` for named individuals, and `app f t` for a unary successor function
  applied to a term). Nested successors are
  first-class, so the certificate can instantiate clauses at `f(g(x))` and the
  verified checker certifies the verdict by kernel.

  The literals and clauses are built over `FTerm`; clauses are `Clause FLit`, so
  the **generic** resolution core of `Basic.lean` (`resolvent`,
  `resolution_sound`, …) applies verbatim — only the term-level pieces
  (evaluation, substitution, paramodulation rewriting a *subterm*) are new.  A
  pleasant consequence of using a real term algebra: substitution commutes with
  evaluation *unconditionally*, so — unlike `CheckerFO` — there is no `clFree`
  side condition on instantiation.

  All `sorry`-free; the generated proofs are kernel-checked
  (`#print axioms` = `[propext, Quot.sound]`).
-/
import ContextCalculus.Basic

namespace ContextCalculus.CheckerTerm

open ContextCalculus

/-! ### Term algebra, atoms, literals -/

/-- A first-order term over constants and unary successor functions. `var i` is
    a variable or neighbour (the engine's `x = 0`, `y = -1`, and
    `z_i = -(i+1)`), `const i` is a named individual whose interpretation does
    not depend on the variable assignment, and `app f t` applies a successor
    function to a term. -/
inductive FTerm where
  | var : Int → FTerm
  | const : Nat → FTerm
  | app : Nat → FTerm → FTerm
deriving DecidableEq, Repr

/-- Concept / role atoms over `FTerm`. -/
inductive FPred where
  | concept (iri : Nat) (t : FTerm)
  | role (iri : Nat) (s t : FTerm)
deriving DecidableEq, Repr

/-- Head / body literals over `FTerm`. -/
inductive FLit where
  | P (p : FPred)
  | eq (s t : FTerm)
  | ineq (s t : FTerm)
deriving DecidableEq, Repr

/-- Clauses over `FLit` — reusing the generic clausal layer of `Basic.lean`. -/
abbrev FCL := Clause FLit

/-! ### Semantics -/

/-- A first-order model with concept, role, individual-constant, and unary
    successor interpretations. -/
structure TModel (D : Type) where
  conc : Nat → D → Prop
  rol : Nat → D → D → Prop
  const : Nat → D
  fn : Nat → D → D

variable {D : Type}

/-- Evaluate a term under an assignment `ρ` of the variables.  Nested successors
    fold the function interpretations — `app f (app g (var 0))` evaluates to
    `fn f (fn g (ρ 0))`. -/
def TModel.evalT (M : TModel D) (ρ : Int → D) : FTerm → D
  | .var i => ρ i
  | .const i => M.const i
  | .app f t => M.fn f (M.evalT ρ t)

/-- Interpret a literal (equality = real equality). -/
def TModel.evalL (M : TModel D) (ρ : Int → D) : FLit → Prop
  | .P (.concept i t) => M.conc i (M.evalT ρ t)
  | .P (.role i s t) => M.rol i (M.evalT ρ s) (M.evalT ρ t)
  | .eq s t => M.evalT ρ s = M.evalT ρ t
  | .ineq s t => M.evalT ρ s ≠ M.evalT ρ t

/-- A clause is valid in `M` when it holds under every assignment. -/
def valid (M : TModel D) (c : FCL) : Prop := ∀ ρ, sat (M.evalL ρ) c

/-! ### Substitution and its soundness -/

/-- Look up a variable in a finite substitution (identity if absent). -/
def substVar (σ : List (Int × FTerm)) (i : Int) : FTerm :=
  match σ.find? (fun p => decide (p.1 = i)) with
  | some p => p.2
  | none => .var i

/-- Apply a substitution to a term (recursively, through successors). -/
def substT (σ : List (Int × FTerm)) : FTerm → FTerm
  | .var i => substVar σ i
  | .const i => .const i
  | .app f t => .app f (substT σ t)

def substL (σ : List (Int × FTerm)) : FLit → FLit
  | .P (.concept i t) => .P (.concept i (substT σ t))
  | .P (.role i s t) => .P (.role i (substT σ s) (substT σ t))
  | .eq s t => .eq (substT σ s) (substT σ t)
  | .ineq s t => .ineq (substT σ s) (substT σ t)

def substCl (σ : List (Int × FTerm)) (c : FCL) : FCL :=
  ⟨c.body.map (substL σ), c.head.map (substL σ)⟩

/-- Evaluating after substitution = evaluating under the shifted assignment.
    No freeness hypothesis is needed — substitution into a term algebra always
    commutes with evaluation. -/
theorem evalT_substT (M : TModel D) (ρ : Int → D) (σ : List (Int × FTerm)) (t : FTerm) :
    M.evalT ρ (substT σ t) = M.evalT (fun i => M.evalT ρ (substVar σ i)) t := by
  induction t with
  | var i => rfl
  | const i => rfl
  | app f t ih => simp only [substT, TModel.evalT, ih]

theorem evalL_substL (M : TModel D) (ρ : Int → D) (σ : List (Int × FTerm)) (l : FLit) :
    M.evalL ρ (substL σ l) = M.evalL (fun i => M.evalT ρ (substVar σ i)) l := by
  cases l with
  | P p =>
    cases p with
    | concept i t => simp only [substL, TModel.evalL, evalT_substT]
    | role i s t => simp only [substL, TModel.evalL, evalT_substT]
  | eq s t => simp only [substL, TModel.evalL, evalT_substT]
  | ineq s t => simp only [substL, TModel.evalL, evalT_substT]

theorem sat_substCl (M : TModel D) (ρ : Int → D) (σ : List (Int × FTerm)) (c : FCL) :
    sat (M.evalL ρ) (substCl σ c) ↔
      sat (M.evalL (fun i => M.evalT ρ (substVar σ i))) c := by
  constructor
  · intro hs hbody
    have hbody' : ∀ a ∈ (substCl σ c).body, M.evalL ρ a := by
      intro a ha
      simp only [substCl, List.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      rw [evalL_substL]; exact hbody b hb
    obtain ⟨a, ha, hIa⟩ := hs hbody'
    simp only [substCl, List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    rw [evalL_substL] at hIa
    exact ⟨b, hb, hIa⟩
  · intro hs hbody
    have hbody' : ∀ b ∈ c.body, M.evalL (fun i => M.evalT ρ (substVar σ i)) b := by
      intro b hb
      rw [← evalL_substL]
      exact hbody (substL σ b) (by simp only [substCl, List.mem_map]; exact ⟨b, hb, rfl⟩)
    obtain ⟨a, ha, hIa⟩ := hs hbody'
    refine ⟨substL σ a, by simp only [substCl, List.mem_map]; exact ⟨a, ha, rfl⟩, ?_⟩
    rw [evalL_substL]; exact hIa

/-- **Universal instantiation is sound.**  Any instance of a valid clause is
    valid — unconditionally (no `clFree` restriction). -/
theorem inst_valid (M : TModel D) {p : FCL} (hp : valid M p) (σ : List (Int × FTerm)) :
    valid M (substCl σ p) := by
  intro ρ
  rw [sat_substCl]
  exact hp _

/-! ### Paramodulation: rewriting a *subterm* inside a literal -/

/-- Rewrite every occurrence of subterm `s` to `t` inside a term. -/
def rwT (s t : FTerm) : FTerm → FTerm
  | .var i => if FTerm.var i = s then t else .var i
  | .const i => if FTerm.const i = s then t else .const i
  | .app f a => if FTerm.app f a = s then t else .app f (rwT s t a)

/-- Subterm rewriting preserves value when `s` and `t` evaluate equally. -/
theorem evalT_rwT (M : TModel D) (ρ : Int → D) (s t : FTerm)
    (heq : M.evalT ρ s = M.evalT ρ t) : ∀ u, M.evalT ρ (rwT s t u) = M.evalT ρ u := by
  intro u
  induction u with
  | var i =>
    simp only [rwT]
    by_cases h : (FTerm.var i) = s
    · rw [if_pos h, h]; exact heq.symm
    · rw [if_neg h]
  | const i =>
    simp only [rwT]
    by_cases h : (FTerm.const i) = s
    · rw [if_pos h, h]; exact heq.symm
    · rw [if_neg h]
  | app f a ih =>
    simp only [rwT]
    by_cases h : (FTerm.app f a) = s
    · rw [if_pos h, h]; exact heq.symm
    · rw [if_neg h]; simp only [TModel.evalT, ih]

/-- Rewrite subterm `s` to `t` inside a literal. -/
def rwL (s t : FTerm) : FLit → FLit
  | .P (.concept i u) => .P (.concept i (rwT s t u))
  | .P (.role i u v) => .P (.role i (rwT s t u) (rwT s t v))
  | .eq u v => .eq (rwT s t u) (rwT s t v)
  | .ineq u v => .ineq (rwT s t u) (rwT s t v)

/-- Rewriting `s ↦ t` inside a literal preserves its truth value when `s` and `t`
    evaluate equally — the first-order version of `Basic.paramodulation_sound`,
    now over a real term algebra. -/
theorem evalL_rwL (M : TModel D) (ρ : Int → D) (s t : FTerm)
    (heq : M.evalT ρ s = M.evalT ρ t) (L : FLit) :
    M.evalL ρ (rwL s t L) ↔ M.evalL ρ L := by
  cases L with
  | P p =>
    cases p with
    | concept i u => simp only [rwL, TModel.evalL, evalT_rwT M ρ s t heq]
    | role i u v => simp only [rwL, TModel.evalL, evalT_rwT M ρ s t heq]
  | eq u v => simp only [rwL, TModel.evalL, evalT_rwT M ρ s t heq]
  | ineq u v => simp only [rwL, TModel.evalL, evalT_rwT M ρ s t heq]

/-- The paramodulant of `c1` (with the equality `s ≈ t` in its head) into the
    literal `L` of `c2`: `L` is rewritten `s ↦ t`. -/
def paraResolvent (c1 c2 : FCL) (s t : FTerm) (L : FLit) : FCL :=
  ⟨c1.body ++ c2.body, rwL s t L :: (without (FLit.eq s t) c1.head ++ without L c2.head)⟩

/-- **Soundness of paramodulation into a literal.** -/
theorem paraResolvent_sound (M : TModel D) (ρ : Int → D) (c1 c2 : FCL)
    (s t : FTerm) (L : FLit) (h1 : sat (M.evalL ρ) c1) (h2 : sat (M.evalL ρ) c2)
    (he : FLit.eq s t ∈ c1.head) (hL : L ∈ c2.head) :
    sat (M.evalL ρ) (paraResolvent c1 c2 s t L) := by
  intro hbody
  have hb1 : ∀ a ∈ c1.body, M.evalL ρ a := fun a ha =>
    hbody a (by simp only [paraResolvent, List.mem_append]; exact Or.inl ha)
  have hb2 : ∀ a ∈ c2.body, M.evalL ρ a := fun a ha =>
    hbody a (by simp only [paraResolvent, List.mem_append]; exact Or.inr ha)
  obtain ⟨a, ha, hIa⟩ := h1 hb1
  by_cases haeq : a = FLit.eq s t
  · have heqv : M.evalT ρ s = M.evalT ρ t := by subst haeq; simpa [TModel.evalL] using hIa
    obtain ⟨b, hb, hIb⟩ := h2 hb2
    by_cases hbL : b = L
    · subst hbL
      refine ⟨rwL s t b, by simp [paraResolvent], ?_⟩
      exact (evalL_rwL M ρ s t heqv b).mpr hIb
    · exact ⟨b, by
        simp only [paraResolvent, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (mem_without.mpr ⟨hb, hbL⟩)), hIb⟩
  · exact ⟨a, by
      simp only [paraResolvent, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inl (mem_without.mpr ⟨ha, haeq⟩)), hIa⟩

/-! ### Clause equivalence (set semantics) -/

/-- Two clauses are equivalent when they have the same body / head atom sets. -/
def clEquivT (c d : FCL) : Prop :=
  c.body ⊆ d.body ∧ d.body ⊆ c.body ∧ c.head ⊆ d.head ∧ d.head ⊆ c.head

instance (c d : FCL) : Decidable (clEquivT c d) := by unfold clEquivT; infer_instance

theorem sat_of_clEquivT {I : Model FLit} {c d : FCL} (h : clEquivT c d) (hd : sat I d) :
    sat I c := by
  intro hbody
  have hbd : ∀ a ∈ d.body, I a := fun a ha => hbody a (h.2.1 ha)
  obtain ⟨a, ha, hIa⟩ := hd hbd
  exact ⟨a, h.2.2.2 ha, hIa⟩

/-! ### The context core and the checker -/

/-- The fact clause `→ A(x)` with `x = var 0`. -/
def coreClauseT (A : Nat) : FCL := ⟨[], [FLit.P (FPred.concept A (FTerm.var 0))]⟩

theorem sat_coreClauseT (I : Model FLit) (A : Nat) :
    sat I (coreClauseT A) ↔ I (FLit.P (FPred.concept A (FTerm.var 0))) := by
  unfold sat coreClauseT
  constructor
  · intro h
    obtain ⟨a, ha, hIa⟩ := h (by intro a ha; cases ha)
    simp only [List.mem_singleton] at ha; subst ha; exact hIa
  · intro h _; exact ⟨_, List.mem_singleton.mpr rfl, h⟩

/-- A justification for a derivation entry. -/
inductive JustifT where
  | prem (i : Nat) (σ : List (Int × FTerm))   -- instance of premise `O[i]`
  | core                                       -- the context core `→ A(x)`
  | taut                                       -- a tautology
  | res (i j : Nat) (a : FLit)                 -- resolvent of entries `i`, `j`
  | para (i j : Nat) (s t : FTerm) (L : FLit)  -- paramodulate `s≈t` of `i` into `L` of `j`
deriving Repr

def stepOkT (O : List FCL) (A : Nat) (done : List FCL) (c : FCL) : JustifT → Bool
  | .prem i σ =>
      match O[i]? with
      | some p => decide (clEquivT c (substCl σ p))
      | none => false
  | .core => decide (clEquivT c (coreClauseT A))
  | .taut => decide (∃ a ∈ c.body, a ∈ c.head)
  | .res i j a =>
      match done[i]?, done[j]? with
      | some c1, some c2 =>
          decide (a ∈ c1.head) && decide (a ∈ c2.body) && decide (clEquivT c (resolvent c1 c2 a))
      | _, _ => false
  | .para i j s t L =>
      match done[i]?, done[j]? with
      | some c1, some c2 =>
          decide (FLit.eq s t ∈ c1.head) && decide (L ∈ c2.head)
            && decide (clEquivT c (paraResolvent c1 c2 s t L))
      | _, _ => false

section Soundness

variable (M : TModel D) (a0 : D) (O : List FCL) (A : Nat)

/-- The fixed assignment placing the context element at `a0`. -/
def ρ0 : Int → D := fun _ => a0

/-- "Entry holds": true under the fixed assignment `ρ0`. -/
private def holds (c : FCL) : Prop := sat (M.evalL (ρ0 a0)) c

theorem stepOkT_sound (hO : ∀ p ∈ O, valid M p) (hA : M.conc A a0)
    {done : List FCL} (hdone : ∀ d ∈ done, holds M a0 d)
    {c : FCL} {j : JustifT} (h : stepOkT O A done c j = true) : holds M a0 c := by
  cases j with
  | prem i σ =>
    simp only [stepOkT] at h
    rcases hi : O[i]? with _ | p
    · rw [hi] at h; simp at h
    · rw [hi] at h
      simp only [decide_eq_true_eq] at h
      have hp : valid M p := hO p (List.mem_of_getElem? hi)
      have hval : holds M a0 (substCl σ p) := inst_valid M hp σ (ρ0 a0)
      exact sat_of_clEquivT h hval
  | core =>
    simp only [stepOkT, decide_eq_true_eq] at h
    refine sat_of_clEquivT h ?_
    show sat (M.evalL (ρ0 a0)) (coreClauseT A)
    refine (sat_coreClauseT (M.evalL (ρ0 a0)) A).mpr ?_
    show M.conc A (M.evalT (ρ0 a0) (FTerm.var 0))
    exact hA
  | taut =>
    simp only [stepOkT, decide_eq_true_eq] at h
    obtain ⟨a, hb, hh⟩ := h
    intro hbody; exact ⟨a, hh, hbody a hb⟩
  | res i j a =>
    simp only [stepOkT] at h
    rcases hi : done[i]? with _ | c1
    · rw [hi] at h; simp at h
    · rcases hj : done[j]? with _ | c2
      · rw [hi, hj] at h; simp at h
      · rw [hi, hj] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨ha1, ha2⟩, heq⟩ := h
        have h1 : holds M a0 c1 := hdone c1 (List.mem_of_getElem? hi)
        have h2 : holds M a0 c2 := hdone c2 (List.mem_of_getElem? hj)
        exact sat_of_clEquivT heq (resolution_sound (M.evalL (ρ0 a0)) c1 c2 a h1 h2 ha1 ha2)
  | para i j s t L =>
    simp only [stepOkT] at h
    rcases hi : done[i]? with _ | c1
    · rw [hi] at h; simp at h
    · rcases hj : done[j]? with _ | c2
      · rw [hi, hj] at h; simp at h
      · rw [hi, hj] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨he, hL⟩, heq⟩ := h
        have h1 : holds M a0 c1 := hdone c1 (List.mem_of_getElem? hi)
        have h2 : holds M a0 c2 := hdone c2 (List.mem_of_getElem? hj)
        exact sat_of_clEquivT heq
          (paraResolvent_sound M (ρ0 a0) c1 c2 s t L h1 h2 he hL)

def checkFoldT (O : List FCL) (A : Nat) : List FCL → List (FCL × JustifT) → Option (List FCL)
  | done, [] => some done
  | done, (c, j) :: rest =>
      if stepOkT O A done c j then checkFoldT O A (done ++ [c]) rest else none

theorem checkFoldT_sound (hO : ∀ p ∈ O, valid M p) (hA : M.conc A a0) :
    ∀ {done : List FCL} {cert : List (FCL × JustifT)} {final : List FCL},
      (∀ d ∈ done, holds M a0 d) → checkFoldT O A done cert = some final →
      ∀ d ∈ final, holds M a0 d := by
  intro done cert
  induction cert generalizing done with
  | nil => intro final hdone hf; simp only [checkFoldT, Option.some.injEq] at hf; subst hf; exact hdone
  | cons hd rest ih =>
    intro final hdone hf
    obtain ⟨c, j⟩ := hd
    simp only [checkFoldT] at hf
    by_cases hstep : stepOkT O A done c j
    · rw [if_pos hstep] at hf
      have hc : holds M a0 c := stepOkT_sound M a0 O A hO hA hdone hstep
      refine ih (fun d hd' => ?_) hf
      rcases List.mem_append.mp hd' with h | h
      · exact hdone d h
      · simp only [List.mem_singleton] at h; subst h; exact hc
    · rw [if_neg hstep] at hf; simp at hf

end Soundness

def checkCertT (O : List FCL) (A : Nat) (cert : List (FCL × JustifT)) (target : FCL) : Bool :=
  match checkFoldT O A [] cert with
  | some final => decide (target ∈ final)
  | none => false

/-- **Validated subsumption (nested terms).**  If the certificate derives `→ B(x)`
    from the premises `O` (used via universal instances, possibly at nested
    successor terms) and the core `→ A(x)`, then `O ⊨ A ⊑ B`: in every
    first-order model of `O`, every `A` is a `B`. -/
theorem certifies_subsumptionT (O : List FCL) (A B : Nat) (cert : List (FCL × JustifT))
    (h : checkCertT O A cert ⟨[], [FLit.P (FPred.concept B (FTerm.var 0))]⟩ = true)
    (M : TModel D) (hO : ∀ p ∈ O, valid M p) (a0 : D) (hA : M.conc A a0) :
    M.conc B a0 := by
  unfold checkCertT at h
  rcases hf : checkFoldT O A [] cert with _ | final
  · rw [hf] at h; simp at h
  · rw [hf] at h
    simp only [decide_eq_true_eq] at h
    have hfin := checkFoldT_sound M a0 O A hO hA (by intro d hd; cases hd) hf
    have htgt : holds M a0 ⟨[], [FLit.P (FPred.concept B (FTerm.var 0))]⟩ := hfin _ h
    obtain ⟨a, ha, hIa⟩ := htgt (by intro a ha; cases ha)
    simp only [List.mem_singleton] at ha; subst ha
    simpa [TModel.evalL, TModel.evalT, ρ0] using hIa

/-- **Validated inconsistency (nested terms).**  If the certificate derives the
    empty clause, then `O ⊨ A ⊑ ⊥`: no first-order model has an `A`. -/
theorem certifies_unsatT (O : List FCL) (A : Nat) (cert : List (FCL × JustifT))
    (h : checkCertT O A cert ⟨[], []⟩ = true)
    (M : TModel D) (hO : ∀ p ∈ O, valid M p) (a0 : D) : ¬ M.conc A a0 := by
  intro hA
  unfold checkCertT at h
  rcases hf : checkFoldT O A [] cert with _ | final
  · rw [hf] at h; simp at h
  · rw [hf] at h
    simp only [decide_eq_true_eq] at h
    have hfin := checkFoldT_sound M a0 O A hO hA (by intro d hd; cases hd) hf
    exact sat_empty (M.evalL (ρ0 a0)) (hfin _ h)

end ContextCalculus.CheckerTerm
