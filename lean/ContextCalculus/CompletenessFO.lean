/-
  ContextCalculus/CompletenessFO.lean
  ===================================
  **First-order Herbrand fusion — the model side (start).**

  `CompletenessClause.lean` gives ground/propositional refutational completeness
  of the engine's resolution.  The remaining first-order content is the `Succ`
  rule: the engine reasons over a genuine **term algebra** (`CheckerTerm.FTerm`,
  successors `f(x)`, `f(g(x))`, …) and instantiates clauses at those terms.  The
  classical bridge is **Herbrand's theorem**: a first-order clause set is
  unsatisfiable iff a set of *ground instances* is propositionally unsatisfiable,
  the ground side then refuted by resolution.

  This file builds the **model side** of that bridge — the Herbrand
  interpretation — over the engine's real term algebra and term model
  (`CheckerTerm.TModel`):

    * `herbrandT`        — from a propositional truth assignment on ground atoms,
                           the term model whose domain is `FTerm`, with successor
                           functions interpreted **syntactically** (`fn = app`);
    * `evalT_rho0` / `evalL_herbrand_of_IsP` — under the canonical assignment the
                           term model's evaluation coincides with the propositional
                           assignment on concept/role atoms;
    * `sat_herbrand_rho0_iff` — hence it satisfies exactly the clauses the
                           assignment does;
    * `herbrand_fo_model_existence` — a clause set the engine **cannot refute**
                           has a genuine first-order term model (`TModel FTerm`);
    * `fo_model_or_refute` — the dichotomy: every clause set either has a
                           first-order term model or is refuted by the engine's
                           resolution.

  Scope.  Equality-free fragment (concept/role atoms — `ALCHI`): `TModel.evalL`
  interprets `FLit.eq` by *real* equality of `FTerm`s, which the syntactic
  Herbrand model does not validate (number restrictions need a congruence/quotient
  model).  Everything here is under the **canonical assignment** `rho0` (the
  generic element `x` of a query) — the classification semantics.  The *remaining*
  open work is the lifting half of Herbrand: that the engine's `Succ` rule
  generates enough ground instances that first-order unsatisfiability already
  shows up propositionally (a compactness / fairness argument over the infinite
  Herbrand universe).  That half is **not** claimed here.
-/
import ContextCalculus.CheckerTerm
import ContextCalculus.CompletenessClause

namespace ContextCalculus.CompletenessFO

open ContextCalculus ContextCalculus.CheckerTerm

/-- The Herbrand term model from a propositional assignment `I` on ground atoms:
    domain = the term algebra `FTerm`, successor functions interpreted
    **syntactically** (`fn f t = app f t`), concepts/roles read off `I`. -/
def herbrandT (I : FLit → Prop) : TModel FTerm where
  conc := fun i d => I (FLit.P (FPred.concept i d))
  rol := fun i s t => I (FLit.P (FPred.role i s t))
  const := FTerm.const
  fn := fun f t => FTerm.app f t

/-- The canonical assignment: every variable to itself (the generic element `x`
    and its neighbours). -/
def rho0 : Int → FTerm := fun i => FTerm.var i

/-- Under the canonical assignment the Herbrand term model evaluates every term to
    itself (functions fold back to `app`). -/
theorem evalT_rho0 (I : FLit → Prop) (t : FTerm) :
    (herbrandT I).evalT rho0 t = t := by
  induction t with
  | var i => rfl
  | const i => rfl
  | app f t ih => exact congrArg ((herbrandT I).fn f) ih

/-- A concept/role literal evaluates, under the canonical assignment, to its
    propositional truth value. -/
theorem evalL_herbrand_P (I : FLit → Prop) (p : FPred) :
    (herbrandT I).evalL rho0 (FLit.P p) = I (FLit.P p) := by
  cases p with
  | concept i t => exact congrArg ((herbrandT I).conc i) (evalT_rho0 I t)
  | role i s t => exact congrArg₂ ((herbrandT I).rol i) (evalT_rho0 I s) (evalT_rho0 I t)

/-- A first-order literal is equality-free (a concept/role atom). -/
def IsP : FLit → Prop
  | FLit.P _ => True
  | _ => False

theorem evalL_herbrand_of_IsP (I : FLit → Prop) {L : FLit} (h : IsP L) :
    (herbrandT I).evalL rho0 L = I L := by
  cases L with
  | P p => exact evalL_herbrand_P I p
  | eq _ _ => exact absurd h (by simp [IsP])
  | ineq _ _ => exact absurd h (by simp [IsP])

/-- A clause is equality-free when all its literals are concept/role atoms. -/
def EqFree (c : FCL) : Prop :=
  (∀ L ∈ c.body, IsP L) ∧ (∀ L ∈ c.head, IsP L)

/-- For an equality-free clause, the Herbrand term model (under the canonical
    assignment) satisfies it iff the propositional assignment does. -/
theorem sat_herbrand_rho0_iff (I : FLit → Prop) {c : FCL} (hf : EqFree c) :
    sat ((herbrandT I).evalL rho0) c ↔ sat I c := by
  have hb : (∀ L ∈ c.body, (herbrandT I).evalL rho0 L) ↔ (∀ L ∈ c.body, I L) := by
    constructor <;> intro h L hL
    · exact (evalL_herbrand_of_IsP I (hf.1 L hL)) ▸ h L hL
    · exact (evalL_herbrand_of_IsP I (hf.1 L hL)).symm ▸ h L hL
  have hh : (∃ L ∈ c.head, (herbrandT I).evalL rho0 L) ↔ (∃ L ∈ c.head, I L) := by
    constructor
    · rintro ⟨L, hL, hev⟩; exact ⟨L, hL, (evalL_herbrand_of_IsP I (hf.2 L hL)) ▸ hev⟩
    · rintro ⟨L, hL, hev⟩; exact ⟨L, hL, (evalL_herbrand_of_IsP I (hf.2 L hL)).symm ▸ hev⟩
  unfold sat; rw [hb, hh]

/-- **First-order Herbrand model existence.**  An equality-free clause set the
    engine's resolution cannot refute has a genuine first-order term model
    (`TModel FTerm`) satisfying every clause under the canonical assignment. -/
theorem herbrand_fo_model_existence (S : List FCL)
    (hf : ∀ c ∈ S, EqFree c)
    (h : ¬ Derivable S (⟨[], []⟩ : FCL)) :
    ∃ M : TModel FTerm, ∀ c ∈ S, sat (M.evalL rho0) c := by
  obtain ⟨I, hI⟩ := ClauseComplete.model_existence S h
  exact ⟨herbrandT I, fun c hc => (sat_herbrand_rho0_iff I (hf c hc)).2 (hI c hc)⟩

/-- **Model-or-refute dichotomy over the term algebra.**  Every equality-free
    clause set either has a first-order term model (under the canonical
    assignment) or is refuted by the engine's resolution. -/
theorem fo_model_or_refute (S : List FCL) (hf : ∀ c ∈ S, EqFree c) :
    (∃ M : TModel FTerm, ∀ c ∈ S, sat (M.evalL rho0) c)
      ∨ Derivable S (⟨[], []⟩ : FCL) := by
  by_cases h : Derivable S (⟨[], []⟩ : FCL)
  · exact Or.inr h
  · exact Or.inl (herbrand_fo_model_existence S hf h)

/-! ### First-order subsumption completeness over term models -/

/-- `→ A(x)` over the term algebra. -/
def coreFCL (A : Nat) : FCL := ⟨[], [FLit.P (FPred.concept A (FTerm.var 0))]⟩
/-- `B(x) →` over the term algebra. -/
def negFCL (B : Nat) : FCL := ⟨[FLit.P (FPred.concept B (FTerm.var 0))], []⟩

theorem eqFree_coreFCL (A : Nat) : EqFree (coreFCL A) := by
  constructor <;> intro L hL <;>
    simp only [coreFCL, List.not_mem_nil, List.mem_singleton] at hL <;>
    first | exact hL.elim | (subst hL; exact trivial)

theorem eqFree_negFCL (B : Nat) : EqFree (negFCL B) := by
  constructor <;> intro L hL <;>
    simp only [negFCL, List.not_mem_nil, List.mem_singleton] at hL <;>
    first | exact hL.elim | (subst hL; exact trivial)

/-- Under the canonical assignment, `A(x)` evaluates to `conc A (var 0)` in any
    term model (the variable case of evaluation is model-independent). -/
theorem evalL_var0 (M : TModel FTerm) (A : Nat) :
    M.evalL rho0 (FLit.P (FPred.concept A (FTerm.var 0))) = M.conc A (FTerm.var 0) := rfl

/-- **First-order subsumption completeness (term models).**  If every Herbrand
    term model of `O` (under the canonical assignment) that carries `A(x)` also
    carries `B(x)`, then the engine's resolution refutes `O ⊓ A ⊓ ¬B`.  This lifts
    `subsumption_refut_complete` from propositional to first-order *term-model*
    semantics over the actual successor term algebra (equality-free fragment). -/
theorem fo_subsumption_refut (O : List FCL) (A B : Nat)
    (hfree : ∀ c ∈ O, EqFree c)
    (hent : ∀ M : TModel FTerm, (∀ c ∈ O, sat (M.evalL rho0) c) →
      M.conc A (FTerm.var 0) → M.conc B (FTerm.var 0)) :
    Derivable (O ++ [coreFCL A, negFCL B]) (⟨[], []⟩ : FCL) := by
  have hfreeS : ∀ c ∈ O ++ [coreFCL A, negFCL B], EqFree c := by
    intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hfree c hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact eqFree_coreFCL A
      · exact eqFree_negFCL B
  rcases fo_model_or_refute (O ++ [coreFCL A, negFCL B]) hfreeS with ⟨M, hM⟩ | hd
  · exfalso
    have hO : ∀ c ∈ O, sat (M.evalL rho0) c := fun c hc => hM c (by simp [hc])
    have hA : M.conc A (FTerm.var 0) := by
      obtain ⟨L, hL, hev⟩ := hM (coreFCL A) (by simp) (by intro a ha; cases ha)
      simp only [coreFCL, List.mem_singleton] at hL
      rw [← evalL_var0 M A, ← hL]; exact hev
    have hB : ¬ M.conc B (FTerm.var 0) := by
      intro hCB
      obtain ⟨L, hL, _⟩ := hM (negFCL B) (by simp)
        (by intro a ha; simp only [negFCL, List.mem_singleton] at ha; subst ha; exact hCB)
      simp only [negFCL, List.not_mem_nil] at hL
    exact hB (hent M hO hA)
  · exact hd

/-- **First-order consistency decidability (term models).**  An equality-free
    clause set has a first-order term model (under the canonical assignment) iff
    the engine's resolution does not derive the empty clause.  Soundness
    (`Basic.derivable_sound` against the term model's propositional reduct) one
    way, Herbrand model existence the other. -/
theorem fo_consistent_iff (S : List FCL) (hf : ∀ c ∈ S, EqFree c) :
    (∃ M : TModel FTerm, ∀ c ∈ S, sat (M.evalL rho0) c)
      ↔ ¬ Derivable S (⟨[], []⟩ : FCL) := by
  constructor
  · rintro ⟨M, hM⟩ hder
    exact sat_empty (M.evalL rho0) (derivable_sound (M.evalL rho0) S hM hder)
  · exact herbrand_fo_model_existence S hf

end ContextCalculus.CompletenessFO
