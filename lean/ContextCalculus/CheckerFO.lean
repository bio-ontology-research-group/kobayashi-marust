/-
  ContextCalculus/CheckerFO.lean
  ==============================
  **A first-order certificate checker** — extends `Checker.lean` from the
  propositional (root, resolution-only) class to verdicts whose engine
  derivation uses **Succ** (existential successors / value restrictions), e.g.

      A ⊑ ∃R.B,  B ⊑ C,  ∃R.C ⊑ D   ⊢   A ⊑ D.

  The reasoner derives this through a successor context for `f(x)`; the
  certificate re-derives it by resolution over **first-order instances** of the
  premises — the value-restriction clause `R(x,z) ∧ C(z) → D(x)` instantiated at
  `z := f(x)`, and `B ⊑ C` at `x := f(x)`.  Universal instantiation is the new,
  sound rule; everything else is resolution (`resolution_sound`).

  Semantics: a first-order model `FModel` (concept/role interpretations plus a
  function interpretation `fn` for the successor symbols).  A clause is *valid*
  (`validFO`) when it holds under every variable assignment `ρ : Term → D` — the
  reading of an ontology axiom.  A premise's instance is therefore valid too
  (`inst_valid`), which is what lets the checker use instances soundly.

  `certifies_subsumptionFO` turns an accepted certificate into `O ⊨ A ⊑ B`.
  All `sorry`-free; the generated proofs are kernel-checked.
-/
import ContextCalculus.Checker

namespace ContextCalculus.CheckerFO

open ContextCalculus ContextCalculus.Checker

/-- A first-order model: concept/role interpretations and a function
    interpretation for the successor symbols `f_i`. -/
structure FModel (D : Type) where
  conc : Nat → D → Prop
  rol : Nat → D → D → Prop
  fn : Nat → D → D

variable {D : Type}

/-- Evaluate a term under an assignment `ρ`.  Successor terms `f_i(x)` (positive
    ids) are `fn_i` applied to the value of the central variable `x` (id `0`). -/
def FModel.evalT (M : FModel D) (ρ : Term → D) (t : Term) : D :=
  if 0 < t then M.fn t.toNat (ρ 0) else ρ t

/-- Interpret a literal as a `Model Lit` (so `Basic.resolution_sound` applies). -/
def FModel.evalL (M : FModel D) (ρ : Term → D) : Lit → Prop
  | Lit.P (Pred.concept i t) => M.conc i (M.evalT ρ t)
  | Lit.P (Pred.role i s t) => M.rol i (M.evalT ρ s) (M.evalT ρ t)
  | Lit.eq s t => M.evalT ρ s = M.evalT ρ t
  | Lit.ineq s t => M.evalT ρ s ≠ M.evalT ρ t

/-- A clause is valid in `M` when it holds under every assignment. -/
def validFO (M : FModel D) (c : CL) : Prop := ∀ ρ, sat (M.evalL ρ) c

/-! ### f-free clauses and substitution -/

def tFree (t : Term) : Bool := decide (t ≤ 0)

def litFree : Lit → Bool
  | Lit.P (Pred.concept _ t) => tFree t
  | Lit.P (Pred.role _ s t) => tFree s && tFree t
  | Lit.eq s t => tFree s && tFree t
  | Lit.ineq s t => tFree s && tFree t

def clFree (c : CL) : Bool := c.body.all litFree && c.head.all litFree

/-- A finite substitution on terms (identity outside the listed pairs). -/
def applyσ (σ : List (Term × Term)) (t : Term) : Term :=
  match σ.find? (fun p => decide (p.1 = t)) with
  | some p => p.2
  | none => t

def litσ (σ : List (Term × Term)) : Lit → Lit
  | Lit.P (Pred.concept i t) => Lit.P (Pred.concept i (applyσ σ t))
  | Lit.P (Pred.role i s t) => Lit.P (Pred.role i (applyσ σ s) (applyσ σ t))
  | Lit.eq s t => Lit.eq (applyσ σ s) (applyσ σ t)
  | Lit.ineq s t => Lit.ineq (applyσ σ s) (applyσ σ t)

def clσ (σ : List (Term × Term)) (c : CL) : CL :=
  ⟨c.body.map (litσ σ), c.head.map (litσ σ)⟩

theorem applyσ_nil (t : Term) : applyσ [] t = t := rfl

theorem litσ_nil (l : Lit) : litσ [] l = l := by
  cases l with
  | P p => cases p <;> simp [litσ, applyσ_nil]
  | eq s t => simp [litσ, applyσ_nil]
  | ineq s t => simp [litσ, applyσ_nil]

theorem clσ_nil (c : CL) : clσ [] c = c := by
  have : (litσ []) = (id : Lit → Lit) := funext litσ_nil
  cases c; simp [clσ, this]

/-- A non-successor term evaluates to its raw assignment. -/
theorem evalT_var (M : FModel D) (ρ : Term → D) {t : Term} (ht : t ≤ 0) :
    M.evalT ρ t = ρ t := by
  simp only [FModel.evalT]; rw [if_neg (Int.not_lt.mpr ht)]

/-- On an f-free literal, evaluating after substitution equals evaluating under
    the shifted assignment `ρ' v = evalT ρ (σ v)`. -/
theorem evalL_litσ (M : FModel D) (ρ : Term → D) (σ : List (Term × Term))
    {l : Lit} (h : litFree l = true) :
    M.evalL ρ (litσ σ l) = M.evalL (fun v => M.evalT ρ (applyσ σ v)) l := by
  cases l with
  | P p =>
    cases p with
    | concept i t =>
      simp only [litFree, tFree, decide_eq_true_eq] at h
      simp only [litσ, FModel.evalL]
      rw [evalT_var M (fun v => M.evalT ρ (applyσ σ v)) h]
    | role i s t =>
      simp only [litFree, Bool.and_eq_true, tFree, decide_eq_true_eq] at h
      simp only [litσ, FModel.evalL]
      rw [evalT_var M (fun v => M.evalT ρ (applyσ σ v)) h.1,
          evalT_var M (fun v => M.evalT ρ (applyσ σ v)) h.2]
  | eq s t =>
    simp only [litFree, Bool.and_eq_true, tFree, decide_eq_true_eq] at h
    simp only [litσ, FModel.evalL]
    rw [evalT_var M (fun v => M.evalT ρ (applyσ σ v)) h.1,
        evalT_var M (fun v => M.evalT ρ (applyσ σ v)) h.2]
  | ineq s t =>
    simp only [litFree, Bool.and_eq_true, tFree, decide_eq_true_eq] at h
    simp only [litσ, FModel.evalL]
    rw [evalT_var M (fun v => M.evalT ρ (applyσ σ v)) h.1,
        evalT_var M (fun v => M.evalT ρ (applyσ σ v)) h.2]

theorem sat_clσ (M : FModel D) (ρ : Term → D) (σ : List (Term × Term))
    {c : CL} (h : clFree c = true) :
    sat (M.evalL ρ) (clσ σ c) ↔ sat (M.evalL (fun v => M.evalT ρ (applyσ σ v))) c := by
  simp only [clFree, Bool.and_eq_true, List.all_eq_true] at h
  constructor
  · intro hs hbody
    have hbody' : ∀ a ∈ (clσ σ c).body, M.evalL ρ a := by
      intro a ha
      simp only [clσ, List.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      rw [evalL_litσ M ρ σ (h.1 b hb)]
      exact hbody b hb
    obtain ⟨a, ha, hIa⟩ := hs hbody'
    simp only [clσ, List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    rw [evalL_litσ M ρ σ (h.2 b hb)] at hIa
    exact ⟨b, hb, hIa⟩
  · intro hs hbody
    have hbody' : ∀ b ∈ c.body, M.evalL (fun v => M.evalT ρ (applyσ σ v)) b := by
      intro b hb
      rw [← evalL_litσ M ρ σ (h.1 b hb)]
      exact hbody (litσ σ b) (by simp only [clσ, List.mem_map]; exact ⟨b, hb, rfl⟩)
    obtain ⟨a, ha, hIa⟩ := hs hbody'
    refine ⟨litσ σ a, by simp only [clσ, List.mem_map]; exact ⟨a, ha, rfl⟩, ?_⟩
    rw [evalL_litσ M ρ σ (h.2 a ha)]; exact hIa

/-- **Universal instantiation is sound.**  An instance of a valid clause is
    valid. -/
theorem inst_valid (M : FModel D) {p : CL} (hp : validFO M p) (hfree : clFree p = true)
    (σ : List (Term × Term)) : validFO M (clσ σ p) := by
  intro ρ
  rw [sat_clσ M ρ σ hfree]
  exact hp _

/-! ### Paramodulation (superposition): rewriting a term *inside* a literal -/

/-- Rewriting `s ↦ t` inside a literal preserves its truth value when `s` and `t`
    have equal values — the first-order version of `Basic.paramodulation_sound`. -/
theorem evalL_rewriteLit (M : FModel D) (ρ : Term → D) (s t : Term)
    (heq : M.evalT ρ s = M.evalT ρ t) {L L' : Lit} (hrw : rewriteLit s t L = some L') :
    M.evalL ρ L ↔ M.evalL ρ L' := by
  cases L with
  | P p =>
    cases p with
    | concept i u =>
      unfold rewriteLit at hrw
      by_cases hu : u = s
      · subst hu; simp at hrw; subst hrw; simp [FModel.evalL, heq]
      · simp [hu] at hrw
    | role i u v =>
      unfold rewriteLit at hrw
      by_cases hu : u = s
      · subst hu; simp at hrw; subst hrw; simp [FModel.evalL, heq]
      · by_cases hv : v = s
        · subst hv; simp [hu] at hrw; subst hrw; simp [FModel.evalL, heq]
        · simp [hu, hv] at hrw
  | eq u v =>
    unfold rewriteLit at hrw
    by_cases hu : u = s
    · subst hu; simp at hrw; subst hrw; simp [FModel.evalL, heq]
    · simp [hu] at hrw
  | ineq u v =>
    unfold rewriteLit at hrw
    by_cases hu : u = s
    · subst hu; simp at hrw; subst hrw; simp [FModel.evalL, heq]
    · simp [hu] at hrw

/-- The paramodulant of `c1` (with the equality `s ≈ t` in its head) into the
    literal `L` of `c2`: `L` is rewritten `s ↦ t`. -/
def paraResolvent (c1 c2 : CL) (s t : Term) (L L' : Lit) : CL :=
  ⟨c1.body ++ c2.body, L' :: (without (Lit.eq s t) c1.head ++ without L c2.head)⟩

/-- **Soundness of paramodulation into a literal.** -/
theorem paraResolvent_sound (M : FModel D) (ρ : Term → D) (c1 c2 : CL)
    (s t : Term) (L L' : Lit) (h1 : sat (M.evalL ρ) c1) (h2 : sat (M.evalL ρ) c2)
    (he : Lit.eq s t ∈ c1.head) (hL : L ∈ c2.head) (hrw : rewriteLit s t L = some L') :
    sat (M.evalL ρ) (paraResolvent c1 c2 s t L L') := by
  intro hbody
  have hb1 : ∀ a ∈ c1.body, M.evalL ρ a := fun a ha =>
    hbody a (by simp only [paraResolvent, List.mem_append]; exact Or.inl ha)
  have hb2 : ∀ a ∈ c2.body, M.evalL ρ a := fun a ha =>
    hbody a (by simp only [paraResolvent, List.mem_append]; exact Or.inr ha)
  obtain ⟨a, ha, hIa⟩ := h1 hb1
  by_cases haeq : a = Lit.eq s t
  · have heqv : M.evalT ρ s = M.evalT ρ t := by subst haeq; simpa [FModel.evalL] using hIa
    obtain ⟨b, hb, hIb⟩ := h2 hb2
    by_cases hbL : b = L
    · subst hbL
      refine ⟨L', by simp [paraResolvent], ?_⟩
      exact (evalL_rewriteLit M ρ s t heqv hrw).mp hIb
    · exact ⟨b, by
        simp only [paraResolvent, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (mem_without.mpr ⟨hb, hbL⟩)), hIb⟩
  · exact ⟨a, by
      simp only [paraResolvent, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inl (mem_without.mpr ⟨ha, haeq⟩)), hIa⟩

/-! ### The checker -/

inductive JustifFO where
  | prem (i : Nat) (σ : List (Term × Term))   -- instance of premise `O[i]`
  | core                                       -- the context core `→ A(x)`
  | taut                                       -- a tautology
  | res (i j : Nat) (a : Lit)                  -- resolvent of entries `i`, `j`
  | para (i j : Nat) (s t : Term) (L : Lit)    -- paramodulate `s≈t` of `i` into `L` of `j`
deriving Repr

def stepOkFO (O : List CL) (A : Nat) (done : List CL) (c : CL) : JustifFO → Bool
  | .prem i σ =>
      match O[i]? with
      | some p => (clFree p || decide (σ = [])) && decide (clEquiv c (clσ σ p))
      | none => false
  | .core => decide (clEquiv c (coreClause A))
  | .taut => decide (∃ a ∈ c.body, a ∈ c.head)
  | .res i j a =>
      match done[i]?, done[j]? with
      | some c1, some c2 =>
          decide (a ∈ c1.head) && decide (a ∈ c2.body) && decide (clEquiv c (resolvent c1 c2 a))
      | _, _ => false
  | .para i j s t L =>
      match done[i]?, done[j]?, rewriteLit s t L with
      | some c1, some c2, some L' =>
          decide (Lit.eq s t ∈ c1.head) && decide (L ∈ c2.head)
            && decide (clEquiv c (paraResolvent c1 c2 s t L L'))
      | _, _, _ => false

section Soundness

variable (M : FModel D) (a0 : D) (O : List CL) (A : Nat)

/-- The fixed assignment placing the context element at `a0`. -/
def ρ0 : Term → D := fun _ => a0

/-- "Entry holds": true under the fixed assignment `ρ0`. -/
private def holds (c : CL) : Prop := sat (M.evalL (ρ0 a0)) c

theorem stepOkFO_sound (hO : ∀ p ∈ O, validFO M p) (hA : M.conc A a0)
    {done : List CL} (hdone : ∀ d ∈ done, holds M a0 d)
    {c : CL} {j : JustifFO} (h : stepOkFO O A done c j = true) : holds M a0 c := by
  cases j with
  | prem i σ =>
    simp only [stepOkFO] at h
    rcases hi : O[i]? with _ | p
    · rw [hi] at h; simp at h
    · rw [hi] at h
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨hfree, heq⟩ := h
      have hp : validFO M p := hO p (List.mem_of_getElem? hi)
      have hval : holds M a0 (clσ σ p) := by
        rcases hfree with hfree | hempty
        · exact inst_valid M hp hfree σ (ρ0 a0)
        · subst hempty; rw [clσ_nil]; exact hp (ρ0 a0)
      exact sat_of_clEquiv heq hval
  | core =>
    simp only [stepOkFO, decide_eq_true_eq] at h
    refine sat_of_clEquiv h ?_
    show sat (M.evalL (ρ0 a0)) (coreClause A)
    refine (sat_coreClause (M.evalL (ρ0 a0)) A).mpr ?_
    show M.conc A (M.evalT (ρ0 a0) Term.x)
    have : M.evalT (ρ0 a0) Term.x = a0 := by simp [FModel.evalT, Term.x, ρ0]
    rw [this]; exact hA
  | taut =>
    simp only [stepOkFO, decide_eq_true_eq] at h
    obtain ⟨a, hb, hh⟩ := h
    intro hbody; exact ⟨a, hh, hbody a hb⟩
  | res i j a =>
    simp only [stepOkFO] at h
    rcases hi : done[i]? with _ | c1
    · rw [hi] at h; simp at h
    · rcases hj : done[j]? with _ | c2
      · rw [hi, hj] at h; simp at h
      · rw [hi, hj] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨ha1, ha2⟩, heq⟩ := h
        have h1 : holds M a0 c1 := hdone c1 (List.mem_of_getElem? hi)
        have h2 : holds M a0 c2 := hdone c2 (List.mem_of_getElem? hj)
        exact sat_of_clEquiv heq (resolution_sound (M.evalL (ρ0 a0)) c1 c2 a h1 h2 ha1 ha2)
  | para i j s t L =>
    simp only [stepOkFO] at h
    rcases hi : done[i]? with _ | c1
    · rw [hi] at h; simp at h
    · rcases hj : done[j]? with _ | c2
      · rw [hi, hj] at h; simp at h
      · rcases hrw : rewriteLit s t L with _ | L'
        · rw [hi, hj, hrw] at h; simp at h
        · rw [hi, hj, hrw] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨he, hL⟩, heq⟩ := h
          have h1 : holds M a0 c1 := hdone c1 (List.mem_of_getElem? hi)
          have h2 : holds M a0 c2 := hdone c2 (List.mem_of_getElem? hj)
          exact sat_of_clEquiv heq
            (paraResolvent_sound M (ρ0 a0) c1 c2 s t L L' h1 h2 he hL hrw)

def checkFoldFO (O : List CL) (A : Nat) : List CL → List (CL × JustifFO) → Option (List CL)
  | done, [] => some done
  | done, (c, j) :: rest =>
      if stepOkFO O A done c j then checkFoldFO O A (done ++ [c]) rest else none

theorem checkFoldFO_sound (hO : ∀ p ∈ O, validFO M p) (hA : M.conc A a0) :
    ∀ {done : List CL} {cert : List (CL × JustifFO)} {final : List CL},
      (∀ d ∈ done, holds M a0 d) → checkFoldFO O A done cert = some final →
      ∀ d ∈ final, holds M a0 d := by
  intro done cert
  induction cert generalizing done with
  | nil => intro final hdone hf; simp only [checkFoldFO, Option.some.injEq] at hf; subst hf; exact hdone
  | cons hd rest ih =>
    intro final hdone hf
    obtain ⟨c, j⟩ := hd
    simp only [checkFoldFO] at hf
    by_cases hstep : stepOkFO O A done c j
    · rw [if_pos hstep] at hf
      have hc : holds M a0 c := stepOkFO_sound M a0 O A hO hA hdone hstep
      refine ih (fun d hd' => ?_) hf
      rcases List.mem_append.mp hd' with h | h
      · exact hdone d h
      · simp only [List.mem_singleton] at h; subst h; exact hc
    · rw [if_neg hstep] at hf; simp at hf

end Soundness

def checkCertFO (O : List CL) (A : Nat) (cert : List (CL × JustifFO)) (target : CL) : Bool :=
  match checkFoldFO O A [] cert with
  | some final => decide (target ∈ final)
  | none => false

/-- **Validated subsumption (first-order).**  If the certificate derives `→ B(x)`
    from the premises `O` (used via universal instances) and the core `→ A(x)`,
    then `O ⊨ A ⊑ B`: in every first-order model of `O`, every `A` is a `B`. -/
theorem certifies_subsumptionFO (O : List CL) (A B : Nat) (cert : List (CL × JustifFO))
    (h : checkCertFO O A cert ⟨[], [Lit.P (Pred.concept B Term.x)]⟩ = true)
    (M : FModel D) (hO : ∀ p ∈ O, validFO M p) (a0 : D) (hA : M.conc A a0) :
    M.conc B a0 := by
  unfold checkCertFO at h
  rcases hf : checkFoldFO O A [] cert with _ | final
  · rw [hf] at h; simp at h
  · rw [hf] at h
    simp only [decide_eq_true_eq] at h
    have hfin := checkFoldFO_sound M a0 O A hO hA (by intro d hd; cases hd) hf
    have htgt : holds M a0 ⟨[], [Lit.P (Pred.concept B Term.x)]⟩ := hfin _ h
    obtain ⟨a, ha, hIa⟩ := htgt (by intro a ha; cases ha)
    simp only [List.mem_singleton] at ha; subst ha
    have : M.evalT (ρ0 a0) Term.x = a0 := by simp [FModel.evalT, Term.x, ρ0]
    simpa [FModel.evalL, this] using hIa

/-- **Validated inconsistency (first-order).**  If the certificate derives the
    empty clause, then `O ⊨ A ⊑ ⊥`: no first-order model has an `A`. -/
theorem certifies_unsatFO (O : List CL) (A : Nat) (cert : List (CL × JustifFO))
    (h : checkCertFO O A cert ⟨[], []⟩ = true)
    (M : FModel D) (hO : ∀ p ∈ O, validFO M p) (a0 : D) : ¬ M.conc A a0 := by
  intro hA
  unfold checkCertFO at h
  rcases hf : checkFoldFO O A [] cert with _ | final
  · rw [hf] at h; simp at h
  · rw [hf] at h
    simp only [decide_eq_true_eq] at h
    have hfin := checkFoldFO_sound M a0 O A hO hA (by intro d hd; cases hd) hf
    exact sat_empty (M.evalL (ρ0 a0)) (hfin _ h)

end ContextCalculus.CheckerFO
