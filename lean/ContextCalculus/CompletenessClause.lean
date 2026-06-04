/-
  ContextCalculus/CompletenessClause.lean
  =======================================
  **Refutational completeness of the engine's resolution, on its real clause
  type.**

  `Basic.lean` proves *soundness* of the engine's resolution closure
  `Derivable` over the concrete clause type `Clause Lit` (`subsumption_sound`,
  `unsat_sound`).  `CompletenessProp.lean` proves *completeness* of propositional
  resolution, but over a *separate* set-based clause type `PropRes.PClause`.  This
  file wires the two together: it transports `PropRes.completeness` onto the
  engine's own `Derivable`, giving — `sorry`-free — the completeness counterpart of
  `subsumption_sound`/`unsat_sound`:

    * `completeness`             — `Basic.Derivable` refutes every (propositionally)
                                   unsatisfiable finite clause set: derives `→` (`⊥`);
    * `unsat_complete`           — if `A` is unsatisfiable then the engine derives `⊥`
                                   in the context of `A`;
    * `subsumption_refut_complete` — if `O ⊨ A ⊑ B` then the engine refutes
                                   `A ⊓ ¬B` (derives `⊥` from `O, →A(x), B(x)→`).

  The bridge is a clause map `toP : Clause Atom → PClause Atom` (lists → finsets)
  that commutes with resolution (`toP_resolvent`) and preserves satisfaction
  (`sat_toP`); a derivation in `PropRes` is then lifted step-for-step back to
  `Basic.Derivable` (`lift`).

  Scope.  This is the **ground/propositional** layer — the Core/Hyper/Pred/Elim
  resolution direction — for the engine's actual clauses.  The orthogonal
  term-generating layer (Succ, instantiating clauses at fresh successor terms
  `f(x)`) is the existential direction handled in `CompletenessEL`/
  `CompletenessContext`; combining the two into one first-order completeness
  theorem for `Derivable` over a saturated term set remains the larger open
  development.
-/
import ContextCalculus.Basic
import ContextCalculus.CompletenessProp

namespace ContextCalculus.ClauseComplete

open ContextCalculus

variable {Atom : Type} [DecidableEq Atom]

/-- Map an engine clause (body/head lists) to a propositional clause
    (neg/pos finsets). -/
def toP (c : Clause Atom) : PropRes.PClause Atom :=
  ⟨c.body.toFinset, c.head.toFinset⟩

/-- Satisfaction is preserved by the list→finset map. -/
theorem sat_toP (I : Atom → Prop) (c : Clause Atom) :
    sat I c ↔ (toP c).sat I := by
  unfold sat PropRes.PClause.sat toP
  simp only [List.mem_toFinset]

theorem without_toFinset (a : Atom) (l : List Atom) :
    (without a l).toFinset = l.toFinset.erase a := by
  ext b
  simp only [List.mem_toFinset, Finset.mem_erase, mem_without]
  tauto

theorem toFinset_eq_empty {l : List Atom} (h : l.toFinset = ∅) : l = [] := by
  cases hl : l with
  | nil => rfl
  | cons x xs =>
      have hx : x ∈ l.toFinset := by rw [hl]; simp
      rw [h] at hx; simp at hx

/-- The clause map commutes with resolution. -/
theorem toP_resolvent (c1 c2 : Clause Atom) (a : Atom) :
    toP (resolvent c1 c2 a) = PropRes.resolvent (toP c1) (toP c2) a := by
  unfold toP resolvent PropRes.resolvent
  simp [List.toFinset_append, without_toFinset]

/-- **Lifting.**  Every `PropRes` derivation from the mapped premises is the image
    of a genuine `Basic.Derivable` derivation. -/
theorem lift (O : List (Clause Atom)) :
    ∀ {D}, PropRes.Derivable ((O.map toP).toFinset) D → ∃ c, Derivable O c ∧ toP c = D := by
  intro D h
  induction h with
  | premise hc =>
      rw [List.mem_toFinset, List.mem_map] at hc
      obtain ⟨o, ho, hoeq⟩ := hc
      exact ⟨o, Derivable.premise ho, hoeq⟩
  | @resolve c1' c2' a _ _ m1 m2 ih1 ih2 =>
      obtain ⟨c1, hc1, he1⟩ := ih1
      obtain ⟨c2, hc2, he2⟩ := ih2
      have ha1' : a ∈ c1.head := by
        have : a ∈ (toP c1).pos := by rw [he1]; exact m1
        simpa [toP, List.mem_toFinset] using this
      have ha2' : a ∈ c2.body := by
        have : a ∈ (toP c2).neg := by rw [he2]; exact m2
        simpa [toP, List.mem_toFinset] using this
      refine ⟨resolvent c1 c2 a, Derivable.resolve hc1 hc2 ha1' ha2', ?_⟩
      rw [toP_resolvent, he1, he2]

/-- **Refutational completeness of the engine's resolution.**  If a finite clause
    set has no propositional model, `Basic.Derivable` derives the empty clause. -/
theorem completeness (O : List (Clause Atom))
    (h : ¬ ∃ I : Atom → Prop, ∀ c ∈ O, sat I c) :
    Derivable O (⟨[], []⟩ : Clause Atom) := by
  have hunsat : PropRes.Unsat ((O.map toP).toFinset) := by
    rintro ⟨I, hI⟩
    exact h ⟨I, fun c hc => (sat_toP I c).2
      (hI (toP c) (by rw [List.mem_toFinset, List.mem_map]; exact ⟨c, hc, rfl⟩))⟩
  obtain ⟨c, hder, hceq⟩ := lift O (PropRes.completeness _ hunsat)
  have hb : c.body = [] := by
    apply toFinset_eq_empty
    have := congrArg PropRes.PClause.neg hceq; simpa [toP, PropRes.PClause.bot] using this
  have hh : c.head = [] := by
    apply toFinset_eq_empty
    have := congrArg PropRes.PClause.pos hceq; simpa [toP, PropRes.PClause.bot] using this
  have : c = ⟨[], []⟩ := by cases c; simp_all
  exact this ▸ hder

/-! ### Classification corollaries (concrete `Lit` clauses) -/

/-- `B(x) →`, the clause negating `B(x)`. -/
def negClause (B : Nat) : Clause Lit := ⟨[Lit.P (Pred.concept B Term.x)], []⟩

theorem sat_negClause (I : Model Lit) (B : Nat) :
    sat I (negClause B) ↔ ¬ I (Lit.P (Pred.concept B Term.x)) := by
  unfold sat negClause
  simp

/-- **Completeness for unsatisfiability.**  If every model of `O` makes `A(x)`
    false (i.e. `O ⊨ A ⊑ ⊥`), the engine derives `⊥` in the context of `A`. -/
theorem unsat_complete (O : List (Clause Lit)) (A : Nat)
    (hent : ∀ I : Model Lit, (∀ c ∈ O, sat I c) → ¬ I (Lit.P (Pred.concept A Term.x))) :
    Derivable (O ++ [coreClause A]) (⟨[], []⟩ : Clause Lit) := by
  apply completeness
  rintro ⟨I, hI⟩
  have hO : ∀ c ∈ O, sat I c := fun c hc => hI c (by simp [hc])
  have hA : I (Lit.P (Pred.concept A Term.x)) :=
    (sat_coreClause I A).1 (hI (coreClause A) (by simp))
  exact hent I hO hA

/-- **Completeness for subsumption (refutational).**  If `O ⊨ A ⊑ B`, the engine
    refutes `A ⊓ ¬B`: it derives `⊥` from `O, →A(x), B(x)→`. -/
theorem subsumption_refut_complete (O : List (Clause Lit)) (A B : Nat)
    (hent : ∀ I : Model Lit, (∀ c ∈ O, sat I c) →
      I (Lit.P (Pred.concept A Term.x)) → I (Lit.P (Pred.concept B Term.x))) :
    Derivable (O ++ [coreClause A, negClause B]) (⟨[], []⟩ : Clause Lit) := by
  apply completeness
  rintro ⟨I, hI⟩
  have hO : ∀ c ∈ O, sat I c := fun c hc => hI c (by simp [hc])
  have hA : I (Lit.P (Pred.concept A Term.x)) :=
    (sat_coreClause I A).1 (hI (coreClause A) (by simp))
  have hnB : ¬ I (Lit.P (Pred.concept B Term.x)) :=
    (sat_negClause I B).1 (hI (negClause B) (by simp))
  exact hnB (hent I hO hA)

end ContextCalculus.ClauseComplete
