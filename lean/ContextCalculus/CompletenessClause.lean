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

/-! ### General ground-clause entailment -/

theorem sat_unit_pos (I : Model Atom) (a : Atom) :
    sat I (⟨[], [a]⟩ : Clause Atom) ↔ I a := by
  unfold sat; simp

theorem sat_unit_neg (I : Model Atom) (a : Atom) :
    sat I (⟨[a], []⟩ : Clause Atom) ↔ ¬ I a := by
  unfold sat; simp

/-- The premise set augmenting `O` with the negation of a ground clause `C`:
    assert every body atom (`→a`) and negate every head atom (`a→`). -/
def aug (O : List (Clause Atom)) (C : Clause Atom) : List (Clause Atom) :=
  O ++ C.body.map (fun a => ⟨[], [a]⟩) ++ C.head.map (fun a => ⟨[a], []⟩)

/-- **Clause-level completeness & soundness for arbitrary ground-clause
    entailment.**  `O ⊨ C` (every model of `O` satisfies the clause `C`) holds
    **iff** the engine's resolution refutes `O` together with the negation of `C`
    (assert `C`'s body, negate `C`'s head).  Atomic subsumption is the special
    case `C = A(x) → B(x)`. -/
theorem entails_refut_iff (O : List (Clause Atom)) (C : Clause Atom) :
    (∀ I : Model Atom, (∀ c ∈ O, sat I c) → sat I C)
      ↔ Derivable (aug O C) (⟨[], []⟩ : Clause Atom) := by
  constructor
  · intro hent
    apply completeness
    rintro ⟨I, hI⟩
    have hmem : ∀ c ∈ O, sat I c :=
      fun c hc => hI c (by unfold aug; rw [List.mem_append, List.mem_append]; tauto)
    have hbody : ∀ a ∈ C.body, I a := by
      intro a ha
      refine (sat_unit_pos I a).1 (hI _ ?_)
      unfold aug; rw [List.mem_append, List.mem_append]
      exact Or.inl (Or.inr (List.mem_map_of_mem ha))
    have hhead : ∀ a ∈ C.head, ¬ I a := by
      intro a ha
      refine (sat_unit_neg I a).1 (hI _ ?_)
      unfold aug; rw [List.mem_append]
      exact Or.inr (List.mem_map_of_mem ha)
    obtain ⟨a, ha, hIa⟩ := hent I hmem hbody
    exact hhead a ha hIa
  · intro hder I hO hbody
    by_contra hno
    have hall : ∀ c ∈ aug O C, sat I c := by
      intro c hc
      unfold aug at hc
      rw [List.mem_append, List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · exact hO c hc
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
        exact (sat_unit_pos I a).2 (hbody a ha)
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
        exact (sat_unit_neg I a).2 (fun hIa => hno ⟨a, ha, hIa⟩)
    exact sat_empty I (derivable_sound I _ hall hder)

/-! ### First-order Herbrand model existence (equality-free fragment)

`Basic.TermModel` interprets `Lit.eq` by *real* equality of valuations, so a
propositional model lifts to a genuine first-order term model only on the
equality-free fragment (concept/role literals — ALC without the number-restriction
`Eq` machinery).  There the engine's failure to refute yields an actual
first-order model. -/

/-- The Herbrand term model from a propositional model: domain = terms, valuation
    the identity, concepts/roles read off the propositional truth assignment. -/
def herbrandModel (I : Model Lit) : TermModel Term where
  val := id
  conc := fun i d => I (Lit.P (Pred.concept i d))
  rol := fun i s t => I (Lit.P (Pred.role i s t))

theorem eval_herbrand_P (I : Model Lit) (p : Pred) :
    (herbrandModel I).eval (Lit.P p) = I (Lit.P p) := by
  cases p <;> rfl

/-- A literal is equality-free (a concept/role atom). -/
def IsP : Lit → Prop
  | Lit.P _ => True
  | _ => False

theorem eval_herbrand_of_IsP (I : Model Lit) {L : Lit} (h : IsP L) :
    (herbrandModel I).eval L = I L := by
  cases L with
  | P p => exact eval_herbrand_P I p
  | eq _ _ => exact absurd h (by simp [IsP])
  | ineq _ _ => exact absurd h (by simp [IsP])

/-- A clause is equality-free when every literal is a concept/role atom. -/
def EqFree (c : Clause Lit) : Prop :=
  (∀ L ∈ c.body, IsP L) ∧ (∀ L ∈ c.head, IsP L)

/-- Satisfaction of a clause in a term model. -/
def tsat {D : Type} (M : TermModel D) (c : Clause Lit) : Prop :=
  (∀ L ∈ c.body, M.eval L) → (∃ L ∈ c.head, M.eval L)

theorem tsat_herbrand_of_sat (I : Model Lit) {c : Clause Lit} (hf : EqFree c) :
    tsat (herbrandModel I) c ↔ sat I c := by
  have hb : (∀ L ∈ c.body, (herbrandModel I).eval L) ↔ (∀ L ∈ c.body, I L) := by
    constructor <;> intro h L hL
    · exact (eval_herbrand_of_IsP I (hf.1 L hL)) ▸ h L hL
    · exact (eval_herbrand_of_IsP I (hf.1 L hL)).symm ▸ h L hL
  have hh : (∃ L ∈ c.head, (herbrandModel I).eval L) ↔ (∃ L ∈ c.head, I L) := by
    constructor
    · rintro ⟨L, hL, hev⟩; exact ⟨L, hL, (eval_herbrand_of_IsP I (hf.2 L hL)) ▸ hev⟩
    · rintro ⟨L, hL, hev⟩; exact ⟨L, hL, (eval_herbrand_of_IsP I (hf.2 L hL)).symm ▸ hev⟩
  unfold tsat sat; rw [hb, hh]

/-- **First-order Herbrand model existence.**  An equality-free clause set the
    engine cannot refute has a genuine first-order term model. -/
theorem herbrand_model_existence (O : List (Clause Lit))
    (hf : ∀ c ∈ O, EqFree c)
    (h : ¬ Derivable O (⟨[], []⟩ : Clause Lit)) :
    ∃ M : TermModel Term, ∀ c ∈ O, tsat M c := by
  have hmodel : ∃ I : Lit → Prop, ∀ c ∈ O, sat I c := by
    by_contra hno; exact h (completeness O hno)
  obtain ⟨I, hI⟩ := hmodel
  exact ⟨herbrandModel I, fun c hc => (tsat_herbrand_of_sat I (hf c hc)).2 (hI c hc)⟩

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

/-- **Soundness companion** (refutational form).  If the engine refutes `A ⊓ ¬B`
    then `O ⊨ A ⊑ B`.  (Re-derived here in the `coreClause`/`negClause`
    formulation so it pairs with `subsumption_refut_complete`.) -/
theorem subsumption_refut_sound (O : List (Clause Lit)) (A B : Nat)
    (hder : Derivable (O ++ [coreClause A, negClause B]) (⟨[], []⟩ : Clause Lit))
    (I : Model Lit) (hO : ∀ c ∈ O, sat I c)
    (hA : I (Lit.P (Pred.concept A Term.x))) : I (Lit.P (Pred.concept B Term.x)) := by
  by_contra hnB
  have hall : ∀ c ∈ (O ++ [coreClause A, negClause B]), sat I c := by
    intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hO c hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact (sat_coreClause I A).2 hA
      · exact (sat_negClause I B).2 hnB
  exact sat_empty I (derivable_sound I _ hall hder)

/-- **Clause-level decidability of subsumption (capstone).**  On the
    ground/propositional fragment, `O ⊨ A ⊑ B` holds **iff** the engine's
    resolution refutes `A ⊓ ¬B` — soundness (`subsumption_refut_sound`,
    `Basic.derivable_sound`) and completeness (`subsumption_refut_complete`,
    `PropRes.completeness`) for the engine's own `Derivable`, in one statement. -/
theorem subsumption_refut_iff (O : List (Clause Lit)) (A B : Nat) :
    (∀ I : Model Lit, (∀ c ∈ O, sat I c) →
        I (Lit.P (Pred.concept A Term.x)) → I (Lit.P (Pred.concept B Term.x)))
      ↔ Derivable (O ++ [coreClause A, negClause B]) (⟨[], []⟩ : Clause Lit) :=
  ⟨subsumption_refut_complete O A B,
   fun hder I hO hA => subsumption_refut_sound O A B hder I hO hA⟩

/-- **Model existence.**  If the engine cannot derive `⊥` from a finite clause
    set, the set has a (propositional) model.  Contrapositive of `completeness`. -/
theorem model_existence (O : List (Clause Atom))
    (h : ¬ Derivable O (⟨[], []⟩ : Clause Atom)) :
    ∃ I : Atom → Prop, ∀ c ∈ O, sat I c := by
  by_contra hno
  exact h (completeness O hno)

/-- **Clause-level consistency decidability.**  A finite clause set is
    (propositionally) satisfiable **iff** the engine's resolution does *not* derive
    the empty clause — soundness (`Basic.derivable_sound`) one way, completeness
    (`completeness`) the other.  This is the consistency-checking counterpart of
    `subsumption_refut_iff`. -/
theorem consistent_iff (O : List (Clause Atom)) :
    (∃ I : Atom → Prop, ∀ c ∈ O, sat I c) ↔ ¬ Derivable O (⟨[], []⟩ : Clause Atom) := by
  constructor
  · rintro ⟨I, hI⟩ hder
    exact sat_empty I (derivable_sound I O hI hder)
  · exact model_existence O

end ContextCalculus.ClauseComplete
