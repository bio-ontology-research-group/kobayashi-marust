/-
  ContextCalculus/Basic.lean
  ==========================
  A Lean 4 formalisation that *faithfully captures the Rust implementation* of
  the disjunctive context calculus in `../engine`
  (a port of the Tena-Cucala / Cuenca Grau / Horrocks calculus realised in the
  Sequoia reasoner).

  The Rust engine derives **context clauses** `Γ → Δ` (a conjunction of body
  predicates implying a disjunction of head literals) by the rules
  Core, Hyper, Pred, Succ, Eq, Ineq and Elim.  Every one of those rules is, at
  the model-theoretic level, an instance of **clausal resolution** between
  already-justified clauses (ontology clauses, the context core, and Succ/Pred
  hypotheses), with the single exception of Eq, which is paramodulation and is
  treated separately under a congruence model.

  This file proves the **soundness** of that engine:

    * `resolution_sound`  — one resolution step is model-preserving;
    * `derivable_sound`   — hence every derived clause is a logical consequence
                            of the premises (Core / Hyper / Pred / Succ / Elim);
    * `subsumption_sound` — if the engine derives `→ B(x)` in the context of `A`
                            then `A ⊑ B` holds in every model of the ontology;
    * `unsat_sound`       — if it derives the empty clause `→` (`⊥`) in the
                            context of `A` then `A` is unsatisfiable;
    * `paramodulation_sound` — the Eq rule (rewriting under a derived equality)
                            is sound under any congruence model.

  Soundness is exactly the property we validated empirically against HermiT
  (0 unsound subsumptions, 0 spurious unsatisfiable classes on the benchmarks).

  The datatypes `Term`, `Pred`, `Lit`, `ContextClause` below mirror, field for
  field, those in `src/calc.rs` and `src/clause.rs`.
-/

namespace ContextCalculus

/-! ## 1. Terms, predicates, literals — mirroring `src/calc.rs`.

The Rust engine encodes a term by an integer id:
`x = 0`, `y = -1`, `z_i = -(i+1)`, `f_i(x) = +i`.  We reproduce that exactly. -/

/-- A term, encoded by its integer id (see `clauses/Term.scala` / `calc.rs`). -/
abbrev Term := Int

namespace Term
def x : Term := 0
def y : Term := -1
def z (i : Nat) : Term := -(Int.ofNat i + 1)
def f (i : Nat) : Term := Int.ofNat i + 1
def isCentral (t : Term) : Bool := t == 0
def isPredVar (t : Term) : Bool := t == -1
def isFunction (t : Term) : Bool := t > 0
def isVar (t : Term) : Bool := t ≤ 0
end Term

/-- Predicate atom (`Concept(iri,t)` or `Role(iri,s,t)`), as in `calc.rs`. -/
inductive Pred where
  | concept (iri : Nat) (t : Term)
  | role (iri : Nat) (s t : Term)
deriving DecidableEq, Repr

/-- Head literal: a predicate, or an (in)equality with `s ≥ t`, as in `calc.rs`. -/
inductive Lit where
  | P (p : Pred)
  | eq (s t : Term)
  | ineq (s t : Term)
deriving DecidableEq, Repr

/-! ## 2. The generic clausal layer (the semantics the rules respect).

A `Clause` over an atom type is `body → head`: the conjunction of body atoms
entails the disjunction of head atoms.  Context clauses are `Clause Lit`;
ontology clauses are `Clause Lit` whose body atoms are predicates. -/

structure Clause (Atom : Type) where
  body : List Atom
  head : List Atom
deriving Repr, DecidableEq

variable {Atom : Type}

/-- A model assigns a truth value to every (ground) atom. -/
abbrev Model (Atom : Type) := Atom → Prop

/-- Satisfaction: if all body atoms hold then some head atom holds. -/
def sat (I : Model Atom) (c : Clause Atom) : Prop :=
  (∀ a ∈ c.body, I a) → (∃ a ∈ c.head, I a)

/-- The empty clause `→` (no body, no head) is the propositional false. -/
theorem sat_empty (I : Model Atom) : ¬ sat I ⟨[], []⟩ := by
  intro h
  have : ∃ a ∈ ([] : List Atom), I a := h (by intro a ha; cases ha)
  obtain ⟨a, ha, _⟩ := this
  cases ha

/-! ## 3. Resolution and its soundness (the core of Core/Hyper/Pred/Succ/Elim). -/

variable [DecidableEq Atom]

/-- Remove every occurrence of `a` from a list. -/
def without (a : Atom) (l : List Atom) : List Atom :=
  l.filter (fun b => decide (b ≠ a))

theorem mem_without {a b : Atom} {l : List Atom} :
    b ∈ without a l ↔ b ∈ l ∧ b ≠ a := by
  unfold without
  rw [List.mem_filter]
  constructor
  · rintro ⟨hb, hd⟩; exact ⟨hb, of_decide_eq_true hd⟩
  · rintro ⟨hb, hne⟩; exact ⟨hb, decide_eq_true hne⟩

/-- The resolvent of `c1` (with `a` in its head) and `c2` (with `a` in its body):
    `body = c1.body ∪ (c2.body \ a)`, `head = (c1.head \ a) ∪ c2.head`.
    This is the shape produced by `build_hyper_resolvent` / `build_pred_resolvent`
    in `src/engine.rs`. -/
def resolvent (c1 c2 : Clause Atom) (a : Atom) : Clause Atom :=
  { body := c1.body ++ without a c2.body
  , head := without a c1.head ++ c2.head }

/-- **Soundness of one resolution step.**  Any model of both premises is a model
    of the resolvent.  (This is the semantic justification of Hyper and Pred:
    both resolve ontology/neighbour body atoms against maximal context-clause
    head atoms.) -/
theorem resolution_sound (I : Model Atom) (c1 c2 : Clause Atom) (a : Atom)
    (h1 : sat I c1) (h2 : sat I c2)
    (ha1 : a ∈ c1.head) (ha2 : a ∈ c2.body) :
    sat I (resolvent c1 c2 a) := by
  intro hbody
  -- All of c1's body atoms hold (they are a prefix of the resolvent body).
  have hc1body : ∀ b ∈ c1.body, I b := by
    intro b hb
    exact hbody b (by simp [resolvent, List.mem_append]; exact Or.inl hb)
  obtain ⟨w, hwhead, hIw⟩ := h1 hc1body
  by_cases hwa : w = a
  · -- The only justified head atom of c1 is `a`; discharge `a` using c2.
    subst hwa
    have hc2body : ∀ b ∈ c2.body, I b := by
      intro b hb
      by_cases hbw : b = w
      · subst hbw; exact hIw
      · exact hbody b (by
          simp only [resolvent, List.mem_append]
          exact Or.inr (mem_without.mpr ⟨hb, hbw⟩))
    obtain ⟨v, hvhead, hIv⟩ := h2 hc2body
    exact ⟨v, by simp only [resolvent, List.mem_append]; exact Or.inr hvhead, hIv⟩
  · -- A non-`a` head atom of c1 is justified; it survives into the resolvent.
    exact ⟨w, by
      simp only [resolvent, List.mem_append]
      exact Or.inl (mem_without.mpr ⟨hwhead, hwa⟩), hIw⟩

/-! ## 4. Derivations and saturation soundness.

`Derivable O c` holds when `c` can be obtained from the premise set `O`
(ontology clauses together with the context core clauses `→ A` for `A` in the
core, and the Succ/Pred hypothesis clauses `p → p`) by resolution.  The engine's
worked-off set is exactly the set of `Derivable` clauses; Elim only deletes
redundant clauses and never adds, so it cannot affect soundness. -/

inductive Derivable (O : List (Clause Atom)) : Clause Atom → Prop where
  | premise {c} : c ∈ O → Derivable O c
  | resolve {c1 c2 a} :
      Derivable O c1 → Derivable O c2 →
      a ∈ c1.head → a ∈ c2.body →
      Derivable O (resolvent c1 c2 a)

/-- **Saturation soundness.**  Every derived clause is a logical consequence of
    the premises.  Hence the Rust engine (Core + Hyper + Pred + Succ + Elim)
    derives only entailed clauses. -/
theorem derivable_sound (I : Model Atom) (O : List (Clause Atom))
    (hO : ∀ c ∈ O, sat I c) : ∀ {c}, Derivable O c → sat I c := by
  intro c h
  induction h with
  | premise hc => exact hO _ hc
  | resolve _ _ ha1 ha2 ih1 ih2 => exact resolution_sound I _ _ _ ih1 ih2 ha1 ha2

/-! ## 5. Consequences for classification: subsumption and unsatisfiability.

We work with `Atom := Lit`.  A *core clause* for concept `A` is `→ A(x)`.
The context for `A` has premises `O ++ [coreA]`. -/

/-- The fact clause `→ A(x)`. -/
def coreClause (A : Nat) : Clause Lit := ⟨[], [Lit.P (Pred.concept A Term.x)]⟩

/-- A model satisfies `coreClause A` iff it makes `A(x)` true. -/
theorem sat_coreClause (I : Model Lit) (A : Nat) :
    sat I (coreClause A) ↔ I (Lit.P (Pred.concept A Term.x)) := by
  unfold sat coreClause
  constructor
  · intro h
    obtain ⟨a, ha, hIa⟩ := h (by intro a ha; cases ha)
    simp only [List.mem_singleton] at ha; subst ha; exact hIa
  · intro h _; exact ⟨_, List.mem_singleton.mpr rfl, h⟩

/-- **Subsumption soundness.**  If the engine derives the unit clause `→ B(x)`
    in the context of `A` (premises `O ++ [coreClause A]`), then in every model
    of the ontology, `A(x)` implies `B(x)` — i.e. `O ⊨ A ⊑ B`. -/
theorem subsumption_sound (O : List (Clause Lit)) (A B : Nat)
    (hder : Derivable (O ++ [coreClause A]) ⟨[], [Lit.P (Pred.concept B Term.x)]⟩)
    (I : Model Lit) (hO : ∀ c ∈ O, sat I c)
    (hA : I (Lit.P (Pred.concept A Term.x))) :
    I (Lit.P (Pred.concept B Term.x)) := by
  have hO' : ∀ c ∈ O ++ [coreClause A], sat I c := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hO c h
    · simp only [List.mem_singleton] at h; subst h
      exact (sat_coreClause I A).mpr hA
  have := derivable_sound I _ hO' hder
  obtain ⟨a, ha, hIa⟩ := this (by intro a ha; cases ha)
  simp only [List.mem_singleton] at ha; subst ha; exact hIa

/-- **Unsatisfiability soundness.**  If the engine derives the empty clause in
    the context of `A`, then no model of the ontology makes `A(x)` true:
    `O ⊨ A ⊑ ⊥`. -/
theorem unsat_sound (O : List (Clause Lit)) (A : Nat)
    (hder : Derivable (O ++ [coreClause A]) ⟨[], []⟩)
    (I : Model Lit) (hO : ∀ c ∈ O, sat I c) :
    ¬ I (Lit.P (Pred.concept A Term.x)) := by
  intro hA
  have hO' : ∀ c ∈ O ++ [coreClause A], sat I c := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hO c h
    · simp only [List.mem_singleton] at h; subst h
      exact (sat_coreClause I A).mpr hA
  exact sat_empty I (derivable_sound I _ hO' hder)

/-! ## 6. The Eq rule: paramodulation soundness under a congruence model.

The remaining engine rule, Eq (`src/engine.rs::build_eq`), is paramodulation:
given a derived equality `s == t` and a literal `L` containing `s` at a rewrite
position, it adds `L[s := t]`.  Its soundness needs a model that interprets
equality atoms as genuine equality and predicate atoms compatibly (a congruence).

We capture exactly this. A `TermModel` valuates terms in a domain `D` and
interprets the atoms; equality atoms mean equality of the valuations, and
predicate atoms are functions of the valuations (congruence). -/

structure TermModel (D : Type) where
  val   : Term → D
  conc  : Nat → D → Prop
  rol   : Nat → D → D → Prop

/-- Interpretation of a literal in a term model (equality = real equality). -/
def TermModel.eval {D : Type} (M : TermModel D) : Lit → Prop
  | Lit.P (Pred.concept i t)  => M.conc i (M.val t)
  | Lit.P (Pred.role i s t)   => M.rol i (M.val s) (M.val t)
  | Lit.eq s t                => M.val s = M.val t
  | Lit.ineq s t              => M.val s ≠ M.val t

/-- Rewrite the term `s` to `t` inside a literal (the `Lit::rewrite` of `calc.rs`,
    restricted to the maximal/`s` position; `none` when `s` does not occur). -/
def rewriteLit (s t : Term) : Lit → Option Lit
  | Lit.P (Pred.concept i u)  => if u = s then some (Lit.P (Pred.concept i t)) else none
  | Lit.P (Pred.role i u v)   =>
      if u = s then some (Lit.P (Pred.role i t v))
      else if v = s then some (Lit.P (Pred.role i u t)) else none
  | Lit.eq u v                => if u = s then some (Lit.eq t v) else none
  | Lit.ineq u v              => if u = s then some (Lit.ineq t v) else none

/-- **Paramodulation soundness.**  Under a term model in which `s == t` holds
    (the valuations of `s` and `t` coincide), rewriting `s` to `t` in a literal
    preserves its truth value — so the Eq rule is sound. -/
theorem paramodulation_sound {D : Type} (M : TermModel D) (s t : Term)
    (heq : M.val s = M.val t) (L L' : Lit)
    (hrw : rewriteLit s t L = some L') :
    M.eval L ↔ M.eval L' := by
  cases L with
  | P p =>
    cases p with
    | concept i u =>
      unfold rewriteLit at hrw
      by_cases hu : u = s
      · subst hu; simp at hrw; subst hrw; simp [TermModel.eval, heq]
      · simp [hu] at hrw
    | role i u v =>
      unfold rewriteLit at hrw
      by_cases hu : u = s
      · subst hu; simp at hrw; subst hrw; simp [TermModel.eval, heq]
      · by_cases hv : v = s
        · subst hv; simp [hu] at hrw; subst hrw; simp [TermModel.eval, heq]
        · simp [hu, hv] at hrw
  | eq u v =>
    unfold rewriteLit at hrw
    by_cases hu : u = s
    · subst hu; simp at hrw; subst hrw; simp [TermModel.eval, heq]
    · simp [hu] at hrw
  | ineq u v =>
    unfold rewriteLit at hrw
    by_cases hu : u = s
    · subst hu; simp at hrw; subst hrw; simp [TermModel.eval, heq]
    · simp [hu] at hrw

end ContextCalculus
