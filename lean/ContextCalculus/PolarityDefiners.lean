import ContextCalculus.UniversalDefinerElimination

/-!
# Polarity encoding of complement definers in the frontend

`engine/src/frontend/normalise.rs` (`polarity_definers`, docs/NOMINALS-CB.md
section 11) post-processes the clause set of the clausifier. For a negation
`¬A` of an atomic operand (a class name, a nominal `{o}` or a value concept)
the clausifier introduces a fresh definer `Q` with the biconditional

* the definition clause `Q(v) ∧ A(v) → ⊥` (`Q ⊑ ¬A`), and
* the excluded middle `→ Q(v) ∨ A(v)` (`¬A ⊑ Q`).

For each candidate pair `(Q, A)`, in order, the pass evaluates a gate on the
current clause set: both clauses are present, `Q ≠ A`, `Q` is not reserved,
and every clause whose body mentions `Q` is the definition clause or a
complement constraint `N(v) ∧ Q(v) → ⊥` with `N ∉ {Q, A}` (the `∀`
introduction of a filler `¬A` emits these). This is the statement "`Q`
occurs in one polarity only": apart from its definition and the complement
constraints, which the pass rewrites, `Q` occurs only in heads. On
acceptance the pass

* rewrites every complement constraint `N(v) ∧ Q(v) → ⊥` to `N(v) → A(v)`,
* removes every excluded middle `→ Q(v) ∨ A(v)` of the pair.

This module states the gate and the transformation exactly as the Rust pass
computes them, over the clause language of `RulesInertSortRelease`, and
proves:

* `step_models_forward`: every model of the input is a model of the result;
* `step_models_backward`: a model `J` of the result becomes a model of the
  input once `Q` is reinterpreted as the complement of `A`
  (`Interp.complementAt`), which changes no other concept, role, constant or
  function;
* `step_equisatisfiable`, `run_equisatisfiable`: the input and the result are
  satisfiable together with any side theory that reads only reserved
  concepts, for one step and for the whole fold over the candidate list;
* `run_answers`: consistency, unsatisfiable reserved classes and
  subsumptions between reserved classes are unchanged.

The candidate list is untrusted: every theorem holds for any list, because
the gate is checked on the clause set each step reads.
-/

namespace ContextCalculus.PolarityDefiners

open Lean
open ContextCalculus.RulesInertSort
open ContextCalculus.UniversalDefiner (Entails ClassUnsat Consistent answers_of_equisatisfiable)

/-! ## Gate and transformation -/

/-- `Q(v) ∧ A(v)` or `Q(v) ∨ A(v)`: exactly the two concept atoms `Q` and `A`
(either order) on one variable (`is_pair` in Rust). -/
def isPair (Q A : Nat) : List Atom → Bool
  | [.concept c₁ (.var v₁), .concept c₂ (.var v₂)] =>
      v₁ == v₂ && ((c₁ == Q && c₂ == A) || (c₁ == A && c₂ == Q))
  | _ => false

/-- The definition clause `Q(v) ∧ A(v) → ⊥` (`is_def_clause`). -/
def isDefClause (Q A : Nat) (clause : Clause) : Bool :=
  clause.head.isEmpty && isPair Q A clause.body

/-- The excluded middle `→ Q(v) ∨ A(v)` (`is_em_clause`). -/
def isEMClause (Q A : Nat) (clause : Clause) : Bool :=
  clause.body.isEmpty && isPair Q A clause.head

/-- A complement constraint `N(v) ∧ Q(v) → ⊥` (either order, `N ∉ {Q, A}`):
its `N` and `v` (`target_of`). -/
def targetOf (Q A : Nat) (clause : Clause) : Option (Nat × Nat) :=
  if clause.head.isEmpty then
    match clause.body with
    | [.concept c₁ (.var v₁), .concept c₂ (.var v₂)] =>
        if v₁ = v₂ then
          if c₂ = Q ∧ c₁ ≠ Q ∧ c₁ ≠ A then some (c₁, v₁)
          else if c₁ = Q ∧ c₂ ≠ Q ∧ c₂ ≠ A then some (c₂, v₁)
          else none
        else none
    | _ => none
  else none

/-- A concept atom on `Q`. -/
def isConceptOn (Q : Nat) : Atom → Bool
  | .concept c _ => c == Q
  | _ => false

/-- The body mentions `Q` (`body_mentions`). -/
def bodyMentions (Q : Nat) (clause : Clause) : Bool :=
  clause.body.any (isConceptOn Q)

/-- **The gate.** `Q` is an unreserved complement definer of `A` with both
definition clauses present, and every clause whose body mentions `Q` is its
definition clause or a complement constraint: `Q` occurs in one polarity
only. -/
def gate (reserved : List Nat) (Q A : Nat) (clauses : List Clause) : Bool :=
  !decide (Q ∈ reserved) && Q != A &&
    clauses.any (isDefClause Q A) && clauses.any (isEMClause Q A) &&
    clauses.all fun clause =>
      !bodyMentions Q clause || isDefClause Q A clause || (targetOf Q A clause).isSome

/-- Rewrite a complement constraint `N(v) ∧ Q(v) → ⊥` to `N(v) → A(v)`. -/
def rewrite (Q A : Nat) (clause : Clause) : Clause :=
  match targetOf Q A clause with
  | some (N, v) => ⟨[.concept N (.var v)], [.concept A (.var v)]⟩
  | none => clause

/-- The transformation of one accepted pair. -/
def transform (Q A : Nat) (clauses : List Clause) : List Clause :=
  (clauses.filter fun clause => !isEMClause Q A clause).map (rewrite Q A)

/-- One step of the pass: transform when the gate accepts. -/
def step (reserved : List Nat) (clauses : List Clause) (pair : Nat × Nat) : List Clause :=
  if gate reserved pair.1 pair.2 clauses then transform pair.1 pair.2 clauses else clauses

/-- The pass over the candidate list, in order (`polarity_definers`). -/
def run (reserved : List Nat) (pairs : List (Nat × Nat)) (clauses : List Clause) :
    List Clause :=
  pairs.foldl (step reserved) clauses

/-! ## Shape lemmas -/

/-- The atoms of a pair are exactly `Q(x)` and `A(x)`. -/
theorem isPair_atoms {Q A : Nat} {atoms : List Atom} (h : isPair Q A atoms = true) :
    ∃ x, ∀ atom, atom ∈ atoms ↔
      (atom = .concept Q (.var x) ∨ atom = .concept A (.var x)) := by
  match atoms, h with
  | [.concept c₁ (.var v₁), .concept c₂ (.var v₂)], h =>
      simp only [isPair, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
      obtain ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := h
      · exact ⟨v₁, fun atom => by simp⟩
      · exact ⟨v₁, fun atom => by simp [or_comm]⟩

/-- The body of a complement constraint is `N(v)` and `Q(v)`. -/
theorem targetOf_spec {Q A N v : Nat} {clause : Clause}
    (h : targetOf Q A clause = some (N, v)) :
    clause.head = [] ∧ N ≠ Q ∧ N ≠ A ∧
      ∀ atom, atom ∈ clause.body ↔
        (atom = .concept N (.var v) ∨ atom = .concept Q (.var v)) := by
  rcases clause with ⟨body, head⟩
  unfold targetOf at h
  cases head with
  | cons _ _ => simp at h
  | nil =>
      simp only [List.isEmpty_nil, if_true] at h
      match body, h with
      | [.concept c₁ (.var v₁), .concept c₂ (.var v₂)], h =>
          simp only at h
          by_cases hv : v₁ = v₂
          · subst hv
            simp only [if_true] at h
            by_cases h1 : c₂ = Q ∧ c₁ ≠ Q ∧ c₁ ≠ A
            · simp only [h1, and_self, if_true, ne_eq, not_false_eq_true,
                Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨rfl, hq, ha⟩ := h1
              exact ⟨rfl, hq, ha, fun atom => by simp⟩
            · rw [if_neg h1] at h
              by_cases h2 : c₁ = Q ∧ c₂ ≠ Q ∧ c₂ ≠ A
              · rw [if_pos h2] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨rfl, hq, ha⟩ := h2
                exact ⟨rfl, hq, ha, fun atom => by simp [or_comm]⟩
              · rw [if_neg h2] at h
                exact absurd h (by simp)
          · simp [hv] at h

theorem targetOf_body_nonempty {Q A : Nat} {clause : Clause}
    (h : (targetOf Q A clause).isSome = true) : clause.body.isEmpty = false := by
  obtain ⟨⟨N, v⟩, hN⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨_, _, _, hbody⟩ := targetOf_spec hN
  have : Atom.concept N (.var v) ∈ clause.body := (hbody _).mpr (Or.inl rfl)
  cases hb : clause.body with
  | nil => rw [hb] at this; simp at this
  | cons _ _ => rfl

/-- A definition clause is not a complement constraint. -/
theorem targetOf_def_none {Q A : Nat} {clause : Clause}
    (h : isDefClause Q A clause = true) : targetOf Q A clause = none := by
  cases ht : targetOf Q A clause with
  | none => rfl
  | some p =>
      obtain ⟨N, v⟩ := p
      obtain ⟨_, hNQ, hNA, hbody⟩ := targetOf_spec ht
      simp only [isDefClause, Bool.and_eq_true] at h
      obtain ⟨x, hpair⟩ := isPair_atoms h.2
      have hN := (hpair _).mp ((hbody _).mpr (Or.inl rfl))
      simp only [Atom.concept.injEq] at hN
      rcases hN with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact absurd rfl hNQ
      · exact absurd rfl hNA

/-- An excluded middle is not rewritten. -/
theorem rewrite_of_not_target {Q A : Nat} {clause : Clause}
    (h : targetOf Q A clause = none) : rewrite Q A clause = clause := by
  simp [rewrite, h]

theorem mem_transform {Q A : Nat} {clauses : List Clause} {clause : Clause}
    (hmem : clause ∈ clauses) (hem : isEMClause Q A clause = false) :
    rewrite Q A clause ∈ transform Q A clauses :=
  List.mem_map.mpr ⟨clause, List.mem_filter.mpr ⟨hmem, by simp [hem]⟩, rfl⟩

theorem em_not_def {Q A : Nat} {clause : Clause} (h : isEMClause Q A clause = true) :
    isDefClause Q A clause = false := by
  simp only [isEMClause, Bool.and_eq_true] at h
  obtain ⟨x, hpair⟩ := isPair_atoms h.2
  have hmem : Atom.concept Q (.var x) ∈ clause.head := (hpair _).mpr (Or.inl rfl)
  have hne : clause.head.isEmpty = false := by
    cases hh : clause.head with
    | nil => rw [hh] at hmem; simp at hmem
    | cons _ _ => rfl
  simp [isDefClause, hne]

theorem def_not_em {Q A : Nat} {clause : Clause} (h : isDefClause Q A clause = true) :
    isEMClause Q A clause = false := by
  cases he : isEMClause Q A clause with
  | false => rfl
  | true => rw [em_not_def he] at h; exact absurd h (by simp)

theorem target_not_em {Q A : Nat} {clause : Clause}
    (h : (targetOf Q A clause).isSome = true) : isEMClause Q A clause = false := by
  simp [isEMClause, targetOf_body_nonempty h]

/-! ## Reading the gate -/

structure GateFacts (reserved : List Nat) (Q A : Nat) (clauses : List Clause) : Prop where
  notReserved : Q ∉ reserved
  ne : Q ≠ A
  hasDef : ∃ clause ∈ clauses, isDefClause Q A clause = true
  hasEM : ∃ clause ∈ clauses, isEMClause Q A clause = true
  polarity : ∀ clause ∈ clauses, bodyMentions Q clause = true →
    isDefClause Q A clause = true ∨ (targetOf Q A clause).isSome = true

theorem gateFacts {reserved : List Nat} {Q A : Nat} {clauses : List Clause}
    (h : gate reserved Q A clauses = true) : GateFacts reserved Q A clauses := by
  simp only [gate, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    bne_iff_ne, ne_eq, List.any_eq_true, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨hres, hne⟩, hdef⟩, hem⟩, hall⟩ := h
  refine ⟨hres, hne, hdef, hem, ?_⟩
  intro clause hmem hbody
  rcases hall clause hmem with (h | h) | h
  · simp [h] at hbody
  · exact Or.inl h
  · exact Or.inr h

/-! ## Input model to result model -/

theorem pair_holds_at {I : Interp α} {Q A : Nat} {atoms : List Atom}
    (h : isPair Q A atoms = true) (a : α) :
    (∃ atom ∈ atoms, atom.Holds I (fun _ => a)) ↔ I.concept Q a ∨ I.concept A a := by
  obtain ⟨x, hpair⟩ := isPair_atoms h
  constructor
  · rintro ⟨atom, hmem, hholds⟩
    rcases (hpair atom).mp hmem with rfl | rfl
    · exact Or.inl hholds
    · exact Or.inr hholds
  · rintro (hq | ha)
    · exact ⟨_, (hpair _).mpr (Or.inl rfl), hq⟩
    · exact ⟨_, (hpair _).mpr (Or.inr rfl), ha⟩

theorem em_holds {I : Interp α} {Q A : Nat} {clause : Clause}
    (hem : isEMClause Q A clause = true) (hholds : clause.Holds I) (a : α) :
    I.concept Q a ∨ I.concept A a := by
  simp only [isEMClause, Bool.and_eq_true, List.isEmpty_iff] at hem
  have := hholds (fun _ => a) (by simp [hem.1])
  exact (pair_holds_at hem.2 a).mp this

theorem def_holds {I : Interp α} {Q A : Nat} {clause : Clause}
    (hdef : isDefClause Q A clause = true) (hholds : clause.Holds I) (a : α) :
    ¬ (I.concept Q a ∧ I.concept A a) := by
  simp only [isDefClause, Bool.and_eq_true, List.isEmpty_iff] at hdef
  rintro ⟨hq, ha⟩
  obtain ⟨x, hpair⟩ := isPair_atoms hdef.2
  obtain ⟨atom, hmem, _⟩ := hholds (fun _ => a) (by
    intro atom hmem
    rcases (hpair atom).mp hmem with rfl | rfl
    · exact hq
    · exact ha)
  rw [hdef.1] at hmem
  simp at hmem

/-- **Forward.** Every model of the input is a model of the result. -/
theorem step_models_forward {reserved : List Nat} {Q A : Nat} {clauses : List Clause}
    (hgate : gate reserved Q A clauses = true) {I : Interp α}
    (hmodels : Models I clauses) : Models I (transform Q A clauses) := by
  have facts := gateFacts hgate
  obtain ⟨em, hemMem, hem⟩ := facts.hasEM
  intro clause' hmem v hbody
  simp only [transform, List.mem_map, List.mem_filter] at hmem
  obtain ⟨clause, ⟨hclause, _⟩, rfl⟩ := hmem
  cases ht : targetOf Q A clause with
  | none =>
      rw [rewrite_of_not_target ht] at hbody ⊢
      exact hmodels clause hclause v hbody
  | some p =>
      obtain ⟨N, x⟩ := p
      obtain ⟨hhead, _, _, hb⟩ := targetOf_spec ht
      simp only [rewrite, ht] at hbody ⊢
      have hN : I.concept N (v x) := hbody (.concept N (.var x)) (by simp)
      refine ⟨.concept A (.var x), by simp, ?_⟩
      show I.concept A (v x)
      rcases em_holds hem (hmodels em hemMem) (v x) with hq | ha
      · exfalso
        obtain ⟨atom, hatom, _⟩ := hmodels clause hclause v (by
          intro atom hatom
          rcases (hb atom).mp hatom with rfl | rfl
          · exact hN
          · exact hq)
        rw [hhead] at hatom
        simp at hatom
      · exact ha

/-! ## Result model to input model -/

/-- Reinterpret `Q` as the complement of `A`; nothing else changes. -/
def _root_.ContextCalculus.RulesInertSort.Interp.complementAt (J : Interp α) (Q A : Nat) :
    Interp α :=
  { J with concept := fun c a => if c = Q then ¬ J.concept A a else J.concept c a }

@[simp] theorem eval_complementAt (J : Interp α) (Q A : Nat) (v : Nat → α)
    (term : RulesInertSort.Term) : term.eval (J.complementAt Q A) v = term.eval J v := by
  induction term with
  | var => rfl
  | ind => rfl
  | app f arg ih => simp only [RulesInertSort.Term.eval, ih]; rfl

theorem complementAt_Q (J : Interp α) {Q A : Nat} (a : α) :
    (J.complementAt Q A).concept Q a ↔ ¬ J.concept A a := by
  simp [Interp.complementAt]

theorem complementAt_other (J : Interp α) {Q A c : Nat} (h : c ≠ Q) :
    (J.complementAt Q A).concept c = J.concept c := by
  funext a
  simp [Interp.complementAt, h]

theorem holds_complementAt_of_not_Q {J : Interp α} {Q A : Nat} {v : Nat → α} {atom : Atom}
    (h : isConceptOn Q atom = false) :
    atom.Holds (J.complementAt Q A) v ↔ atom.Holds J v := by
  cases atom with
  | concept c t =>
      simp only [isConceptOn, beq_eq_false_iff_ne, ne_eq] at h
      simp only [Atom.Holds, eval_complementAt, complementAt_other J h]
  | role r s t => simp only [Atom.Holds, eval_complementAt]; exact Iff.rfl
  | eq l r => simp only [Atom.Holds, eval_complementAt]

/-- **Backward.** A model of the result becomes a model of the input once
`Q` is interpreted as the complement of `A`. -/
theorem step_models_backward {reserved : List Nat} {Q A : Nat} {clauses : List Clause}
    (hgate : gate reserved Q A clauses = true) {J : Interp α}
    (hmodels : Models J (transform Q A clauses)) : Models (J.complementAt Q A) clauses := by
  have facts := gateFacts hgate
  have hAQ : A ≠ Q := fun h => facts.ne h.symm
  have hA : (J.complementAt Q A).concept A = J.concept A := complementAt_other J hAQ
  -- The definition clause survives, so `J.Q ⊆ ¬ J.A`.
  obtain ⟨dclause, hdMem, hdef⟩ := facts.hasDef
  have hdefJ : ∀ a, J.concept Q a → ¬ J.concept A a := by
    intro a hq ha
    have hmem := mem_transform hdMem (def_not_em hdef)
    rw [rewrite_of_not_target (targetOf_def_none hdef)] at hmem
    exact def_holds hdef (hmodels _ hmem) a ⟨hq, ha⟩
  intro clause hclause v hbody
  cases hem : isEMClause Q A clause with
  | true =>
      -- The excluded middle holds under the complement.
      simp only [isEMClause, Bool.and_eq_true, List.isEmpty_iff] at hem
      obtain ⟨x, hpair⟩ := isPair_atoms hem.2
      by_cases ha : J.concept A (v x)
      · exact ⟨_, (hpair _).mpr (Or.inr rfl), show (J.complementAt Q A).concept A (v x) by
          rw [hA]; exact ha⟩
      · exact ⟨_, (hpair _).mpr (Or.inl rfl), show (J.complementAt Q A).concept Q (v x) from
          (complementAt_Q J (v x)).mpr ha⟩
  | false =>
  have hmem := mem_transform hclause hem
  by_cases hd : isDefClause Q A clause = true
  · -- The definition clause holds under the complement.
    exfalso
    simp only [isDefClause, Bool.and_eq_true] at hd
    obtain ⟨x, hpair⟩ := isPair_atoms hd.2
    have hq := hbody _ ((hpair _).mpr (Or.inl rfl))
    have ha := hbody _ ((hpair _).mpr (Or.inr rfl))
    change (J.complementAt Q A).concept Q (v x) at hq
    change (J.complementAt Q A).concept A (v x) at ha
    rw [hA] at ha
    exact (complementAt_Q J (v x)).mp hq ha
  · cases ht : targetOf Q A clause with
    | some p =>
        -- A complement constraint follows from its rewrite `N → A`.
        exfalso
        obtain ⟨N, x⟩ := p
        obtain ⟨_, hNQ, _, hb⟩ := targetOf_spec ht
        simp only [rewrite, ht] at hmem
        have hN := hbody _ ((hb _).mpr (Or.inl rfl))
        have hq := hbody _ ((hb _).mpr (Or.inr rfl))
        change (J.complementAt Q A).concept N (v x) at hN
        change (J.complementAt Q A).concept Q (v x) at hq
        rw [complementAt_other J hNQ] at hN
        obtain ⟨atom, hatom, hholds⟩ := hmodels _ hmem v (by simpa using hN)
        simp only [List.mem_singleton] at hatom
        subst hatom
        exact (complementAt_Q J (v x)).mp hq hholds
    | none =>
        -- Otherwise `Q` occurs only in the head, where enlarging it is harmless.
        have hnot : bodyMentions Q clause = false := by
          cases hb : bodyMentions Q clause with
          | false => rfl
          | true =>
              rcases facts.polarity clause hclause hb with h | h
              · exact absurd h hd
              · rw [ht] at h; exact absurd h (by simp)
        rw [rewrite_of_not_target ht] at hmem
        obtain ⟨atom, hatom, hholds⟩ := hmodels clause hmem v (by
          intro atom hatom
          have hq : isConceptOn Q atom = false := by
            simp only [bodyMentions, List.any_eq_false] at hnot
            simpa using hnot atom hatom
          exact (holds_complementAt_of_not_Q hq).mp (hbody atom hatom))
        refine ⟨atom, hatom, ?_⟩
        cases hq : isConceptOn Q atom with
        | false => exact (holds_complementAt_of_not_Q hq).mpr hholds
        | true =>
            cases atom with
            | concept c t =>
                simp only [isConceptOn, beq_iff_eq] at hq
                subst hq
                change (J.complementAt c A).concept c (t.eval (J.complementAt c A) v)
                rw [eval_complementAt, complementAt_Q]
                exact hdefJ _ hholds
            | role => simp [isConceptOn] at hq
            | eq => simp [isConceptOn] at hq

theorem complementAt_agrees {J : Interp α} {reserved : List Nat} {Q A : Nat}
    (hres : Q ∉ reserved) :
    ∀ concept ∈ reserved, (J.complementAt Q A).concept concept = J.concept concept :=
  fun _ hmem => complementAt_other J (fun h => hres (h ▸ hmem))

/-! ## Capstones -/

/-- **Equisatisfiability of one step.** -/
theorem step_equisatisfiable {reserved : List Nat} {clauses : List Clause} (pair : Nat × Nat)
    {side : SideTheory} (hside : ReadsOnly reserved side) :
    Satisfiable clauses side ↔ Satisfiable (step reserved clauses pair) side := by
  unfold step
  split
  · rename_i hgate
    constructor
    · rintro ⟨α, I, hne, hmodels, hsideI⟩
      exact ⟨α, I, hne, step_models_forward hgate hmodels, hsideI⟩
    · rintro ⟨α, J, hne, hmodels, hsideJ⟩
      refine ⟨α, J.complementAt pair.1 pair.2, hne, step_models_backward hgate hmodels, ?_⟩
      exact (hside α (J.complementAt pair.1 pair.2) J rfl rfl rfl
        (complementAt_agrees (gateFacts hgate).notReserved)).mpr hsideJ
  · exact Iff.rfl

/-- **Equisatisfiability of the pass** over any candidate list. -/
theorem run_equisatisfiable {reserved : List Nat} (pairs : List (Nat × Nat))
    (clauses : List Clause) {side : SideTheory} (hside : ReadsOnly reserved side) :
    Satisfiable clauses side ↔ Satisfiable (run reserved pairs clauses) side := by
  induction pairs generalizing clauses with
  | nil => exact Iff.rfl
  | cons pair rest ih =>
      simp only [run, List.foldl_cons] at ih ⊢
      exact (step_equisatisfiable pair hside).trans (ih _)

/-- **Answers of the pass.** Consistency, the unsatisfiable reserved classes
and the subsumptions between reserved classes are unchanged. -/
theorem run_answers {reserved : List Nat} (pairs : List (Nat × Nat)) (clauses : List Clause) :
    (Consistent clauses ↔ Consistent (run reserved pairs clauses)) ∧
      (∀ A ∈ reserved, ClassUnsat clauses A ↔ ClassUnsat (run reserved pairs clauses) A) ∧
      (∀ A ∈ reserved, ∀ B ∈ reserved,
        Entails clauses A B ↔ Entails (run reserved pairs clauses) A B) :=
  answers_of_equisatisfiable fun _ hside => run_equisatisfiable pairs clauses hside

/-! ## The object-value case of `universal_role_and_top_data_range` -/

section Example

/-- `Q_1 ≡ ¬{e}` with `e = 1`, `Q_1 = 0`, `Q_0 = 2`, `p = 0`, `Q_3 = 3`:
propagation `Q_0(x) ∧ p(x,y) → Q_1(y)`, the definition clause, the excluded
middle and the `∀` introduction's `Q_3(x) ∧ Q_1(x) → ⊥`. -/
def exampleClauses : List Clause :=
  [ ⟨[.concept 2 (.var 0), .role 0 (.var 0) (.var 1)], [.concept 0 (.var 1)]⟩,
    ⟨[.concept 0 (.var 0), .concept 1 (.var 0)], []⟩,
    ⟨[], [.concept 0 (.var 0), .concept 1 (.var 0)]⟩,
    ⟨[.concept 3 (.var 0), .concept 0 (.var 0)], []⟩ ]

example : gate [] 0 1 exampleClauses = true := by decide

example : run [] [(0, 1)] exampleClauses =
    [ ⟨[.concept 2 (.var 0), .role 0 (.var 0) (.var 1)], [.concept 0 (.var 1)]⟩,
      ⟨[.concept 0 (.var 0), .concept 1 (.var 0)], []⟩,
      ⟨[.concept 3 (.var 0)], [.concept 1 (.var 0)]⟩ ] := by decide

/-- A body occurrence of `Q_1` outside its definition and the complement
constraints closes the gate. -/
example : gate [] 0 1
    (exampleClauses ++ [⟨[.concept 0 (.var 0)], [.concept 4 (.var 0)]⟩]) = false := by decide

end Example

#print axioms step_models_forward
#print axioms step_models_backward
#print axioms step_equisatisfiable
#print axioms run_equisatisfiable
#print axioms run_answers

end ContextCalculus.PolarityDefiners
