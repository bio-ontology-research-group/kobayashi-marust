import ContextCalculus.RulesInertSortRelease

/-!
# Universal-definer elimination in the nominal CB input

`engine/src/orchestrate/inert_sorts.rs` (`eliminate_universal_definers`,
docs/NOMINALS-CB.md "Inert object sorts in the nominal CB input
(2026-10-30)") rewrites the clause set the nominal CB engine reads, after the
inert-sort release (`ContextCalculus.RulesInertSort.release`). For a set `U`
of internal definers, each of which has a unit fact `→ Q(x)` (empty body, one
concept atom on a variable) in the clause set, it

* drops every clause whose head holds an atom `Q(t)` with `Q ∈ U` (the unit
  facts included), and then
* drops every body atom `Q(t)` with `Q ∈ U` from the remaining clauses.

This module states that transformation exactly as the Rust pass computes it,
over the clause language of `RulesInertSortRelease` (concepts, roles,
equality, individual constants, unary Skolem functions), and proves:

* `models_iff`: an interpretation is a model of the input iff it is a model
  of the result and interprets every `Q ∈ U` as the whole domain;
* `eliminate_equisatisfiable`: the input and the result are satisfiable
  together with any side theory that reads only reserved concepts;
* for the composed pass of the CB arm (release, then elimination), the same
  equisatisfiability and the preservation of consistency, of class
  unsatisfiability and of subsumption between reserved concepts
  (`WireNominalCBInput.check_sound`, `check_consistent`, `check_unsat`,
  `check_entails`).

The eliminated set `U` is untrusted: the checker requires a unit fact for
each of its members in the clause set the elimination reads and requires
`U` to be disjoint from the reserved concepts. The Rust pass's cost guards
(clause sets with inverse roles, fillers of an at-most asserted on an
individual, definers whose elimination would leave an unconditional role or
Skolem head) only shrink `U`, so they need no proof.
-/

namespace ContextCalculus.UniversalDefiner

open Lean
open ContextCalculus.RulesInertSort

/-! ## The transformation -/

/-- A concept atom on an eliminated definer (`is_universal` in Rust). -/
def isEliminated (U : List Nat) : Atom → Bool
  | .concept concept _ => decide (concept ∈ U)
  | _ => false

/-- Drop the eliminated body atoms of one clause. -/
def stripBody (U : List Nat) (clause : Clause) : Clause :=
  { clause with body := clause.body.filter fun atom => !isEliminated U atom }

/-- The eliminated clause set, in the order the Rust pass produces it: first
`retain` the clauses whose head holds no eliminated atom, then strip the
bodies. -/
def eliminate (U : List Nat) (clauses : List Clause) : List Clause :=
  (clauses.filter fun clause => !clause.head.any (isEliminated U)).map (stripBody U)

/-- `Q` of a unit fact `→ Q(x)` on a variable. -/
def unitFactOf : Clause → Option Nat
  | ⟨[], [.concept concept (.var _)]⟩ => some concept
  | _ => none

/-- Executable acceptance condition of an elimination: every eliminated
definer is unreserved and has a unit fact in the clause set. -/
def elimConditions (U reserved : List Nat) (clauses : List Clause) : Bool :=
  U.all fun concept =>
    !decide (concept ∈ reserved) && clauses.any fun clause => unitFactOf clause == some concept

/-! ## Answers -/

/-- Every model of the clause set puts every `A` element into `B`. -/
def Entails (clauses : List Clause) (A B : Nat) : Prop :=
  ∀ (α : Type) (I : Interp α), Models I clauses → ∀ a, I.concept A a → I.concept B a

/-- Every model of the clause set interprets `A` as empty. -/
def ClassUnsat (clauses : List Clause) (A : Nat) : Prop :=
  ∀ (α : Type) (I : Interp α), Models I clauses → ∀ a, ¬ I.concept A a

/-- The clause set has a model over a nonempty domain. -/
def Consistent (clauses : List Clause) : Prop :=
  Satisfiable clauses (fun _ _ => True)

/-! ## Unit facts -/

theorem unitFact_universal {I : Interp α} {clause : Clause} {concept : Nat}
    (hfact : unitFactOf clause = some concept) (hholds : clause.Holds I) :
    ∀ a, I.concept concept a := by
  intro a
  rcases clause with ⟨body, head⟩
  match body, head, hfact, hholds with
  | [], [.concept c (.var x)], hfact, hholds =>
      simp only [unitFactOf, Option.some.injEq] at hfact
      subst hfact
      obtain ⟨atom, hmem, hatom⟩ := hholds (fun _ => a) (by simp)
      simp only [List.mem_singleton] at hmem
      subst hmem
      exact hatom

theorem universal_of_conditions {U reserved : List Nat} {clauses : List Clause}
    (hcheck : elimConditions U reserved clauses = true) {I : Interp α}
    (hmodels : Models I clauses) : ∀ concept ∈ U, ∀ a, I.concept concept a := by
  intro concept hU
  simp only [elimConditions, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, List.any_eq_true, beq_iff_eq] at hcheck
  obtain ⟨clause, hmem, hfact⟩ := (hcheck concept hU).2
  exact unitFact_universal hfact (hmodels clause hmem)

theorem notReserved_of_conditions {U reserved : List Nat} {clauses : List Clause}
    (hcheck : elimConditions U reserved clauses = true) :
    ∀ concept ∈ reserved, concept ∉ U := by
  intro concept hres hU
  simp only [elimConditions, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hcheck
  exact (hcheck concept hU).1 hres

theorem eliminated_holds {I : Interp α} {U : List Nat}
    (huniv : ∀ concept ∈ U, ∀ a, I.concept concept a) {atom : Atom}
    (h : isEliminated U atom = true) (v : Nat → α) : atom.Holds I v := by
  cases atom with
  | concept c t =>
      simp only [isEliminated, decide_eq_true_eq] at h
      exact huniv c h _
  | role => simp [isEliminated] at h
  | eq => simp [isEliminated] at h

theorem mem_eliminate {U : List Nat} {clauses : List Clause} {clause : Clause}
    (hmem : clause ∈ clauses) (hhead : clause.head.any (isEliminated U) = false) :
    stripBody U clause ∈ eliminate U clauses :=
  List.mem_map.mpr ⟨clause, List.mem_filter.mpr ⟨hmem, by simp [hhead]⟩, rfl⟩

/-! ## Input model to result model -/

/-- A model of the input in which every eliminated definer holds everywhere
is a model of the result. -/
theorem eliminate_models_of_universal {U : List Nat} {clauses : List Clause}
    {I : Interp α} (huniv : ∀ concept ∈ U, ∀ a, I.concept concept a)
    (hmodels : Models I clauses) : Models I (eliminate U clauses) := by
  intro clause' hmem v hbody
  simp only [eliminate, List.mem_map, List.mem_filter] at hmem
  obtain ⟨clause, ⟨hclause, _⟩, rfl⟩ := hmem
  apply hmodels clause hclause v
  intro atom hatom
  cases he : isEliminated U atom with
  | true => exact eliminated_holds huniv he v
  | false =>
      apply hbody atom
      simp only [stripBody, List.mem_filter]
      exact ⟨hatom, by simp [he]⟩

/-! ## Result model to input model -/

/-- Interpret every eliminated definer as the whole domain. -/
def _root_.ContextCalculus.RulesInertSort.Interp.saturate (I : Interp α) (U : List Nat) : Interp α :=
  { I with concept := fun concept value => concept ∈ U ∨ I.concept concept value }

@[simp] theorem _root_.ContextCalculus.RulesInertSort.Term.eval_saturate (I : Interp α) (U : List Nat) (v : Nat → α)
    (term : RulesInertSort.Term) : term.eval (I.saturate U) v = term.eval I v := by
  induction term with
  | var => rfl
  | ind => rfl
  | app f arg ih => simp only [Term.eval, ih]; rfl

theorem saturate_universal (I : Interp α) (U : List Nat) :
    ∀ concept ∈ U, ∀ a, (I.saturate U).concept concept a :=
  fun _ hU _ => Or.inl hU

theorem saturate_concept_notMem {I : Interp α} {U : List Nat} {concept : Nat}
    (h : concept ∉ U) : (I.saturate U).concept concept = I.concept concept := by
  funext value
  apply propext
  simp [Interp.saturate, h]

theorem holds_saturate_mono {I : Interp α} {U : List Nat} {v : Nat → α} {atom : Atom}
    (h : atom.Holds I v) : atom.Holds (I.saturate U) v := by
  cases atom with
  | concept c t => simp only [Atom.Holds, RulesInertSort.Term.eval_saturate] at h ⊢; exact Or.inr h
  | role r s t => simpa [Atom.Holds] using h
  | eq l r => simpa [Atom.Holds] using h

theorem holds_saturate_of_not_eliminated {I : Interp α} {U : List Nat} {v : Nat → α}
    {atom : Atom} (he : isEliminated U atom = false) :
    atom.Holds (I.saturate U) v → atom.Holds I v := by
  cases atom with
  | concept c t =>
      simp only [isEliminated, decide_eq_false_iff_not] at he
      intro h
      simp only [Atom.Holds, RulesInertSort.Term.eval_saturate] at h ⊢
      rcases h with h | h
      · exact absurd h he
      · exact h
  | role r s t => intro h; simpa [Atom.Holds] using h
  | eq l r => intro h; simpa [Atom.Holds] using h

/-- A model of the result becomes a model of the input once every eliminated
definer is interpreted as the whole domain. -/
theorem saturate_models {U : List Nat} {clauses : List Clause} {J : Interp α}
    (hmodels : Models J (eliminate U clauses)) : Models (J.saturate U) clauses := by
  intro clause hclause v hbody
  cases hhead : clause.head.any (isEliminated U) with
  | true =>
      obtain ⟨atom, hatom, he⟩ := List.any_eq_true.mp hhead
      exact ⟨atom, hatom, eliminated_holds (saturate_universal J U) he v⟩
  | false =>
      obtain ⟨atom, hatom, hholds⟩ := hmodels _ (mem_eliminate hclause hhead) v (by
        intro atom hatom
        simp only [stripBody, List.mem_filter] at hatom
        have he : isEliminated U atom = false := by simpa using hatom.2
        exact holds_saturate_of_not_eliminated he (hbody atom hatom.1))
      exact ⟨atom, hatom, holds_saturate_mono hholds⟩

theorem saturate_eq_of_universal {I : Interp α} {U : List Nat}
    (huniv : ∀ concept ∈ U, ∀ a, I.concept concept a) : I.saturate U = I := by
  cases I with
  | mk concept role ind app =>
      simp only [Interp.saturate, Interp.mk.injEq, and_true]
      funext c value
      apply propext
      constructor
      · rintro (h | h)
        · exact huniv c h value
        · exact h
      · exact Or.inr

/-! ## Capstones of the elimination -/

/-- **Model correspondence.** Under the executable conditions, the models of
the input are exactly the models of the result that interpret every
eliminated definer as the whole domain. -/
theorem models_iff {U reserved : List Nat} {clauses : List Clause}
    (hcheck : elimConditions U reserved clauses = true) (I : Interp α) :
    Models I clauses ↔
      Models I (eliminate U clauses) ∧ ∀ concept ∈ U, ∀ a, I.concept concept a := by
  constructor
  · intro hmodels
    have huniv := universal_of_conditions hcheck hmodels
    exact ⟨eliminate_models_of_universal huniv hmodels, huniv⟩
  · rintro ⟨hmodels, huniv⟩
    have h := saturate_models hmodels
    rwa [saturate_eq_of_universal huniv] at h

theorem saturate_agrees {J : Interp α} {U reserved : List Nat}
    (hdisjoint : ∀ concept ∈ reserved, concept ∉ U) :
    ∀ concept ∈ reserved, (J.saturate U).concept concept = J.concept concept :=
  fun concept hres => saturate_concept_notMem (hdisjoint concept hres)

/-- **Equisatisfiability of the elimination.** Under the executable
conditions, the input and the result are satisfiable together with any side
theory that reads only reserved concepts. -/
theorem eliminate_equisatisfiable {U reserved : List Nat} {clauses : List Clause}
    (hcheck : elimConditions U reserved clauses = true)
    {side : SideTheory} (hside : ReadsOnly reserved side) :
    Satisfiable clauses side ↔ Satisfiable (eliminate U clauses) side := by
  constructor
  · rintro ⟨α, I, hne, hmodels, hsideI⟩
    exact ⟨α, I, hne, ((models_iff hcheck I).mp hmodels).1, hsideI⟩
  · rintro ⟨α, J, hne, hmodels, hsideJ⟩
    refine ⟨α, J.saturate U, hne, saturate_models hmodels, ?_⟩
    exact (hside α (J.saturate U) J rfl rfl rfl
      (saturate_agrees (notReserved_of_conditions hcheck))).mpr hsideJ

/-! ## From equisatisfiability to the reported answers -/

/-- The side theory "some element is in `A` and not in `B`". -/
def subCounterexample (A B : Nat) : SideTheory :=
  fun _ I => ∃ a, I.concept A a ∧ ¬ I.concept B a

/-- The side theory "some element is in `A`". -/
def classWitness (A : Nat) : SideTheory :=
  fun _ I => ∃ a, I.concept A a

theorem readsOnly_subCounterexample {reserved : List Nat} {A B : Nat}
    (hA : A ∈ reserved) (hB : B ∈ reserved) :
    ReadsOnly reserved (subCounterexample A B) := by
  intro α I J _ _ _ hagree
  simp only [subCounterexample, hagree A hA, hagree B hB]

theorem readsOnly_classWitness {reserved : List Nat} {A : Nat} (hA : A ∈ reserved) :
    ReadsOnly reserved (classWitness A) := by
  intro α I J _ _ _ hagree
  simp only [classWitness, hagree A hA]

theorem entails_iff_not_satisfiable (clauses : List Clause) (A B : Nat) :
    Entails clauses A B ↔ ¬ Satisfiable clauses (subCounterexample A B) := by
  constructor
  · rintro hentails ⟨α, I, _, hmodels, a, hA, hB⟩
    exact hB (hentails α I hmodels a hA)
  · intro hnot α I hmodels a hA
    by_cases hB : I.concept B a
    · exact hB
    · exact absurd ⟨α, I, ⟨a⟩, hmodels, a, hA, hB⟩ hnot

theorem classUnsat_iff_not_satisfiable (clauses : List Clause) (A : Nat) :
    ClassUnsat clauses A ↔ ¬ Satisfiable clauses (classWitness A) := by
  constructor
  · rintro hunsat ⟨α, I, _, hmodels, a, hA⟩
    exact hunsat α I hmodels a hA
  · intro hnot α I hmodels a hA
    exact hnot ⟨α, I, ⟨a⟩, hmodels, a, hA⟩

/-- Two clause sets that are equisatisfiable with every side theory reading
only reserved concepts have the same consistency verdict, the same
unsatisfiable reserved classes and the same subsumptions between reserved
classes. -/
theorem answers_of_equisatisfiable {reserved : List Nat} {S S' : List Clause}
    (h : ∀ side : SideTheory, ReadsOnly reserved side →
      (Satisfiable S side ↔ Satisfiable S' side)) :
    (Consistent S ↔ Consistent S') ∧
      (∀ A ∈ reserved, ClassUnsat S A ↔ ClassUnsat S' A) ∧
      (∀ A ∈ reserved, ∀ B ∈ reserved, Entails S A B ↔ Entails S' A B) := by
  refine ⟨h _ (readsOnly_true reserved), ?_, ?_⟩
  · intro A hA
    rw [classUnsat_iff_not_satisfiable, classUnsat_iff_not_satisfiable,
      h _ (readsOnly_classWitness hA)]
  · intro A hA B hB
    rw [entails_iff_not_satisfiable, entails_iff_not_satisfiable,
      h _ (readsOnly_subCounterexample hA hB)]

/-- The elimination preserves every reported answer over reserved names. -/
theorem eliminate_answers {U reserved : List Nat} {clauses : List Clause}
    (hcheck : elimConditions U reserved clauses = true) :
    (Consistent clauses ↔ Consistent (eliminate U clauses)) ∧
      (∀ A ∈ reserved, ClassUnsat clauses A ↔ ClassUnsat (eliminate U clauses) A) ∧
      (∀ A ∈ reserved, ∀ B ∈ reserved,
        Entails clauses A B ↔ Entails (eliminate U clauses) A B) :=
  answers_of_equisatisfiable fun _ hside => eliminate_equisatisfiable hcheck hside

/-! ## The nominal CB input: release, then elimination -/

/-- The clause set the nominal CB engine reads: the inert-sort release of the
frontend's clauses, then the universal-definer elimination. -/
def nominalCBInput (D : Nat) (P U : List Nat) (clauses : List Clause) : List Clause :=
  eliminate U (release D P clauses)

/-- Executable acceptance condition of the composed pass, with one reserved
set for both steps. -/
def pipelineConditions (D : Nat) (P U reserved : List Nat) (clauses : List Clause) : Bool :=
  conditions D P reserved clauses && elimConditions U reserved (release D P clauses)

theorem pipeline_equisatisfiable {D : Nat} {P U reserved : List Nat}
    {clauses : List Clause} (hcheck : pipelineConditions D P U reserved clauses = true)
    {side : SideTheory} (hside : ReadsOnly reserved side) :
    Satisfiable clauses side ↔ Satisfiable (nominalCBInput D P U clauses) side := by
  simp only [pipelineConditions, Bool.and_eq_true] at hcheck
  exact (release_equisatisfiable hcheck.1 hside).trans
    (eliminate_equisatisfiable hcheck.2 hside)

/-! ## Certificate document -/

/-- The certificate KM emits for the nominal CB input
(`KM_NOMINAL_CB_INPUT_CERT`, or under `KM_LEAN_CHECKERS`): the frontend's
clause set, the released and the eliminated definers, the reserved concepts
(every name the CB answer is read on: source names, queries, asserted
markers, nominal proxies and assertion markers, rule atoms, and every
concept that is not an internal definer) and the clause set the CB engine
reads. Names are for audit only; the checker uses the numeric ids. -/
structure WireNominalCBInput where
  version : Nat
  data_sort : Nat
  released : List Nat
  eliminated : List Nat
  reserved : List Nat
  original : List Clause
  result : List Clause
  concept_names : List String
  role_names : List String
deriving FromJson, ToJson, Repr

def WireNominalCBInput.check (wire : WireNominalCBInput) : Bool :=
  wire.version == 1 &&
    pipelineConditions wire.data_sort wire.released wire.eliminated wire.reserved wire.original &&
    decide (nominalCBInput wire.data_sort wire.released wire.eliminated wire.original = wire.result)

theorem WireNominalCBInput.check_equisatisfiable (wire : WireNominalCBInput)
    (hcheck : wire.check = true) :
    ∀ side : SideTheory, ReadsOnly wire.reserved side →
      (Satisfiable wire.original side ↔ Satisfiable wire.result side) := by
  intro side hside
  simp only [WireNominalCBInput.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨_, hconditions⟩, hresult⟩
  rw [← hresult]
  exact pipeline_equisatisfiable hconditions hside

/-- **Checker soundness.** An accepted certificate's CB input is satisfiable
with a side theory reading only reserved concepts iff the frontend's clause
set is. -/
theorem WireNominalCBInput.check_sound (wire : WireNominalCBInput)
    (hcheck : wire.check = true) {side : SideTheory}
    (hside : ReadsOnly wire.reserved side) :
    Satisfiable wire.original side ↔ Satisfiable wire.result side :=
  wire.check_equisatisfiable hcheck side hside

/-- An accepted certificate's CB input has the consistency verdict of the
frontend's clause set. -/
theorem WireNominalCBInput.check_consistent (wire : WireNominalCBInput)
    (hcheck : wire.check = true) :
    Consistent wire.original ↔ Consistent wire.result :=
  (answers_of_equisatisfiable (wire.check_equisatisfiable hcheck)).1

/-- An accepted certificate's CB input has the unsatisfiable reserved classes
of the frontend's clause set. -/
theorem WireNominalCBInput.check_unsat (wire : WireNominalCBInput)
    (hcheck : wire.check = true) {A : Nat} (hA : A ∈ wire.reserved) :
    ClassUnsat wire.original A ↔ ClassUnsat wire.result A :=
  (answers_of_equisatisfiable (wire.check_equisatisfiable hcheck)).2.1 A hA

/-- An accepted certificate's CB input entails exactly the subsumptions
between reserved classes that the frontend's clause set entails. -/
theorem WireNominalCBInput.check_entails (wire : WireNominalCBInput)
    (hcheck : wire.check = true) {A B : Nat} (hA : A ∈ wire.reserved)
    (hB : B ∈ wire.reserved) :
    Entails wire.original A B ↔ Entails wire.result A B :=
  (answers_of_equisatisfiable (wire.check_equisatisfiable hcheck)).2.2 A hA B hB

namespace Tests

private def x : RulesInertSort.Term := .var 0
private def y : RulesInertSort.Term := .var 1
private def a : RulesInertSort.Term := .ind 0
private def D : Nat := 0
private def Qtop : Nat := 1
private def Q : Nat := 2
private def A : Nat := 3
private def B : Nat := 4
private def r : Nat := 0

/-- `→ Q_⊤(x)`, `Q_⊤(x) ∧ A(x) → B(x)`, `A(x) → Q_⊤(f(x))`,
`Q_⊤(y) ∧ r(x, y) → A(x)`, `→ A(a)`. -/
private def input : List Clause := [
  ⟨[], [.concept Qtop x]⟩,
  ⟨[.concept Qtop x, .concept A x], [.concept B x]⟩,
  ⟨[.concept A x], [.concept Qtop (.app 0 x)]⟩,
  ⟨[.concept Qtop y, .role r x y], [.concept A x]⟩,
  ⟨[], [.concept A a]⟩
]

example : elimConditions [Qtop] [A, B] input = true := by native_decide

example : eliminate [Qtop] input = [
  ⟨[.concept A x], [.concept B x]⟩,
  ⟨[.role r x y], [.concept A x]⟩,
  ⟨[], [.concept A a]⟩
] := by native_decide

/-- A definer without a unit fact is rejected. -/
example : elimConditions [Q] [A, B] input = false := by native_decide

/-- A unit fact on an individual does not make a definer universal. -/
example : elimConditions [A] [] input = false := by native_decide

/-- A reserved definer is never eliminated. -/
example : elimConditions [Qtop] [Qtop] input = false := by native_decide

/-- With no released definer the release is the identity, so the composed
check covers runs where only the elimination fires. -/
example : release D [] input = input := by native_decide

example : pipelineConditions D [] [Qtop] [A, B] input = true := by native_decide

end Tests

#print axioms models_iff
#print axioms eliminate_equisatisfiable
#print axioms eliminate_answers
#print axioms pipeline_equisatisfiable
#print axioms WireNominalCBInput.check_sound
#print axioms WireNominalCBInput.check_consistent
#print axioms WireNominalCBInput.check_unsat
#print axioms WireNominalCBInput.check_entails

end ContextCalculus.UniversalDefiner
