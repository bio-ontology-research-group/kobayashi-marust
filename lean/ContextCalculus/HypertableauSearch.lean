import ContextCalculus.HypertableauTerminal

/-!
# Exact exhaustive hypertableau transition shapes

This module removes the abstract child-combination premise from the finite HT
completeness theorem. An exhaustive transition is exactly either one child for
every branchable head atom of a matched clause, or one fresh existential
witness child. If every enumerated child refutes, the corresponding `Refutes`
constructor closes the parent.
-/

namespace ContextCalculus.Hypertableau

abbrev GuardedFact (Node Concept Role : Type) :=
  (Node × Lit Concept) ⊕ ((Role × Node × Node) ⊕ (Role × Lit Concept × Node))

def State.holdsFact (state : State Node Concept Role) :
    GuardedFact Node Concept Role → Prop
  | .inl (node, literal) => state.label node literal
  | .inr (.inl (role, source, target)) => state.edge role source target
  | .inr (.inr (role, filler, node)) => state.obligation role filler node

noncomputable def State.guardedFacts
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) : Finset (GuardedFact Node Concept Role) := by
  classical
  exact Finset.univ.filter state.holdsFact

@[simp] theorem State.mem_guardedFacts
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) (fact : GuardedFact Node Concept Role) :
    fact ∈ state.guardedFacts ↔ state.holdsFact fact := by
  classical
  simp [State.guardedFacts]

def stateOfGuardedFacts
    (facts : Finset (GuardedFact Node Concept Role)) : State Node Concept Role where
  label node literal := Sum.inl (node, literal) ∈ facts
  edge role source target := Sum.inr (Sum.inl (role, source, target)) ∈ facts
  obligation role filler node := Sum.inr (Sum.inr (role, filler, node)) ∈ facts

/-- Finite guarded facts are an exact representation of a finite HT state. -/
@[simp] theorem stateOfGuardedFacts_guardedFacts
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (facts : Finset (GuardedFact Node Concept Role)) :
    (stateOfGuardedFacts facts).guardedFacts = facts := by
  classical
  ext fact
  rcases fact with label | fact
  · simp [stateOfGuardedFacts, State.holdsFact]
  · rcases fact with edge | obligation <;>
      simp [stateOfGuardedFacts, State.holdsFact]

@[simp] theorem State.stateOfGuardedFacts_guardedFacts
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) :
    stateOfGuardedFacts state.guardedFacts = state := by
  classical
  apply State.ext <;> funext <;> simp [stateOfGuardedFacts, State.holdsFact]

/-- Every branchable head assertion is a strict finite-fact update when that
head is not already discharged. -/
theorem State.guardedFacts_assertAtom_ssubset
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) (assignment : Variable → Node)
    (atom : Atom Variable Concept Role)
    (hbranchable : Branchable atom)
    (habsent : ¬state.holdsAtom assignment atom) :
    state.guardedFacts ⊂ (state.assertAtom assignment atom).guardedFacts := by
  classical
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro fact hfact
    simp only [State.mem_guardedFacts] at hfact ⊢
    rcases fact with label | fact
    · cases atom <;> simp_all [State.holdsFact, State.assertAtom]
    · rcases fact with edge | obligation
      · cases atom <;> simp_all [State.holdsFact, State.assertAtom]
      · cases atom <;> simp_all [State.holdsFact, State.assertAtom]
  · intro hequal
    cases atom with
    | concept literal position =>
        have hnew : (Sum.inl (assignment position, literal) :
            GuardedFact Node Concept Role) ∈
            (state.assertAtom assignment (.concept literal position)).guardedFacts := by
          simp [State.holdsFact, State.assertAtom]
        rw [← hequal] at hnew
        exact habsent (by simpa [State.holdsAtom, State.holdsFact] using hnew)
    | role role source target =>
        have hnew : (Sum.inr (Sum.inl (role, assignment source, assignment target)) :
            GuardedFact Node Concept Role) ∈
            (state.assertAtom assignment (.role role source target)).guardedFacts := by
          simp [State.holdsFact, State.assertAtom]
        rw [← hequal] at hnew
        exact habsent (by simpa [State.holdsAtom, State.holdsFact] using hnew)
    | exists_ role filler position =>
        have hnew : (Sum.inr (Sum.inr (role, filler, assignment position)) :
            GuardedFact Node Concept Role) ∈
            (state.assertAtom assignment (.exists_ role filler position)).guardedFacts := by
          simp [State.holdsFact, State.assertAtom]
        rw [← hequal] at hnew
        exact habsent (by simpa [State.holdsAtom, State.holdsFact] using hnew)
    | eq left right => contradiction

/-- Fresh witness materialization is also a strict finite-fact update. -/
theorem State.guardedFacts_materializeWitness_ssubset
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role)
    (source target : Node) (role : Role) (filler : Lit Concept)
    (hfresh : state.Fresh target) :
    state.guardedFacts ⊂
      (state.materializeWitness source target role filler).guardedFacts := by
  classical
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro fact hfact
    simp only [State.mem_guardedFacts] at hfact ⊢
    rcases fact with label | fact
    · simp_all [State.holdsFact, State.materializeWitness]
    · rcases fact with edge | obligation <;>
        simp_all [State.holdsFact, State.materializeWitness]
  · intro hequal
    have hnew : (Sum.inl (target, filler) : GuardedFact Node Concept Role) ∈
        (state.materializeWitness source target role filler).guardedFacts := by
      simp [State.holdsFact, State.materializeWitness]
    rw [← hequal] at hnew
    exact hfresh.1 filler (by simpa [State.holdsFact] using hnew)

inductive ExhaustiveStep
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role) :
    List (State Node Concept Role) → Prop where
  | branch
      (clause : Clause Variable Concept Role)
      (hclause : clause ∈ ontology)
      (assignment : Variable → Node)
      (hbody : ∀ atom ∈ clause.body, state.holdsAtom assignment atom)
      (hbranchable : ∀ atom ∈ clause.head, Branchable atom) :
      ExhaustiveStep ontology state
        (clause.head.map (state.assertAtom assignment))
  | witness
      (source target : Node) (role : Role) (filler : Lit Concept)
      (hobligation : state.obligation role filler source)
      (hfresh : state.Fresh target) :
      ExhaustiveStep ontology state
        [state.materializeWitness source target role filler]

theorem ExhaustiveStep.refutes_of_children
    {ontology : List (Clause Variable Concept Role)}
    {state : State Node Concept Role}
    {children : List (State Node Concept Role)}
    (step : ExhaustiveStep ontology state children)
    (hchildren : ∀ child, child ∈ children → Refutes Node ontology child) :
    Refutes Node ontology state := by
  cases step with
  | branch clause hclause assignment hbody hbranchable =>
      apply Refutes.branch state clause hclause assignment hbody hbranchable
      intro atom hatom
      exact hchildren (state.assertAtom assignment atom)
        (List.mem_map_of_mem (f := state.assertAtom assignment) hatom)
  | witness source target role filler hobligation hfresh =>
      apply Refutes.witness state source target role filler hobligation hfresh
      exact hchildren (state.materializeWitness source target role filler) (by simp)

/-- Every equality-free obstruction has one of the exact exhaustive transition
shapes, provided the finite blocked universe still offers a fresh witness for
an unwitnessed existential. -/
theorem obstruction_has_exhaustive_step
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role)
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom)
    (hfresh : state.HasUnwitnessed → ∃ target, state.Fresh target)
    (hobstruction : state.HasUnwitnessed ∨ state.HasUndischarged ontology) :
    ∃ children, ExhaustiveStep ontology state children := by
  rcases hobstruction with hwitness | hundischarged
  · rcases hwitness with ⟨source, role, filler, hobligation, hnowitness⟩
    rcases hfresh ⟨source, role, filler, hobligation, hnowitness⟩ with ⟨target, htarget⟩
    exact ⟨[state.materializeWitness source target role filler],
      ExhaustiveStep.witness source target role filler hobligation htarget⟩
  · rcases hundischarged with
      ⟨clause, hclause, assignment, hbody, _⟩
    exact ⟨clause.head.map (state.assertAtom assignment),
      ExhaustiveStep.branch clause hclause assignment hbody (hheads clause hclause)⟩

/-- Concrete finite-search capstone. The transition premise now states only
that Rust's enumerated children decode to one of the two exact HT transition
shapes; child closure is derived rather than assumed. -/
theorem finite_concrete_ht_complete
    {Fact : Type} [Fintype Fact] [DecidableEq Fact]
    (ontology : List (Clause Variable Concept Role))
    (decode : Finset Fact → State Node Concept Role)
    (next : Finset Fact → List (Finset Fact))
    (hguarded : ∀ clause ∈ ontology, clause.GuardedBody)
    (hgrowth : ∀ parent child, child ∈ next parent → StrictGrowth child parent)
    (hstep : ∀ facts, next facts ≠ [] →
      ExhaustiveStep ontology (decode facts) ((next facts).map decode))
    (hterminal : ∀ facts, next facts = [] →
      Refutes Node ontology (decode facts) ∨
      (¬(decode facts).HasUnwitnessed ∧
        ¬(decode facts).HasUndischarged ontology)) :
    ∀ root, Refutes Node ontology (decode root) ∨
      ∃ leaf, SearchDescends next root leaf ∧
        (decode leaf).canonical.models ontology := by
  apply finite_exhaustive_ht_complete ontology decode next hguarded hgrowth hterminal
  intro facts hnonempty hclosed
  apply (hstep facts hnonempty).refutes_of_children
  intro child hchild
  rcases List.mem_map.mp hchild with ⟨factsChild, hfactsChild, rfl⟩
  exact hclosed factsChild hfactsChild

/-- Fully concrete finite-fact specialization used by the certificate producer:
there is no abstract decoder, because `stateOfGuardedFacts` is proved inverse to
the exact finite label/edge/obligation representation above. -/
theorem finite_guarded_fact_ht_complete
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (next : Finset (GuardedFact Node Concept Role) →
      List (Finset (GuardedFact Node Concept Role)))
    (hguarded : ∀ clause ∈ ontology, clause.GuardedBody)
    (hgrowth : ∀ parent child, child ∈ next parent → StrictGrowth child parent)
    (hstep : ∀ facts, next facts ≠ [] →
      ExhaustiveStep ontology (stateOfGuardedFacts facts)
        ((next facts).map stateOfGuardedFacts))
    (hterminal : ∀ facts, next facts = [] →
      Refutes Node ontology (stateOfGuardedFacts facts) ∨
      (¬(stateOfGuardedFacts facts).HasUnwitnessed ∧
        ¬(stateOfGuardedFacts facts).HasUndischarged ontology)) :
    ∀ root, Refutes Node ontology (stateOfGuardedFacts root) ∨
      ∃ leaf, SearchDescends next root leaf ∧
        (stateOfGuardedFacts leaf).canonical.models ontology := by
  exact finite_concrete_ht_complete ontology stateOfGuardedFacts next
    hguarded hgrowth hstep hterminal

#print axioms ExhaustiveStep.refutes_of_children
#print axioms State.guardedFacts_assertAtom_ssubset
#print axioms State.guardedFacts_materializeWitness_ssubset
#print axioms stateOfGuardedFacts_guardedFacts
#print axioms State.stateOfGuardedFacts_guardedFacts
#print axioms obstruction_has_exhaustive_step
#print axioms finite_concrete_ht_complete
#print axioms finite_guarded_fact_ht_complete

end ContextCalculus.Hypertableau
