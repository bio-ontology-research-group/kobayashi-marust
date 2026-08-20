import ContextCalculus.HypertableauBlockingCertificate
import ContextCalculus.Termination
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Monotone.Basic

/-!
# Finite progress for blocked hypertableau evidence search

Once blocking bounds the node universe, every monotone HT branch update adds a
fact from a finite vocabulary. This module includes the ordinary guarded facts,
equality and apartness pairs, and first-class cardinality minimum markers used
by the Rust evidence producers. It proves that no branch can contain infinitely
many strict updates and that the complete set of duplicate-free update traces
is finite.

This is the branch-local termination component. A runtime refinement must still
show that every recursive Rust call either closes, returns a checked finite
model, or performs one of these strict updates over the blocking-bounded node
universe.
-/

namespace ContextCalculus.Hypertableau

/-- Every monotone fact kind stored by the plain, equality-aware, and
cardinality-aware finite HT evidence searches. `Definition` indexes the finite
list of first-class cardinality definitions. -/
abbrev BranchFact (Node Concept Role Definition : Type) :=
  (Node × Lit Concept) ⊕
  ((Role × Node × Node) ⊕
  ((Role × Lit Concept × Node) ⊕
  ((Node × Node) ⊕
  ((Node × Node) ⊕ (Definition × Node)))))

/-- A branch state is represented extensionally by the finite facts accumulated
on that branch. -/
abbrev FiniteBranchState (Node Concept Role Definition : Type)
    [Fintype Node] [Fintype Concept] [Fintype Role] [Fintype Definition]
    [DecidableEq Node] [DecidableEq Concept] [DecidableEq Role]
    [DecidableEq Definition] :=
  Finset (BranchFact Node Concept Role Definition)

/-- Strict monotone branch growth cannot continue forever after blocking has
made nodes finite. -/
theorem no_infinite_strict_branch_growth
    {Node Concept Role Definition : Type}
    [Fintype Node] [Fintype Concept] [Fintype Role] [Fintype Definition]
    [DecidableEq Node] [DecidableEq Concept] [DecidableEq Role]
    [DecidableEq Definition]
    (states : ℕ → FiniteBranchState Node Concept Role Definition)
    (hstep : ∀ step, states step ⊂ states (step + 1)) : False := by
  have hstrict : StrictMono states :=
    strictMono_nat_of_lt_succ hstep
  exact not_injective_infinite_finite states hstrict.injective

/-- Recording one fresh fact for every recursive update gives a duplicate-free
trace. The family of all such traces is finite. Consequently a finitely
branching exhaustive evidence search over these updates has a finite search
tree. -/
theorem finite_branch_progress_traces
    {Node Concept Role Definition : Type}
    [Fintype Node] [Fintype Concept] [Fintype Role] [Fintype Definition]
    [DecidableEq Node] [DecidableEq Concept] [DecidableEq Role]
    [DecidableEq Definition] :
    {trace : List (BranchFact Node Concept Role Definition) | trace.Nodup}.Finite := by
  exact ContextCalculus.Termination.reachable_finite
    (L := BranchFact Node Concept Role Definition)

/-! The following generic result turns finite strict growth into the recursion
principle needed by an exhaustive HT search. It separates termination from the
calculus-specific proof that a closed family of children refutes its parent. -/

def StrictGrowth {Fact : Type} (child parent : Finset Fact) : Prop :=
  parent ⊂ child

def branchRemaining {Fact : Type} [Fintype Fact] (state : Finset Fact) : Nat :=
  Fintype.card Fact - state.card

theorem strictGrowth_remaining_lt
    {Fact : Type} [Fintype Fact] [DecidableEq Fact]
    {child parent : Finset Fact} (hgrowth : StrictGrowth child parent) :
    branchRemaining child < branchRemaining parent := by
  have hcard : parent.card < child.card := Finset.card_lt_card hgrowth
  have hbound : child.card ≤ Fintype.card Fact := Finset.card_le_univ child
  change Fintype.card Fact - child.card < Fintype.card Fact - parent.card
  omega

theorem strictGrowth_wellFounded
    (Fact : Type) [Fintype Fact] [DecidableEq Fact] :
    WellFounded (@StrictGrowth Fact) := by
  exact Subrelation.wf
    (fun {_ _} hgrowth => strictGrowth_remaining_lt hgrowth)
    (measure (@branchRemaining Fact _)).wf

/-- Reflexive-transitive descent through the child lists of an exhaustive
search. -/
inductive SearchDescends {State : Type} (next : State → List State) :
    State → State → Prop where
  | refl (state) : SearchDescends next state state
  | step {parent child leaf}
      (hchild : child ∈ next parent)
      (hrest : SearchDescends next child leaf) :
      SearchDescends next parent leaf

/-- A finite, strictly growing, exhaustive search either closes its root or
reaches an open terminal leaf. `closeChildren` is the calculus-specific rule
that combines exhaustive closed children into evidence for their parent. -/
theorem finite_exhaustive_search_total
    {Fact : Type} [Fintype Fact] [DecidableEq Fact]
    (next : Finset Fact → List (Finset Fact))
    (Closed Open : Finset Fact → Prop)
    (hgrowth : ∀ parent child, child ∈ next parent → StrictGrowth child parent)
    (terminal : ∀ state, next state = [] → Closed state ∨ Open state)
    (closeChildren : ∀ state, next state ≠ [] →
      (∀ child, child ∈ next state → Closed child) → Closed state) :
    ∀ root, Closed root ∨
      ∃ leaf, SearchDescends next root leaf ∧ Open leaf := by
  intro root
  induction root using (strictGrowth_wellFounded Fact).induction with
  | h state ih =>
      by_cases hempty : next state = []
      · rcases terminal state hempty with hclosed | hopen
        · exact Or.inl hclosed
        · exact Or.inr ⟨state, SearchDescends.refl state, hopen⟩
      · by_cases hall : ∀ child, child ∈ next state → Closed child
        · exact Or.inl (closeChildren state hempty hall)
        · push_neg at hall
          obtain ⟨child, hchild, hnotClosed⟩ := hall
          rcases ih child (hgrowth state child hchild) with hclosed | ⟨leaf, hpath, hopen⟩
          · exact (hnotClosed hclosed).elim
          · exact Or.inr ⟨leaf, SearchDescends.step hchild hpath, hopen⟩

#print axioms no_infinite_strict_branch_growth
#print axioms finite_branch_progress_traces
#print axioms strictGrowth_wellFounded
#print axioms finite_exhaustive_search_total

end ContextCalculus.Hypertableau
