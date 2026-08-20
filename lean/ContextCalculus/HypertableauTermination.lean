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

#print axioms no_infinite_strict_branch_growth
#print axioms finite_branch_progress_traces

end ContextCalculus.Hypertableau
