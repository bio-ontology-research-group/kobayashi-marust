import ContextCalculus.HypertableauRuntimeSearch
import ContextCalculus.HypertableauRegularCertificate

/-!
# Equality-free blocked-open regular certificate production

This module composes the concrete blocker-aware terminal selector with the
regular certificate producer boundary. The finite certificate retains the raw
saturated terminal graph. Existential witnesses are read at blocker redirects,
so certificate production neither copies edges nor creates new clause matches.
-/

namespace ContextCalculus.Hypertableau

/-! ## Finite progress of rejected blocker learning -/

/-- At one fixed node budget, production cannot reject blocked-open candidates
forever when each rejection blacklists at least one previously available fold.
This is the termination measure implemented by Rust's equality-free certified
producer: fold pairs range over the finite node universe and the forbidden set
grows strictly after every rejected candidate. -/
theorem no_infinite_fresh_fold_rejections
    [Fintype Node] [DecidableEq Node]
    (forbidden learned : Nat → Finset (Node × Node))
    (hstep : ∀ round,
      forbidden (round + 1) = forbidden round ∪ learned round)
    (hfresh : ∀ round, ∃ fold ∈ learned round, fold ∉ forbidden round) : False := by
  have hstrict : ∀ round, forbidden round ⊂ forbidden (round + 1) := by
    intro round
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · rw [hstep]
      exact Finset.subset_union_left
    · obtain ⟨fold, hlearned, hnew⟩ := hfresh round
      intro heq
      have hnext : fold ∈ forbidden (round + 1) := by
        rw [hstep]
        exact Finset.mem_union_right _ hlearned
      exact hnew (heq ▸ hnext)
  have hcard : ∀ round,
      (forbidden 0).card + round ≤ (forbidden round).card := by
    intro round
    induction round with
    | zero => simp
    | succ round ih =>
        have hlt := Finset.card_lt_card (hstrict round)
        omega
  have huniv := Finset.card_le_card
    (show forbidden (Fintype.card (Node × Node) + 1) ⊆ Finset.univ by
      exact Finset.subset_univ _)
  have hbound := hcard (Fintype.card (Node × Node) + 1)
  simp only [Finset.card_univ] at huniv
  omega

/-- One producer attempt at a fixed node budget either returns the checked
round result consumed by the outer doubling proof or rejects a finite set of
blocker folds. Rejection is an internal search refinement, never a verdict. -/
inductive FoldLearningOutcome (Node Result : Type) where
  | done (result : Result)
  | rejected (folds : Finset (Node × Node))

/-- The concrete retry layer terminates at every fixed node budget. This turns
the Rust producer's learned-fold loop into a total constructor of the checked
round outcome expected by the existing doubling theorem. -/
theorem fold_learning_eventually_done
    [Fintype Node] [DecidableEq Node]
    (run : Nat → FoldLearningOutcome Node Result)
    (forbidden : Nat → Finset (Node × Node))
    (hlearn : ∀ round folds, run round = .rejected folds →
      forbidden (round + 1) = forbidden round ∪ folds ∧
        ∃ fold ∈ folds, fold ∉ forbidden round) :
    ∃ round result, run round = .done result := by
  by_contra hdone
  have hrejected : ∀ round, ∃ folds, run round = .rejected folds := by
    intro round
    cases houtcome : run round with
    | done result =>
        exact False.elim (hdone ⟨round, result, houtcome⟩)
    | rejected folds => exact ⟨folds, rfl⟩
  choose learned hruns using hrejected
  apply no_infinite_fresh_fold_rejections forbidden learned
  · intro round
    exact (hlearn round (learned round) (hruns round)).1
  · intro round
    exact (hlearn round (learned round) (hruns round)).2

/-- A blocker-aware runtime terminal and checked fold metadata supply every
regular-model invariant. In particular, saturation transfers by state equality
because the serializer no longer mutates the completion graph. -/
theorem FiniteRegularCertificate.check_of_blocked_runtime_terminal
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (runtime : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    (blocked : Fin nodeCount → Bool)
    (fold : Fin nodeCount → Fin nodeCount → Prop)
    (hstate : certificate.state = runtime)
    (hterminal : runtime.BlockedRuntimeTerminal certificate.residual blocked)
    (hwitnessRefines : runtime.BlockedWitnessRefines blocked fold)
    (hredirectRefines : State.BlockedRedirectRefines blocked fold
      certificate.redirect)
    (hauthorized : ∀ rule ∈ certificate.roleClauses,
      rule.Authorized certificate.rules)
    (hguarded : ∀ clause ∈ certificate.residual, clause.GuardedBody)
    (hheads : ∀ clause ∈ certificate.residual, ∀ atom ∈ clause.head,
      PathLiftableHead atom)
    (hcoverClosed : certificate.CoverClosed)
    (hcoverEdge : ∀ role source target,
      certificate.coverRelation role source target →
        certificate.state.edge role source target) :
    certificate.check = true := by
  have hclash : certificate.state.ClashFree := by
    rw [hstate]
    exact hterminal.clashFree
  have hwitness : certificate.state.RedirectWitnessComplete
      certificate.redirect := by
    rw [hstate]
    exact runtime.blockedRedirectWitnessComplete certificate.residual blocked
      fold certificate.redirect hterminal hwitnessRefines hredirectRefines
  have hsaturated : certificate.state.SaturatedFor certificate.residual := by
    rw [hstate]
    exact hterminal.saturatedFor
  exact certificate.check_of_producer_invariants hauthorized hguarded hheads
    hclash hwitness hcoverClosed hcoverEdge hsaturated

#print axioms FiniteRegularCertificate.check_of_blocked_runtime_terminal
#print axioms no_infinite_fresh_fold_rejections
#print axioms fold_learning_eventually_done

end ContextCalculus.Hypertableau
