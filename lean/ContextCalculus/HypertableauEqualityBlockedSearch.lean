import ContextCalculus.HypertableauEqualityRuntimeSearch
import ContextCalculus.HypertableauEqualityBlockingCertificate

/-!
# Globally terminating equality search with checked blocked terminals

A blocked equality terminal is not trusted as a model. The runtime must supply
a finite equality fold, and `FiniteEqFoldCertificate.check` validates its fully
materialized quotient graph against the exact ontology. This module composes
that fail-closed boundary with the concrete globally terminating equality
runtime.
-/

namespace ContextCalculus.Hypertableau

def HasCheckedEqFoldModel
    (nodeCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) : Prop :=
  ∃ certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount,
    certificate.base.base.ontology = ontology ∧ certificate.check = true

theorem hasModel_of_hasCheckedEqFoldModel
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (hfold : HasCheckedEqFoldModel (nodeCount := nodeCount) ontology) :
    HasModel ontology := by
  rcases hfold with ⟨certificate, hontology, hcheck⟩
  rcases certificate.check_satisfiable hcheck with ⟨Domain, I, hmodels⟩
  exact ⟨Domain, I, by simpa [hontology] using hmodels⟩

/-- Typed result of one fixed-budget equality-aware search. A frontier remains
explicitly inconclusive. -/
inductive EqBoundedSearchOutcome
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (state : EqState (Fin nodeCount) (Fin conceptCount) (Fin roleCount)) : Type where
  | closed (proof : ClosedEqRefutes (Fin nodeCount) ontology state)
  | model (fold : HasCheckedEqFoldModel (nodeCount := nodeCount) ontology)
  | frontier

theorem EqBoundedSearchOutcome.semantic_or_frontier
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {state : EqState (Fin nodeCount) (Fin conceptCount) (Fin roleCount)}
    (result : EqBoundedSearchOutcome nodeCount conceptCount roleCount variableCount
      ontology state) :
    ClosedEqRefutes (Fin nodeCount) ontology state ∨ HasModel ontology ∨
      result = .frontier := by
  cases result with
  | closed proof => exact Or.inl proof
  | model fold => exact Or.inr (Or.inl (hasModel_of_hasCheckedEqFoldModel fold))
  | frontier => exact Or.inr (Or.inr rfl)

/-- Compose the concrete, well-founded clash-first equality runtime with the
checked fold boundary. The only remaining inconclusive result is explicit node
exhaustion. `hterminal` is the exact producer obligation: every
blocked/saturated leaf must provide evidence accepted by the independent fold
checker. -/
theorem finite_eqRuntime_decides_with_checked_folds
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (parent : EqState (Fin nodeCount) (Fin conceptCount) (Fin roleCount) →
      Fin nodeCount → Option (Fin nodeCount))
    (ancestors : EqState (Fin nodeCount) (Fin conceptCount) (Fin roleCount) →
      Fin nodeCount → List (Fin nodeCount))
    (hterminal : ∀ state, EqRuntimeTerminal ontology parent ancestors state →
      HasCheckedEqFoldModel (nodeCount := nodeCount) ontology) :
    ∀ root,
      ClosedEqRefutes (Fin nodeCount) ontology root ∨ HasModel ontology ∨
      ∃ leaf, SearchDescends
          (eqRuntimeNextClashFirst ontology parent ancestors) root leaf ∧
        EqRuntimeNodeFrontier ontology leaf (parent leaf) (ancestors leaf) := by
  intro root
  rcases finite_eqRuntime_semantic_or_terminal ontology parent ancestors root with
    hrefutes | ⟨leaf, hpath, hterminalOrFrontier⟩
  · exact Or.inl hrefutes
  · rcases hterminalOrFrontier with hleaf | hfrontier
    · exact Or.inr (Or.inl
        (hasModel_of_hasCheckedEqFoldModel (hterminal leaf hleaf)))
    · exact Or.inr (Or.inr ⟨leaf, hpath, hfrontier⟩)

/-- If the finite node budget is sufficient, the concrete equality runtime
decides the root semantically. This theorem cannot silently turn node
exhaustion into SAT. -/
theorem finite_eqRuntime_decides_of_no_frontier
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (parent : EqState (Fin nodeCount) (Fin conceptCount) (Fin roleCount) →
      Fin nodeCount → Option (Fin nodeCount))
    (ancestors : EqState (Fin nodeCount) (Fin conceptCount) (Fin roleCount) →
      Fin nodeCount → List (Fin nodeCount))
    (hterminal : ∀ state, EqRuntimeTerminal ontology parent ancestors state →
      HasCheckedEqFoldModel (nodeCount := nodeCount) ontology)
    (hcapacity : ∀ state,
      ¬EqRuntimeNodeFrontier ontology state (parent state) (ancestors state)) :
    ∀ root,
      ClosedEqRefutes (Fin nodeCount) ontology root ∨ HasModel ontology := by
  intro root
  rcases finite_eqRuntime_decides_with_checked_folds ontology parent ancestors
      hterminal root with hrefutes | hmodel | ⟨leaf, hpath, hfrontier⟩
  · exact Or.inl hrefutes
  · exact Or.inr hmodel
  · exact (hcapacity leaf hfrontier).elim

#print axioms hasModel_of_hasCheckedEqFoldModel
#print axioms EqBoundedSearchOutcome.semantic_or_frontier
#print axioms finite_eqRuntime_decides_with_checked_folds
#print axioms finite_eqRuntime_decides_of_no_frontier

end ContextCalculus.Hypertableau
