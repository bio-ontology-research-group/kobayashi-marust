import ContextCalculus.HypertableauCardinalityRuntimeSearch

/-!
# Production-shaped cardinality hypertableau expansion

This module packages the six cardinality runtime controls into one typed
first-obstruction layer.  Each recursive constructor carries the exact selected
site and the earlier-selector exhaustion facts that establish production
priority.  Witness and minimum allocation use Rust's active-prefix IDs;
maximum expansion uses the deterministic greedy prefix vector.
-/

namespace ContextCalculus.Hypertableau

/-- One selected production-shaped cardinality obstruction.  Immediate clashes
have no recursive children; the other constructors expose exactly the child
family required by the corresponding quotient-closed refutation rule. -/
inductive CardinalityProductionStep
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (expanded : CardinalityDef Concept Role → Fin nodeCount → Prop)
    (active : Nat) : Type where
  | equalityApart
      (candidate : EqualityApartCandidate (Fin nodeCount))
      (hselect : selectEqualityApartClash state = some candidate)
  | conceptClash
      (hnoApart : selectEqualityApartClash state = none)
      (candidate : EqClashCandidate (Fin nodeCount) Concept)
      (hselect : selectCardinalityConceptClash state = some candidate)
  | branch
      (hnoApart : selectEqualityApartClash state = none)
      (hnoClash : selectCardinalityConceptClash state = none)
      (grounding : Grounding Variable (Fin nodeCount) Concept Role)
      (hselect : selectCardinalityClauseGrounding ontology state = some grounding)
  | witness
      (hnoApart : selectEqualityApartClash state = none)
      (hnoClash : selectCardinalityConceptClash state = none)
      (hnoClause : selectCardinalityClauseGrounding ontology state = none)
      (candidate : WitnessCandidate (Fin nodeCount) Concept Role)
      (hselect : selectEqUnblockedUnwitnessed state.base parent ancestors = some candidate)
      (hfit : active < nodeCount)
      (hprefix : state.InactivePrefixFresh active)
  | minimum
      (hnoApart : selectEqualityApartClash state = none)
      (hnoClash : selectCardinalityConceptClash state = none)
      (hnoClause : selectCardinalityClauseGrounding ontology state = none)
      (hnoWitness : selectEqUnblockedUnwitnessed state.base parent ancestors = none)
      (candidate : MinimumCandidate (Fin nodeCount) Concept Role)
      (hselect : selectRustExpandableMinimum definitions state parent ancestors expanded =
        some candidate)
      (hfit : active + candidate.1.bound ≤ nodeCount)
      (hprefix : state.InactivePrefixFresh active)
  | maximum
      (hnoApart : selectEqualityApartClash state = none)
      (hnoClash : selectCardinalityConceptClash state = none)
      (hnoClause : selectCardinalityClauseGrounding ontology state = none)
      (hnoWitness : selectEqUnblockedUnwitnessed state.base parent ancestors = none)
      (hnoMinimum : selectRustExpandableMinimum definitions state parent ancestors expanded =
        none)
      (site : RustMaximumSite nodeCount Concept Role)
      (hselect : selectRustViolatingMaximumSite definitions state = some site)
      (hwidth : site.1.bound + 1 ≤
        (rustMaximumRepresentatives state site.1 site.2).length)
      (hprefix : state.InactivePrefixFresh active)

/-- Every recursive child selected by a production step is closed. -/
def CardinalityProductionStep.ChildrenClosed
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    {ontology : List (Clause Variable Concept Role)}
    {definitions : List (CardinalityDef Concept Role)}
    {state : DistinctEqState (Fin nodeCount) Concept Role}
    {parent : Fin nodeCount → Option (Fin nodeCount)}
    {ancestors : Fin nodeCount → List (Fin nodeCount)}
    {expanded : CardinalityDef Concept Role → Fin nodeCount → Prop}
    {active : Nat}
    (step : CardinalityProductionStep ontology definitions state parent ancestors expanded
      active) : Prop :=
  match step with
  | .equalityApart _ _ => True
  | .conceptClash _ _ _ => True
  | .branch _ _ grounding _ =>
      ∀ atom, atom ∈ grounding.1.head →
        ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions
          (state.assertAtom grounding.2 atom)
  | .witness _ _ _ candidate _ hfit _ =>
      ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions
        (state.materializeWitness candidate.2.2
          (rustNextTarget active nodeCount hfit) candidate.1 candidate.2.1)
  | .minimum _ _ _ _ candidate _ hfit _ =>
      ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions
        (state.materializeMinimum candidate.2
          (rustConsecutiveTargets active candidate.1.bound nodeCount hfit)
          candidate.1.role candidate.1.filler)
  | .maximum _ _ _ _ _ site _ hwidth _ =>
      ∀ left right : Fin (site.1.bound + 1), left ≠ right →
        ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions
          (state.merge
            (rustPrefixVector (rustMaximumRepresentatives state site.1 site.2)
              (site.1.bound + 1) hwidth left)
            (rustPrefixVector (rustMaximumRepresentatives state site.1 site.2)
              (site.1.bound + 1) hwidth right))

/-- Closing every recursive child of the selected first obstruction closes the
parent state.  Earlier-selector exhaustion fields are operational evidence;
soundness itself follows from the selected rule. -/
theorem CardinalityProductionStep.closedRefutes_of_children
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    {ontology : List (Clause Variable Concept Role)}
    {definitions : List (CardinalityDef Concept Role)}
    {state : DistinctEqState (Fin nodeCount) Concept Role}
    {parent : Fin nodeCount → Option (Fin nodeCount)}
    {ancestors : Fin nodeCount → List (Fin nodeCount)}
    {expanded : CardinalityDef Concept Role → Fin nodeCount → Prop}
    {active : Nat}
    (step : CardinalityProductionStep ontology definitions state parent ancestors expanded
      active)
    (hchildren : step.ChildrenClosed) :
    ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions state := by
  cases step with
  | equalityApart candidate hselect =>
      exact (selectEqualityApartClash_refutes ontology definitions state hselect).toClosed
  | conceptClash hnoApart candidate hselect =>
      exact (selectCardinalityConceptClash_refutes ontology definitions state hselect).toClosed
  | branch hnoApart hnoClash grounding hselect =>
      exact selectCardinalityClauseGrounding_closedRefutes ontology definitions state
        hselect hchildren
  | witness hnoApart hnoClash hnoClause candidate hselect hfit hprefix =>
      classical
      have hcandidate := firstMatch_eq_some_mem
        (by simpa [selectEqUnblockedUnwitnessed] using hselect)
      have hproperties :=
        (eqUnblockedWitnessCandidateBool_eq_true_iff state.base parent ancestors
          candidate).mp hcandidate.2
      exact .witness state candidate.2.2 (rustNextTarget active nodeCount hfit)
        candidate.1 candidate.2.1 hproperties.1
        (hprefix (rustNextTarget active nodeCount hfit) (by simp [rustNextTarget]))
        hchildren
  | minimum hnoApart hnoClash hnoClause hnoWitness candidate hselect hfit hprefix =>
      exact selectRustExpandableMinimum_consecutive_closedRefutes ontology definitions state
        parent ancestors expanded hselect active hprefix hfit hchildren
  | maximum hnoApart hnoClash hnoClause hnoWitness hnoMinimum site hselect hwidth hprefix =>
      exact selectRustViolatingMaximumSite_closedRefutes ontology definitions state hselect
        hwidth hchildren

#print axioms CardinalityProductionStep.closedRefutes_of_children

end ContextCalculus.Hypertableau
