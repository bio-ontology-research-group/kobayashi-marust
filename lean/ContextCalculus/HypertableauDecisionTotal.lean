import ContextCalculus.HypertableauRegularDecisionTotal
import ContextCalculus.HypertableauEqualitySearch
import ContextCalculus.HypertableauCardinalitySearch

/-!
# Unified total checked hypertableau routes

This module gives the three total bounded HT searches one source-level result
type. A route may use regular equality-free models, finite equality quotients,
or cardinality-aware quotients. Each route carries exact model equivalence from
the source ontology to its internal target and the checked frontier facts used
by its doubling theorem.
-/

namespace ContextCalculus.Hypertableau

inductive CertifiedHTVerdict
    (source : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) : Type where
  | sat (semantics : CardinalityHasNonemptyModel source definitions)
  | unsat (semantics : ¬CardinalityHasNonemptyModel source definitions)

inductive CertifiedHTRoute
    (conceptCount roleCount variableCount : Nat)
    (source : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Type where
  | regular
      {target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      (hdefinitions : definitions = [])
      (equivalent : ModelEquivalent source target)
      (run : Nat → CheckedRegularRoundOutcome
        conceptCount roleCount variableCount target)
      (hnodes : ∀ round document hconcepts hroles hcheck,
        run round = .frontier document hconcepts hroles hcheck →
          document.node_count = 8 * 2 ^ round)
  | equality
      {target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      (hdefinitions : definitions = [])
      (equivalent : ModelEquivalent source target)
      (run : Nat → CheckedEqualityDecisionOutcome
        conceptCount roleCount variableCount target)
      (hnodes : ∀ round document hconcepts hroles hcheck,
        run round = .frontier document hconcepts hroles hcheck →
          document.node_count = 8 * 2 ^ round)
  | cardinality
      {target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      (equivalent : ModelEquivalent source target)
      (maxWidth : Nat)
      (run : Nat → CheckedCardinalityDecisionOutcome
        conceptCount roleCount variableCount target definitions)
      (hnodes : ∀ round document hconcepts hroles hdefinitions hcheck,
        run round = .frontier document hconcepts hroles hdefinitions hcheck →
          document.node_count = 8 * 2 ^ round)
      (hwidth : ∀ round document hconcepts hroles hdefinitions hcheck,
        run round = .frontier document hconcepts hroles hdefinitions hcheck →
          document.max_width = maxWidth)

/-- Every certified total HT route returns a source-level SAT or UNSAT verdict.
The route tag changes only the checked evidence used to obtain that verdict. -/
theorem CertifiedHTRoute.decides
    {source : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (route : CertifiedHTRoute conceptCount roleCount variableCount
      source definitions) :
    Nonempty (CertifiedHTVerdict source definitions) := by
  cases route with
  | regular hdefinitions equivalent run hnodes =>
      subst definitions
      obtain ⟨round, hsemantics⟩ :=
        checked_regular_doubling_decides_source equivalent run hnodes
      generalize houtcome : run round = outcome at hsemantics
      cases outcome with
      | regularSat certificate hontology hnonempty hcheck =>
          simp only [CheckedRegularRoundOutcome.SourceSemantics] at hsemantics
          rcases hsemantics with ⟨Domain, I, hdomain, hmodels⟩
          exact ⟨.sat ⟨Domain, I, hdomain, hmodels, by
            simp [Interp.modelsCardinalityDefs]⟩⟩
      | finiteUnsat certificate tree hontology hnonempty hempty hcheck =>
          simp only [CheckedRegularRoundOutcome.SourceSemantics] at hsemantics
          refine ⟨.unsat ?_⟩
          rintro ⟨Domain, I, hdomain, hmodels, hdefinitions⟩
          exact hsemantics ⟨Domain, I, hdomain, hmodels⟩
      | frontier document hconcepts hroles hcheck =>
          simp only [CheckedRegularRoundOutcome.SourceSemantics] at hsemantics
  | equality hdefinitions equivalent run hnodes =>
      subst definitions
      obtain ⟨round, hsemantics⟩ :=
        checked_equality_doubling_decides_source equivalent run hnodes
      generalize houtcome : run round = outcome at hsemantics
      cases outcome with
      | sat certificate hontology hnonempty hcheck =>
          simp only [CheckedEqualityDecisionOutcome.SourceSemantics] at hsemantics
          rcases hsemantics with ⟨Domain, I, hdomain, hmodels⟩
          exact ⟨.sat ⟨Domain, I, hdomain, hmodels, by
            simp [Interp.modelsCardinalityDefs]⟩⟩
      | closed certificate tree hontology hnonempty hempty hcheck =>
          simp only [CheckedEqualityDecisionOutcome.SourceSemantics] at hsemantics
          refine ⟨.unsat ?_⟩
          rintro ⟨Domain, I, hdomain, hmodels, hdefinitions⟩
          exact hsemantics ⟨Domain, I, hdomain, hmodels⟩
      | frontier document hconcepts hroles hcheck =>
          simp only [CheckedEqualityDecisionOutcome.SourceSemantics] at hsemantics
  | cardinality equivalent maxWidth run hnodes hwidth =>
      obtain ⟨round, hsemantics⟩ :=
        checked_cardinality_doubling_decides_source equivalent maxWidth run
          hnodes hwidth
      generalize houtcome : run round = outcome at hsemantics
      cases outcome with
      | sat certificate hontology hnonempty hcheck =>
          exact ⟨.sat (by
            simpa only [CheckedCardinalityDecisionOutcome.SourceSemantics]
              using hsemantics)⟩
      | closed certificate tree hontology hnonempty hempty hapart hcheck =>
          exact ⟨.unsat (by
            simpa only [CheckedCardinalityDecisionOutcome.SourceSemantics]
              using hsemantics)⟩
      | frontier document hconcepts hroles hdefinitions hcheck =>
          simp only [CheckedCardinalityDecisionOutcome.SourceSemantics] at hsemantics

#print axioms CertifiedHTRoute.decides

end ContextCalculus.Hypertableau
