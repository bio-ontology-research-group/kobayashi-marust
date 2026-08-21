import ContextCalculus.HypertableauDecisionTotal
import ContextCalculus.HypertableauNativeABoxSearch

/-!
# Total production hypertableau global decision

This module puts every global decision family selected by
`Ht.lean_global_decision_certificate_json` behind one semantic interface. The
regular, equality, cardinality, and native-ABox searches use different checked
certificate types, but all four return either a proof of the exact source
problem or a proof of its negation. A frontier is never a verdict.
-/

namespace ContextCalculus.Hypertableau

/-- The common semantic result of a certified production-global route. -/
inductive CertifiedHTGlobalVerdict (semantics : Prop) : Type where
  | sat (proof : semantics)
  | unsat (proof : ¬semantics)

/-- The four total checked global-search families used by the production HT
certificate producer. The index records the exact source-level semantics of
the selected family, including native ABox and cardinality data where present.
-/
inductive CertifiedHTProductionGlobalRoute : (semantics : Prop) → Type 2 where
  | regular
      {source target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      (equivalent : ModelEquivalent source target)
      (producer : ∀ budget, FreshFoldProducer (Fin (8 * 2 ^ budget))
        (CheckedRegularRoundOutcome conceptCount roleCount variableCount target))
      (hnodes : ∀ budget retry document hconcepts hroles hcheck,
        (producer budget).run retry = .done
          (.frontier document hconcepts hroles hcheck) →
        document.node_count = 8 * 2 ^ budget) :
      CertifiedHTProductionGlobalRoute (HasNonemptyModel source)
  | equality
      {source target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      (equivalent : ModelEquivalent source target)
      (producer : ∀ budget, FreshFoldProducer (Fin (8 * 2 ^ budget))
        (CheckedEqualityDecisionOutcome conceptCount roleCount variableCount target))
      (hnodes : ∀ budget retry document hconcepts hroles hcheck,
        (producer budget).run retry = .done
          (.frontier document hconcepts hroles hcheck) →
          document.node_count = 8 * 2 ^ budget) :
      CertifiedHTProductionGlobalRoute (EqualityHasNonemptyModel source)
  | cardinality
      {source target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      {definitions : List
        (CardinalityDef (Fin conceptCount) (Fin roleCount))}
      (equivalent : ModelEquivalent source target)
      (maxWidth : Nat)
      (producer : ∀ budget, FreshFoldProducer (Fin (8 * 2 ^ budget))
        (CheckedCardinalityDecisionOutcome conceptCount roleCount variableCount
          target definitions))
      (hnodes : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
        (producer budget).run retry = .done
          (.frontier document hconcepts hroles hdefinitions hcheck) →
          document.node_count = 8 * 2 ^ budget)
      (hwidth : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
        (producer budget).run retry = .done
          (.frontier document hconcepts hroles hdefinitions hcheck) →
          document.max_width = maxWidth) :
      CertifiedHTProductionGlobalRoute
        (CardinalityHasNonemptyModel source definitions)
  | nativeABox
      {Individual : Type}
      {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
      {source target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      {definitions : List
        (CardinalityDef (Fin conceptCount) (Fin roleCount))}
      (equivalent : ModelEquivalent source target)
      (maxWidth : Nat)
      (producer : ∀ budget, FreshFoldProducer (Fin (8 * 2 ^ budget))
        (CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
          variableCount abox target definitions))
      (hnodes : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
        (producer budget).run retry = .done
          (.frontier document hconcepts hroles hdefinitions hcheck) →
          document.node_count = 8 * 2 ^ budget)
      (hwidth : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
        (producer budget).run retry = .done
          (.frontier document hconcepts hroles hdefinitions hcheck) →
          document.max_width = maxWidth) :
      CertifiedHTProductionGlobalRoute
        (abox.SatisfiableWithCardinality source definitions)

/-- Every checked production-global HT family eventually returns a conclusive
source-level SAT or UNSAT theorem. In particular, this theorem includes the
native-ABox family omitted from `CertifiedHTRoute.decides`.
-/
theorem CertifiedHTProductionGlobalRoute.decides
    {semantics : Prop}
    (route : CertifiedHTProductionGlobalRoute semantics) :
    Nonempty (CertifiedHTGlobalVerdict semantics) := by
  cases route with
  | regular equivalent producer hnodes =>
      obtain ⟨_, _, outcome, _, hsemantics⟩ :=
        checked_regular_fresh_fold_producer_decides_source equivalent producer hnodes
      cases outcome with
      | regularSat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | finiteSat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | finiteUnsat certificate tree hontology hnonempty hempty hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hcheck =>
          simp only [CheckedRegularRoundOutcome.SourceSemantics] at hsemantics
  | equality equivalent producer hnodes =>
      obtain ⟨_, _, outcome, _, hsemantics⟩ :=
        checked_equality_fresh_fold_producer_decides_source equivalent producer hnodes
      cases outcome with
      | sat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | closed certificate tree hontology hnonempty hempty hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hcheck =>
          simp only [CheckedEqualityDecisionOutcome.SourceSemantics] at hsemantics
  | cardinality equivalent maxWidth producer hnodes hwidth =>
      obtain ⟨_, _, outcome, _, hsemantics⟩ :=
        checked_cardinality_fresh_fold_producer_decides_source equivalent
          maxWidth producer hnodes hwidth
      cases outcome with
      | sat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | closed certificate tree hontology hnonempty hempty hapart hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hdefinitions hcheck =>
          simp only [CheckedCardinalityDecisionOutcome.SourceSemantics] at hsemantics
  | nativeABox equivalent maxWidth producer hnodes hwidth =>
      obtain ⟨_, _, outcome, _, hsemantics⟩ :=
        checked_native_abox_cardinality_fresh_fold_producer_decides_source
          equivalent maxWidth producer hnodes hwidth
      cases outcome with
      | sat certificate root hontology hnonempty hseeded hcheck hapart
          hsingletons hnegative =>
          exact ⟨.sat hsemantics⟩
      | closed certificate tree hontology hinitial hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hdefinitions hcheck =>
          simp only [CheckedNativeABoxCardinalityOutcome.SourceSemantics] at hsemantics

#print axioms CertifiedHTProductionGlobalRoute.decides

end ContextCalculus.Hypertableau
