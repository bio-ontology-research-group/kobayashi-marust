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
      (producer : ∀ budget,
        CheckedRegularControlProducer conceptCount roleCount variableCount
          target budget) :
      CertifiedHTProductionGlobalRoute (HasNonemptyModel source)
  | equality
      {source target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      (equivalent : ModelEquivalent source target)
      (producer : ∀ budget,
        CheckedEqualityControlProducer conceptCount roleCount variableCount
          target budget) :
      CertifiedHTProductionGlobalRoute (EqualityHasNonemptyModel source)
  | cardinality
      {source target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      {definitions : List
        (CardinalityDef (Fin conceptCount) (Fin roleCount))}
      (equivalent : ModelEquivalent source target)
      (maxWidth : Nat)
      (producer : ∀ budget,
        CheckedCardinalityControlProducer conceptCount roleCount variableCount
          target definitions budget maxWidth) :
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
      (producer : ∀ budget,
        CheckedNativeABoxCardinalityControlProducer Individual conceptCount
          roleCount variableCount abox target definitions budget maxWidth) :
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
  | regular equivalent producer =>
      obtain ⟨_, _, outcome, _, hsemantics⟩ :=
        checked_regular_control_producer_decides_source equivalent producer
      cases outcome with
      | regularSat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | finiteSat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | finiteUnsat certificate tree hontology hnonempty hempty hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hcheck =>
          simp only [CheckedRegularRoundOutcome.SourceSemantics] at hsemantics
  | equality equivalent producer =>
      obtain ⟨_, _, outcome, _, hsemantics⟩ :=
        checked_equality_control_producer_decides_source equivalent producer
      cases outcome with
      | sat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | closed certificate tree hontology hnonempty hempty hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hcheck =>
          simp only [CheckedEqualityDecisionOutcome.SourceSemantics] at hsemantics
  | cardinality equivalent maxWidth producer =>
      obtain ⟨_, _, outcome, _, hsemantics⟩ :=
        checked_cardinality_control_producer_decides_source equivalent
          maxWidth producer
      cases outcome with
      | sat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | closed certificate tree hontology hnonempty hempty hapart hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hdefinitions hcheck =>
          simp only [CheckedCardinalityDecisionOutcome.SourceSemantics] at hsemantics
  | nativeABox equivalent maxWidth producer =>
      obtain ⟨_, _, outcome, _, hsemantics⟩ :=
        checked_native_abox_cardinality_control_producer_decides_source
          equivalent maxWidth producer
      cases outcome with
      | sat certificate root hontology hnonempty hseeded hcheck hapart
          hsingletons hnegative =>
          exact ⟨.sat hsemantics⟩
      | closed certificate tree hontology hinitial hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hdefinitions hcheck =>
          simp only [CheckedNativeABoxCardinalityOutcome.SourceSemantics] at hsemantics

/-! ## Current complete-assignment production route

The legacy route above records pair-set rejection.  Current KM rejects one
complete simultaneous fold assignment and retains its constituent pairs for
other candidates.  This route is the end-to-end semantic interface for that
control. -/

inductive CertifiedHTAssignmentProductionGlobalRoute :
    (semantics : Prop) → Type 2 where
  | regular
      {source target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      (equivalent : ModelEquivalent source target)
      (producer : ∀ budget, CartesianFoldAssignmentProducer
        (Fin (8 * 2 ^ budget))
        (CheckedRegularRoundOutcome conceptCount roleCount variableCount target))
      (scheduled : ∀ budget retry document hconcepts hroles hcheck,
        (producer budget).toGuarded.toFoldAssignmentProducer.run retry = .done
          (.frontier document hconcepts hroles hcheck) →
        document.checkScheduled budget = true) :
      CertifiedHTAssignmentProductionGlobalRoute (HasNonemptyModel source)
  | equality
      {source target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      (equivalent : ModelEquivalent source target)
      (producer : ∀ budget, CartesianFoldAssignmentProducer
        (Fin (8 * 2 ^ budget))
        (CheckedEqualityDecisionOutcome conceptCount roleCount variableCount target))
      (nodes : ∀ budget retry document hconcepts hroles hcheck,
        (producer budget).toGuarded.toFoldAssignmentProducer.run retry = .done
          (.frontier document hconcepts hroles hcheck) →
        document.node_count = 8 * 2 ^ budget) :
      CertifiedHTAssignmentProductionGlobalRoute (EqualityHasNonemptyModel source)
  | cardinality
      {source target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      {definitions : List
        (CardinalityDef (Fin conceptCount) (Fin roleCount))}
      (equivalent : ModelEquivalent source target)
      (maxWidth : Nat)
      (producer : ∀ budget, CartesianFoldAssignmentProducer
        (Fin (8 * 2 ^ budget))
        (CheckedCardinalityDecisionOutcome conceptCount roleCount variableCount
          target definitions))
      (nodes : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
        (producer budget).toGuarded.toFoldAssignmentProducer.run retry = .done
          (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.node_count = 8 * 2 ^ budget)
      (width : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
        (producer budget).toGuarded.toFoldAssignmentProducer.run retry = .done
          (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.max_width = maxWidth) :
      CertifiedHTAssignmentProductionGlobalRoute
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
      (producer : ∀ budget, CartesianFoldAssignmentProducer
        (Fin (8 * 2 ^ budget))
        (CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
          variableCount abox target definitions))
      (nodes : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
        (producer budget).toGuarded.toFoldAssignmentProducer.run retry = .done
          (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.node_count = 8 * 2 ^ budget)
      (width : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
        (producer budget).toGuarded.toFoldAssignmentProducer.run retry = .done
          (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.max_width = maxWidth) :
      CertifiedHTAssignmentProductionGlobalRoute
        (abox.SatisfiableWithCardinality source definitions)

theorem CertifiedHTAssignmentProductionGlobalRoute.decides
    {semantics : Prop}
    (route : CertifiedHTAssignmentProductionGlobalRoute semantics) :
    Nonempty (CertifiedHTGlobalVerdict semantics) := by
  cases route with
  | regular equivalent producer scheduled =>
      obtain ⟨_, _, outcome, _, hsemantics⟩ :=
        checked_regular_scheduled_fold_assignment_producer_decides_source equivalent
          (fun budget => (producer budget).toGuarded.toFoldAssignmentProducer) scheduled
      cases outcome with
      | regularSat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | finiteSat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | finiteUnsat certificate tree hontology hnonempty hempty hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hcheck =>
          simp only [CheckedRegularRoundOutcome.SourceSemantics] at hsemantics
  | equality equivalent producer nodes =>
      obtain ⟨_, _, outcome, _, hsemantics⟩ :=
        checked_equality_fold_assignment_producer_decides_source equivalent
          (fun budget => (producer budget).toGuarded.toFoldAssignmentProducer) nodes
      cases outcome with
      | sat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | closed certificate tree hontology hnonempty hempty hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hcheck =>
          simp only [CheckedEqualityDecisionOutcome.SourceSemantics] at hsemantics
  | cardinality equivalent maxWidth producer nodes width =>
      obtain ⟨_, _, outcome, _, hsemantics⟩ :=
        checked_cardinality_fold_assignment_producer_decides_source equivalent
          maxWidth (fun budget =>
            (producer budget).toGuarded.toFoldAssignmentProducer)
          nodes width
      cases outcome with
      | sat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | closed certificate tree hontology hnonempty hempty hapart hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hdefinitions hcheck =>
          simp only [CheckedCardinalityDecisionOutcome.SourceSemantics] at hsemantics
  | nativeABox equivalent maxWidth producer nodes width =>
      obtain ⟨_, _, outcome, _, hsemantics⟩ :=
        checked_native_abox_cardinality_guarded_fold_assignment_producer_decides_source
          equivalent maxWidth (fun budget => (producer budget).toGuarded)
          nodes width
      cases outcome with
      | sat certificate root hontology hnonempty hseeded hcheck hapart
          hsingletons hnegative =>
          exact ⟨.sat hsemantics⟩
      | closed certificate tree hontology hinitial hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hdefinitions hcheck =>
          simp only [CheckedNativeABoxCardinalityOutcome.SourceSemantics] at hsemantics

#print axioms CertifiedHTProductionGlobalRoute.decides
#print axioms CertifiedHTAssignmentProductionGlobalRoute.decides

end ContextCalculus.Hypertableau
