import ContextCalculus.HypertableauDecisionTotal
import ContextCalculus.HypertableauNativeABoxSearch
import ContextCalculus.HypertableauExpansionProduction

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

/-! ## Concrete execution publication

These predicates specialize the generic nested execution trace to each
production outcome family. A frontier step must carry the exact checked
doubling schedule; the terminal predicate excludes frontiers. -/

def RegularProductionFrontier
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (budget : Nat)
    (outcome : CheckedRegularRoundOutcome
      conceptCount roleCount variableCount ontology) : Prop :=
  ∃ document hconcepts hroles hcheck,
    outcome = .frontier document hconcepts hroles hcheck ∧
      document.checkScheduled budget = true

def RegularProductionConclusive
    {conceptCount roleCount variableCount : Nat}
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedRegularRoundOutcome
      conceptCount roleCount variableCount ontology) : Prop :=
  match outcome with | .frontier .. => False | _ => True

/-- A concrete, fully traced regular execution publishes a source-level
decision without invoking the abstract producer-totality interface. -/
theorem checked_regular_doubling_execution_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedRegularRoundOutcome conceptCount roleCount variableCount target))
    {outcome : CheckedRegularRoundOutcome
      conceptCount roleCount variableCount target}
    (trace : CartesianFoldDoublingExecution _ runtime
      (RegularProductionFrontier conceptCount roleCount variableCount target)
      RegularProductionConclusive 0 outcome) :
    outcome.SourceSemantics source := by
  have hconclusive := trace.conclusive
  cases outcome with
  | regularSat certificate hontology hnonempty hcheck =>
      exact CheckedRegularRoundOutcome.source_semantics_of_equivalent _ equivalent
        (CheckedRegularRoundOutcome.regularSat_semantics certificate hontology
          hnonempty hcheck)
  | finiteSat certificate hontology hnonempty hcheck =>
      exact CheckedRegularRoundOutcome.source_semantics_of_equivalent _ equivalent
        (CheckedRegularRoundOutcome.finiteSat_semantics certificate hontology
          hnonempty hcheck)
  | finiteUnsat certificate tree hontology hnonempty hempty hcheck =>
      exact CheckedRegularRoundOutcome.source_semantics_of_equivalent _ equivalent
        (CheckedRegularRoundOutcome.finiteUnsat_semantics certificate tree
          hontology hnonempty hempty hcheck)
  | frontier => simp [RegularProductionConclusive] at hconclusive

def EqualityProductionFrontier
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (budget : Nat)
    (outcome : CheckedEqualityDecisionOutcome
      conceptCount roleCount variableCount ontology) : Prop :=
  ∃ document hconcepts hroles hcheck,
    outcome = .frontier document hconcepts hroles hcheck ∧
      document.checkScheduled budget = true

def EqualityProductionConclusive
    {conceptCount roleCount variableCount : Nat}
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedEqualityDecisionOutcome
      conceptCount roleCount variableCount ontology) : Prop :=
  match outcome with | .frontier .. => False | _ => True

theorem checked_equality_doubling_execution_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedEqualityDecisionOutcome conceptCount roleCount variableCount target))
    {outcome : CheckedEqualityDecisionOutcome
      conceptCount roleCount variableCount target}
    (trace : CartesianFoldDoublingExecution _ runtime
      (EqualityProductionFrontier conceptCount roleCount variableCount target)
      EqualityProductionConclusive 0 outcome) :
    outcome.SourceSemantics source := by
  have hconclusive := trace.conclusive
  cases outcome with
  | sat certificate hontology hnonempty hcheck =>
      exact CheckedEqualityDecisionOutcome.source_semantics_of_equivalent _ equivalent
        (CheckedEqualityDecisionOutcome.sat_semantics certificate hontology
          hnonempty hcheck)
  | closed certificate tree hontology hnonempty hempty hcheck =>
      exact CheckedEqualityDecisionOutcome.source_semantics_of_equivalent _ equivalent
        (CheckedEqualityDecisionOutcome.closed_semantics certificate tree
          hontology hnonempty hempty hcheck)
  | frontier => simp [EqualityProductionConclusive] at hconclusive

def CardinalityProductionFrontier
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (maxWidth budget : Nat)
    (outcome : CheckedCardinalityDecisionOutcome conceptCount roleCount
      variableCount ontology definitions) : Prop :=
  ∃ document hconcepts hroles hdefinitions hcheck,
    outcome = .frontier document hconcepts hroles hdefinitions hcheck ∧
      document.checkScheduled budget maxWidth = true

def CardinalityProductionConclusive
    {conceptCount roleCount variableCount : Nat}
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedCardinalityDecisionOutcome conceptCount roleCount
      variableCount ontology definitions) : Prop :=
  match outcome with | .frontier .. => False | _ => True

theorem checked_cardinality_doubling_execution_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (maxWidth : Nat)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedCardinalityDecisionOutcome conceptCount roleCount variableCount
        target definitions))
    {outcome : CheckedCardinalityDecisionOutcome conceptCount roleCount
      variableCount target definitions}
    (trace : CartesianFoldDoublingExecution _ runtime
      (CardinalityProductionFrontier conceptCount roleCount variableCount target
        definitions maxWidth)
      CardinalityProductionConclusive 0 outcome) :
    outcome.SourceSemantics source := by
  have hconclusive := trace.conclusive
  cases outcome with
  | sat certificate hontology hnonempty hcheck =>
      exact CheckedCardinalityDecisionOutcome.source_semantics_of_equivalent _
        equivalent (CheckedCardinalityDecisionOutcome.sat_semantics certificate
          hontology hnonempty hcheck)
  | closed certificate tree hontology hnonempty hempty hapart hcheck =>
      exact CheckedCardinalityDecisionOutcome.source_semantics_of_equivalent _
        equivalent (CheckedCardinalityDecisionOutcome.closed_semantics certificate
          tree hontology hnonempty hempty hapart hcheck)
  | frontier => simp [CardinalityProductionConclusive] at hconclusive

def NativeABoxProductionFrontier
    (Individual : Type)
    (conceptCount roleCount variableCount : Nat)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (maxWidth budget : Nat)
    (outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox ontology definitions) : Prop :=
  ∃ document hconcepts hroles hdefinitions hcheck,
    outcome = .frontier document hconcepts hroles hdefinitions hcheck ∧
      document.checkScheduled budget maxWidth = true

def NativeABoxProductionConclusive
    {Individual : Type}
    {conceptCount roleCount variableCount : Nat}
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox ontology definitions) : Prop :=
  match outcome with | .frontier .. => False | _ => True

theorem checked_native_abox_doubling_execution_decides_source
    {Individual : Type}
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (maxWidth : Nat)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
        variableCount abox target definitions))
    {outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox target definitions}
    (trace : CartesianFoldDoublingExecution _ runtime
      (NativeABoxProductionFrontier Individual conceptCount roleCount
        variableCount abox target definitions maxWidth)
      NativeABoxProductionConclusive 0 outcome) :
    outcome.SourceSemantics source := by
  have hconclusive := trace.conclusive
  cases outcome with
  | sat certificate root hontology hnonempty hseeded hcheck hapart
      hsingletons hnegative =>
      exact CheckedNativeABoxCardinalityOutcome.source_semantics_of_equivalent _
        equivalent (CheckedNativeABoxCardinalityOutcome.sat_semantics
          certificate root hontology hnonempty hseeded hcheck hapart
          hsingletons hnegative)
  | closed certificate tree hontology hinitial hcheck =>
      exact CheckedNativeABoxCardinalityOutcome.source_semantics_of_equivalent _
        equivalent (CheckedNativeABoxCardinalityOutcome.closed_semantics
          certificate tree hontology hinitial hcheck)
  | frontier => simp [NativeABoxProductionConclusive] at hconclusive

/-! ### Runtime-constructed source decisions

These theorems close the gap between a concrete nested runtime and the traced
publication theorems above. The caller supplies a checked classification of
each computed budget and a proof that one finite budget is conclusive; Lean
constructs every intervening fold-learning and doubling step itself. -/

theorem checked_regular_runtime_through_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedRegularRoundOutcome conceptCount roleCount variableCount target))
    (classify : ∀ budget,
      let fixed := (runtime budget).execute ∅
      PLift (RegularProductionConclusive fixed.1) ⊕
        PLift (RegularProductionFrontier conceptCount roleCount variableCount
          target budget fixed.1))
    (fuel : Nat)
    (terminal :
      let fixed := (runtime fuel).execute ∅
      RegularProductionConclusive fixed.1) :
    ∃ outcome : CheckedRegularRoundOutcome conceptCount roleCount variableCount
      target, outcome.SourceSemantics source := by
  let run := CartesianFoldDoublingExecution.executeThrough runtime
    (RegularProductionFrontier conceptCount roleCount variableCount target)
    RegularProductionConclusive classify 0 fuel (by
      rw [Nat.zero_add]
      exact terminal)
  exact ⟨run.1, checked_regular_doubling_execution_decides_source equivalent
    runtime run.2⟩

theorem checked_equality_runtime_through_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedEqualityDecisionOutcome conceptCount roleCount variableCount target))
    (classify : ∀ budget,
      let fixed := (runtime budget).execute ∅
      PLift (EqualityProductionConclusive fixed.1) ⊕
        PLift (EqualityProductionFrontier conceptCount roleCount variableCount
          target budget fixed.1))
    (fuel : Nat)
    (terminal :
      let fixed := (runtime fuel).execute ∅
      EqualityProductionConclusive fixed.1) :
    ∃ outcome : CheckedEqualityDecisionOutcome conceptCount roleCount
      variableCount target, outcome.SourceSemantics source := by
  let run := CartesianFoldDoublingExecution.executeThrough runtime
    (EqualityProductionFrontier conceptCount roleCount variableCount target)
    EqualityProductionConclusive classify 0 fuel (by
      rw [Nat.zero_add]
      exact terminal)
  exact ⟨run.1, checked_equality_doubling_execution_decides_source equivalent
    runtime run.2⟩

theorem checked_cardinality_runtime_through_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (maxWidth : Nat)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedCardinalityDecisionOutcome conceptCount roleCount variableCount
        target definitions))
    (classify : ∀ budget,
      let fixed := (runtime budget).execute ∅
      PLift (CardinalityProductionConclusive fixed.1) ⊕
        PLift (CardinalityProductionFrontier conceptCount roleCount variableCount
          target definitions maxWidth budget fixed.1))
    (fuel : Nat)
    (terminal :
      let fixed := (runtime fuel).execute ∅
      CardinalityProductionConclusive fixed.1) :
    ∃ outcome : CheckedCardinalityDecisionOutcome conceptCount roleCount
      variableCount target definitions, outcome.SourceSemantics source := by
  let run := CartesianFoldDoublingExecution.executeThrough runtime
    (CardinalityProductionFrontier conceptCount roleCount variableCount target
      definitions maxWidth) CardinalityProductionConclusive classify 0 fuel
      (by
        rw [Nat.zero_add]
        exact terminal)
  exact ⟨run.1, checked_cardinality_doubling_execution_decides_source
    equivalent maxWidth runtime run.2⟩

theorem checked_native_abox_runtime_through_decides_source
    {Individual : Type}
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (maxWidth : Nat)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
        variableCount abox target definitions))
    (classify : ∀ budget,
      let fixed := (runtime budget).execute ∅
      PLift (NativeABoxProductionConclusive fixed.1) ⊕
        PLift (NativeABoxProductionFrontier Individual conceptCount roleCount
          variableCount abox target definitions maxWidth budget fixed.1))
    (fuel : Nat)
    (terminal :
      let fixed := (runtime fuel).execute ∅
      NativeABoxProductionConclusive fixed.1) :
    ∃ outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox target definitions,
        outcome.SourceSemantics source := by
  let run := CartesianFoldDoublingExecution.executeThrough runtime
    (NativeABoxProductionFrontier Individual conceptCount roleCount variableCount
      abox target definitions maxWidth) NativeABoxProductionConclusive classify
      0 fuel (by
        rw [Nat.zero_add]
        exact terminal)
  exact ⟨run.1, checked_native_abox_doubling_execution_decides_source
    equivalent maxWidth runtime run.2⟩

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

/-! ## Current complete-assignment and expansion production route

The legacy route above records pair-set rejection.  Current KM rejects one
complete simultaneous fold assignment and retains its constituent pairs for
other candidates. After exact assignment exhaustion, a rerun must add a fresh
forbidden pair. This route is the end-to-end semantic interface for both finite
learning layers. -/

inductive CertifiedHTAssignmentProductionGlobalRoute :
    (semantics : Prop) → Type 2 where
  | regular
      {source target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      (equivalent : ModelEquivalent source target)
      (producer : ∀ budget, CartesianFoldExpansionRuntime
        (Fin (8 * 2 ^ budget))
        (CheckedRegularRoundOutcome conceptCount roleCount variableCount target))
      (scheduled : ∀ budget retry document hconcepts hroles hcheck,
        (producer budget).toGuardedFoldProducer.toFreshFoldProducer.run retry = .done
          (.frontier document hconcepts hroles hcheck) →
        document.checkScheduled budget = true) :
      CertifiedHTAssignmentProductionGlobalRoute (HasNonemptyModel source)
  | equality
      {source target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      (equivalent : ModelEquivalent source target)
      (producer : ∀ budget, CartesianFoldExpansionRuntime
        (Fin (8 * 2 ^ budget))
        (CheckedEqualityDecisionOutcome conceptCount roleCount variableCount target))
      (nodes : ∀ budget retry document hconcepts hroles hcheck,
        (producer budget).toGuardedFoldProducer.toFreshFoldProducer.run retry = .done
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
      (producer : ∀ budget, CartesianFoldExpansionRuntime
        (Fin (8 * 2 ^ budget))
        (CheckedCardinalityDecisionOutcome conceptCount roleCount variableCount
          target definitions))
      (nodes : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
        (producer budget).toGuardedFoldProducer.toFreshFoldProducer.run retry = .done
          (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.node_count = 8 * 2 ^ budget)
      (width : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
        (producer budget).toGuardedFoldProducer.toFreshFoldProducer.run retry = .done
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
      (producer : ∀ budget, CartesianFoldExpansionRuntime
        (Fin (8 * 2 ^ budget))
        (CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
          variableCount abox target definitions))
      (nodes : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
        (producer budget).toGuardedFoldProducer.toFreshFoldProducer.run retry = .done
          (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.node_count = 8 * 2 ^ budget)
      (width : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
        (producer budget).toGuardedFoldProducer.toFreshFoldProducer.run retry = .done
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
        checked_regular_scheduled_fresh_fold_producer_decides_source equivalent
          (fun budget =>
            (producer budget).toGuardedFoldProducer.toFreshFoldProducer)
          scheduled
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
        checked_equality_fresh_fold_producer_decides_source equivalent
          (fun budget =>
            (producer budget).toGuardedFoldProducer.toFreshFoldProducer)
          nodes
      cases outcome with
      | sat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | closed certificate tree hontology hnonempty hempty hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hcheck =>
          simp only [CheckedEqualityDecisionOutcome.SourceSemantics] at hsemantics
  | cardinality equivalent maxWidth producer nodes width =>
      obtain ⟨_, _, outcome, _, hsemantics⟩ :=
        checked_cardinality_fresh_fold_producer_decides_source equivalent
          maxWidth (fun budget =>
            (producer budget).toGuardedFoldProducer.toFreshFoldProducer)
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
        checked_native_abox_cardinality_fresh_fold_producer_decides_source
          equivalent maxWidth
          (fun budget =>
            (producer budget).toGuardedFoldProducer.toFreshFoldProducer)
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
#print axioms checked_regular_doubling_execution_decides_source
#print axioms checked_equality_doubling_execution_decides_source
#print axioms checked_cardinality_doubling_execution_decides_source
#print axioms checked_native_abox_doubling_execution_decides_source
#print axioms checked_regular_runtime_through_decides_source
#print axioms checked_equality_runtime_through_decides_source
#print axioms checked_cardinality_runtime_through_decides_source
#print axioms checked_native_abox_runtime_through_decides_source

end ContextCalculus.Hypertableau
