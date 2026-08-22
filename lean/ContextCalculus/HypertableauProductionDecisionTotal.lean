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

theorem regularProductionFrontier_of_address
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (address : Fin (8 * 2 ^ budget) →
      WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    RegularProductionFrontier conceptCount roleCount variableCount ontology
      budget (CheckedRegularRoundOutcome.frontier_of_address address hinjective) := by
  let document := WireAddressFrontier.ofAddress address
  refine ⟨document, rfl, rfl,
    document.checkScheduled_check budget
      (WireAddressFrontier.ofAddress_checkScheduled address hinjective rfl), ?_, ?_⟩
  · rfl
  · exact WireAddressFrontier.ofAddress_checkScheduled address hinjective rfl

def classifyRegularAddressFrontier
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (address : Fin (8 * 2 ^ budget) →
      WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    PLift (RegularProductionConclusive
      (CheckedRegularRoundOutcome.frontier_of_address
        (variableCount := variableCount) (ontology := ontology) address hinjective)) ⊕
    PLift (RegularProductionFrontier conceptCount roleCount variableCount
      ontology budget (CheckedRegularRoundOutcome.frontier_of_address
        (variableCount := variableCount) (ontology := ontology) address hinjective)) :=
  .inr ⟨regularProductionFrontier_of_address
    (variableCount := variableCount) (ontology := ontology) address hinjective⟩

inductive RegularBudgetOutcomeConstruction
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (budget : Nat)
    (outcome : CheckedRegularRoundOutcome conceptCount roleCount variableCount
      ontology) : Type where
  | conclusive (proof : RegularProductionConclusive outcome)
  | frontier
      (address : Fin (8 * 2 ^ budget) →
        WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount))
      (injective : Function.Injective address)
      (produced : outcome =
        CheckedRegularRoundOutcome.frontier_of_address address injective)

/-- Fixed-budget regular result whose construction evidence is inseparable
from the checked outcome.  Using this as the finite-learning runtime's result
type makes every accepted candidate preserve its certification provenance. -/
abbrev ConstructedRegularBudgetResult
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (budget : Nat) :=
  Σ outcome : CheckedRegularRoundOutcome conceptCount roleCount variableCount
      ontology,
    RegularBudgetOutcomeConstruction conceptCount roleCount variableCount
      ontology budget outcome

def RegularBudgetOutcomeConstruction.classify
    (construction : RegularBudgetOutcomeConstruction conceptCount roleCount
      variableCount ontology budget outcome) :
    PLift (RegularProductionConclusive outcome) ⊕
      PLift (RegularProductionFrontier conceptCount roleCount variableCount
        ontology budget outcome) :=
  match construction with
  | .conclusive proof => .inl ⟨proof⟩
  | .frontier address injective produced => by
      subst outcome
      exact classifyRegularAddressFrontier address injective

/-- Translate the witness-preserving result of exhaustive regular search into
the construction interface consumed by the global production route. -/
def ConstructedRegularRoundOutcome.toBudgetConstruction
    (constructed : ConstructedRegularRoundOutcome conceptCount roleCount
      variableCount ontology budget) :
    RegularBudgetOutcomeConstruction conceptCount roleCount variableCount
      ontology budget constructed.outcome :=
  match constructed with
  | .conclusive _ proof => .conclusive proof
  | .frontier address injective => .frontier address injective rfl

/-- Every early result of the concrete exhaustive regular search carries the
exact typed construction evidence required by the global decision route.  The
other arm is a genuine blocked leaf and is intentionally left to the finite
fold-assignment settlement. -/
noncomputable def finiteProductionRoundBudgetConstructionSettlement
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (parent : Finset (GuardedFact (Fin (8 * 2 ^ budget)) (Fin conceptCount)
      (Fin roleCount)) → Fin (8 * 2 ^ budget) → Option (Fin (8 * 2 ^ budget)))
    (ancestors : Finset (GuardedFact (Fin (8 * 2 ^ budget)) (Fin conceptCount)
      (Fin roleCount)) → Fin (8 * 2 ^ budget) → List (Fin (8 * 2 ^ budget)))
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom)
    (root : Finset (GuardedFact (Fin (8 * 2 ^ budget)) (Fin conceptCount)
      (Fin roleCount)))
    (hrootEmpty : root = ∅)
    (frontierAddress : ∀
      (forbidden : Finset
        (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget)))
      (leaf : Finset (GuardedFact (Fin (8 * 2 ^ budget)) (Fin conceptCount)
        (Fin roleCount))),
      SearchDescends
        (runtimeNextBlockedFacts ontology
          (productionBlockedFacts parent ancestors forbidden)) root leaf →
      (stateOfGuardedFacts leaf).BlockedRuntimeFrontier ontology
        ((stateOfGuardedFacts leaf).productionBlocked (parent leaf)
          (ancestors leaf) forbidden) →
      ∃ address : Fin (8 * 2 ^ budget) →
          WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount),
        (stateOfGuardedFacts leaf).checkRootedAddressRefines address = true) :
    ∀ forbidden : Finset
        (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget)),
      (Σ outcome : CheckedRegularRoundOutcome conceptCount roleCount
          variableCount ontology,
        RegularBudgetOutcomeConstruction conceptCount roleCount variableCount
          ontology budget outcome) ⊕
        ProductionBlockedLeafAt (Fin (8 * 2 ^ budget)) (Fin conceptCount)
          (Fin roleCount) (Fin variableCount) ontology forbidden := by
  intro forbidden
  let settled := finiteProductionRoundConstructionSettlement ontology parent
    ancestors hheads root hrootEmpty frontierAddress forbidden
  exact match settled with
  | .inl constructed =>
      .inl ⟨constructed.outcome, constructed.toBudgetConstruction⟩
  | .inr blocked => .inr blocked

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

theorem equalityProductionFrontier_of_address
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (address : Fin (8 * 2 ^ budget) →
      WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    EqualityProductionFrontier conceptCount roleCount variableCount ontology
      budget (CheckedEqualityDecisionOutcome.frontier_of_address address hinjective) := by
  let document := WireAddressFrontier.ofAddress address
  refine ⟨document, rfl, rfl,
    document.checkScheduled_check budget
      (WireAddressFrontier.ofAddress_checkScheduled address hinjective rfl), ?_, ?_⟩
  · rfl
  · exact WireAddressFrontier.ofAddress_checkScheduled address hinjective rfl

def classifyEqualityAddressFrontier
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (address : Fin (8 * 2 ^ budget) →
      WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    PLift (EqualityProductionConclusive
      (CheckedEqualityDecisionOutcome.frontier_of_address
        (variableCount := variableCount) (ontology := ontology) address hinjective)) ⊕
    PLift (EqualityProductionFrontier conceptCount roleCount variableCount
      ontology budget (CheckedEqualityDecisionOutcome.frontier_of_address
        (variableCount := variableCount) (ontology := ontology) address hinjective)) :=
  .inr ⟨equalityProductionFrontier_of_address
    (variableCount := variableCount) (ontology := ontology) address hinjective⟩

inductive EqualityBudgetOutcomeConstruction
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (budget : Nat)
    (outcome : CheckedEqualityDecisionOutcome conceptCount roleCount
      variableCount ontology) : Type where
  | conclusive (proof : EqualityProductionConclusive outcome)
  | frontier
      (address : Fin (8 * 2 ^ budget) →
        WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount))
      (injective : Function.Injective address)
      (produced : outcome =
        CheckedEqualityDecisionOutcome.frontier_of_address address injective)

abbrev ConstructedEqualityBudgetResult
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (budget : Nat) :=
  Σ outcome : CheckedEqualityDecisionOutcome conceptCount roleCount
      variableCount ontology,
    EqualityBudgetOutcomeConstruction conceptCount roleCount variableCount
      ontology budget outcome

def EqualityBudgetOutcomeConstruction.classify
    (construction : EqualityBudgetOutcomeConstruction conceptCount roleCount
      variableCount ontology budget outcome) :
    PLift (EqualityProductionConclusive outcome) ⊕
      PLift (EqualityProductionFrontier conceptCount roleCount variableCount
        ontology budget outcome) :=
  match construction with
  | .conclusive proof => .inl ⟨proof⟩
  | .frontier address injective produced => by
      subst outcome
      exact classifyEqualityAddressFrontier address injective

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

theorem cardinalityProductionFrontier_of_address
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (address : Fin (8 * 2 ^ budget) → RootedRoleBlockedAddress (Fin 1)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitions.length maxWidth)
      (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    CardinalityProductionFrontier conceptCount roleCount variableCount ontology
      definitions maxWidth budget
      (CheckedCardinalityDecisionOutcome.frontier_of_address address hinjective) := by
  let document := WireCardinalityAddressFrontier.ofAddress address
  refine ⟨document, rfl, rfl, rfl,
    document.checkScheduled_check budget maxWidth
      (WireCardinalityAddressFrontier.ofAddress_checkScheduled
        address hinjective rfl), ?_, ?_⟩
  · rfl
  · exact WireCardinalityAddressFrontier.ofAddress_checkScheduled
      address hinjective rfl

def classifyCardinalityAddressFrontier
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (address : Fin (8 * 2 ^ budget) → RootedRoleBlockedAddress (Fin 1)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitions.length maxWidth)
      (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    PLift (CardinalityProductionConclusive
      (CheckedCardinalityDecisionOutcome.frontier_of_address
        (variableCount := variableCount) (ontology := ontology) address hinjective)) ⊕
    PLift (CardinalityProductionFrontier conceptCount roleCount variableCount
      ontology definitions maxWidth budget
      (CheckedCardinalityDecisionOutcome.frontier_of_address
        (variableCount := variableCount) (ontology := ontology) address hinjective)) :=
  .inr ⟨cardinalityProductionFrontier_of_address
    (variableCount := variableCount) (ontology := ontology) address hinjective⟩

inductive CardinalityBudgetOutcomeConstruction
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (maxWidth budget : Nat)
    (outcome : CheckedCardinalityDecisionOutcome conceptCount roleCount
      variableCount ontology definitions) : Type where
  | conclusive (proof : CardinalityProductionConclusive outcome)
  | frontier
      (address : Fin (8 * 2 ^ budget) → RootedRoleBlockedAddress (Fin 1)
        (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
          definitions.length maxWidth)
        (Fin conceptCount) (Fin roleCount))
      (injective : Function.Injective address)
      (produced : outcome =
        CheckedCardinalityDecisionOutcome.frontier_of_address address injective)

abbrev ConstructedCardinalityBudgetResult
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (maxWidth budget : Nat) :=
  Σ outcome : CheckedCardinalityDecisionOutcome conceptCount roleCount
      variableCount ontology definitions,
    CardinalityBudgetOutcomeConstruction conceptCount roleCount variableCount
      ontology definitions maxWidth budget outcome

def CardinalityBudgetOutcomeConstruction.classify
    (construction : CardinalityBudgetOutcomeConstruction conceptCount roleCount
      variableCount ontology definitions maxWidth budget outcome) :
    PLift (CardinalityProductionConclusive outcome) ⊕
      PLift (CardinalityProductionFrontier conceptCount roleCount variableCount
        ontology definitions maxWidth budget outcome) :=
  match construction with
  | .conclusive proof => .inl ⟨proof⟩
  | .frontier address injective produced => by
      subst outcome
      exact classifyCardinalityAddressFrontier address injective

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
    (rootCount maxWidth budget : Nat)
    (outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox ontology definitions) : Prop :=
  ∃ document hconcepts hroles hdefinitions hcheck,
    outcome = .frontier document hconcepts hroles hdefinitions hcheck ∧
      document.checkScheduled budget rootCount maxWidth = true

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

/-- The canonical multi-root address constructor supplies exactly the checked
frontier proposition consumed by the concrete doubling executor. -/
theorem nativeABoxProductionFrontier_of_address
    {Individual : Type}
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (address : Fin (8 * 2 ^ budget) → RootedRoleBlockedAddress (Fin rootCount)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitions.length maxWidth)
      (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    NativeABoxProductionFrontier Individual conceptCount roleCount variableCount
      abox ontology definitions rootCount maxWidth budget
      (CheckedNativeABoxCardinalityOutcome.frontier_of_address address hinjective) := by
  let document := WireRootedCardinalityAddressFrontier.ofAddress address
  refine ⟨document, rfl, rfl, rfl,
    document.checkScheduled_check budget rootCount maxWidth
      (WireRootedCardinalityAddressFrontier.ofAddress_checkScheduled
        address hinjective rfl), ?_, ?_⟩
  · rfl
  · exact WireRootedCardinalityAddressFrontier.ofAddress_checkScheduled
      address hinjective rfl

/-- Executable route classification for a concrete native-ABox address
frontier. This removes a caller-supplied classification proof for that arm. -/
def classifyNativeABoxAddressFrontier
    {Individual : Type}
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (address : Fin (8 * 2 ^ budget) → RootedRoleBlockedAddress (Fin rootCount)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitions.length maxWidth)
      (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    PLift (NativeABoxProductionConclusive
      (CheckedNativeABoxCardinalityOutcome.frontier_of_address
        (Individual := Individual) (variableCount := variableCount)
        (abox := abox) (ontology := ontology) address hinjective)) ⊕
    PLift (NativeABoxProductionFrontier Individual conceptCount roleCount
      variableCount abox ontology definitions rootCount maxWidth budget
      (CheckedNativeABoxCardinalityOutcome.frontier_of_address
        (Individual := Individual) (variableCount := variableCount)
        (abox := abox) (ontology := ontology) address hinjective)) :=
  .inr ⟨nativeABoxProductionFrontier_of_address
    (Individual := Individual) (variableCount := variableCount)
    (abox := abox) (ontology := ontology) address hinjective⟩

/-- Typed construction evidence for one computed native-ABox budget outcome.
The frontier arm stores the concrete address map from which the checked wire
outcome was constructed, rather than an independently supplied proposition. -/
inductive NativeABoxBudgetOutcomeConstruction
    (Individual : Type)
    (conceptCount roleCount variableCount : Nat)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (rootCount maxWidth budget : Nat)
    (outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox ontology definitions) : Type where
  | conclusive (proof : NativeABoxProductionConclusive outcome)
  | frontier
      (address : Fin (8 * 2 ^ budget) →
        RootedRoleBlockedAddress (Fin rootCount)
          (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
            definitions.length maxWidth)
          (Fin conceptCount) (Fin roleCount))
      (injective : Function.Injective address)
      (produced : outcome =
        CheckedNativeABoxCardinalityOutcome.frontier_of_address address injective)

abbrev ConstructedNativeABoxBudgetResult
    (Individual : Type)
    (conceptCount roleCount variableCount : Nat)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (rootCount maxWidth budget : Nat) :=
  Σ outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox ontology definitions,
    NativeABoxBudgetOutcomeConstruction Individual conceptCount roleCount
      variableCount abox ontology definitions rootCount maxWidth budget outcome

def NativeABoxBudgetOutcomeConstruction.classify
    (construction : NativeABoxBudgetOutcomeConstruction Individual conceptCount
      roleCount variableCount abox ontology definitions rootCount maxWidth budget
      outcome) :
    PLift (NativeABoxProductionConclusive outcome) ⊕
      PLift (NativeABoxProductionFrontier Individual conceptCount roleCount
        variableCount abox ontology definitions rootCount maxWidth budget outcome) :=
  match construction with
  | .conclusive proof => .inl ⟨proof⟩
  | .frontier address injective produced => by
      subst outcome
      exact classifyNativeABoxAddressFrontier address injective

theorem checked_native_abox_doubling_execution_decides_source
    {Individual : Type}
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (rootCount : Nat)
    (maxWidth : Nat)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
        variableCount abox target definitions))
    {outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox target definitions}
    (trace : CartesianFoldDoublingExecution _ runtime
      (NativeABoxProductionFrontier Individual conceptCount roleCount
        variableCount abox target definitions rootCount maxWidth)
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

/-- Checked address-frontier impossibility supplies a conclusive budget for
the concrete regular runtime. No retry index or terminal trace is selected by
the caller. -/
theorem checked_regular_runtime_eventually_conclusive
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedRegularRoundOutcome conceptCount roleCount variableCount target))
    (classify : ∀ budget,
      let fixed := (runtime budget).execute ∅
      PLift (RegularProductionConclusive fixed.1) ⊕
        PLift (RegularProductionFrontier conceptCount roleCount variableCount
          target budget fixed.1)) :
    ∃ budget,
      let fixed := (runtime budget).execute ∅
      RegularProductionConclusive fixed.1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hfrontier : ∀ budget,
      RegularProductionFrontier conceptCount roleCount variableCount target
        budget ((runtime budget).execute ∅).1 := by
    intro budget
    rcases classify budget with hconclusive | hfrontier
    · exact False.elim (hnone budget hconclusive.down)
    · exact hfrontier.down
  choose document hconcepts hroles hcheck heq hscheduled using hfrontier
  obtain ⟨budget, hrejected⟩ :=
    mode6_doubling_eventually_rejects_checked_frontier document conceptCount
      roleCount
      (fun budget => (document budget).checkScheduled_node_count budget
        (hscheduled budget)) hconcepts hroles
  exact hrejected ((document budget).checkScheduled_check budget
    (hscheduled budget))

/-- The concrete regular production runtime decides source satisfiability.
Both finite learning loops, frontier doubling, and the terminal budget are
constructed or derived in Lean. -/
theorem checked_regular_runtime_decides_source
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
          target budget fixed.1)) :
    ∃ outcome : CheckedRegularRoundOutcome conceptCount roleCount variableCount
      target, outcome.SourceSemantics source := by
  obtain ⟨budget, hterminal⟩ :=
    checked_regular_runtime_eventually_conclusive runtime classify
  exact checked_regular_runtime_through_decides_source equivalent runtime
    classify budget hterminal

theorem checked_regular_runtime_decides_source_of_construction
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedRegularRoundOutcome conceptCount roleCount variableCount target))
    (construct : ∀ budget,
      let fixed := (runtime budget).execute ∅
      RegularBudgetOutcomeConstruction conceptCount roleCount variableCount
        target budget fixed.1) :
    ∃ outcome : CheckedRegularRoundOutcome conceptCount roleCount variableCount
      target, outcome.SourceSemantics source := by
  apply checked_regular_runtime_decides_source equivalent runtime
  intro budget
  exact (construct budget).classify

/-- A regular runtime whose result carries its own construction evidence
decides the source ontology.  No independent outcome-classification function
appears at this boundary: the finite inner and outer learning loops can return
only a result containing the required proof. -/
theorem checked_constructed_regular_runtime_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (ConstructedRegularBudgetResult conceptCount roleCount variableCount
        target budget)) :
    ∃ outcome : CheckedRegularRoundOutcome conceptCount roleCount variableCount
      target, outcome.SourceSemantics source := by
  classical
  by_cases hterminal : ∃ budget,
      RegularProductionConclusive ((runtime budget).execute ∅).1.1
  · obtain ⟨budget, hconclusive⟩ := hterminal
    let result := ((runtime budget).execute ∅).1
    have hconclusive' : RegularProductionConclusive result.1 := by
      simpa [result] using hconclusive
    have hsemantics : result.1.Semantics := by
      cases hresult : result.1 with
      | regularSat certificate hontology hnonempty hcheck =>
          exact CheckedRegularRoundOutcome.regularSat_semantics certificate
            hontology hnonempty hcheck
      | finiteSat certificate hontology hnonempty hcheck =>
          exact CheckedRegularRoundOutcome.finiteSat_semantics certificate
            hontology hnonempty hcheck
      | finiteUnsat certificate tree hontology hnonempty hempty hcheck =>
          exact CheckedRegularRoundOutcome.finiteUnsat_semantics certificate tree
            hontology hnonempty hempty hcheck
      | frontier document hconcepts hroles hcheck =>
          simp [RegularProductionConclusive, hresult] at hconclusive'
    exact ⟨result.1,
      CheckedRegularRoundOutcome.source_semantics_of_equivalent result.1
        equivalent hsemantics⟩
  · push Not at hterminal
    have hfrontier : ∀ budget,
        RegularProductionFrontier conceptCount roleCount variableCount target
          budget ((runtime budget).execute ∅).1.1 := by
      intro budget
      rcases ((runtime budget).execute ∅).1.2.classify with
        hconclusive | hfrontier
      · exact False.elim (hterminal budget hconclusive.down)
      · exact hfrontier.down
    choose document hconcepts hroles hcheck heq hscheduled using hfrontier
    obtain ⟨budget, hrejected⟩ :=
      mode6_doubling_eventually_rejects_checked_frontier document conceptCount
        roleCount
        (fun budget => (document budget).checkScheduled_node_count budget
          (hscheduled budget)) hconcepts hroles
    exact False.elim
      (hrejected ((document budget).checkScheduled_check budget
        (hscheduled budget)))

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

theorem checked_equality_runtime_eventually_conclusive
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedEqualityDecisionOutcome conceptCount roleCount variableCount target))
    (classify : ∀ budget,
      let fixed := (runtime budget).execute ∅
      PLift (EqualityProductionConclusive fixed.1) ⊕
        PLift (EqualityProductionFrontier conceptCount roleCount variableCount
          target budget fixed.1)) :
    ∃ budget,
      let fixed := (runtime budget).execute ∅
      EqualityProductionConclusive fixed.1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hfrontier : ∀ budget,
      EqualityProductionFrontier conceptCount roleCount variableCount target
        budget ((runtime budget).execute ∅).1 := by
    intro budget
    rcases classify budget with hconclusive | hfrontier
    · exact False.elim (hnone budget hconclusive.down)
    · exact hfrontier.down
  choose document hconcepts hroles hcheck heq hscheduled using hfrontier
  obtain ⟨budget, hrejected⟩ :=
    mode6_doubling_eventually_rejects_checked_frontier document conceptCount
      roleCount
      (fun budget => (document budget).checkScheduled_node_count budget
        (hscheduled budget)) hconcepts hroles
  exact hrejected ((document budget).checkScheduled_check budget
    (hscheduled budget))

theorem checked_equality_runtime_decides_source
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
          target budget fixed.1)) :
    ∃ outcome : CheckedEqualityDecisionOutcome conceptCount roleCount
      variableCount target, outcome.SourceSemantics source := by
  obtain ⟨budget, hterminal⟩ :=
    checked_equality_runtime_eventually_conclusive runtime classify
  exact checked_equality_runtime_through_decides_source equivalent runtime
    classify budget hterminal

theorem checked_equality_runtime_decides_source_of_construction
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedEqualityDecisionOutcome conceptCount roleCount variableCount target))
    (construct : ∀ budget,
      let fixed := (runtime budget).execute ∅
      EqualityBudgetOutcomeConstruction conceptCount roleCount variableCount
        target budget fixed.1) :
    ∃ outcome : CheckedEqualityDecisionOutcome conceptCount roleCount
      variableCount target, outcome.SourceSemantics source := by
  apply checked_equality_runtime_decides_source equivalent runtime
  intro budget
  exact (construct budget).classify

theorem checked_constructed_equality_runtime_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (ConstructedEqualityBudgetResult conceptCount roleCount variableCount
        target budget)) :
    ∃ outcome : CheckedEqualityDecisionOutcome conceptCount roleCount
      variableCount target, outcome.SourceSemantics source := by
  classical
  by_cases hterminal : ∃ budget,
      EqualityProductionConclusive ((runtime budget).execute ∅).1.1
  · obtain ⟨budget, hconclusive⟩ := hterminal
    let result := ((runtime budget).execute ∅).1
    have hconclusive' : EqualityProductionConclusive result.1 := by
      simpa [result] using hconclusive
    have hsemantics : result.1.Semantics := by
      cases hresult : result.1 with
      | sat certificate hontology hnonempty hcheck =>
          exact CheckedEqualityDecisionOutcome.sat_semantics certificate
            hontology hnonempty hcheck
      | closed certificate tree hontology hnonempty hempty hcheck =>
          exact CheckedEqualityDecisionOutcome.closed_semantics certificate tree
            hontology hnonempty hempty hcheck
      | frontier document hconcepts hroles hcheck =>
          simp [EqualityProductionConclusive, hresult] at hconclusive'
    exact ⟨result.1,
      CheckedEqualityDecisionOutcome.source_semantics_of_equivalent result.1
        equivalent hsemantics⟩
  · push Not at hterminal
    have hfrontier : ∀ budget,
        EqualityProductionFrontier conceptCount roleCount variableCount target
          budget ((runtime budget).execute ∅).1.1 := by
      intro budget
      rcases ((runtime budget).execute ∅).1.2.classify with
        hconclusive | hfrontier
      · exact False.elim (hterminal budget hconclusive.down)
      · exact hfrontier.down
    choose document hconcepts hroles hcheck heq hscheduled using hfrontier
    obtain ⟨budget, hrejected⟩ :=
      mode6_doubling_eventually_rejects_checked_frontier document conceptCount
        roleCount
        (fun budget => (document budget).checkScheduled_node_count budget
          (hscheduled budget)) hconcepts hroles
    exact False.elim
      (hrejected ((document budget).checkScheduled_check budget
        (hscheduled budget)))

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

theorem checked_cardinality_runtime_eventually_conclusive
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (maxWidth : Nat)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedCardinalityDecisionOutcome conceptCount roleCount variableCount
        target definitions))
    (classify : ∀ budget,
      let fixed := (runtime budget).execute ∅
      PLift (CardinalityProductionConclusive fixed.1) ⊕
        PLift (CardinalityProductionFrontier conceptCount roleCount variableCount
          target definitions maxWidth budget fixed.1)) :
    ∃ budget,
      let fixed := (runtime budget).execute ∅
      CardinalityProductionConclusive fixed.1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hfrontier : ∀ budget,
      CardinalityProductionFrontier conceptCount roleCount variableCount target
        definitions maxWidth budget ((runtime budget).execute ∅).1 := by
    intro budget
    rcases classify budget with hconclusive | hfrontier
    · exact False.elim (hnone budget hconclusive.down)
    · exact hfrontier.down
  choose document hconcepts hroles hdefinitions hcheck heq hscheduled using
    hfrontier
  obtain ⟨budget, hrejected⟩ :=
    cardinality_doubling_eventually_rejects_checked_frontier document
      conceptCount roleCount definitions.length maxWidth
      (fun budget => (document budget).checkScheduled_node_count budget maxWidth
        (hscheduled budget)) hconcepts hroles hdefinitions
      (fun budget => (document budget).checkScheduled_max_width budget maxWidth
        (hscheduled budget))
  exact hrejected ((document budget).checkScheduled_check budget maxWidth
    (hscheduled budget))

theorem checked_cardinality_runtime_decides_source
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
          target definitions maxWidth budget fixed.1)) :
    ∃ outcome : CheckedCardinalityDecisionOutcome conceptCount roleCount
      variableCount target definitions, outcome.SourceSemantics source := by
  obtain ⟨budget, hterminal⟩ :=
    checked_cardinality_runtime_eventually_conclusive maxWidth runtime classify
  exact checked_cardinality_runtime_through_decides_source equivalent maxWidth
    runtime classify budget hterminal

theorem checked_cardinality_runtime_decides_source_of_construction
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
    (construct : ∀ budget,
      let fixed := (runtime budget).execute ∅
      CardinalityBudgetOutcomeConstruction conceptCount roleCount variableCount
        target definitions maxWidth budget fixed.1) :
    ∃ outcome : CheckedCardinalityDecisionOutcome conceptCount roleCount
      variableCount target definitions, outcome.SourceSemantics source := by
  apply checked_cardinality_runtime_decides_source equivalent maxWidth runtime
  intro budget
  exact (construct budget).classify

theorem checked_constructed_cardinality_runtime_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (maxWidth : Nat)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (ConstructedCardinalityBudgetResult conceptCount roleCount variableCount
        target definitions maxWidth budget)) :
    ∃ outcome : CheckedCardinalityDecisionOutcome conceptCount roleCount
      variableCount target definitions, outcome.SourceSemantics source := by
  classical
  by_cases hterminal : ∃ budget,
      CardinalityProductionConclusive ((runtime budget).execute ∅).1.1
  · obtain ⟨budget, hconclusive⟩ := hterminal
    let result := ((runtime budget).execute ∅).1
    have hconclusive' : CardinalityProductionConclusive result.1 := by
      simpa [result] using hconclusive
    have hsemantics : result.1.Semantics := by
      cases hresult : result.1 with
      | sat certificate hontology hnonempty hcheck =>
          exact CheckedCardinalityDecisionOutcome.sat_semantics certificate
            hontology hnonempty hcheck
      | closed certificate tree hontology hnonempty hempty hapart hcheck =>
          exact CheckedCardinalityDecisionOutcome.closed_semantics certificate
            tree hontology hnonempty hempty hapart hcheck
      | frontier document hconcepts hroles hdefinitions hcheck =>
          simp [CardinalityProductionConclusive, hresult] at hconclusive'
    exact ⟨result.1,
      CheckedCardinalityDecisionOutcome.source_semantics_of_equivalent result.1
        equivalent hsemantics⟩
  · push Not at hterminal
    have hfrontier : ∀ budget,
        CardinalityProductionFrontier conceptCount roleCount variableCount target
          definitions maxWidth budget ((runtime budget).execute ∅).1.1 := by
      intro budget
      rcases ((runtime budget).execute ∅).1.2.classify with
        hconclusive | hfrontier
      · exact False.elim (hterminal budget hconclusive.down)
      · exact hfrontier.down
    choose document hconcepts hroles hdefinitions hcheck heq hscheduled using
      hfrontier
    obtain ⟨budget, hrejected⟩ :=
      cardinality_doubling_eventually_rejects_checked_frontier document
        conceptCount roleCount definitions.length maxWidth
        (fun budget => (document budget).checkScheduled_node_count budget maxWidth
          (hscheduled budget)) hconcepts hroles hdefinitions
        (fun budget => (document budget).checkScheduled_max_width budget maxWidth
          (hscheduled budget))
    exact False.elim
      (hrejected ((document budget).checkScheduled_check budget maxWidth
        (hscheduled budget)))

theorem checked_native_abox_runtime_through_decides_source
    {Individual : Type}
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (rootCount : Nat)
    (maxWidth : Nat)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
        variableCount abox target definitions))
    (classify : ∀ budget,
      let fixed := (runtime budget).execute ∅
      PLift (NativeABoxProductionConclusive fixed.1) ⊕
        PLift (NativeABoxProductionFrontier Individual conceptCount roleCount
          variableCount abox target definitions rootCount maxWidth budget fixed.1))
    (fuel : Nat)
    (terminal :
      let fixed := (runtime fuel).execute ∅
      NativeABoxProductionConclusive fixed.1) :
    ∃ outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox target definitions,
        outcome.SourceSemantics source := by
  let run := CartesianFoldDoublingExecution.executeThrough runtime
    (NativeABoxProductionFrontier Individual conceptCount roleCount variableCount
      abox target definitions rootCount maxWidth) NativeABoxProductionConclusive classify
      0 fuel (by
        rw [Nat.zero_add]
        exact terminal)
  exact ⟨run.1, checked_native_abox_doubling_execution_decides_source
    equivalent rootCount maxWidth runtime run.2⟩

theorem checked_native_abox_runtime_eventually_conclusive
    {Individual : Type}
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (rootCount : Nat)
    (maxWidth : Nat)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
        variableCount abox target definitions))
    (classify : ∀ budget,
      let fixed := (runtime budget).execute ∅
      PLift (NativeABoxProductionConclusive fixed.1) ⊕
        PLift (NativeABoxProductionFrontier Individual conceptCount roleCount
          variableCount abox target definitions rootCount maxWidth budget fixed.1)) :
    ∃ budget,
      let fixed := (runtime budget).execute ∅
      NativeABoxProductionConclusive fixed.1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hfrontier : ∀ budget,
      NativeABoxProductionFrontier Individual conceptCount roleCount variableCount
        abox target definitions rootCount maxWidth budget
          ((runtime budget).execute ∅).1 := by
    intro budget
    rcases classify budget with hconclusive | hfrontier
    · exact False.elim (hnone budget hconclusive.down)
    · exact hfrontier.down
  choose document hconcepts hroles hdefinitions hcheck heq hscheduled using
    hfrontier
  obtain ⟨budget, hrejected⟩ :=
    rooted_cardinality_doubling_eventually_rejects_checked_frontier document
      rootCount conceptCount roleCount definitions.length maxWidth
      (fun budget => (document budget).checkScheduled_node_count budget rootCount
        maxWidth (hscheduled budget))
      (fun budget => (document budget).checkScheduled_root_count budget rootCount
        maxWidth (hscheduled budget))
      hconcepts hroles hdefinitions
      (fun budget => (document budget).checkScheduled_max_width budget rootCount maxWidth
        (hscheduled budget))
  exact hrejected ((document budget).checkScheduled_check budget rootCount maxWidth
    (hscheduled budget))

theorem checked_native_abox_runtime_decides_source
    {Individual : Type}
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (rootCount : Nat)
    (maxWidth : Nat)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
        variableCount abox target definitions))
    (classify : ∀ budget,
      let fixed := (runtime budget).execute ∅
      PLift (NativeABoxProductionConclusive fixed.1) ⊕
        PLift (NativeABoxProductionFrontier Individual conceptCount roleCount
          variableCount abox target definitions rootCount maxWidth budget fixed.1)) :
    ∃ outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox target definitions,
        outcome.SourceSemantics source := by
  obtain ⟨budget, hterminal⟩ :=
    checked_native_abox_runtime_eventually_conclusive rootCount maxWidth runtime classify
  exact checked_native_abox_runtime_through_decides_source equivalent rootCount
    maxWidth runtime classify budget hterminal

/-- Native-ABox runtime publication from typed outcome construction. The
caller supplies concrete construction evidence for each computed result;
Lean derives the conclusive/frontier classifier used by doubling totality. -/
theorem checked_native_abox_runtime_decides_source_of_construction
    {Individual : Type}
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (rootCount maxWidth : Nat)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
        variableCount abox target definitions))
    (construct : ∀ budget,
      let fixed := (runtime budget).execute ∅
      NativeABoxBudgetOutcomeConstruction Individual conceptCount roleCount
        variableCount abox target definitions rootCount maxWidth budget fixed.1) :
    ∃ outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox target definitions,
        outcome.SourceSemantics source := by
  apply checked_native_abox_runtime_decides_source equivalent rootCount maxWidth
    runtime
  intro budget
  exact (construct budget).classify

theorem checked_constructed_native_abox_runtime_decides_source
    {Individual : Type}
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (rootCount maxWidth : Nat)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget))
      (ConstructedNativeABoxBudgetResult Individual conceptCount roleCount
        variableCount abox target definitions rootCount maxWidth budget)) :
    ∃ outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox target definitions,
        outcome.SourceSemantics source := by
  classical
  by_cases hterminal : ∃ budget,
      NativeABoxProductionConclusive ((runtime budget).execute ∅).1.1
  · obtain ⟨budget, hconclusive⟩ := hterminal
    let result := ((runtime budget).execute ∅).1
    have hconclusive' : NativeABoxProductionConclusive result.1 := by
      simpa [result] using hconclusive
    have hsemantics : result.1.Semantics := by
      cases hresult : result.1 with
      | sat certificate root hontology hnonempty hseeded hcheck hapart
          hsingletons hnegative =>
          exact CheckedNativeABoxCardinalityOutcome.sat_semantics certificate
            root hontology hnonempty hseeded hcheck hapart hsingletons hnegative
      | closed certificate tree hontology hinitial hcheck =>
          exact CheckedNativeABoxCardinalityOutcome.closed_semantics certificate
            tree hontology hinitial hcheck
      | frontier document hconcepts hroles hdefinitions hcheck =>
          simp [NativeABoxProductionConclusive, hresult] at hconclusive'
    exact ⟨result.1,
      CheckedNativeABoxCardinalityOutcome.source_semantics_of_equivalent result.1
        equivalent hsemantics⟩
  · push Not at hterminal
    have hfrontier : ∀ budget,
        NativeABoxProductionFrontier Individual conceptCount roleCount
          variableCount abox target definitions rootCount maxWidth budget
          ((runtime budget).execute ∅).1.1 := by
      intro budget
      rcases ((runtime budget).execute ∅).1.2.classify with
        hconclusive | hfrontier
      · exact False.elim (hterminal budget hconclusive.down)
      · exact hfrontier.down
    choose document hconcepts hroles hdefinitions hcheck heq hscheduled using
      hfrontier
    obtain ⟨budget, hrejected⟩ :=
      rooted_cardinality_doubling_eventually_rejects_checked_frontier document
        rootCount conceptCount roleCount definitions.length maxWidth
        (fun budget => (document budget).checkScheduled_node_count budget
          rootCount maxWidth (hscheduled budget))
        (fun budget => (document budget).checkScheduled_root_count budget
          rootCount maxWidth (hscheduled budget))
        hconcepts hroles hdefinitions
        (fun budget => (document budget).checkScheduled_max_width budget
          rootCount maxWidth (hscheduled budget))
    exact False.elim
      (hrejected ((document budget).checkScheduled_check budget rootCount
        maxWidth (hscheduled budget)))

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
      (rootCount : Nat)
      (maxWidth : Nat)
      (producer : ∀ budget,
        CheckedNativeABoxCardinalityControlProducer Individual conceptCount
          roleCount variableCount abox target definitions budget rootCount maxWidth) :
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
  | nativeABox equivalent rootCount maxWidth producer =>
      obtain ⟨_, _, outcome, _, hsemantics⟩ :=
        checked_native_abox_cardinality_control_producer_decides_source
          equivalent rootCount maxWidth producer
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
        (ConstructedRegularBudgetResult conceptCount roleCount variableCount
          target budget)) :
      CertifiedHTAssignmentProductionGlobalRoute (HasNonemptyModel source)
  | equality
      {source target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      (equivalent : ModelEquivalent source target)
      (producer : ∀ budget, CartesianFoldExpansionRuntime
        (Fin (8 * 2 ^ budget))
        (ConstructedEqualityBudgetResult conceptCount roleCount variableCount
          target budget)) :
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
        (ConstructedCardinalityBudgetResult conceptCount roleCount variableCount
          target definitions maxWidth budget)) :
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
      (rootCount : Nat)
      (maxWidth : Nat)
      (producer : ∀ budget, CartesianFoldExpansionRuntime
        (Fin (8 * 2 ^ budget))
        (ConstructedNativeABoxBudgetResult Individual conceptCount roleCount
          variableCount abox target definitions rootCount maxWidth budget)) :
      CertifiedHTAssignmentProductionGlobalRoute
        (abox.SatisfiableWithCardinality source definitions)

theorem CertifiedHTAssignmentProductionGlobalRoute.decides
    {semantics : Prop}
    (route : CertifiedHTAssignmentProductionGlobalRoute semantics) :
    Nonempty (CertifiedHTGlobalVerdict semantics) := by
  cases route with
  | regular equivalent producer =>
      obtain ⟨outcome, hsemantics⟩ :=
        checked_constructed_regular_runtime_decides_source equivalent producer
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
      obtain ⟨outcome, hsemantics⟩ :=
        checked_constructed_equality_runtime_decides_source equivalent producer
      cases outcome with
      | sat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | closed certificate tree hontology hnonempty hempty hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hcheck =>
          simp only [CheckedEqualityDecisionOutcome.SourceSemantics] at hsemantics
  | cardinality equivalent maxWidth producer =>
      obtain ⟨outcome, hsemantics⟩ :=
        checked_constructed_cardinality_runtime_decides_source equivalent
          maxWidth producer
      cases outcome with
      | sat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | closed certificate tree hontology hnonempty hempty hapart hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hdefinitions hcheck =>
          simp only [CheckedCardinalityDecisionOutcome.SourceSemantics] at hsemantics
  | nativeABox equivalent rootCount maxWidth producer =>
      obtain ⟨outcome, hsemantics⟩ :=
        checked_constructed_native_abox_runtime_decides_source equivalent
          rootCount maxWidth producer
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
#print axioms nativeABoxProductionFrontier_of_address
#print axioms classifyNativeABoxAddressFrontier
#print axioms checked_regular_runtime_through_decides_source
#print axioms checked_equality_runtime_through_decides_source
#print axioms checked_cardinality_runtime_through_decides_source
#print axioms checked_native_abox_runtime_through_decides_source
#print axioms checked_regular_runtime_eventually_conclusive
#print axioms checked_regular_runtime_decides_source
#print axioms RegularBudgetOutcomeConstruction.classify
#print axioms ConstructedRegularRoundOutcome.toBudgetConstruction
#print axioms finiteProductionRoundBudgetConstructionSettlement
#print axioms checked_regular_runtime_decides_source_of_construction
#print axioms checked_constructed_regular_runtime_decides_source
#print axioms checked_equality_runtime_eventually_conclusive
#print axioms checked_equality_runtime_decides_source
#print axioms EqualityBudgetOutcomeConstruction.classify
#print axioms checked_equality_runtime_decides_source_of_construction
#print axioms checked_constructed_equality_runtime_decides_source
#print axioms checked_cardinality_runtime_eventually_conclusive
#print axioms checked_cardinality_runtime_decides_source
#print axioms CardinalityBudgetOutcomeConstruction.classify
#print axioms checked_cardinality_runtime_decides_source_of_construction
#print axioms checked_constructed_cardinality_runtime_decides_source
#print axioms checked_native_abox_runtime_eventually_conclusive
#print axioms checked_native_abox_runtime_decides_source
#print axioms NativeABoxBudgetOutcomeConstruction.classify
#print axioms checked_native_abox_runtime_decides_source_of_construction
#print axioms checked_constructed_native_abox_runtime_decides_source

end ContextCalculus.Hypertableau
