import ContextCalculus.HypertableauDecisionTotal
import ContextCalculus.HypertableauNativeABoxSearch
import ContextCalculus.HypertableauExpansionProduction
import ContextCalculus.HypertableauEqualityBlockedSearch
import ContextCalculus.HypertableauEqualityProductionBlockingWire
import ContextCalculus.HypertableauCardinalityProductionSearch
import ContextCalculus.HypertableauCardinalityProductionWire
import ContextCalculus.HypertableauCardinalityClosedCompleteness

/-!
# Total production hypertableau global decision

This module puts every global decision family selected by
`Ht.lean_global_decision_certificate_json` behind one semantic interface. The
regular, equality, cardinality, and native-ABox searches use different checked
certificate types, but all four return either a proof of the exact source
problem or a proof of its negation. A frontier is never a verdict.
-/

namespace ContextCalculus.Hypertableau

/-- A checker-accepted equality-only assignment from the production wire is
exactly the checked fold model required by a finite equality terminal. -/
theorem DecodedEqProductionBlockingTable.hasCheckedEqFoldModel_of_assignment
    (decoded : DecodedEqProductionBlockingTable)
    (assignment : FoldAssignment (Fin decoded.nodeCount))
    (hmode : decoded.table.allBlockableSources = false)
    (hcheck : decoded.assignmentCandidateValidB assignment = true) :
    HasCheckedEqFoldModel (nodeCount := decoded.nodeCount)
      decoded.table.base.base.ontology := by
  let certificate := decoded.assignmentFoldCertificate assignment
  refine ⟨certificate, rfl, ?_⟩
  have heq := decoded.assignmentCandidateValidB_eq_foldCheck assignment hmode
  simpa [certificate] using heq ▸ hcheck

/-- Equality terminal evidence is tied to the exact terminal state, not merely
to another checked model of the same ontology. -/
structure CheckedEqualityTerminalCandidate
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (state : EqState (Fin nodeCount) (Fin conceptCount) (Fin roleCount)) where
  certificate : FiniteEqFoldCertificate nodeCount conceptCount roleCount
    variableCount
  state_eq : certificate.base.state = state
  ontology_eq : certificate.base.base.ontology = ontology
  check : certificate.check = true

def CheckedEqualityTerminalCandidate.hasCheckedFoldModel
    (candidate : CheckedEqualityTerminalCandidate nodeCount conceptCount
      roleCount variableCount ontology state) :
    HasCheckedEqFoldModel (nodeCount := nodeCount) ontology :=
  ⟨candidate.certificate, candidate.ontology_eq, candidate.check⟩

/-- Construct equality terminal evidence from the exact decoded production
state and one checker-accepted Cartesian assignment.  The fold certificate
reuses `decoded.table.base`, so its state and ontology provenance are
definitionally exact rather than supplied by the producer. -/
def DecodedEqProductionBlockingTable.checkedEqualityTerminalCandidate
    (decoded : DecodedEqProductionBlockingTable)
    (assignment : FoldAssignment (Fin decoded.nodeCount))
    (hmode : decoded.table.allBlockableSources = false)
    (hcheck : decoded.assignmentCandidateValidB assignment = true) :
    CheckedEqualityTerminalCandidate decoded.nodeCount decoded.conceptCount
      decoded.roleCount decoded.variableCount
      decoded.table.base.base.ontology decoded.table.base.state := by
  refine ⟨decoded.assignmentFoldCertificate assignment, rfl, rfl, ?_⟩
  have heq := decoded.assignmentCandidateValidB_eq_foldCheck assignment hmode
  simpa using heq ▸ hcheck

/-- Acceptance of the executable terminal wire constructs the exact typed
terminal candidate consumed by production search. -/
def WireEqProductionTerminal.checkedEqualityTerminalCandidate
    (wire : WireEqProductionTerminal)
    (decoded : DecodedEqProductionTerminal)
    (hdecode : wire.decode = .ok decoded)
    (hcheck : wire.check = .ok true) :
    CheckedEqualityTerminalCandidate decoded.table.nodeCount
      decoded.table.conceptCount decoded.table.roleCount
      decoded.table.variableCount decoded.table.table.base.base.ontology
      decoded.table.table.base.state :=
  let checked := wire.check_sound decoded hdecode hcheck
  decoded.table.checkedEqualityTerminalCandidate decoded.assignment checked.1
    checked.2.2.2

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

/-- A fold-free blocked terminal is not a producer obligation. Lean rebuilds
the exact finite state, applies the complete finite-SAT checker, and constructs
the conclusive production result directly. -/
noncomputable def ProductionBlockedLeafAt.regularFoldFreeResult
    (leaf : ProductionBlockedLeafAt (Fin (8 * 2 ^ budget))
      (Fin conceptCount) (Fin roleCount) (Fin variableCount) ontology
      forbidden)
    (hguarded : ∀ clause ∈ ontology, clause.GuardedBody)
    (hempty : leaf.unwitnessedSources = []) :
    ConstructedRegularBudgetResult conceptCount roleCount variableCount
      ontology budget := by
  letI := leaf.decision
  let certificate := FiniteSatCertificate.ofState ontology leaf.state
  have hempty' : leaf.state.productionUnwitnessedSources = [] := by
    simpa [ProductionBlockedLeafAt.unwitnessedSources] using hempty
  have hcheck : certificate.checkSat = true := by
    exact FiniteSatCertificate.checkSat_of_empty_production_terminal ontology
      leaf.state leaf.parent leaf.ancestors forbidden hguarded leaf.terminal
      hempty'
  let outcome : CheckedRegularRoundOutcome conceptCount roleCount variableCount
      ontology := .finiteSat certificate rfl (by positivity) hcheck
  exact ⟨outcome, .conclusive (by
    simp [outcome, RegularProductionConclusive])⟩

/-- Check one simultaneous blocker assignment as an ordinary finite model.
The blocked leaf and assignment determine the complete certificate; rejection
is explicit and cannot produce a semantic result. -/
noncomputable def ProductionBlockedLeafAt.checkedFiniteFoldCandidate
    (leaf : ProductionBlockedLeafAt (Fin (8 * 2 ^ budget))
      (Fin conceptCount) (Fin roleCount) (Fin variableCount) ontology
      forbidden)
    (assignment : FoldAssignment (Fin (8 * 2 ^ budget))) :
    Option (ConstructedRegularBudgetResult conceptCount roleCount variableCount
      ontology budget) := by
  letI := leaf.decision
  let certificate : FiniteFoldCertificate (8 * 2 ^ budget) conceptCount
      roleCount variableCount := {
    base := FiniteSatCertificate.ofState ontology leaf.state
    folds := assignment.toList
  }
  by_cases hcheck : certificate.check = true
  ·
    let outcome : CheckedRegularRoundOutcome conceptCount roleCount variableCount
        ontology := .finiteSat certificate.materialize rfl (by positivity)
          (by simpa [FiniteFoldCertificate.check] using hcheck)
    exact some ⟨outcome, .conclusive (by
      simp [outcome, RegularProductionConclusive])⟩
  · exact none

/-- The only admissible fallback after a finite fold rejects: a regular
unravelling certificate for the exact ontology that passes its executable
checker. -/
structure CheckedRegularFallbackCandidate
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount)) where
  certificate : FiniteRegularCertificate nodeCount conceptCount roleCount
    variableCount
  state_eq : certificate.state = state
  ontology_eq : certificate.ontology = ontology
  check : certificate.check = true

def CheckedRegularFallbackCandidate.ofDecoded
    (decoded : DecodedRegularCertificateAt conceptCount roleCount variableCount)
    (hnodes : decoded.nodeCount = 8 * 2 ^ budget)
    (state : State (Fin (8 * 2 ^ budget)) (Fin conceptCount) (Fin roleCount))
    (hstate : HEq decoded.certificate.state state)
    (hontology : decoded.certificate.ontology = ontology)
    (hcheck : decoded.certificate.check = true) :
    CheckedRegularFallbackCandidate (8 * 2 ^ budget) conceptCount roleCount
      variableCount ontology state := by
  cases decoded with
  | mk nodeCount positive certificate =>
      dsimp at hnodes
      subst nodeCount
      exact ⟨certificate, eq_of_heq hstate, hontology, hcheck⟩

/-- Decode and recheck an untrusted regular fallback at the exact finite-search
schedule. Vocabulary, node budget, ontology, and semantic checker acceptance
are all enforced before typed evidence is returned. -/
def CheckedRegularFallbackCandidate.decodeWire
    (wire : WireRegularCertificate)
    (conceptCount roleCount variableCount budget : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (state : State (Fin (8 * 2 ^ budget)) (Fin conceptCount) (Fin roleCount))
    (stateMatches : ∀ decoded : DecodedRegularCertificateAt conceptCount
      roleCount variableCount, decoded.nodeCount = 8 * 2 ^ budget →
      HEq decoded.certificate.state state) :
    Except String (CheckedRegularFallbackCandidate (8 * 2 ^ budget)
      conceptCount roleCount variableCount ontology state) := do
  let decoded ← wire.decodeAt conceptCount roleCount variableCount
  if hnodes : decoded.nodeCount = 8 * 2 ^ budget then
    if hontology : decoded.certificate.ontology = ontology then
      if hcheck : decoded.certificate.check = true then
        return .ofDecoded decoded hnodes state (stateMatches decoded hnodes)
          hontology hcheck
      else
        throw "regular fallback certificate failed its semantic checker"
    else
      throw "regular fallback certificate ontology differs from the search ontology"
  else
    throw "regular fallback certificate node count differs from the search budget"

def CheckedRegularFallbackCandidate.toBudgetResult
    (candidate : CheckedRegularFallbackCandidate (8 * 2 ^ budget)
      conceptCount roleCount variableCount ontology state) :
    ConstructedRegularBudgetResult conceptCount roleCount variableCount
      ontology budget :=
  let outcome : CheckedRegularRoundOutcome conceptCount roleCount variableCount
      ontology := .regularSat candidate.certificate candidate.ontology_eq
        (by positivity) candidate.check
  ⟨outcome, .conclusive (by
    simp [outcome, RegularProductionConclusive])⟩

/-- KM first tries the completely reconstructed finite fold. Only when that
checker rejects does it consult the regular-unravelling fallback producer. -/
noncomputable def ProductionBlockedLeafAt.checkedRegularCandidate
    (leaf : ProductionBlockedLeafAt (Fin (8 * 2 ^ budget))
      (Fin conceptCount) (Fin roleCount) (Fin variableCount) ontology
      forbidden)
    (regularFallback : Option (CheckedRegularFallbackCandidate
      (8 * 2 ^ budget) conceptCount roleCount variableCount ontology
      leaf.state))
    (assignment : FoldAssignment (Fin (8 * 2 ^ budget))) :
    Option (ConstructedRegularBudgetResult conceptCount roleCount variableCount
      ontology budget) :=
  match leaf.checkedFiniteFoldCandidate assignment with
  | some result => some result
  | none => regularFallback.map CheckedRegularFallbackCandidate.toBudgetResult

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

/-- Build KM's complete fixed-budget regular runtime from exhaustive finite
search while preserving construction evidence through both blocker-learning
layers.  The early-search settlement, every accepted simultaneous fold
assignment, and the fold-free terminal all return the same dependent result
type consumed by the certified global route. -/
noncomputable def CartesianFoldExpansionRuntime.ofConstructedRegularFiniteSearch
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (parent : Finset (GuardedFact (Fin (8 * 2 ^ budget)) (Fin conceptCount)
      (Fin roleCount)) → Fin (8 * 2 ^ budget) → Option (Fin (8 * 2 ^ budget)))
    (ancestors : Finset (GuardedFact (Fin (8 * 2 ^ budget)) (Fin conceptCount)
      (Fin roleCount)) → Fin (8 * 2 ^ budget) → List (Fin (8 * 2 ^ budget)))
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom)
    (hguarded : ∀ clause ∈ ontology, clause.GuardedBody)
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
        (stateOfGuardedFacts leaf).checkRootedAddressRefines address = true)
    (regularFallback : ∀ (forbidden : Finset
        (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget))),
      (leaf : ProductionBlockedLeafAt (Fin (8 * 2 ^ budget)) (Fin conceptCount)
          (Fin roleCount) (Fin variableCount) ontology forbidden) →
        Finset (FoldAssignment (Fin (8 * 2 ^ budget))) →
          FoldAssignment (Fin (8 * 2 ^ budget)) →
            Option (CheckedRegularFallbackCandidate (8 * 2 ^ budget)
              conceptCount roleCount variableCount ontology leaf.state)) :
    CartesianFoldExpansionRuntime (Fin (8 * 2 ^ budget))
      (ConstructedRegularBudgetResult conceptCount roleCount variableCount
        ontology budget) :=
  CartesianFoldExpansionRuntime.ofSettledProductionSearch ontology
    (finiteProductionRoundBudgetConstructionSettlement ontology parent ancestors
      hheads root hrootEmpty frontierAddress)
    (fun forbidden leaf rejected assignment =>
      leaf.checkedRegularCandidate
        (regularFallback forbidden leaf rejected assignment) assignment)
    (fun _forbidden leaf hempty =>
      ProductionBlockedLeafAt.regularFoldFreeResult leaf hguarded hempty)

/-- All data needed to construct KM's regular finite search at every doubling
budget. The global route derives its runtime from this family. -/
structure ConstructedRegularFiniteSearchFamily
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) where
  parent : ∀ budget,
    Finset (GuardedFact (Fin (8 * 2 ^ budget)) (Fin conceptCount)
      (Fin roleCount)) →
      Fin (8 * 2 ^ budget) → Option (Fin (8 * 2 ^ budget))
  ancestors : ∀ budget,
    Finset (GuardedFact (Fin (8 * 2 ^ budget)) (Fin conceptCount)
      (Fin roleCount)) →
      Fin (8 * 2 ^ budget) → List (Fin (8 * 2 ^ budget))
  branchable : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom
  guarded : ∀ clause ∈ ontology, clause.GuardedBody
  frontierAddress : ∀ budget
    (forbidden : Finset
      (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget)))
    (leaf : Finset (GuardedFact (Fin (8 * 2 ^ budget)) (Fin conceptCount)
      (Fin roleCount))),
    SearchDescends
      (runtimeNextBlockedFacts ontology
        (productionBlockedFacts (parent budget) (ancestors budget) forbidden))
      ∅ leaf →
    (stateOfGuardedFacts leaf).BlockedRuntimeFrontier ontology
      ((stateOfGuardedFacts leaf).productionBlocked (parent budget leaf)
        (ancestors budget leaf) forbidden) →
    ∃ address : Fin (8 * 2 ^ budget) →
        WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount),
      (stateOfGuardedFacts leaf).checkRootedAddressRefines address = true
  regularFallback : ∀ budget (forbidden : Finset
      (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget))),
    (leaf : ProductionBlockedLeafAt (Fin (8 * 2 ^ budget)) (Fin conceptCount)
        (Fin roleCount) (Fin variableCount) ontology forbidden) →
      Finset (FoldAssignment (Fin (8 * 2 ^ budget))) →
        FoldAssignment (Fin (8 * 2 ^ budget)) →
          Option (CheckedRegularFallbackCandidate (8 * 2 ^ budget)
            conceptCount roleCount variableCount ontology leaf.state)

noncomputable def ConstructedRegularFiniteSearchFamily.runtime
    (family : ConstructedRegularFiniteSearchFamily conceptCount roleCount
      variableCount ontology)
    (budget : Nat) :
    CartesianFoldExpansionRuntime (Fin (8 * 2 ^ budget))
      (ConstructedRegularBudgetResult conceptCount roleCount variableCount
        ontology budget) :=
  CartesianFoldExpansionRuntime.ofConstructedRegularFiniteSearch ontology
    (family.parent budget) (family.ancestors budget) family.branchable
    family.guarded ∅ rfl (family.frontierAddress budget)
    (family.regularFallback budget)

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

/-- Execute one complete equality-aware finite search and construct the exact
checked production result.  Semantic closure is reified as a checked canonical
refutation tree, a blocked terminal is accepted only through the independent
fold checker, and node exhaustion retains its injective address witness. -/
noncomputable def finiteEqualityRoundBudgetConstruction
    (root : FiniteEqCertificate (8 * 2 ^ budget) conceptCount roleCount
      variableCount)
    (hontology : root.base.ontology = ontology)
    (hempty : root.EmptyRoot)
    (parent : EqState (Fin (8 * 2 ^ budget)) (Fin conceptCount)
      (Fin roleCount) → Fin (8 * 2 ^ budget) → Option (Fin (8 * 2 ^ budget)))
    (ancestors : EqState (Fin (8 * 2 ^ budget)) (Fin conceptCount)
      (Fin roleCount) → Fin (8 * 2 ^ budget) → List (Fin (8 * 2 ^ budget)))
    (terminalFold : ∀ state,
      EqRuntimeTerminal ontology parent ancestors state →
        CheckedEqualityTerminalCandidate (8 * 2 ^ budget) conceptCount
          roleCount variableCount ontology state)
    (frontierAddress : ∀ leaf,
      SearchDescends (eqRuntimeNextClashFirst ontology parent ancestors)
        root.state leaf →
      EqRuntimeNodeFrontier ontology leaf (parent leaf) (ancestors leaf) →
      ∃ address : Fin (8 * 2 ^ budget) →
          WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount),
        Function.Injective address) :
    ConstructedEqualityBudgetResult conceptCount roleCount variableCount
      ontology budget := by
  classical
  exact Classical.choice (show Nonempty
      (ConstructedEqualityBudgetResult conceptCount roleCount variableCount
        ontology budget) from by
    rcases finite_eqRuntime_semantic_or_terminal ontology parent ancestors
        root.state with hrefutes | ⟨leaf, hdescends, hterminal⟩
    · let certificate := root.canonicalizeEqualityClosure
      obtain ⟨tree, htree⟩ := hrefutes.exists_checkClosed_tree certificate
        (by simpa [certificate] using hontology) rfl
        (by exact root.canonicalizeEqualityClosure_valid)
      have hempty' : certificate.EmptyRoot := by
        simpa [certificate, FiniteEqCertificate.EmptyRoot,
          FiniteEqCertificate.canonicalizeEqualityClosure] using hempty
      let outcome : CheckedEqualityDecisionOutcome conceptCount roleCount
          variableCount ontology :=
        .closed certificate tree (by simpa [certificate] using hontology)
          (by positivity) hempty' htree
      exact ⟨⟨outcome, .conclusive (by
        simp [outcome, EqualityProductionConclusive])⟩⟩
    · rcases hterminal with hblocked | hfrontier
      · obtain ⟨fold, hfoldOntology, hfoldCheck⟩ :=
          (terminalFold leaf hblocked).hasCheckedFoldModel
        let outcome : CheckedEqualityDecisionOutcome conceptCount roleCount
            variableCount ontology :=
          .sat fold.materialize (by simpa using hfoldOntology) (by positivity)
            hfoldCheck
        exact ⟨⟨outcome, .conclusive (by
          simp [outcome, EqualityProductionConclusive])⟩⟩
      · obtain ⟨address, hinjective⟩ :=
          frontierAddress leaf hdescends hfrontier
        exact ⟨⟨CheckedEqualityDecisionOutcome.frontier_of_address address
          hinjective, .frontier address hinjective rfl⟩⟩)

/-- Embed the exhaustive equality search at one node budget into the common
evidence-carrying production runtime. Equality search has already settled its
own finite branching and blocking, so no synthetic blocker-learning choices
are introduced here. -/
noncomputable def CartesianFoldExpansionRuntime.ofConstructedEqualityFiniteSearch
    (root : FiniteEqCertificate (8 * 2 ^ budget) conceptCount roleCount
      variableCount)
    (hontology : root.base.ontology = ontology)
    (hempty : root.EmptyRoot)
    (parent : EqState (Fin (8 * 2 ^ budget)) (Fin conceptCount)
      (Fin roleCount) → Fin (8 * 2 ^ budget) → Option (Fin (8 * 2 ^ budget)))
    (ancestors : EqState (Fin (8 * 2 ^ budget)) (Fin conceptCount)
      (Fin roleCount) → Fin (8 * 2 ^ budget) → List (Fin (8 * 2 ^ budget)))
    (terminalFold : ∀ state,
      EqRuntimeTerminal ontology parent ancestors state →
        CheckedEqualityTerminalCandidate (8 * 2 ^ budget) conceptCount
          roleCount variableCount ontology state)
    (frontierAddress : ∀ leaf,
      SearchDescends (eqRuntimeNextClashFirst ontology parent ancestors)
        root.state leaf →
      EqRuntimeNodeFrontier ontology leaf (parent leaf) (ancestors leaf) →
      ∃ address : Fin (8 * 2 ^ budget) →
          WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount),
        Function.Injective address) :
    CartesianFoldExpansionRuntime (Fin (8 * 2 ^ budget))
      (ConstructedEqualityBudgetResult conceptCount roleCount variableCount
        ontology budget) :=
  CartesianFoldExpansionRuntime.done
    (finiteEqualityRoundBudgetConstruction root hontology hempty parent
      ancestors terminalFold frontierAddress)

/-- All data needed to construct KM's equality-aware finite search at every
doubling budget. The global route derives its runtime from this family. -/
structure ConstructedEqualityFiniteSearchFamily
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) where
  root : ∀ budget, FiniteEqCertificate (8 * 2 ^ budget) conceptCount
    roleCount variableCount
  ontology_eq : ∀ budget, (root budget).base.ontology = ontology
  empty : ∀ budget, (root budget).EmptyRoot
  parent : ∀ budget,
    EqState (Fin (8 * 2 ^ budget)) (Fin conceptCount) (Fin roleCount) →
      Fin (8 * 2 ^ budget) → Option (Fin (8 * 2 ^ budget))
  ancestors : ∀ budget,
    EqState (Fin (8 * 2 ^ budget)) (Fin conceptCount) (Fin roleCount) →
      Fin (8 * 2 ^ budget) → List (Fin (8 * 2 ^ budget))
  terminalFold : ∀ budget state,
    EqRuntimeTerminal ontology (parent budget) (ancestors budget) state →
      CheckedEqualityTerminalCandidate (8 * 2 ^ budget) conceptCount
        roleCount variableCount ontology state
  frontierAddress : ∀ budget leaf,
    SearchDescends
      (eqRuntimeNextClashFirst ontology (parent budget) (ancestors budget))
      (root budget).state leaf →
    EqRuntimeNodeFrontier ontology leaf (parent budget leaf)
      (ancestors budget leaf) →
    ∃ address : Fin (8 * 2 ^ budget) →
        WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount),
      Function.Injective address

noncomputable def ConstructedEqualityFiniteSearchFamily.runtime
    (family : ConstructedEqualityFiniteSearchFamily conceptCount roleCount
      variableCount ontology)
    (budget : Nat) :
    CartesianFoldExpansionRuntime (Fin (8 * 2 ^ budget))
      (ConstructedEqualityBudgetResult conceptCount roleCount variableCount
        ontology budget) :=
  CartesianFoldExpansionRuntime.ofConstructedEqualityFiniteSearch
    (family.root budget) (family.ontology_eq budget) (family.empty budget)
    (family.parent budget) (family.ancestors budget)
    (family.terminalFold budget) (family.frontierAddress budget)

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

/-- Positive cardinality terminal evidence is tied to the exact reached leaf.
The model certificate cannot be substituted by an unrelated checked model of
the same ontology. -/
structure CheckedCardinalityTerminalCandidate
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (state : DistinctEqState (Fin nodeCount) (Fin conceptCount)
      (Fin roleCount)) where
  certificate : FiniteEqCertificate nodeCount conceptCount roleCount
    variableCount
  state_eq : certificate.state = state.base
  positive : 0 < nodeCount
  ontology_eq : certificate.base.ontology = ontology
  check : certificate.checkEqSatWithCardinality definitions = true

def CheckedCardinalityTerminalCandidate.hasCheckedModel
    (candidate : CheckedCardinalityTerminalCandidate nodeCount conceptCount
      roleCount variableCount ontology definitions state) :
    HasCheckedCardinalityModel (nodeCount := nodeCount) ontology definitions :=
  ⟨candidate.certificate, candidate.positive, candidate.ontology_eq,
    candidate.check⟩

/-- Build a cardinality terminal candidate from the exact runtime fields
decoded by the production wire.  The certificate and runtime configuration
share their state by construction. -/
def FiniteCardinalityRuntimeFields.checkedTerminalCandidate
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount
      variableCount definitions)
    (hfields : fields.check = true)
    (hpositive : 0 < nodeCount)
    (hcheck : fields.certificate.base.checkEqSatWithCardinality definitions =
      true) :
    CheckedCardinalityTerminalCandidate nodeCount conceptCount roleCount
      variableCount fields.certificate.base.base.ontology definitions
      (fields.toConfig hfields).state :=
  ⟨fields.certificate.base, rfl, hpositive, rfl, hcheck⟩

/-- Execute one fixed-budget cardinality production search and construct its
checked result.  Closure is serialized through the quotient-closed checker
completeness theorem. Every non-closed stop supplies either an independently
accepted finite cardinality model or the injective address map for the exact
scheduled frontier. -/
noncomputable def finiteCardinalityRoundBudgetConstruction
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (maxWidth : Nat)
    (rootCertificate : FiniteDistinctEqCertificate (8 * 2 ^ budget)
      conceptCount roleCount variableCount)
    (hontology : rootCertificate.base.base.ontology = ontology)
    (hempty : rootCertificate.base.EmptyRoot)
    (hapart : rootCertificate.apart = [])
    (root : CardinalityRuntimeConfig (Fin conceptCount) (Fin roleCount)
      definitions (8 * 2 ^ budget))
    (hrootState : root.state = rootCertificate.state)
    (parent : Fin (8 * 2 ^ budget) → Option (Fin (8 * 2 ^ budget)))
    (ancestors : Fin (8 * 2 ^ budget) → List (Fin (8 * 2 ^ budget)))
    (stopResult : ∀ leaf,
      CardinalityProductionDescends ontology definitions parent ancestors
        root leaf →
      (cardinalityControl ontology definitions leaf parent ancestors).IsStop →
      CheckedCardinalityTerminalCandidate (8 * 2 ^ budget) conceptCount
          roleCount variableCount ontology definitions leaf.state ⊕
        { address : Fin (8 * 2 ^ budget) →
            RootedRoleBlockedAddress (Fin 1)
              (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
                definitions.length maxWidth)
              (Fin conceptCount) (Fin roleCount) //
          Function.Injective address }) :
    ConstructedCardinalityBudgetResult conceptCount roleCount variableCount
      ontology definitions maxWidth budget := by
  classical
  exact Classical.choice (show Nonempty
      (ConstructedCardinalityBudgetResult conceptCount roleCount variableCount
        ontology definitions maxWidth budget) from by
    rcases cardinalityControl_search_total ontology definitions
        (8 * 2 ^ budget) parent ancestors root with
      hrefutes | ⟨leaf, hdescends, hstop⟩
    · let certificate := rootCertificate.canonicalizeEqualityClosure
      have hcertificateState : certificate.state = root.state := by
        simpa [certificate] using hrootState.symm
      obtain ⟨depth, tree, htree⟩ := hrefutes.exists_checkClosed_tree
        certificate (by simpa [certificate] using hontology) hcertificateState
        rootCertificate.canonicalizeEqualityClosure_valid
      have hempty' : certificate.base.EmptyRoot := by
        simpa [certificate, FiniteDistinctEqCertificate.canonicalizeEqualityClosure,
          FiniteEqCertificate.canonicalizeEqualityClosure,
          FiniteEqCertificate.EmptyRoot] using hempty
      have hapart' : certificate.apart = [] := by
        simpa [certificate, FiniteDistinctEqCertificate.canonicalizeEqualityClosure]
          using hapart
      let outcome : CheckedCardinalityDecisionOutcome conceptCount roleCount
          variableCount ontology definitions :=
        .closed certificate tree (by simpa [certificate] using hontology)
          (by positivity) hempty' hapart' htree
      exact ⟨⟨outcome, .conclusive (by
        simp [outcome, CardinalityProductionConclusive])⟩⟩
    · rcases stopResult leaf hdescends hstop with hmodel | haddress
      · obtain ⟨certificate, hpositive, hmodelOntology, hcheck⟩ :=
          hmodel.hasCheckedModel
        let outcome : CheckedCardinalityDecisionOutcome conceptCount roleCount
            variableCount ontology definitions :=
          .sat certificate hmodelOntology hpositive hcheck
        exact ⟨⟨outcome, .conclusive (by
          simp [outcome, CardinalityProductionConclusive])⟩⟩
      · rcases haddress with ⟨address, hinjective⟩
        exact ⟨⟨CheckedCardinalityDecisionOutcome.frontier_of_address
          address hinjective, .frontier address hinjective rfl⟩⟩)

noncomputable def
    CartesianFoldExpansionRuntime.ofConstructedCardinalityFiniteSearch
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (maxWidth : Nat)
    (rootCertificate : FiniteDistinctEqCertificate (8 * 2 ^ budget)
      conceptCount roleCount variableCount)
    (hontology : rootCertificate.base.base.ontology = ontology)
    (hempty : rootCertificate.base.EmptyRoot)
    (hapart : rootCertificate.apart = [])
    (root : CardinalityRuntimeConfig (Fin conceptCount) (Fin roleCount)
      definitions (8 * 2 ^ budget))
    (hrootState : root.state = rootCertificate.state)
    (parent : Fin (8 * 2 ^ budget) → Option (Fin (8 * 2 ^ budget)))
    (ancestors : Fin (8 * 2 ^ budget) → List (Fin (8 * 2 ^ budget)))
    (stopResult : ∀ leaf,
      CardinalityProductionDescends ontology definitions parent ancestors
        root leaf →
      (cardinalityControl ontology definitions leaf parent ancestors).IsStop →
      CheckedCardinalityTerminalCandidate (8 * 2 ^ budget) conceptCount
          roleCount variableCount ontology definitions leaf.state ⊕
        { address : Fin (8 * 2 ^ budget) →
            RootedRoleBlockedAddress (Fin 1)
              (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
                definitions.length maxWidth)
              (Fin conceptCount) (Fin roleCount) //
          Function.Injective address }) :
    CartesianFoldExpansionRuntime (Fin (8 * 2 ^ budget))
      (ConstructedCardinalityBudgetResult conceptCount roleCount variableCount
        ontology definitions maxWidth budget) :=
  CartesianFoldExpansionRuntime.done
    (finiteCardinalityRoundBudgetConstruction definitions maxWidth
      rootCertificate hontology hempty hapart root hrootState parent ancestors
      stopResult)

/-- Concrete cross-budget inputs for cardinality production search. -/
structure ConstructedCardinalityFiniteSearchFamily
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (maxWidth : Nat) where
  certificate : ∀ budget, FiniteDistinctEqCertificate (8 * 2 ^ budget)
    conceptCount roleCount variableCount
  ontology_eq : ∀ budget, (certificate budget).base.base.ontology = ontology
  empty : ∀ budget, (certificate budget).base.EmptyRoot
  apart_empty : ∀ budget, (certificate budget).apart = []
  root : ∀ budget, CardinalityRuntimeConfig (Fin conceptCount)
    (Fin roleCount) definitions (8 * 2 ^ budget)
  root_state : ∀ budget, (root budget).state = (certificate budget).state
  parent : ∀ budget,
    Fin (8 * 2 ^ budget) → Option (Fin (8 * 2 ^ budget))
  ancestors : ∀ budget,
    Fin (8 * 2 ^ budget) → List (Fin (8 * 2 ^ budget))
  stopResult : ∀ budget leaf,
    CardinalityProductionDescends ontology definitions (parent budget)
      (ancestors budget) (root budget) leaf →
    (cardinalityControl ontology definitions leaf (parent budget)
      (ancestors budget)).IsStop →
    CheckedCardinalityTerminalCandidate (8 * 2 ^ budget) conceptCount
        roleCount variableCount ontology definitions leaf.state ⊕
      { address : Fin (8 * 2 ^ budget) →
          RootedRoleBlockedAddress (Fin 1)
            (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
              definitions.length maxWidth)
            (Fin conceptCount) (Fin roleCount) //
        Function.Injective address }

noncomputable def ConstructedCardinalityFiniteSearchFamily.runtime
    (family : ConstructedCardinalityFiniteSearchFamily conceptCount roleCount
      variableCount ontology definitions maxWidth)
    (budget : Nat) :
    CartesianFoldExpansionRuntime (Fin (8 * 2 ^ budget))
      (ConstructedCardinalityBudgetResult conceptCount roleCount variableCount
        ontology definitions maxWidth budget) :=
  CartesianFoldExpansionRuntime.ofConstructedCardinalityFiniteSearch definitions
    maxWidth (family.certificate budget) (family.ontology_eq budget)
    (family.empty budget) (family.apart_empty budget) (family.root budget)
    (family.root_state budget) (family.parent budget) (family.ancestors budget)
    (family.stopResult budget)

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

/-- Exact independently checked evidence required for a positive native-ABox
cardinality result. -/
def HasCheckedNativeABoxCardinalityModel
    (Individual : Type)
    (conceptCount roleCount variableCount nodeCount : Nat)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Prop :=
  ∃ certificate : FiniteDistinctEqCertificate nodeCount conceptCount roleCount
      variableCount,
    ∃ root : Individual → Fin nodeCount,
      certificate.base.base.ontology = ontology ∧ 0 < nodeCount ∧
      abox.SeededIn certificate.state root ∧
      certificate.base.checkEqSatWithCardinality definitions = true ∧
      certificate.apartSeparatedB = true ∧
      abox.ProxySingletons certificate.base.state.quotientCanonical
        (fun individual ↦ Quotient.mk certificate.base.state.nodeSetoid
          (root individual)) ∧
      abox.NegativeRoles certificate.base.state.quotientCanonical
        (fun individual ↦ Quotient.mk certificate.base.state.nodeSetoid
          (root individual))

/-- Native-ABox cardinality SAT evidence is tied to the exact reached search
leaf while retaining every independent ABox model-checking obligation. -/
structure CheckedNativeABoxCardinalityTerminalCandidate
    (Individual : Type)
    (conceptCount roleCount variableCount nodeCount : Nat)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (state : DistinctEqState (Fin nodeCount) (Fin conceptCount)
      (Fin roleCount)) where
  certificate : FiniteDistinctEqCertificate nodeCount conceptCount roleCount
    variableCount
  root : Individual → Fin nodeCount
  state_eq : certificate.state = state
  ontology_eq : certificate.base.base.ontology = ontology
  positive : 0 < nodeCount
  seeded : abox.SeededIn certificate.state root
  check : certificate.base.checkEqSatWithCardinality definitions = true
  apart : certificate.apartSeparatedB = true
  singletons : abox.ProxySingletons certificate.base.state.quotientCanonical
    (fun individual ↦ Quotient.mk certificate.base.state.nodeSetoid
      (root individual))
  negative : abox.NegativeRoles certificate.base.state.quotientCanonical
    (fun individual ↦ Quotient.mk certificate.base.state.nodeSetoid
      (root individual))

def CheckedNativeABoxCardinalityTerminalCandidate.hasCheckedModel
    (candidate : CheckedNativeABoxCardinalityTerminalCandidate Individual
      conceptCount roleCount variableCount nodeCount abox ontology definitions
      state) :
    HasCheckedNativeABoxCardinalityModel Individual conceptCount roleCount
      variableCount nodeCount abox ontology definitions :=
  ⟨candidate.certificate, candidate.root, candidate.ontology_eq,
    candidate.positive, candidate.seeded, candidate.check, candidate.apart,
    candidate.singletons, candidate.negative⟩

/-- Build a native-ABox cardinality terminal from the same decoded runtime
fields used to construct the reached leaf. -/
def FiniteCardinalityRuntimeFields.checkedNativeABoxTerminalCandidate
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount
      variableCount definitions)
    (hfields : fields.check = true)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (root : Individual → Fin nodeCount)
    (hpositive : 0 < nodeCount)
    (hseeded : abox.SeededIn fields.certificate.state root)
    (hcheck : fields.certificate.base.checkEqSatWithCardinality definitions =
      true)
    (hapart : fields.certificate.apartSeparatedB = true)
    (hsingletons : abox.ProxySingletons
      fields.certificate.base.state.quotientCanonical
      (fun individual ↦ Quotient.mk
        fields.certificate.base.state.nodeSetoid (root individual)))
    (hnegative : abox.NegativeRoles
      fields.certificate.base.state.quotientCanonical
      (fun individual ↦ Quotient.mk
        fields.certificate.base.state.nodeSetoid (root individual))) :
    CheckedNativeABoxCardinalityTerminalCandidate Individual conceptCount
      roleCount variableCount nodeCount abox
      fields.certificate.base.base.ontology definitions
      (fields.toConfig hfields).state :=
  ⟨fields.certificate, root, rfl, rfl, hpositive, hseeded, hcheck, hapart,
    hsingletons, hnegative⟩

/-- Construct one native-ABox cardinality result from the certified
cardinality production search started at the exact named-individual state. -/
noncomputable def finiteNativeABoxRoundBudgetConstruction
    (rootCount maxWidth : Nat)
    (rootCertificate : FiniteDistinctEqCertificate (8 * 2 ^ budget)
      conceptCount roleCount variableCount)
    (hontology : rootCertificate.base.base.ontology = ontology)
    (hinitial : abox.InitializesDistinctState rootCertificate.state)
    (root : CardinalityRuntimeConfig (Fin conceptCount) (Fin roleCount)
      definitions (8 * 2 ^ budget))
    (hrootState : root.state = rootCertificate.state)
    (parent : Fin (8 * 2 ^ budget) → Option (Fin (8 * 2 ^ budget)))
    (ancestors : Fin (8 * 2 ^ budget) → List (Fin (8 * 2 ^ budget)))
    (stopResult : ∀ leaf,
      CardinalityProductionDescends ontology definitions parent ancestors
        root leaf →
      (cardinalityControl ontology definitions leaf parent ancestors).IsStop →
      CheckedNativeABoxCardinalityTerminalCandidate Individual conceptCount
          roleCount variableCount (8 * 2 ^ budget) abox ontology definitions
          leaf.state ⊕
        { address : Fin (8 * 2 ^ budget) →
            RootedRoleBlockedAddress (Fin rootCount)
              (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
                definitions.length maxWidth)
              (Fin conceptCount) (Fin roleCount) //
          Function.Injective address }) :
    ConstructedNativeABoxBudgetResult Individual conceptCount roleCount
      variableCount abox ontology definitions rootCount maxWidth budget := by
  classical
  exact Classical.choice (show Nonempty
      (ConstructedNativeABoxBudgetResult Individual conceptCount roleCount
        variableCount abox ontology definitions rootCount maxWidth budget) from by
    rcases cardinalityControl_search_total ontology definitions
        (8 * 2 ^ budget) parent ancestors root with
      hrefutes | ⟨leaf, hdescends, hstop⟩
    · let certificate := rootCertificate.canonicalizeEqualityClosure
      have hcertificateState : certificate.state = root.state := by
        simpa [certificate] using hrootState.symm
      obtain ⟨depth, tree, htree⟩ := hrefutes.exists_checkClosed_tree
        certificate (by simpa [certificate] using hontology) hcertificateState
        rootCertificate.canonicalizeEqualityClosure_valid
      have hinitial' : abox.InitializesDistinctState certificate.state := by
        simpa [certificate] using hinitial
      let outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
          roleCount variableCount abox ontology definitions :=
        .closed certificate tree (by simpa [certificate] using hontology)
          hinitial' htree
      exact ⟨⟨outcome, .conclusive (by
        simp [outcome, NativeABoxProductionConclusive])⟩⟩
    · rcases stopResult leaf hdescends hstop with hmodel | haddress
      · rcases hmodel.hasCheckedModel with
          ⟨certificate, namedRoot, hmodelOntology, hpositive, hseeded,
            hcheck, hapart, hsingletons, hnegative⟩
        let outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
            roleCount variableCount abox ontology definitions :=
          .sat certificate namedRoot hmodelOntology hpositive hseeded hcheck
            hapart hsingletons hnegative
        exact ⟨⟨outcome, .conclusive (by
          simp [outcome, NativeABoxProductionConclusive])⟩⟩
      · rcases haddress with ⟨address, hinjective⟩
        exact ⟨⟨CheckedNativeABoxCardinalityOutcome.frontier_of_address
          address hinjective, .frontier address hinjective rfl⟩⟩)

noncomputable def
    CartesianFoldExpansionRuntime.ofConstructedNativeABoxFiniteSearch
    (rootCount maxWidth : Nat)
    (rootCertificate : FiniteDistinctEqCertificate (8 * 2 ^ budget)
      conceptCount roleCount variableCount)
    (hontology : rootCertificate.base.base.ontology = ontology)
    (hinitial : abox.InitializesDistinctState rootCertificate.state)
    (root : CardinalityRuntimeConfig (Fin conceptCount) (Fin roleCount)
      definitions (8 * 2 ^ budget))
    (hrootState : root.state = rootCertificate.state)
    (parent : Fin (8 * 2 ^ budget) → Option (Fin (8 * 2 ^ budget)))
    (ancestors : Fin (8 * 2 ^ budget) → List (Fin (8 * 2 ^ budget)))
    (stopResult : ∀ leaf,
      CardinalityProductionDescends ontology definitions parent ancestors
        root leaf →
      (cardinalityControl ontology definitions leaf parent ancestors).IsStop →
      CheckedNativeABoxCardinalityTerminalCandidate Individual conceptCount
          roleCount variableCount (8 * 2 ^ budget) abox ontology definitions
          leaf.state ⊕
        { address : Fin (8 * 2 ^ budget) →
            RootedRoleBlockedAddress (Fin rootCount)
              (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
                definitions.length maxWidth)
              (Fin conceptCount) (Fin roleCount) //
          Function.Injective address }) :
    CartesianFoldExpansionRuntime (Fin (8 * 2 ^ budget))
      (ConstructedNativeABoxBudgetResult Individual conceptCount roleCount
        variableCount abox ontology definitions rootCount maxWidth budget) :=
  CartesianFoldExpansionRuntime.done
    (finiteNativeABoxRoundBudgetConstruction rootCount maxWidth rootCertificate
      hontology hinitial root hrootState parent ancestors stopResult)

structure ConstructedNativeABoxFiniteSearchFamily
    (Individual : Type)
    (conceptCount roleCount variableCount : Nat)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (rootCount maxWidth : Nat) where
  certificate : ∀ budget, FiniteDistinctEqCertificate (8 * 2 ^ budget)
    conceptCount roleCount variableCount
  ontology_eq : ∀ budget, (certificate budget).base.base.ontology = ontology
  initial : ∀ budget, abox.InitializesDistinctState (certificate budget).state
  root : ∀ budget, CardinalityRuntimeConfig (Fin conceptCount)
    (Fin roleCount) definitions (8 * 2 ^ budget)
  root_state : ∀ budget, (root budget).state = (certificate budget).state
  parent : ∀ budget,
    Fin (8 * 2 ^ budget) → Option (Fin (8 * 2 ^ budget))
  ancestors : ∀ budget,
    Fin (8 * 2 ^ budget) → List (Fin (8 * 2 ^ budget))
  stopResult : ∀ budget leaf,
    CardinalityProductionDescends ontology definitions (parent budget)
      (ancestors budget) (root budget) leaf →
    (cardinalityControl ontology definitions leaf (parent budget)
      (ancestors budget)).IsStop →
    CheckedNativeABoxCardinalityTerminalCandidate Individual conceptCount
        roleCount variableCount (8 * 2 ^ budget) abox ontology definitions
        leaf.state ⊕
      { address : Fin (8 * 2 ^ budget) →
          RootedRoleBlockedAddress (Fin rootCount)
            (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
              definitions.length maxWidth)
            (Fin conceptCount) (Fin roleCount) //
        Function.Injective address }

noncomputable def ConstructedNativeABoxFiniteSearchFamily.runtime
    (family : ConstructedNativeABoxFiniteSearchFamily Individual conceptCount
      roleCount variableCount abox ontology definitions rootCount maxWidth)
    (budget : Nat) :
    CartesianFoldExpansionRuntime (Fin (8 * 2 ^ budget))
      (ConstructedNativeABoxBudgetResult Individual conceptCount roleCount
        variableCount abox ontology definitions rootCount maxWidth budget) :=
  CartesianFoldExpansionRuntime.ofConstructedNativeABoxFiniteSearch rootCount
    maxWidth (family.certificate budget) (family.ontology_eq budget)
    (family.initial budget) (family.root budget) (family.root_state budget)
    (family.parent budget) (family.ancestors budget) (family.stopResult budget)

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

/-- End-to-end regular decision built from the concrete exhaustive search data
at every doubling budget.  The theorem constructs both finite learning loops
and their evidence-carrying accepted results before deriving the source-level
decision. -/
theorem checked_regular_finite_search_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (parent : ∀ budget,
      Finset (GuardedFact (Fin (8 * 2 ^ budget)) (Fin conceptCount)
        (Fin roleCount)) →
        Fin (8 * 2 ^ budget) → Option (Fin (8 * 2 ^ budget)))
    (ancestors : ∀ budget,
      Finset (GuardedFact (Fin (8 * 2 ^ budget)) (Fin conceptCount)
        (Fin roleCount)) →
        Fin (8 * 2 ^ budget) → List (Fin (8 * 2 ^ budget)))
    (hheads : ∀ clause ∈ target, ∀ atom ∈ clause.head, Branchable atom)
    (hguarded : ∀ clause ∈ target, clause.GuardedBody)
    (frontierAddress : ∀ budget
      (forbidden : Finset
        (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget)))
      (leaf : Finset (GuardedFact (Fin (8 * 2 ^ budget)) (Fin conceptCount)
        (Fin roleCount))),
      SearchDescends
        (runtimeNextBlockedFacts target
          (productionBlockedFacts (parent budget) (ancestors budget) forbidden))
        ∅ leaf →
      (stateOfGuardedFacts leaf).BlockedRuntimeFrontier target
        ((stateOfGuardedFacts leaf).productionBlocked (parent budget leaf)
          (ancestors budget leaf) forbidden) →
      ∃ address : Fin (8 * 2 ^ budget) →
          WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount),
        (stateOfGuardedFacts leaf).checkRootedAddressRefines address = true)
    (regularFallback : ∀ budget (forbidden : Finset
        (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget))),
      (leaf : ProductionBlockedLeafAt (Fin (8 * 2 ^ budget)) (Fin conceptCount)
          (Fin roleCount) (Fin variableCount) target forbidden) →
        Finset (FoldAssignment (Fin (8 * 2 ^ budget))) →
          FoldAssignment (Fin (8 * 2 ^ budget)) →
            Option (CheckedRegularFallbackCandidate (8 * 2 ^ budget)
              conceptCount roleCount variableCount target leaf.state)) :
    ∃ outcome : CheckedRegularRoundOutcome conceptCount roleCount variableCount
      target, outcome.SourceSemantics source := by
  apply checked_constructed_regular_runtime_decides_source equivalent
  intro budget
  exact CartesianFoldExpansionRuntime.ofConstructedRegularFiniteSearch target
    (parent budget) (ancestors budget) hheads hguarded ∅ rfl
    (frontierAddress budget) (regularFallback budget)

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

/-- End-to-end equality-aware source decision constructed from the concrete
well-founded finite search at every doubling budget. -/
theorem checked_equality_finite_search_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (root : ∀ budget, FiniteEqCertificate (8 * 2 ^ budget) conceptCount
      roleCount variableCount)
    (hontology : ∀ budget, (root budget).base.ontology = target)
    (hempty : ∀ budget, (root budget).EmptyRoot)
    (parent : ∀ budget,
      EqState (Fin (8 * 2 ^ budget)) (Fin conceptCount) (Fin roleCount) →
        Fin (8 * 2 ^ budget) → Option (Fin (8 * 2 ^ budget)))
    (ancestors : ∀ budget,
      EqState (Fin (8 * 2 ^ budget)) (Fin conceptCount) (Fin roleCount) →
        Fin (8 * 2 ^ budget) → List (Fin (8 * 2 ^ budget)))
    (terminalFold : ∀ budget state,
      EqRuntimeTerminal target (parent budget) (ancestors budget) state →
        CheckedEqualityTerminalCandidate (8 * 2 ^ budget) conceptCount
          roleCount variableCount target state)
    (frontierAddress : ∀ budget leaf,
      SearchDescends
        (eqRuntimeNextClashFirst target (parent budget) (ancestors budget))
        (root budget).state leaf →
      EqRuntimeNodeFrontier target leaf (parent budget leaf)
        (ancestors budget leaf) →
      ∃ address : Fin (8 * 2 ^ budget) →
          WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount),
        Function.Injective address) :
    ∃ outcome : CheckedEqualityDecisionOutcome conceptCount roleCount
      variableCount target, outcome.SourceSemantics source := by
  apply checked_constructed_equality_runtime_decides_source equivalent
  intro budget
  exact CartesianFoldExpansionRuntime.ofConstructedEqualityFiniteSearch
    (root budget) (hontology budget) (hempty budget) (parent budget)
    (ancestors budget) (terminalFold budget) (frontierAddress budget)

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

theorem checked_cardinality_finite_search_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (maxWidth : Nat)
    (family : ConstructedCardinalityFiniteSearchFamily conceptCount roleCount
      variableCount target definitions maxWidth) :
    ∃ outcome : CheckedCardinalityDecisionOutcome conceptCount roleCount
      variableCount target definitions, outcome.SourceSemantics source :=
  checked_constructed_cardinality_runtime_decides_source equivalent maxWidth
    family.runtime

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

theorem checked_native_abox_finite_search_decides_source
    {Individual : Type}
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (rootCount maxWidth : Nat)
    (family : ConstructedNativeABoxFiniteSearchFamily Individual conceptCount
      roleCount variableCount abox target definitions rootCount maxWidth) :
    ∃ outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox target definitions,
        outcome.SourceSemantics source :=
  checked_constructed_native_abox_runtime_decides_source equivalent rootCount
    maxWidth family.runtime

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
      (family : ConstructedRegularFiniteSearchFamily conceptCount roleCount
        variableCount target) :
      CertifiedHTAssignmentProductionGlobalRoute (HasNonemptyModel source)
  | equality
      {source target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      (equivalent : ModelEquivalent source target)
      (family : ConstructedEqualityFiniteSearchFamily conceptCount roleCount
        variableCount target) :
      CertifiedHTAssignmentProductionGlobalRoute (EqualityHasNonemptyModel source)
  | cardinality
      {source target : List
        (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
      {definitions : List
        (CardinalityDef (Fin conceptCount) (Fin roleCount))}
      (equivalent : ModelEquivalent source target)
      (maxWidth : Nat)
      (family : ConstructedCardinalityFiniteSearchFamily conceptCount roleCount
        variableCount target definitions maxWidth) :
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
      (family : ConstructedNativeABoxFiniteSearchFamily Individual conceptCount
        roleCount variableCount abox target definitions rootCount maxWidth) :
      CertifiedHTAssignmentProductionGlobalRoute
        (abox.SatisfiableWithCardinality source definitions)

theorem CertifiedHTAssignmentProductionGlobalRoute.decides
    {semantics : Prop}
    (route : CertifiedHTAssignmentProductionGlobalRoute semantics) :
    Nonempty (CertifiedHTGlobalVerdict semantics) := by
  cases route with
  | regular equivalent family =>
      obtain ⟨outcome, hsemantics⟩ :=
        checked_constructed_regular_runtime_decides_source equivalent family.runtime
      cases outcome with
      | regularSat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | finiteSat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | finiteUnsat certificate tree hontology hnonempty hempty hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hcheck =>
          simp only [CheckedRegularRoundOutcome.SourceSemantics] at hsemantics
  | equality equivalent family =>
      obtain ⟨outcome, hsemantics⟩ :=
        checked_constructed_equality_runtime_decides_source equivalent family.runtime
      cases outcome with
      | sat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | closed certificate tree hontology hnonempty hempty hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hcheck =>
          simp only [CheckedEqualityDecisionOutcome.SourceSemantics] at hsemantics
  | cardinality equivalent maxWidth family =>
      obtain ⟨outcome, hsemantics⟩ :=
        checked_constructed_cardinality_runtime_decides_source equivalent
          maxWidth family.runtime
      cases outcome with
      | sat certificate hontology hnonempty hcheck =>
          exact ⟨.sat hsemantics⟩
      | closed certificate tree hontology hnonempty hempty hapart hcheck =>
          exact ⟨.unsat hsemantics⟩
      | frontier document hconcepts hroles hdefinitions hcheck =>
          simp only [CheckedCardinalityDecisionOutcome.SourceSemantics] at hsemantics
  | nativeABox equivalent rootCount maxWidth family =>
      obtain ⟨outcome, hsemantics⟩ :=
        checked_constructed_native_abox_runtime_decides_source equivalent
          rootCount maxWidth family.runtime
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
#print axioms CartesianFoldExpansionRuntime.ofConstructedRegularFiniteSearch
#print axioms checked_regular_runtime_decides_source_of_construction
#print axioms checked_constructed_regular_runtime_decides_source
#print axioms checked_regular_finite_search_decides_source
#print axioms checked_equality_runtime_eventually_conclusive
#print axioms checked_equality_runtime_decides_source
#print axioms EqualityBudgetOutcomeConstruction.classify
#print axioms finiteEqualityRoundBudgetConstruction
#print axioms CartesianFoldExpansionRuntime.ofConstructedEqualityFiniteSearch
#print axioms checked_equality_runtime_decides_source_of_construction
#print axioms checked_constructed_equality_runtime_decides_source
#print axioms checked_equality_finite_search_decides_source
#print axioms checked_cardinality_runtime_eventually_conclusive
#print axioms checked_cardinality_runtime_decides_source
#print axioms CardinalityBudgetOutcomeConstruction.classify
#print axioms finiteCardinalityRoundBudgetConstruction
#print axioms CartesianFoldExpansionRuntime.ofConstructedCardinalityFiniteSearch
#print axioms ConstructedCardinalityFiniteSearchFamily.runtime
#print axioms checked_cardinality_runtime_decides_source_of_construction
#print axioms checked_constructed_cardinality_runtime_decides_source
#print axioms checked_cardinality_finite_search_decides_source
#print axioms checked_native_abox_runtime_eventually_conclusive
#print axioms checked_native_abox_runtime_decides_source
#print axioms NativeABoxBudgetOutcomeConstruction.classify
#print axioms finiteNativeABoxRoundBudgetConstruction
#print axioms CartesianFoldExpansionRuntime.ofConstructedNativeABoxFiniteSearch
#print axioms ConstructedNativeABoxFiniteSearchFamily.runtime
#print axioms checked_native_abox_runtime_decides_source_of_construction
#print axioms checked_constructed_native_abox_runtime_decides_source
#print axioms checked_native_abox_finite_search_decides_source

end ContextCalculus.Hypertableau
