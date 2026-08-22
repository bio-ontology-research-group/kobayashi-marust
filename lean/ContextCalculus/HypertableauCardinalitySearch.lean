import ContextCalculus.HypertableauCardinalityRuntimeSearch
import ContextCalculus.HypertableauCardinalityCertificate
import ContextCalculus.HypertableauCardinalityFrontierWire
import ContextCalculus.HypertableauEqualityNormalization
import ContextCalculus.HypertableauRegularProduction

/-!
# Checked bounded cardinality-aware HT outcomes

The concrete distinct-cardinality decision search reports a checked quotient
model, checked closure, or exhaustion of its node budget. The first two are
semantically conclusive; frontier exhaustion is not.
-/

namespace ContextCalculus.Hypertableau

abbrev CardinalityHasNonemptyModel
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role),
    Nonempty Domain ∧ I.models ontology ∧ I.modelsCardinalityDefs definitions

inductive CheckedCardinalityDecisionOutcome
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Type where
  | sat
      {nodeCount : Nat}
      (certificate : FiniteEqCertificate
        nodeCount conceptCount roleCount variableCount)
      (hontology : certificate.base.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hcheck : certificate.checkEqSatWithCardinality definitions = true)
  | closed
      {nodeCount depth : Nat}
      (certificate : FiniteDistinctEqCertificate
        nodeCount conceptCount roleCount variableCount)
      (tree : FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount depth)
      (hontology : certificate.base.base.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hempty : certificate.base.EmptyRoot)
      (hapart : certificate.apart = [])
      (hcheck : tree.checkClosed definitions certificate = true)
  | frontier
      (document : WireCardinalityAddressFrontier)
      (hconcepts : document.concept_count = conceptCount)
      (hroles : document.role_count = roleCount)
      (hdefinitions : document.definition_count = definitions.length)
      (hcheck : document.check = true)

/-- Construct a checked cardinality frontier from the mathematical tagged
address invariant. -/
def CheckedCardinalityDecisionOutcome.frontier_of_address
    (address : Fin (8 * 2 ^ budget) → RootedRoleBlockedAddress (Fin 1)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitions.length maxWidth)
      (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    CheckedCardinalityDecisionOutcome conceptCount roleCount variableCount
      ontology definitions :=
  let document := WireCardinalityAddressFrontier.ofAddress address
  .frontier document rfl rfl rfl
    (document.checkScheduled_check budget maxWidth
      (WireCardinalityAddressFrontier.ofAddress_checkScheduled
        address hinjective rfl))

/-- One cardinality-aware production attempt. The scheduled frontier stores
both changing dimensions used by the termination proof. -/
inductive CheckedCardinalityControlAttempt
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (budget maxWidth : Nat)
    (forbidden : Finset
      (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget))) : Type where
  | sat
      {nodeCount : Nat}
      (certificate : FiniteEqCertificate
        nodeCount conceptCount roleCount variableCount)
      (hontology : certificate.base.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hcheck : certificate.checkEqSatWithCardinality definitions = true)
  | closed
      {nodeCount depth : Nat}
      (certificate : FiniteDistinctEqCertificate
        nodeCount conceptCount roleCount variableCount)
      (tree : FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount depth)
      (hontology : certificate.base.base.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hempty : certificate.base.EmptyRoot)
      (hapart : certificate.apart = [])
      (hcheck : tree.checkClosed definitions certificate = true)
  | frontier
      (document : WireCardinalityAddressFrontier)
      (hconcepts : document.concept_count = conceptCount)
      (hroles : document.role_count = roleCount)
      (hdefinitions : document.definition_count = definitions.length)
      (hscheduled : document.checkScheduled budget maxWidth = true)
  | rejected
      (folds : Finset
        (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget)))
      (fresh : ∃ fold ∈ folds, fold ∉ forbidden)

/-- Construct the scheduled cardinality control frontier directly from an
injective tagged address map. -/
def CheckedCardinalityControlAttempt.frontier_of_address
    (address : Fin (8 * 2 ^ budget) → RootedRoleBlockedAddress (Fin 1)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitions.length maxWidth)
      (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    CheckedCardinalityControlAttempt conceptCount roleCount variableCount
      ontology definitions budget maxWidth forbidden :=
  let document := WireCardinalityAddressFrontier.ofAddress address
  .frontier document rfl rfl rfl
    (WireCardinalityAddressFrontier.ofAddress_checkScheduled
      address hinjective rfl)

def CheckedCardinalityControlAttempt.toGuarded
    {forbidden : Finset
      (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget))}
    (attempt : CheckedCardinalityControlAttempt conceptCount roleCount variableCount
      ontology definitions budget maxWidth forbidden) :
    GuardedFoldAttempt (Fin (8 * 2 ^ budget))
      (CheckedCardinalityDecisionOutcome conceptCount roleCount variableCount
        ontology definitions) forbidden :=
  match attempt with
  | .sat certificate hontology hnonempty hcheck =>
      .done (.sat certificate hontology hnonempty hcheck)
  | .closed certificate tree hontology hnonempty hempty hapart hcheck =>
      .done (.closed certificate tree hontology hnonempty hempty hapart hcheck)
  | .frontier document hconcepts hroles hdefinitions hscheduled =>
      .done (.frontier document hconcepts hroles hdefinitions
        (document.checkScheduled_check budget maxWidth hscheduled))
  | .rejected folds fresh => .rejected folds fresh

theorem CheckedCardinalityControlAttempt.frontier_scheduled
    {forbidden : Finset
      (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget))}
    (attempt : CheckedCardinalityControlAttempt conceptCount roleCount variableCount
      ontology definitions budget maxWidth forbidden)
    {document : WireCardinalityAddressFrontier}
    {hconcepts : document.concept_count = conceptCount}
    {hroles : document.role_count = roleCount}
    {hdefinitions : document.definition_count = definitions.length}
    {hcheck : document.check = true}
    (herase : attempt.toGuarded.erase = .done
      (.frontier document hconcepts hroles hdefinitions hcheck)) :
    document.checkScheduled budget maxWidth = true := by
  cases attempt with
  | sat certificate hontology hnonempty hcertificate =>
      simp [CheckedCardinalityControlAttempt.toGuarded,
        GuardedFoldAttempt.erase] at herase
  | closed certificate tree hontology hnonempty hempty hapart hcertificate =>
      simp [CheckedCardinalityControlAttempt.toGuarded,
        GuardedFoldAttempt.erase] at herase
  | frontier frontier frontierConcepts frontierRoles frontierDefinitions hscheduled =>
      simp only [CheckedCardinalityControlAttempt.toGuarded,
        GuardedFoldAttempt.erase] at herase
      cases herase
      exact hscheduled
  | rejected folds fresh =>
      simp [CheckedCardinalityControlAttempt.toGuarded,
        GuardedFoldAttempt.erase] at herase

structure CheckedCardinalityControlProducer
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (budget maxWidth : Nat) where
  attempt : ∀ forbidden : Finset
      (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget)),
    CheckedCardinalityControlAttempt conceptCount roleCount variableCount
      ontology definitions budget maxWidth forbidden

def CheckedCardinalityControlProducer.toGuarded
    (producer : CheckedCardinalityControlProducer conceptCount roleCount
      variableCount ontology definitions budget maxWidth) :
    GuardedFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedCardinalityDecisionOutcome conceptCount roleCount variableCount
        ontology definitions) where
  attempt forbidden := (producer.attempt forbidden).toGuarded

theorem CheckedCardinalityControlProducer.frontier_scheduled
    (producer : CheckedCardinalityControlProducer conceptCount roleCount
      variableCount ontology definitions budget maxWidth)
    {retry : Nat} {document : WireCardinalityAddressFrontier}
    {hconcepts : document.concept_count = conceptCount}
    {hroles : document.role_count = roleCount}
    {hdefinitions : document.definition_count = definitions.length}
    {hcheck : document.check = true}
    (hrun : producer.toGuarded.toFreshFoldProducer.run retry = .done
      (.frontier document hconcepts hroles hdefinitions hcheck)) :
    document.checkScheduled budget maxWidth = true := by
  apply CheckedCardinalityControlAttempt.frontier_scheduled
    (producer.attempt
      (producer.toGuarded.toFreshFoldProducer.forbidden retry))
  simpa [GuardedFoldProducer.toFreshFoldProducer, FreshFoldProducer.run,
    CheckedCardinalityControlProducer.toGuarded] using hrun

def CheckedCardinalityDecisionOutcome.Semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedCardinalityDecisionOutcome
      conceptCount roleCount variableCount ontology definitions) : Prop :=
  match outcome with
  | .sat .. => CardinalityHasNonemptyModel ontology definitions
  | .closed .. => ¬CardinalityHasNonemptyModel ontology definitions
  | .frontier .. => False

def CheckedCardinalityDecisionOutcome.SourceSemantics
    {target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (source : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedCardinalityDecisionOutcome
      conceptCount roleCount variableCount target definitions) : Prop :=
  match outcome with
  | .sat .. => CardinalityHasNonemptyModel source definitions
  | .closed .. => ¬CardinalityHasNonemptyModel source definitions
  | .frontier .. => False

theorem CheckedCardinalityDecisionOutcome.source_semantics_of_equivalent
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedCardinalityDecisionOutcome
      conceptCount roleCount variableCount target definitions)
    (equivalent : ModelEquivalent source target)
    (hsemantics : outcome.Semantics) :
    outcome.SourceSemantics source := by
  cases outcome with
  | sat certificate hontology hnonempty hcheck =>
      simp only [CheckedCardinalityDecisionOutcome.Semantics,
        CheckedCardinalityDecisionOutcome.SourceSemantics,
        CardinalityHasNonemptyModel] at hsemantics ⊢
      rcases hsemantics with ⟨Domain, I, hdomain, htarget, hdefinitions⟩
      exact ⟨Domain, I, hdomain, (equivalent Domain I).mpr htarget, hdefinitions⟩
  | closed certificate tree hontology hnonempty hempty hapart hcheck =>
      simp only [CheckedCardinalityDecisionOutcome.Semantics,
        CheckedCardinalityDecisionOutcome.SourceSemantics,
        CardinalityHasNonemptyModel] at hsemantics ⊢
      rintro ⟨Domain, I, hdomain, hsource, hdefinitions⟩
      exact hsemantics ⟨Domain, I, hdomain,
        (equivalent Domain I).mp hsource, hdefinitions⟩
  | frontier document hconcepts hroles hdefinitions hcheck =>
      exact hsemantics

theorem CheckedCardinalityDecisionOutcome.sat_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    {nodeCount : Nat}
    (certificate : FiniteEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hontology : certificate.base.ontology = ontology)
    (hnonempty : 0 < nodeCount)
    (hcheck : certificate.checkEqSatWithCardinality definitions = true) :
    CardinalityHasNonemptyModel ontology definitions := by
  letI : Nonempty (Fin nodeCount) := ⟨⟨0, hnonempty⟩⟩
  have hmodels := certificate.checkEqSatWithCardinality_models definitions hcheck
  refine ⟨certificate.state.QuotientDomain, certificate.state.quotientCanonical, ?_, ?_, hmodels.2⟩
  · exact ⟨Quotient.mk certificate.state.nodeSetoid (Classical.choice inferInstance)⟩
  · simpa [hontology] using hmodels.1

theorem CheckedCardinalityDecisionOutcome.closed_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    {nodeCount depth : Nat}
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (hontology : certificate.base.base.ontology = ontology)
    (hnonempty : 0 < nodeCount)
    (hempty : certificate.base.EmptyRoot)
    (hapart : certificate.apart = [])
    (hcheck : tree.checkClosed definitions certificate = true) :
    ¬CardinalityHasNonemptyModel ontology definitions := by
  letI : Nonempty (Fin nodeCount) := ⟨⟨0, hnonempty⟩⟩
  have hnot := tree.checkClosed_ontology_unsatisfiable
    definitions certificate hempty hapart hcheck
  simpa [CardinalityHasNonemptyModel, hontology] using hnot

theorem CheckedCardinalityDecisionOutcome.conclusive_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedCardinalityDecisionOutcome
      conceptCount roleCount variableCount ontology definitions) :
    (match outcome with | .frontier .. => False | _ => True) →
      outcome.Semantics := by
  cases outcome with
  | sat certificate hontology hnonempty hcheck =>
      intro _
      exact CheckedCardinalityDecisionOutcome.sat_semantics
        certificate hontology hnonempty hcheck
  | closed certificate tree hontology hnonempty hempty hapart hcheck =>
      intro _
      exact CheckedCardinalityDecisionOutcome.closed_semantics
        certificate tree hontology hnonempty hempty hapart hcheck
  | frontier document hconcepts hroles hdefinitions hcheck => simp

/-- For a fixed cardinality vocabulary and maximum minimum width, checked
tagged frontiers cannot persist through iterative doubling. Hence some round
returns a checked model or checked refutation. -/
theorem checked_cardinality_doubling_decides
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (maxWidth : Nat)
    (run : Nat → CheckedCardinalityDecisionOutcome
      conceptCount roleCount variableCount ontology definitions)
    (hnodes : ∀ round document hconcepts hroles hdefinitions hcheck,
      run round = .frontier document hconcepts hroles hdefinitions hcheck →
        document.node_count = 8 * 2 ^ round)
    (hwidth : ∀ round document hconcepts hroles hdefinitions hcheck,
      run round = .frontier document hconcepts hroles hdefinitions hcheck →
        document.max_width = maxWidth) :
    ∃ round, (run round).Semantics := by
  classical
  by_contra hconclusive
  have hnone : ∀ round, ¬(run round).Semantics := not_exists.mp hconclusive
  have hfrontier : ∀ round, ∃ document hconcepts hroles hdefinitions hcheck,
      run round = .frontier document hconcepts hroles hdefinitions hcheck := by
    intro round
    generalize houtcome : run round = outcome
    cases outcome with
    | sat certificate hontology hnonempty hcheck =>
        exfalso
        exact hnone round (by
          rw [houtcome]
          exact CheckedCardinalityDecisionOutcome.sat_semantics
            certificate hontology hnonempty hcheck)
    | closed certificate tree hontology hnonempty hempty hapart hcheck =>
        exfalso
        exact hnone round (by
          rw [houtcome]
          exact CheckedCardinalityDecisionOutcome.closed_semantics
            certificate tree hontology hnonempty hempty hapart hcheck)
    | frontier document hconcepts hroles hdefinitions hcheck =>
        exact ⟨document, hconcepts, hroles, hdefinitions, hcheck, rfl⟩
  choose document hconcepts hroles hdefinitions hchecks heq using hfrontier
  obtain ⟨round, hrejected⟩ :=
    cardinality_doubling_eventually_rejects_checked_frontier
      document conceptCount roleCount definitions.length maxWidth
      (fun round => hnodes round (document round) (hconcepts round)
        (hroles round) (hdefinitions round) (hchecks round) (heq round))
      hconcepts hroles hdefinitions
      (fun round => hwidth round (document round) (hconcepts round)
        (hroles round) (hdefinitions round) (hchecks round) (heq round))
  exact hrejected (hchecks round)

theorem checked_cardinality_doubling_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (maxWidth : Nat)
    (run : Nat → CheckedCardinalityDecisionOutcome
      conceptCount roleCount variableCount target definitions)
    (hnodes : ∀ round document hconcepts hroles hdefinitions hcheck,
      run round = .frontier document hconcepts hroles hdefinitions hcheck →
        document.node_count = 8 * 2 ^ round)
    (hwidth : ∀ round document hconcepts hroles hdefinitions hcheck,
      run round = .frontier document hconcepts hroles hdefinitions hcheck →
        document.max_width = maxWidth) :
    ∃ round, (run round).SourceSemantics source := by
  obtain ⟨round, hsemantics⟩ :=
    checked_cardinality_doubling_decides maxWidth run hnodes hwidth
  exact ⟨round, (run round).source_semantics_of_equivalent equivalent hsemantics⟩

/-- Cardinality-aware production exhausts fresh rejected blocker folds at one
budget before a checked cardinality frontier can trigger budget doubling. -/
theorem checked_cardinality_fold_learning_doubling_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (maxWidth : Nat)
    (attempt : ∀ budget, Nat → FoldLearningOutcome (Fin (8 * 2 ^ budget))
      (CheckedCardinalityDecisionOutcome conceptCount roleCount variableCount
        target definitions))
    (forbidden : ∀ budget,
      Nat → Finset (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget)))
    (hlearn : ∀ budget retry folds,
      attempt budget retry = .rejected folds →
        forbidden budget (retry + 1) = forbidden budget retry ∪ folds ∧
          ∃ fold ∈ folds, fold ∉ forbidden budget retry)
    (hnodes : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
      attempt budget retry = .done
        (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.node_count = 8 * 2 ^ budget)
    (hwidth : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
      attempt budget retry = .done
        (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.max_width = maxWidth) :
    ∃ budget retry outcome,
      attempt budget retry = .done outcome ∧ outcome.SourceSemantics source := by
  have hsettles : ∀ budget, ∃ retry outcome,
      attempt budget retry = .done outcome := by
    intro budget
    exact fold_learning_eventually_done (attempt budget) (forbidden budget)
      (hlearn budget)
  choose retry settled hsettled using hsettles
  have hsettledNodes : ∀ budget document hconcepts hroles hdefinitions hcheck,
      settled budget = .frontier document hconcepts hroles hdefinitions hcheck →
        document.node_count = 8 * 2 ^ budget := by
    intro budget document hconcepts hroles hdefinitions hcheck houtcome
    exact hnodes budget (retry budget) document hconcepts hroles hdefinitions hcheck
      (by rw [hsettled budget, houtcome])
  have hsettledWidth : ∀ budget document hconcepts hroles hdefinitions hcheck,
      settled budget = .frontier document hconcepts hroles hdefinitions hcheck →
        document.max_width = maxWidth := by
    intro budget document hconcepts hroles hdefinitions hcheck houtcome
    exact hwidth budget (retry budget) document hconcepts hroles hdefinitions hcheck
      (by rw [hsettled budget, houtcome])
  obtain ⟨budget, hsemantics⟩ := checked_cardinality_doubling_decides_source
    equivalent maxWidth settled hsettledNodes hsettledWidth
  exact ⟨budget, retry budget, settled budget, hsettled budget, hsemantics⟩

theorem checked_cardinality_fresh_fold_producer_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
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
    ∃ budget retry outcome,
      (producer budget).run retry = .done outcome ∧
        outcome.SourceSemantics source := by
  exact checked_cardinality_fold_learning_doubling_decides_source equivalent
    maxWidth (fun budget => (producer budget).run)
    (fun budget => (producer budget).forbidden)
    (fun _ _ _ hrun => FreshFoldProducer.rejected_step _ hrun) hnodes hwidth

theorem checked_cardinality_fold_assignment_producer_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (maxWidth : Nat)
    (producer : ∀ budget, FoldAssignmentProducer (Fin (8 * 2 ^ budget))
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
    ∃ budget retry outcome,
      (producer budget).run retry = .done outcome ∧
        outcome.SourceSemantics source := by
  have hsettles : ∀ budget, ∃ retry outcome,
      (producer budget).run retry = .done outcome := fun budget =>
    (producer budget).eventually_done
  choose retry settled hsettled using hsettles
  have hsettledNodes : ∀ budget document hconcepts hroles hdefinitions hcheck,
      settled budget = .frontier document hconcepts hroles hdefinitions hcheck →
        document.node_count = 8 * 2 ^ budget := by
    intro budget document hconcepts hroles hdefinitions hcheck houtcome
    exact hnodes budget (retry budget) document hconcepts hroles hdefinitions hcheck
      (by rw [hsettled budget, houtcome])
  have hsettledWidth : ∀ budget document hconcepts hroles hdefinitions hcheck,
      settled budget = .frontier document hconcepts hroles hdefinitions hcheck →
        document.max_width = maxWidth := by
    intro budget document hconcepts hroles hdefinitions hcheck houtcome
    exact hwidth budget (retry budget) document hconcepts hroles hdefinitions hcheck
      (by rw [hsettled budget, houtcome])
  obtain ⟨budget, hsemantics⟩ := checked_cardinality_doubling_decides_source
    equivalent maxWidth settled hsettledNodes hsettledWidth
  exact ⟨budget, retry budget, settled budget, hsettled budget, hsemantics⟩

/-- Cardinality-aware production totality with fresh retries, node scheduling,
and maximum-width scheduling all intrinsic to the checked producer. -/
theorem checked_cardinality_control_producer_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (maxWidth : Nat)
    (producer : ∀ budget,
      CheckedCardinalityControlProducer conceptCount roleCount variableCount
        target definitions budget maxWidth) :
    ∃ budget retry outcome,
      (producer budget).toGuarded.toFreshFoldProducer.run retry = .done outcome ∧
        outcome.SourceSemantics source := by
  apply checked_cardinality_fresh_fold_producer_decides_source equivalent maxWidth
    (fun budget => (producer budget).toGuarded.toFreshFoldProducer)
  · intro budget retry document hconcepts hroles hdefinitions hcheck hrun
    exact document.checkScheduled_node_count budget maxWidth
      ((producer budget).frontier_scheduled hrun)
  · intro budget retry document hconcepts hroles hdefinitions hcheck hrun
    exact document.checkScheduled_max_width budget maxWidth
      ((producer budget).frontier_scheduled hrun)

#print axioms CheckedCardinalityDecisionOutcome.sat_semantics
#print axioms CheckedCardinalityDecisionOutcome.closed_semantics
#print axioms CheckedCardinalityDecisionOutcome.frontier_of_address
#print axioms CheckedCardinalityDecisionOutcome.conclusive_semantics
#print axioms checked_cardinality_doubling_decides
#print axioms CheckedCardinalityDecisionOutcome.source_semantics_of_equivalent
#print axioms checked_cardinality_doubling_decides_source
#print axioms checked_cardinality_fold_learning_doubling_decides_source
#print axioms checked_cardinality_fresh_fold_producer_decides_source
#print axioms checked_cardinality_fold_assignment_producer_decides_source
#print axioms CheckedCardinalityControlAttempt.frontier_scheduled
#print axioms CheckedCardinalityControlAttempt.frontier_of_address
#print axioms CheckedCardinalityControlProducer.frontier_scheduled
#print axioms checked_cardinality_control_producer_decides_source

end ContextCalculus.Hypertableau
