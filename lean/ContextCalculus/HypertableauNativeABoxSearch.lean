import ContextCalculus.HypertableauNativeABoxDecision
import ContextCalculus.HypertableauRootedCardinalityFrontierWire
import ContextCalculus.HypertableauEqualityNormalization
import ContextCalculus.HypertableauRegularProduction

/-!
# Total checked native-ABox cardinality search

The source problem contains a TBox, cardinality definitions, and KM's native
named-individual ABox. A checked open quotient must preserve the native roots,
apart relation, singleton proxies, and negative roles. A checked closed tree
must start from an exact native-ABox initialization. Node exhaustion remains an
explicit checked frontier.
-/

namespace ContextCalculus.Hypertableau

inductive CheckedNativeABoxCardinalityOutcome
    (Individual : Type)
    (conceptCount roleCount variableCount : Nat)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Type where
  | sat
      {nodeCount : Nat}
      (certificate : FiniteDistinctEqCertificate
        nodeCount conceptCount roleCount variableCount)
      (root : Individual → Fin nodeCount)
      (hontology : certificate.base.base.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hseeded : abox.SeededIn certificate.state root)
      (hcheck : certificate.base.checkEqSatWithCardinality definitions = true)
      (hapart : certificate.apartSeparatedB = true)
      (hsingletons : abox.ProxySingletons
        certificate.base.state.quotientCanonical
        (fun individual ↦ Quotient.mk certificate.base.state.nodeSetoid
          (root individual)))
      (hnegative : abox.NegativeRoles
        certificate.base.state.quotientCanonical
        (fun individual ↦ Quotient.mk certificate.base.state.nodeSetoid
          (root individual)))
  | closed
      {nodeCount depth : Nat}
      (certificate : FiniteDistinctEqCertificate
        nodeCount conceptCount roleCount variableCount)
      (tree : FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount depth)
      (hontology : certificate.base.base.ontology = ontology)
      (hinitial : abox.InitializesDistinctState certificate.state)
      (hcheck : tree.checkClosed definitions certificate = true)
  | frontier
      (document : WireRootedCardinalityAddressFrontier)
      (hconcepts : document.concept_count = conceptCount)
      (hroles : document.role_count = roleCount)
      (hdefinitions : document.definition_count = definitions.length)
      (hcheck : document.check = true)

/-- Construct a checked native-ABox cardinality frontier from an injective
root-tagged address map. Root identity is part of the address, so distinct
parentless named individuals may all have the empty path. -/
def CheckedNativeABoxCardinalityOutcome.frontier_of_address
    (address : Fin (8 * 2 ^ budget) → RootedRoleBlockedAddress (Fin rootCount)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitions.length maxWidth)
      (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
      variableCount abox ontology definitions :=
  let document := WireRootedCardinalityAddressFrontier.ofAddress address
  .frontier document rfl rfl rfl
    (document.checkScheduled_check budget rootCount maxWidth
      (WireRootedCardinalityAddressFrontier.ofAddress_checkScheduled
        address hinjective rfl))

/-- One native-ABox cardinality control attempt with checked verdict,
scheduled frontier, or fresh fold rejection. -/
inductive CheckedNativeABoxCardinalityControlAttempt
    (Individual : Type)
    (conceptCount roleCount variableCount : Nat)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (budget rootCount maxWidth : Nat)
    (forbidden : Finset
      (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget))) : Type where
  | sat
      {nodeCount : Nat}
      (certificate : FiniteDistinctEqCertificate
        nodeCount conceptCount roleCount variableCount)
      (root : Individual → Fin nodeCount)
      (hontology : certificate.base.base.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hseeded : abox.SeededIn certificate.state root)
      (hcheck : certificate.base.checkEqSatWithCardinality definitions = true)
      (hapart : certificate.apartSeparatedB = true)
      (hsingletons : abox.ProxySingletons
        certificate.base.state.quotientCanonical
        (fun individual ↦ Quotient.mk certificate.base.state.nodeSetoid
          (root individual)))
      (hnegative : abox.NegativeRoles
        certificate.base.state.quotientCanonical
        (fun individual ↦ Quotient.mk certificate.base.state.nodeSetoid
          (root individual)))
  | closed
      {nodeCount depth : Nat}
      (certificate : FiniteDistinctEqCertificate
        nodeCount conceptCount roleCount variableCount)
      (tree : FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount depth)
      (hontology : certificate.base.base.ontology = ontology)
      (hinitial : abox.InitializesDistinctState certificate.state)
      (hcheck : tree.checkClosed definitions certificate = true)
  | frontier
      (document : WireRootedCardinalityAddressFrontier)
      (hconcepts : document.concept_count = conceptCount)
      (hroles : document.role_count = roleCount)
      (hdefinitions : document.definition_count = definitions.length)
      (hscheduled : document.checkScheduled budget rootCount maxWidth = true)
  | rejected
      (folds : Finset
        (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget)))
      (fresh : ∃ fold ∈ folds, fold ∉ forbidden)

/-- Construct the scheduled native-ABox frontier control attempt directly
from the concrete multi-root cardinality address invariant. -/
def CheckedNativeABoxCardinalityControlAttempt.frontier_of_address
    (address : Fin (8 * 2 ^ budget) → RootedRoleBlockedAddress (Fin rootCount)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitions.length maxWidth)
      (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    CheckedNativeABoxCardinalityControlAttempt Individual conceptCount roleCount
      variableCount abox ontology definitions budget rootCount maxWidth forbidden :=
  let document := WireRootedCardinalityAddressFrontier.ofAddress address
  .frontier document rfl rfl rfl
    (WireRootedCardinalityAddressFrontier.ofAddress_checkScheduled
      address hinjective rfl)

def CheckedNativeABoxCardinalityControlAttempt.toGuarded
    {forbidden : Finset
      (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget))}
    (attempt : CheckedNativeABoxCardinalityControlAttempt Individual conceptCount
      roleCount variableCount abox ontology definitions budget rootCount maxWidth forbidden) :
    GuardedFoldAttempt (Fin (8 * 2 ^ budget))
      (CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
        variableCount abox ontology definitions) forbidden :=
  match attempt with
  | .sat certificate root hontology hnonempty hseeded hcheck hapart
      hsingletons hnegative =>
      .done (.sat certificate root hontology hnonempty hseeded hcheck hapart
        hsingletons hnegative)
  | .closed certificate tree hontology hinitial hcheck =>
      .done (.closed certificate tree hontology hinitial hcheck)
  | .frontier document hconcepts hroles hdefinitions hscheduled =>
      .done (.frontier document hconcepts hroles hdefinitions
        (document.checkScheduled_check budget rootCount maxWidth hscheduled))
  | .rejected folds fresh => .rejected folds fresh

theorem CheckedNativeABoxCardinalityControlAttempt.frontier_scheduled
    {forbidden : Finset
      (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget))}
    (attempt : CheckedNativeABoxCardinalityControlAttempt Individual conceptCount
      roleCount variableCount abox ontology definitions budget rootCount maxWidth forbidden)
    {document : WireRootedCardinalityAddressFrontier}
    {hconcepts : document.concept_count = conceptCount}
    {hroles : document.role_count = roleCount}
    {hdefinitions : document.definition_count = definitions.length}
    {hcheck : document.check = true}
    (herase : attempt.toGuarded.erase = .done
      (.frontier document hconcepts hroles hdefinitions hcheck)) :
    document.checkScheduled budget rootCount maxWidth = true := by
  cases attempt with
  | sat certificate root hontology hnonempty hseeded hcertificate hapart
      hsingletons hnegative =>
      simp [CheckedNativeABoxCardinalityControlAttempt.toGuarded,
        GuardedFoldAttempt.erase] at herase
  | closed certificate tree hontology hinitial hcertificate =>
      simp [CheckedNativeABoxCardinalityControlAttempt.toGuarded,
        GuardedFoldAttempt.erase] at herase
  | frontier frontier frontierConcepts frontierRoles frontierDefinitions hscheduled =>
      simp only [CheckedNativeABoxCardinalityControlAttempt.toGuarded,
        GuardedFoldAttempt.erase] at herase
      cases herase
      exact hscheduled
  | rejected folds fresh =>
      simp [CheckedNativeABoxCardinalityControlAttempt.toGuarded,
        GuardedFoldAttempt.erase] at herase

structure CheckedNativeABoxCardinalityControlProducer
    (Individual : Type)
    (conceptCount roleCount variableCount : Nat)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (budget rootCount maxWidth : Nat) where
  attempt : ∀ forbidden : Finset
      (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget)),
    CheckedNativeABoxCardinalityControlAttempt Individual conceptCount roleCount
      variableCount abox ontology definitions budget rootCount maxWidth forbidden

/-- Build the fixed-budget producer for a concrete address frontier. The same
checked frontier is conclusive for every inner forbidden-fold set because node
exhaustion precedes blocker assignment enumeration. -/
def CheckedNativeABoxCardinalityControlProducer.frontier_of_address
    (address : Fin (8 * 2 ^ budget) → RootedRoleBlockedAddress (Fin rootCount)
      (CardinalityWitnessSlot (Fin conceptCount) (Fin roleCount)
        definitions.length maxWidth)
      (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    CheckedNativeABoxCardinalityControlProducer Individual conceptCount roleCount
      variableCount abox ontology definitions budget rootCount maxWidth where
  attempt forbidden :=
    CheckedNativeABoxCardinalityControlAttempt.frontier_of_address
      (forbidden := forbidden) address hinjective

def CheckedNativeABoxCardinalityControlProducer.toGuarded
    (producer : CheckedNativeABoxCardinalityControlProducer Individual conceptCount
      roleCount variableCount abox ontology definitions budget rootCount maxWidth) :
    GuardedFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
        variableCount abox ontology definitions) where
  attempt forbidden := (producer.attempt forbidden).toGuarded

theorem CheckedNativeABoxCardinalityControlProducer.frontier_scheduled
    (producer : CheckedNativeABoxCardinalityControlProducer Individual conceptCount
      roleCount variableCount abox ontology definitions budget rootCount maxWidth)
    {retry : Nat} {document : WireRootedCardinalityAddressFrontier}
    {hconcepts : document.concept_count = conceptCount}
    {hroles : document.role_count = roleCount}
    {hdefinitions : document.definition_count = definitions.length}
    {hcheck : document.check = true}
    (hrun : producer.toGuarded.toFreshFoldProducer.run retry = .done
      (.frontier document hconcepts hroles hdefinitions hcheck)) :
    document.checkScheduled budget rootCount maxWidth = true := by
  apply CheckedNativeABoxCardinalityControlAttempt.frontier_scheduled
    (producer.attempt
      (producer.toGuarded.toFreshFoldProducer.forbidden retry))
  simpa [GuardedFoldProducer.toFreshFoldProducer, FreshFoldProducer.run,
    CheckedNativeABoxCardinalityControlProducer.toGuarded] using hrun

def CheckedNativeABoxCardinalityOutcome.Semantics
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox ontology definitions) : Prop :=
  match outcome with
  | .sat .. => abox.SatisfiableWithCardinality ontology definitions
  | .closed .. => ¬abox.SatisfiableWithCardinality ontology definitions
  | .frontier .. => False

theorem CheckedNativeABoxCardinalityOutcome.sat_semantics
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    {nodeCount : Nat}
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (root : Individual → Fin nodeCount)
    (hontology : certificate.base.base.ontology = ontology)
    (hnonempty : 0 < nodeCount)
    (hseeded : abox.SeededIn certificate.state root)
    (hcheck : certificate.base.checkEqSatWithCardinality definitions = true)
    (hapart : certificate.apartSeparatedB = true)
    (hsingletons : abox.ProxySingletons
      certificate.base.state.quotientCanonical
      (fun individual ↦ Quotient.mk certificate.base.state.nodeSetoid
        (root individual)))
    (hnegative : abox.NegativeRoles
      certificate.base.state.quotientCanonical
      (fun individual ↦ Quotient.mk certificate.base.state.nodeSetoid
        (root individual))) :
    abox.SatisfiableWithCardinality ontology definitions := by
  letI : Nonempty (Fin nodeCount) := ⟨⟨0, hnonempty⟩⟩
  simpa [hontology] using
    certificate.checkEqSatWithCardinality_native_satisfiable definitions abox
      root hseeded hcheck hapart hsingletons hnegative

theorem CheckedNativeABoxCardinalityOutcome.closed_semantics
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    {nodeCount depth : Nat}
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (hontology : certificate.base.base.ontology = ontology)
    (hinitial : abox.InitializesDistinctState certificate.state)
    (hcheck : tree.checkClosed definitions certificate = true) :
    ¬abox.SatisfiableWithCardinality ontology definitions := by
  have hnot := tree.checkClosed_native_abox_unsatisfiable definitions
    certificate abox hinitial hcheck
  simpa [NativeABox.SatisfiableWithCardinality, hontology] using hnot

def CheckedNativeABoxCardinalityOutcome.SourceSemantics
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (source : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox target definitions) : Prop :=
  match outcome with
  | .sat .. => abox.SatisfiableWithCardinality source definitions
  | .closed .. => ¬abox.SatisfiableWithCardinality source definitions
  | .frontier .. => False

theorem CheckedNativeABoxCardinalityOutcome.source_semantics_of_equivalent
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox target definitions)
    (equivalent : ModelEquivalent source target)
    (hsemantics : outcome.Semantics) :
    outcome.SourceSemantics source := by
  cases outcome with
  | sat certificate root hontology hnonempty hseeded hcheck hapart
      hsingletons hnegative =>
      simp only [CheckedNativeABoxCardinalityOutcome.Semantics,
        CheckedNativeABoxCardinalityOutcome.SourceSemantics,
        NativeABox.SatisfiableWithCardinality] at hsemantics ⊢
      rcases hsemantics with
        ⟨Domain, I, value, hdomain, htarget, hdefinitions, habox⟩
      exact ⟨Domain, I, value, hdomain, (equivalent Domain I).mpr htarget,
        hdefinitions, habox⟩
  | closed certificate tree hontology hinitial hcheck =>
      simp only [CheckedNativeABoxCardinalityOutcome.Semantics,
        CheckedNativeABoxCardinalityOutcome.SourceSemantics,
        NativeABox.SatisfiableWithCardinality] at hsemantics ⊢
      rintro ⟨Domain, I, value, hdomain, hsource, hdefinitions, habox⟩
      exact hsemantics ⟨Domain, I, value, hdomain,
        (equivalent Domain I).mp hsource, hdefinitions, habox⟩
  | frontier document hconcepts hroles hdefinitions hcheck =>
      exact hsemantics

theorem checked_native_abox_cardinality_doubling_decides_source
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (rootCount : Nat)
    (maxWidth : Nat)
    (run : Nat → CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox target definitions)
    (hnodes : ∀ round document hconcepts hroles hdefinitions hcheck,
      run round = .frontier document hconcepts hroles hdefinitions hcheck →
        document.node_count = 8 * 2 ^ round)
    (hroots : ∀ round document hconcepts hroles hdefinitions hcheck,
      run round = .frontier document hconcepts hroles hdefinitions hcheck →
        document.root_count = rootCount)
    (hwidth : ∀ round document hconcepts hroles hdefinitions hcheck,
      run round = .frontier document hconcepts hroles hdefinitions hcheck →
        document.max_width = maxWidth) :
    ∃ round, (run round).SourceSemantics source := by
  classical
  by_contra hdecision
  have hnone : ∀ round, ¬(run round).SourceSemantics source :=
    not_exists.mp hdecision
  have hfrontier : ∀ round, ∃ document hconcepts hroles hdefinitions hcheck,
      run round = .frontier document hconcepts hroles hdefinitions hcheck := by
    intro round
    generalize houtcome : run round = outcome
    cases outcome with
    | sat certificate root hontology hnonempty hseeded hcheck hapart
        hsingletons hnegative =>
        exfalso
        apply hnone round
        rw [houtcome]
        exact (CheckedNativeABoxCardinalityOutcome.source_semantics_of_equivalent
          _ equivalent (CheckedNativeABoxCardinalityOutcome.sat_semantics
            certificate root hontology hnonempty hseeded hcheck hapart
            hsingletons hnegative))
    | closed certificate tree hontology hinitial hcheck =>
        exfalso
        apply hnone round
        rw [houtcome]
        exact (CheckedNativeABoxCardinalityOutcome.source_semantics_of_equivalent
          _ equivalent (CheckedNativeABoxCardinalityOutcome.closed_semantics
            certificate tree hontology hinitial hcheck))
    | frontier document hconcepts hroles hdefinitions hcheck =>
        exact ⟨document, hconcepts, hroles, hdefinitions, hcheck, rfl⟩
  choose document hconcepts hroles hdefinitions hchecks heq using hfrontier
  obtain ⟨round, hrejected⟩ :=
    rooted_cardinality_doubling_eventually_rejects_checked_frontier
      document rootCount conceptCount roleCount definitions.length maxWidth
      (fun round ↦ hnodes round (document round) (hconcepts round)
        (hroles round) (hdefinitions round) (hchecks round) (heq round))
      (fun round ↦ hroots round (document round) (hconcepts round)
        (hroles round) (hdefinitions round) (hchecks round) (heq round))
      hconcepts hroles hdefinitions
      (fun round ↦ hwidth round (document round) (hconcepts round)
        (hroles round) (hdefinitions round) (hchecks round) (heq round))
  exact hrejected (hchecks round)

/-- Native-ABox production also settles all fresh blocker rejections at a fixed
budget before its checked cardinality frontier can justify doubling. -/
theorem checked_native_abox_cardinality_fold_learning_doubling_decides_source
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (rootCount : Nat)
    (maxWidth : Nat)
    (attempt : ∀ budget, Nat → FoldLearningOutcome (Fin (8 * 2 ^ budget))
      (CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
        variableCount abox target definitions))
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
    (hroots : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
      attempt budget retry = .done
        (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.root_count = rootCount)
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
  have hsettledRoots : ∀ budget document hconcepts hroles hdefinitions hcheck,
      settled budget = .frontier document hconcepts hroles hdefinitions hcheck →
        document.root_count = rootCount := by
    intro budget document hconcepts hroles hdefinitions hcheck houtcome
    exact hroots budget (retry budget) document hconcepts hroles hdefinitions hcheck
      (by rw [hsettled budget, houtcome])
  obtain ⟨budget, hsemantics⟩ :=
    checked_native_abox_cardinality_doubling_decides_source equivalent rootCount
      maxWidth settled hsettledNodes hsettledRoots hsettledWidth
  exact ⟨budget, retry budget, settled budget, hsettled budget, hsemantics⟩

theorem checked_native_abox_cardinality_fresh_fold_producer_decides_source
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (rootCount : Nat)
    (maxWidth : Nat)
    (producer : ∀ budget, FreshFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
        variableCount abox target definitions))
    (hnodes : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
      (producer budget).run retry = .done
        (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.node_count = 8 * 2 ^ budget)
    (hroots : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
      (producer budget).run retry = .done
        (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.root_count = rootCount)
    (hwidth : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
      (producer budget).run retry = .done
        (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.max_width = maxWidth) :
    ∃ budget retry outcome,
      (producer budget).run retry = .done outcome ∧
        outcome.SourceSemantics source := by
  exact checked_native_abox_cardinality_fold_learning_doubling_decides_source
    equivalent rootCount maxWidth (fun budget => (producer budget).run)
    (fun budget => (producer budget).forbidden)
    (fun _ _ _ hrun => FreshFoldProducer.rejected_step _ hrun) hnodes hroots hwidth

/-- Native-ABox source-level totality for complete simultaneous blocker
assignments.  Rejection is assignment-indexed, so constituent fold pairs remain
available in other candidates. -/
theorem checked_native_abox_cardinality_fold_assignment_producer_decides_source
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (rootCount : Nat)
    (maxWidth : Nat)
    (producer : ∀ budget, FoldAssignmentProducer (Fin (8 * 2 ^ budget))
      (CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
        variableCount abox target definitions))
    (hnodes : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
      (producer budget).run retry = .done
        (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.node_count = 8 * 2 ^ budget)
    (hroots : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
      (producer budget).run retry = .done
        (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.root_count = rootCount)
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
  have hsettledRoots : ∀ budget document hconcepts hroles hdefinitions hcheck,
      settled budget = .frontier document hconcepts hroles hdefinitions hcheck →
        document.root_count = rootCount := by
    intro budget document hconcepts hroles hdefinitions hcheck houtcome
    exact hroots budget (retry budget) document hconcepts hroles hdefinitions hcheck
      (by rw [hsettled budget, houtcome])
  obtain ⟨budget, hsemantics⟩ :=
    checked_native_abox_cardinality_doubling_decides_source equivalent rootCount
      maxWidth settled hsettledNodes hsettledRoots hsettledWidth
  exact ⟨budget, retry budget, settled budget, hsettled budget, hsemantics⟩

theorem checked_native_abox_cardinality_guarded_fold_assignment_producer_decides_source
    {abox : NativeABox Individual (Fin conceptCount) (Fin roleCount)}
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (rootCount : Nat)
    (maxWidth : Nat)
    (producer : ∀ budget, GuardedFoldAssignmentProducer
      (Fin (8 * 2 ^ budget))
      (CheckedNativeABoxCardinalityOutcome Individual conceptCount roleCount
        variableCount abox target definitions))
    (hnodes : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
      (producer budget).toFoldAssignmentProducer.run retry = .done
        (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.node_count = 8 * 2 ^ budget)
    (hroots : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
      (producer budget).toFoldAssignmentProducer.run retry = .done
        (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.root_count = rootCount)
    (hwidth : ∀ budget retry document hconcepts hroles hdefinitions hcheck,
      (producer budget).toFoldAssignmentProducer.run retry = .done
        (.frontier document hconcepts hroles hdefinitions hcheck) →
        document.max_width = maxWidth) :
    ∃ budget retry outcome,
      (producer budget).toFoldAssignmentProducer.run retry = .done outcome ∧
        outcome.SourceSemantics source := by
  exact checked_native_abox_cardinality_fold_assignment_producer_decides_source
    equivalent rootCount maxWidth
    (fun budget => (producer budget).toFoldAssignmentProducer) hnodes hroots hwidth

/-- Native-ABox cardinality totality with every control-flow obligation stored
by the checked producer. -/
theorem checked_native_abox_cardinality_control_producer_decides_source
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
    ∃ budget retry outcome,
      (producer budget).toGuarded.toFreshFoldProducer.run retry = .done outcome ∧
        outcome.SourceSemantics source := by
  apply checked_native_abox_cardinality_fresh_fold_producer_decides_source
    equivalent rootCount maxWidth
    (fun budget => (producer budget).toGuarded.toFreshFoldProducer)
  · intro budget retry document hconcepts hroles hdefinitions hcheck hrun
    exact document.checkScheduled_node_count budget rootCount maxWidth
      ((producer budget).frontier_scheduled hrun)
  · intro budget retry document hconcepts hroles hdefinitions hcheck hrun
    exact document.checkScheduled_root_count budget rootCount maxWidth
      ((producer budget).frontier_scheduled hrun)
  · intro budget retry document hconcepts hroles hdefinitions hcheck hrun
    exact document.checkScheduled_max_width budget rootCount maxWidth
      ((producer budget).frontier_scheduled hrun)

#print axioms CheckedNativeABoxCardinalityOutcome.sat_semantics
#print axioms CheckedNativeABoxCardinalityOutcome.closed_semantics
#print axioms CheckedNativeABoxCardinalityOutcome.frontier_of_address
#print axioms CheckedNativeABoxCardinalityControlAttempt.frontier_of_address
#print axioms CheckedNativeABoxCardinalityControlProducer.frontier_of_address
#print axioms CheckedNativeABoxCardinalityOutcome.source_semantics_of_equivalent
#print axioms checked_native_abox_cardinality_doubling_decides_source
#print axioms checked_native_abox_cardinality_fold_learning_doubling_decides_source
#print axioms checked_native_abox_cardinality_fold_assignment_producer_decides_source
#print axioms checked_native_abox_cardinality_guarded_fold_assignment_producer_decides_source
#print axioms checked_native_abox_cardinality_fresh_fold_producer_decides_source
#print axioms CheckedNativeABoxCardinalityControlAttempt.frontier_scheduled
#print axioms CheckedNativeABoxCardinalityControlProducer.frontier_scheduled
#print axioms checked_native_abox_cardinality_control_producer_decides_source

end ContextCalculus.Hypertableau
