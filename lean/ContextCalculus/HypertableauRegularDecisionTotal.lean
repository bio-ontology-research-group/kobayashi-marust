import ContextCalculus.HypertableauRegularDecisionWire
import ContextCalculus.HypertableauFrontierWire
import ContextCalculus.HypertableauEqualityFreeDecision
import ContextCalculus.HypertableauRegularProduction
import ContextCalculus.HypertableauNormalizedWire

/-!
# Total checked regular equality-free HT decision

This module closes the semantic mismatch in the earlier equality-free doubling
theorem: a blocked open branch is not an ordinary finite model. Its conclusive
SAT outcome is a checked regular-unravelling certificate, while a closed branch
remains a checked finite refutation. A checked address frontier is the only
inconclusive round, and fixed-vocabulary doubling cannot produce such frontiers
forever.
-/

namespace ContextCalculus.Hypertableau

inductive CheckedRegularRoundOutcome
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) : Type where
  | regularSat
      {nodeCount : Nat}
      (certificate : FiniteRegularCertificate
        nodeCount conceptCount roleCount variableCount)
      (hontology : certificate.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hcheck : certificate.check = true)
  | finiteSat
      {nodeCount : Nat}
      (certificate : FiniteSatCertificate
        nodeCount conceptCount roleCount variableCount)
      (hontology : certificate.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hcheck : certificate.checkSat = true)
  | finiteUnsat
      {nodeCount : Nat}
      (certificate : FiniteSatCertificate
        nodeCount conceptCount roleCount variableCount)
      (tree : FiniteRefutationTree
        nodeCount conceptCount roleCount variableCount)
      (hontology : certificate.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hempty : certificate.EmptyRoot)
      (hcheck : tree.check certificate = true)
  | frontier
      (document : WireAddressFrontier)
      (hconcepts : document.concept_count = conceptCount)
      (hroles : document.role_count = roleCount)
      (hcheck : document.check = true)

/-- Construct the conclusive SAT outcome directly from the concrete blocked
runtime terminal and serializer refinement data. The certificate check is a
theorem result, not an additional producer assumption. -/
def CheckedRegularRoundOutcome.regularSat_of_blocked_runtime_terminal
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {nodeCount : Nat}
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (runtime : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    (blocked : Fin nodeCount → Bool)
    (fold : Fin nodeCount → Fin nodeCount → Prop)
    (hontology : certificate.ontology = ontology)
    (hnonempty : 0 < nodeCount)
    (hstate : certificate.state = runtime)
    (hterminal : runtime.BlockedRuntimeTerminal certificate.residual blocked)
    (hwitnessRefines : runtime.BlockedWitnessRefines blocked fold)
    (hredirectRefines : State.BlockedRedirectRefines blocked fold
      certificate.redirect)
    (hauthorized : ∀ rule ∈ certificate.roleClauses,
      rule.Authorized certificate.rules)
    (hguarded : ∀ clause ∈ certificate.residual, clause.GuardedBody)
    (hshape : ∀ clause ∈ certificate.residual, clause.SingleDirectRoleBody)
    (hheads : ∀ clause ∈ certificate.residual, ∀ atom ∈ clause.head,
      PathLiftableHead atom)
    (hfoldTotal : State.BlockedFoldTotal blocked fold)
    (hfoldPreserves : certificate.state.FoldPreservesLocalFacts fold)
    (hdirect : ∀ clause ∈ certificate.residual,
      certificate.state.DirectCoverForBody certificate.redirect
        certificate.coverRelation clause)
    (hcoverClosed : certificate.CoverClosed)
    :
    CheckedRegularRoundOutcome conceptCount roleCount variableCount ontology :=
  have hlocal : certificate.state.RedirectLocalFacts certificate.redirect :=
    certificate.state.redirectLocalFacts_of_fold blocked fold certificate.redirect
      hfoldTotal hfoldPreserves hredirectRefines
  .regularSat certificate hontology hnonempty
    (certificate.check_of_local_blocked_runtime_terminal runtime blocked fold hstate
      hterminal hwitnessRefines hredirectRefines hauthorized hguarded hshape
      hheads hlocal hdirect hcoverClosed)

def CheckedRegularRoundOutcome.Semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedRegularRoundOutcome
      conceptCount roleCount variableCount ontology) : Prop :=
  match outcome with
  | .regularSat .. => HasNonemptyModel ontology
  | .finiteSat .. => HasNonemptyModel ontology
  | .finiteUnsat .. => ¬HasNonemptyModel ontology
  | .frontier .. => False

/-- Interpret a checked target-ontology round at the source side of a
model-equivalent normalization. This is the statement needed by the public
source-ontology decision boundary. -/
def CheckedRegularRoundOutcome.SourceSemantics
    {target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (source : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (outcome : CheckedRegularRoundOutcome
      conceptCount roleCount variableCount target) : Prop :=
  match outcome with
  | .regularSat .. => HasNonemptyModel source
  | .finiteSat .. => HasNonemptyModel source
  | .finiteUnsat .. => ¬HasNonemptyModel source
  | .frontier .. => False

/-- Exact model equivalence transports both conclusive regular decisions from
the normalized target back to the original source ontology. -/
theorem CheckedRegularRoundOutcome.source_semantics_of_equivalent
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedRegularRoundOutcome
      conceptCount roleCount variableCount target)
    (equivalent : ModelEquivalent source target)
    (hsemantics : outcome.Semantics) :
    outcome.SourceSemantics source := by
  cases outcome with
  | regularSat certificate hontology hnonempty hcheck =>
      simp only [CheckedRegularRoundOutcome.Semantics,
        CheckedRegularRoundOutcome.SourceSemantics] at hsemantics ⊢
      rcases hsemantics with ⟨Domain, I, hdomain, htarget⟩
      exact ⟨Domain, I, hdomain, (equivalent Domain I).mpr htarget⟩
  | finiteSat certificate hontology hnonempty hcheck =>
      simp only [CheckedRegularRoundOutcome.Semantics,
        CheckedRegularRoundOutcome.SourceSemantics] at hsemantics ⊢
      rcases hsemantics with ⟨Domain, I, hdomain, htarget⟩
      exact ⟨Domain, I, hdomain, (equivalent Domain I).mpr htarget⟩
  | finiteUnsat certificate tree hontology hnonempty hempty hcheck =>
      simp only [CheckedRegularRoundOutcome.Semantics,
        CheckedRegularRoundOutcome.SourceSemantics] at hsemantics ⊢
      rintro ⟨Domain, I, hdomain, hsource⟩
      exact hsemantics ⟨Domain, I, hdomain, (equivalent Domain I).mp hsource⟩
  | frontier document hconcepts hroles hcheck =>
      exact hsemantics

theorem CheckedRegularRoundOutcome.regularSat_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {nodeCount : Nat}
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (hontology : certificate.ontology = ontology)
    (hnonempty : 0 < nodeCount)
    (hcheck : certificate.check = true) :
    HasNonemptyModel ontology := by
  letI : NeZero nodeCount := ⟨Nat.ne_of_gt hnonempty⟩
  let Domain := UnravellingDomain certificate.state certificate.redirect
    (fun _ _ _ _ => True) 0
  let interpretation := certificate.state.regularUnravelling
    certificate.redirect (fun _ _ _ _ => True) 0 certificate.rules
  refine ⟨Domain, interpretation, ⟨⟨0, .root⟩⟩, ?_⟩
  simpa [hontology] using certificate.check_models hcheck

theorem CheckedRegularRoundOutcome.finiteSat_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {nodeCount : Nat}
    (certificate : FiniteSatCertificate
      nodeCount conceptCount roleCount variableCount)
    (hontology : certificate.ontology = ontology)
    (hnonempty : 0 < nodeCount)
    (hcheck : certificate.checkSat = true) :
    HasNonemptyModel ontology := by
  letI : Nonempty (Fin nodeCount) := ⟨⟨0, hnonempty⟩⟩
  exact ⟨Fin nodeCount, certificate.state.canonical, inferInstance,
    by simpa [hontology] using certificate.checkSat_models hcheck⟩

theorem CheckedRegularRoundOutcome.finiteUnsat_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {nodeCount : Nat}
    (certificate : FiniteSatCertificate
      nodeCount conceptCount roleCount variableCount)
    (tree : FiniteRefutationTree
      nodeCount conceptCount roleCount variableCount)
    (hontology : certificate.ontology = ontology)
    (hnonempty : 0 < nodeCount)
    (hempty : certificate.EmptyRoot)
    (hcheck : tree.check certificate = true) :
    ¬HasNonemptyModel ontology := by
  letI : Nonempty (Fin nodeCount) := ⟨⟨0, hnonempty⟩⟩
  have hnot := tree.check_ontology_unsatisfiable certificate hempty hcheck
  simpa [HasNonemptyModel, hontology] using hnot

theorem CheckedRegularRoundOutcome.conclusive_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedRegularRoundOutcome
      conceptCount roleCount variableCount ontology) :
    (match outcome with | .frontier .. => False | _ => True) →
      outcome.Semantics := by
  cases outcome with
  | regularSat certificate hontology hnonempty hcheck =>
      intro _
      exact CheckedRegularRoundOutcome.regularSat_semantics certificate
        hontology hnonempty hcheck
  | finiteSat certificate hontology hnonempty hcheck =>
      intro _
      exact CheckedRegularRoundOutcome.finiteSat_semantics certificate
        hontology hnonempty hcheck
  | finiteUnsat certificate tree hontology hnonempty hempty hcheck =>
      intro _
      exact CheckedRegularRoundOutcome.finiteUnsat_semantics certificate tree
        hontology hnonempty hempty hcheck
  | frontier document hconcepts hroles hcheck => simp

/-- Every checked round either decides the exact normalized ontology or
publishes a checked full address frontier. Under KM's doubling schedule, some
round therefore produces a semantically correct regular SAT model or finite
UNSAT refutation. -/
theorem checked_regular_doubling_decides
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (run : Nat → CheckedRegularRoundOutcome
      conceptCount roleCount variableCount ontology)
    (hnodes : ∀ round document hconcepts hroles hcheck,
      run round = .frontier document hconcepts hroles hcheck →
        document.node_count = 8 * 2 ^ round) :
    ∃ round, (run round).Semantics := by
  classical
  by_contra hconclusive
  have hnone : ∀ round, ¬(run round).Semantics :=
    not_exists.mp hconclusive
  have hfrontier : ∀ round, ∃ document hconcepts hroles hcheck,
      run round = .frontier document hconcepts hroles hcheck := by
    intro round
    generalize houtcome : run round = outcome
    cases outcome with
    | regularSat certificate hontology hnonempty hcheck =>
        exfalso
        exact hnone round (by
          rw [houtcome]
          exact CheckedRegularRoundOutcome.regularSat_semantics certificate
            hontology hnonempty hcheck)
    | finiteSat certificate hontology hnonempty hcheck =>
        exfalso
        exact hnone round (by
          rw [houtcome]
          exact CheckedRegularRoundOutcome.finiteSat_semantics certificate
            hontology hnonempty hcheck)
    | finiteUnsat certificate tree hontology hnonempty hempty hcheck =>
        exfalso
        exact hnone round (by
          rw [houtcome]
          exact CheckedRegularRoundOutcome.finiteUnsat_semantics certificate
            tree hontology hnonempty hempty hcheck)
    | frontier document hconcepts hroles hcheck =>
        exact ⟨document, hconcepts, hroles, hcheck, rfl⟩
  choose document hconcepts hroles hchecks heq using hfrontier
  obtain ⟨round, hrejected⟩ :=
    mode6_doubling_eventually_rejects_checked_frontier
      document conceptCount roleCount
      (fun round => hnodes round (document round) (hconcepts round)
        (hroles round) (hchecks round) (heq round))
      hconcepts hroles
  exact hrejected (hchecks round)

/-- Totality of the actual two-level equality-free producer shape. At each
doubling budget, rejected blocker candidates are learned away until one
checked round outcome remains. Those settled outcomes then satisfy the outer
address-frontier doubling theorem. -/
theorem checked_regular_fold_learning_doubling_decides
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (attempt : ∀ budget, Nat → FoldLearningOutcome (Fin (8 * 2 ^ budget))
      (CheckedRegularRoundOutcome conceptCount roleCount variableCount ontology))
    (forbidden : ∀ budget,
      Nat → Finset (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget)))
    (hlearn : ∀ budget retry folds,
      attempt budget retry = .rejected folds →
        forbidden budget (retry + 1) = forbidden budget retry ∪ folds ∧
          ∃ fold ∈ folds, fold ∉ forbidden budget retry)
    (hnodes : ∀ budget retry document hconcepts hroles hcheck,
      attempt budget retry = .done
        (.frontier document hconcepts hroles hcheck) →
      document.node_count = 8 * 2 ^ budget) :
    ∃ budget retry outcome,
      attempt budget retry = .done outcome ∧ outcome.Semantics := by
  have hsettles : ∀ budget, ∃ retry outcome,
      attempt budget retry = .done outcome := by
    intro budget
    exact fold_learning_eventually_done (attempt budget) (forbidden budget)
      (hlearn budget)
  choose retry settled hsettled using hsettles
  have hsettledNodes : ∀ budget document hconcepts hroles hcheck,
      settled budget = .frontier document hconcepts hroles hcheck →
        document.node_count = 8 * 2 ^ budget := by
    intro budget document hconcepts hroles hcheck houtcome
    exact hnodes budget (retry budget) document hconcepts hroles hcheck
      (by rw [hsettled budget, houtcome])
  obtain ⟨budget, hsemantics⟩ :=
    checked_regular_doubling_decides settled hsettledNodes
  exact ⟨budget, retry budget, settled budget, hsettled budget, hsemantics⟩

/-- Source-level totality for the checked equality-free regular route. Under
KM's doubling schedule, a target normalization that is model-equivalent to the
source eventually yields the correct SAT or UNSAT statement for the source. -/
theorem checked_regular_doubling_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (run : Nat → CheckedRegularRoundOutcome
      conceptCount roleCount variableCount target)
    (hnodes : ∀ round document hconcepts hroles hcheck,
      run round = .frontier document hconcepts hroles hcheck →
        document.node_count = 8 * 2 ^ round) :
    ∃ round, (run round).SourceSemantics source := by
  obtain ⟨round, hsemantics⟩ := checked_regular_doubling_decides run hnodes
  exact ⟨round, (run round).source_semantics_of_equivalent equivalent hsemantics⟩

/-- Source-level form of the concrete learned-fold producer theorem. This is
the equality-free global-route capstone used by production: internal rejected
folds terminate, checked frontiers drive doubling, and a conclusive normalized
result transports across the exact source projection. -/
theorem checked_regular_fold_learning_doubling_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (attempt : ∀ budget, Nat → FoldLearningOutcome (Fin (8 * 2 ^ budget))
      (CheckedRegularRoundOutcome conceptCount roleCount variableCount target))
    (forbidden : ∀ budget,
      Nat → Finset (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget)))
    (hlearn : ∀ budget retry folds,
      attempt budget retry = .rejected folds →
        forbidden budget (retry + 1) = forbidden budget retry ∪ folds ∧
          ∃ fold ∈ folds, fold ∉ forbidden budget retry)
    (hnodes : ∀ budget retry document hconcepts hroles hcheck,
      attempt budget retry = .done
        (.frontier document hconcepts hroles hcheck) →
      document.node_count = 8 * 2 ^ budget) :
    ∃ budget retry outcome,
      attempt budget retry = .done outcome ∧ outcome.SourceSemantics source := by
  obtain ⟨budget, retry, outcome, hattempt, hsemantics⟩ :=
    checked_regular_fold_learning_doubling_decides attempt forbidden hlearn hnodes
  exact ⟨budget, retry, outcome, hattempt,
    outcome.source_semantics_of_equivalent equivalent hsemantics⟩

/-- Concrete fixed-budget retry form: blacklist evolution and fresh-fold
progress are derived from `FreshFoldProducer`, leaving only the checked
frontier dimensions as an outer producer-refinement obligation. -/
theorem checked_regular_fresh_fold_producer_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (producer : ∀ budget, FreshFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedRegularRoundOutcome conceptCount roleCount variableCount target))
    (hnodes : ∀ budget retry document hconcepts hroles hcheck,
      (producer budget).run retry = .done
        (.frontier document hconcepts hroles hcheck) →
      document.node_count = 8 * 2 ^ budget) :
    ∃ budget retry outcome,
      (producer budget).run retry = .done outcome ∧
        outcome.SourceSemantics source := by
  exact checked_regular_fold_learning_doubling_decides_source equivalent
    (fun budget => (producer budget).run)
    (fun budget => (producer budget).forbidden)
    (fun _ _ _ hrun => FreshFoldProducer.rejected_step _ hrun) hnodes

/-- Wire-scheduled source capstone. Frontier dimensions are recovered from the
executable serialized schedule check, removing the free node-count equality
from the equality-free global producer boundary. -/
theorem checked_regular_scheduled_fresh_fold_producer_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (producer : ∀ budget, FreshFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedRegularRoundOutcome conceptCount roleCount variableCount target))
    (hscheduled : ∀ budget retry document hconcepts hroles hcheck,
      (producer budget).run retry = .done
        (.frontier document hconcepts hroles hcheck) →
      document.checkScheduled budget = true) :
    ∃ budget retry outcome,
      (producer budget).run retry = .done outcome ∧
        outcome.SourceSemantics source := by
  apply checked_regular_fresh_fold_producer_decides_source equivalent producer
  intro budget retry document hconcepts hroles hcheck hrun
  exact document.checkScheduled_node_count budget
    (hscheduled budget retry document hconcepts hroles hcheck hrun)

/-- Rust-branch form of the equality-free source capstone. Fresh rejection is
carried by `GuardedFoldAttempt`, then erased into the generic finite-learning
proof; callers no longer construct or justify a `FreshFoldProducer`. -/
theorem checked_regular_guarded_fold_producer_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (producer : ∀ budget, GuardedFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedRegularRoundOutcome conceptCount roleCount variableCount target))
    (hscheduled : ∀ budget retry document hconcepts hroles hcheck,
      ((producer budget).toFreshFoldProducer.run retry) = .done
        (.frontier document hconcepts hroles hcheck) →
      document.checkScheduled budget = true) :
    ∃ budget retry outcome,
      (producer budget).toFreshFoldProducer.run retry = .done outcome ∧
        outcome.SourceSemantics source := by
  exact checked_regular_scheduled_fresh_fold_producer_decides_source equivalent
    (fun budget => (producer budget).toFreshFoldProducer) hscheduled

#print axioms CheckedRegularRoundOutcome.regularSat_semantics
#print axioms CheckedRegularRoundOutcome.finiteSat_semantics
#print axioms CheckedRegularRoundOutcome.finiteUnsat_semantics
#print axioms CheckedRegularRoundOutcome.conclusive_semantics
#print axioms checked_regular_doubling_decides
#print axioms checked_regular_fold_learning_doubling_decides
#print axioms CheckedRegularRoundOutcome.source_semantics_of_equivalent
#print axioms checked_regular_doubling_decides_source
#print axioms checked_regular_fold_learning_doubling_decides_source
#print axioms checked_regular_fresh_fold_producer_decides_source
#print axioms checked_regular_scheduled_fresh_fold_producer_decides_source
#print axioms checked_regular_guarded_fold_producer_decides_source

end ContextCalculus.Hypertableau
