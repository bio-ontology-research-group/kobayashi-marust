import ContextCalculus.HypertableauRegularDecisionWire
import ContextCalculus.HypertableauFrontierWire
import ContextCalculus.HypertableauAddressRefinement
import ContextCalculus.HypertableauEqualityFreeDecision
import ContextCalculus.HypertableauRegularProduction
import ContextCalculus.HypertableauNormalizedWire
import ContextCalculus.HypertableauRegularRouteProduction

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

/-- Construct an accepted regular frontier outcome from the mathematical
rooted-address invariant. The wire payload and checker proof are generated in
Lean rather than supplied by the runtime producer. -/
def CheckedRegularRoundOutcome.frontier_of_address
    (address : Fin (8 * 2 ^ budget) →
      WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    CheckedRegularRoundOutcome conceptCount roleCount variableCount ontology :=
  let document := WireAddressFrontier.ofAddress address
  .frontier document rfl rfl
    (document.checkScheduled_check budget
      (WireAddressFrontier.ofAddress_checkScheduled address hinjective rfl))

/-- Settle one complete equality-free production search using semantic search
results plus the concrete rooted-address refinement. Closure and frontier wire
evidence are constructed here; neither is accepted as a producer-selected
Boolean result. -/
noncomputable def finiteProductionRoundSettlement
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
      CheckedRegularRoundOutcome conceptCount roleCount variableCount ontology ⊕
        ProductionBlockedLeafAt (Fin (8 * 2 ^ budget)) (Fin conceptCount)
          (Fin roleCount) (Fin variableCount) ontology forbidden := by
  classical
  apply finiteProductionSearchSettlement ontology parent ancestors hheads root
  · intro _forbidden hrefutes
    subst root
    exact Classical.choice (show Nonempty
        (CheckedRegularRoundOutcome conceptCount roleCount variableCount ontology)
        from by
      obtain ⟨certificate, tree, hontology, hnodes, hempty, hcheck⟩ :=
        hrefutes.exists_checked_empty_root_certificate ontology (by positivity)
      exact ⟨.finiteUnsat certificate tree hontology hnodes hempty hcheck⟩)
  · intro forbidden leaf hdescends hfrontier
    exact Classical.choice (show Nonempty
        (CheckedRegularRoundOutcome conceptCount roleCount variableCount ontology)
        from by
      obtain ⟨address, hrefines⟩ :=
        frontierAddress forbidden leaf hdescends hfrontier
      have hrefines' :=
        (stateOfGuardedFacts leaf).checkRootedAddressRefines_sound address hrefines
      exact ⟨CheckedRegularRoundOutcome.frontier_of_address address hrefines'.1⟩)

/-- Construct KM's exact checked regular-UNSAT outcome directly from the
semantic refutation returned by exhaustive finite search at the empty global
root. The finite certificate, recursive tree, empty-root proof, and Boolean
checker acceptance are all derived in Lean. -/
noncomputable def CheckedRegularRoundOutcome.finiteUnsat_of_empty_root_refutes
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (hnonempty : 0 < nodeCount)
    (hrefutes : Refutes (Fin nodeCount) ontology
      (stateOfGuardedFacts
        (∅ : Finset (GuardedFact (Fin nodeCount) (Fin conceptCount)
          (Fin roleCount))))) :
    CheckedRegularRoundOutcome conceptCount roleCount variableCount ontology := by
  exact Classical.choice (show Nonempty
      (CheckedRegularRoundOutcome conceptCount roleCount variableCount ontology)
      from by
    obtain ⟨certificate, tree, hontology, hnodes, hempty, hcheck⟩ :=
      hrefutes.exists_checked_empty_root_certificate ontology hnonempty
    exact ⟨.finiteUnsat certificate tree hontology hnodes hempty hcheck⟩)

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

/-- Construct a conclusive regular-SAT outcome from the exact cover-aware
terminal condition. Unlike the local producer constructor, this accepts any
guarded residual body once runtime cover saturation has been established. -/
def CheckedRegularRoundOutcome.regularSat_of_cover_saturated_runtime_terminal
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
    (hheads : ∀ clause ∈ certificate.residual, ∀ atom ∈ clause.head,
      PathLiftableHead atom)
    (hcoverClosed : certificate.CoverClosed)
    (hcoverSaturated : ∀ clause ∈ certificate.residual,
      certificate.state.CoverDischarges certificate.coverRelation clause) :
    CheckedRegularRoundOutcome conceptCount roleCount variableCount ontology :=
  .regularSat certificate hontology hnonempty
    (certificate.check_of_cover_saturated_runtime_terminal runtime blocked fold
      hstate hterminal hwitnessRefines hredirectRefines hauthorized hguarded
      hheads hcoverClosed hcoverSaturated)

/-- Construct the conclusive regular-SAT outcome for the final retry with no
blocker folds.  This is the concrete endpoint of KM's two-level fold search:
once every blocked source has no selected fold, fold-table totality forces all
sources to be unblocked, so the runtime terminal already contains ordinary
witnesses for every existential obligation.  The regular checker therefore
cannot reject this candidate under the serializer's role-cover invariants. -/
def CheckedRegularRoundOutcome.regularSat_of_fold_free_runtime_terminal
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
    (hfoldTotal : State.BlockedFoldTotal blocked fold)
    (hfoldFree : ∀ source blocker, ¬ fold source blocker)
    (hredirect : certificate.redirect = id)
    (hauthorized : ∀ rule ∈ certificate.roleClauses,
      rule.Authorized certificate.rules)
    (hguarded : ∀ clause ∈ certificate.residual, clause.GuardedBody)
    (hheads : ∀ clause ∈ certificate.residual, ∀ atom ∈ clause.head,
      PathLiftableHead atom)
    (hcoverClosed : certificate.CoverClosed)
    (hcoverGenerated : certificate.CoverGenerated)
    (hroleClosed : certificate.state.RoleClosed certificate.rules) :
    CheckedRegularRoundOutcome conceptCount roleCount variableCount ontology :=
  .regularSat certificate hontology hnonempty
    (certificate.check_of_fold_free_roleClosed_runtime_terminal runtime blocked
      fold hstate
      hterminal hfoldTotal hfoldFree hredirect hauthorized hguarded hheads
      hcoverClosed hcoverGenerated hroleClosed)

/-- Complete checked result of one Rust equality-free control attempt. Every
accepted serializer branch stores the proof returned by its Lean checker;
frontiers additionally store the executable schedule check. Rejection stores
the exact candidate folds and a successful fresh insertion. -/
inductive CheckedRegularControlAttempt
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (budget : Nat)
    (forbidden : Finset
      (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget))) : Type where
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
      (hscheduled : document.checkScheduled budget = true)
  | rejected
      (folds : Finset
        (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget)))
      (fresh : ∃ fold ∈ folds, fold ∉ forbidden)

/-- Construct the scheduled control frontier directly from an injective
rooted-address map at the current production budget. -/
def CheckedRegularControlAttempt.frontier_of_address
    (address : Fin (8 * 2 ^ budget) →
      WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount))
    (hinjective : Function.Injective address) :
    CheckedRegularControlAttempt conceptCount roleCount variableCount ontology
      budget forbidden :=
  let document := WireAddressFrontier.ofAddress address
  .frontier document rfl rfl
    (WireAddressFrontier.ofAddress_checkScheduled address hinjective rfl)

def CheckedRegularControlAttempt.toGuarded
    {forbidden : Finset
      (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget))}
    (attempt : CheckedRegularControlAttempt conceptCount roleCount variableCount
      ontology budget forbidden) :
    GuardedFoldAttempt (Fin (8 * 2 ^ budget))
      (CheckedRegularRoundOutcome conceptCount roleCount variableCount ontology)
      forbidden :=
  match attempt with
  | .regularSat certificate hontology hnonempty hcheck =>
      .done (.regularSat certificate hontology hnonempty hcheck)
  | .finiteSat certificate hontology hnonempty hcheck =>
      .done (.finiteSat certificate hontology hnonempty hcheck)
  | .finiteUnsat certificate tree hontology hnonempty hempty hcheck =>
      .done (.finiteUnsat certificate tree hontology hnonempty hempty hcheck)
  | .frontier document hconcepts hroles hscheduled =>
      .done (.frontier document hconcepts hroles
        (document.checkScheduled_check budget hscheduled))
  | .rejected folds fresh => .rejected folds fresh

theorem CheckedRegularControlAttempt.frontier_scheduled
    {forbidden : Finset
      (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget))}
    (attempt : CheckedRegularControlAttempt conceptCount roleCount variableCount
      ontology budget forbidden)
    {document : WireAddressFrontier}
    {hconcepts : document.concept_count = conceptCount}
    {hroles : document.role_count = roleCount}
    {hcheck : document.check = true}
    (herase : attempt.toGuarded.erase = .done
      (.frontier document hconcepts hroles hcheck)) :
    document.checkScheduled budget = true := by
  cases attempt with
  | regularSat certificate hontology hnonempty hcertificate =>
      simp [CheckedRegularControlAttempt.toGuarded,
        GuardedFoldAttempt.erase] at herase
  | finiteSat certificate hontology hnonempty hcertificate =>
      simp [CheckedRegularControlAttempt.toGuarded,
        GuardedFoldAttempt.erase] at herase
  | finiteUnsat certificate tree hontology hnonempty hempty hcertificate =>
      simp [CheckedRegularControlAttempt.toGuarded,
        GuardedFoldAttempt.erase] at herase
  | frontier frontier frontierConcepts frontierRoles hscheduled =>
      simp only [CheckedRegularControlAttempt.toGuarded,
        GuardedFoldAttempt.erase] at herase
      cases herase
      exact hscheduled
  | rejected folds fresh =>
      simp [CheckedRegularControlAttempt.toGuarded,
        GuardedFoldAttempt.erase] at herase

/-- Fixed-budget Rust control family. The blacklist indexes each attempt, so
its erasure constructs the guarded producer expected by the termination proof
without any additional producer-refinement assumptions. -/
structure CheckedRegularControlProducer
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (budget : Nat) where
  attempt : ∀ forbidden : Finset
      (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget)),
    CheckedRegularControlAttempt conceptCount roleCount variableCount ontology
      budget forbidden

def CheckedRegularControlProducer.toGuarded
    (producer : CheckedRegularControlProducer conceptCount roleCount variableCount
      ontology budget) :
    GuardedFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedRegularRoundOutcome conceptCount roleCount variableCount ontology) where
  attempt forbidden := (producer.attempt forbidden).toGuarded

theorem CheckedRegularControlProducer.frontier_scheduled
    (producer : CheckedRegularControlProducer conceptCount roleCount variableCount
      ontology budget)
    {retry : Nat} {document : WireAddressFrontier}
    {hconcepts : document.concept_count = conceptCount}
    {hroles : document.role_count = roleCount}
    {hcheck : document.check = true}
    (hrun : producer.toGuarded.toFreshFoldProducer.run retry = .done
      (.frontier document hconcepts hroles hcheck)) :
    document.checkScheduled budget = true := by
  apply CheckedRegularControlAttempt.frontier_scheduled
    (producer.attempt
      (producer.toGuarded.toFreshFoldProducer.forbidden retry))
  simpa [GuardedFoldProducer.toFreshFoldProducer, FreshFoldProducer.run,
    CheckedRegularControlProducer.toGuarded] using hrun

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

/-- Source-level capstone for the production control actually used by KM:
checker rejection learns one complete simultaneous fold assignment. -/
theorem checked_regular_fold_assignment_producer_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (producer : ∀ budget, FoldAssignmentProducer (Fin (8 * 2 ^ budget))
      (CheckedRegularRoundOutcome conceptCount roleCount variableCount target))
    (hnodes : ∀ budget retry document hconcepts hroles hcheck,
      (producer budget).run retry = .done
        (.frontier document hconcepts hroles hcheck) →
      document.node_count = 8 * 2 ^ budget) :
    ∃ budget retry outcome,
      (producer budget).run retry = .done outcome ∧
        outcome.SourceSemantics source := by
  have hsettles : ∀ budget, ∃ retry outcome,
      (producer budget).run retry = .done outcome := fun budget =>
    (producer budget).eventually_done
  choose retry settled hsettled using hsettles
  have hsettledNodes : ∀ budget document hconcepts hroles hcheck,
      settled budget = .frontier document hconcepts hroles hcheck →
        document.node_count = 8 * 2 ^ budget := by
    intro budget document hconcepts hroles hcheck houtcome
    exact hnodes budget (retry budget) document hconcepts hroles hcheck
      (by rw [hsettled budget, houtcome])
  obtain ⟨budget, hsemantics⟩ :=
    checked_regular_doubling_decides_source equivalent settled hsettledNodes
  exact ⟨budget, retry budget, settled budget, hsettled budget, hsemantics⟩

theorem checked_regular_scheduled_fold_assignment_producer_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (producer : ∀ budget, FoldAssignmentProducer (Fin (8 * 2 ^ budget))
      (CheckedRegularRoundOutcome conceptCount roleCount variableCount target))
    (hscheduled : ∀ budget retry document hconcepts hroles hcheck,
      (producer budget).run retry = .done
        (.frontier document hconcepts hroles hcheck) →
      document.checkScheduled budget = true) :
    ∃ budget retry outcome,
      (producer budget).run retry = .done outcome ∧
        outcome.SourceSemantics source := by
  apply checked_regular_fold_assignment_producer_decides_source equivalent producer
  intro budget retry document hconcepts hroles hcheck hrun
  exact document.checkScheduled_node_count budget
    (hscheduled budget retry document hconcepts hroles hcheck hrun)

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

/-- Fully checked Rust-control form of the equality-free source capstone.
Fresh fold progress and the exact frontier-doubling schedule are both carried
by the producer's branch type, so totality has no residual control-flow
premises beyond model equivalence of preprocessing. -/
theorem checked_regular_control_producer_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (producer : ∀ budget,
      CheckedRegularControlProducer conceptCount roleCount variableCount
        target budget) :
    ∃ budget retry outcome,
      (producer budget).toGuarded.toFreshFoldProducer.run retry = .done outcome ∧
        outcome.SourceSemantics source := by
  apply checked_regular_guarded_fold_producer_decides_source equivalent
    (fun budget => (producer budget).toGuarded)
  intro budget retry document hconcepts hroles hcheck hrun
  exact (producer budget).frontier_scheduled hrun

#print axioms CheckedRegularRoundOutcome.regularSat_semantics
#print axioms CheckedRegularRoundOutcome.finiteSat_semantics
#print axioms CheckedRegularRoundOutcome.finiteUnsat_semantics
#print axioms CheckedRegularRoundOutcome.finiteUnsat_of_empty_root_refutes
#print axioms CheckedRegularRoundOutcome.frontier_of_address
#print axioms finiteProductionRoundSettlement
#print axioms CheckedRegularRoundOutcome.conclusive_semantics
#print axioms checked_regular_doubling_decides
#print axioms checked_regular_fold_learning_doubling_decides
#print axioms CheckedRegularRoundOutcome.source_semantics_of_equivalent
#print axioms checked_regular_doubling_decides_source
#print axioms checked_regular_fold_learning_doubling_decides_source
#print axioms checked_regular_fresh_fold_producer_decides_source
#print axioms checked_regular_fold_assignment_producer_decides_source
#print axioms checked_regular_scheduled_fold_assignment_producer_decides_source
#print axioms checked_regular_scheduled_fresh_fold_producer_decides_source
#print axioms checked_regular_guarded_fold_producer_decides_source
#print axioms CheckedRegularControlAttempt.frontier_scheduled
#print axioms CheckedRegularControlAttempt.frontier_of_address
#print axioms CheckedRegularControlProducer.frontier_scheduled
#print axioms checked_regular_control_producer_decides_source

end ContextCalculus.Hypertableau
