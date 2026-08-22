import ContextCalculus.HypertableauTaxonomyCertificate
import ContextCalculus.HypertableauFrontierWire
import ContextCalculus.HypertableauCardinalityTaxonomyWire
import ContextCalculus.HypertableauNativeABoxTaxonomy
import ContextCalculus.HypertableauNativeABoxCardinalityTaxonomyWire
import ContextCalculus.HypertableauRegularProduction

/-!
# Total production hypertableau taxonomy search

Production classification runs one checked, iteratively deepened decision
search for every named concept and every ordered named-concept pair.  The
certificate family used by a cell may differ, but its checker must refine the
cell to the exact semantic proposition or its negation.  A checked node-budget
frontier remains a non-verdict.

This module composes those cell searches into one complete taxonomy.  In
particular, completeness cannot be inferred from the positive cells alone:
every negative concept and non-subsumption cell must also terminate with a
checked countermodel.
-/

namespace ContextCalculus.Hypertableau

/-- The common checked result of one production taxonomy search round.  The
`holds` and `refutes` constructors are reached only after the selected wire
checker has produced the corresponding semantic theorem. -/
inductive CheckedTaxonomyRoundOutcome
    (conceptCount roleCount : Nat) (statement : Prop) : Type where
  | holds (proof : statement)
  | refutes (proof : ¬statement)
  | frontier
      (document : WireAddressFrontier)
      (hconcepts : document.concept_count = conceptCount)
      (hroles : document.role_count = roleCount)
      (hcheck : document.check = true)

def CheckedTaxonomyRoundOutcome.Semantics
    (outcome : CheckedTaxonomyRoundOutcome conceptCount roleCount statement) : Prop :=
  match outcome with
  | .holds .. => statement
  | .refutes .. => ¬statement
  | .frontier .. => False

/-- Embed a checker-produced concept decision in the common production-round
result. -/
def CheckedTaxonomyRoundOutcome.ofConceptDecision
    (decision : ConceptDecision ontology concept) :
    CheckedTaxonomyRoundOutcome conceptCount roleCount
      (UnsatisfiableConcept ontology concept) :=
  match decision with
  | .unsatisfiable proof => .holds proof
  | .satisfiable counterexample => .refutes counterexample

/-- Embed a checker-produced subsumption decision in the common
production-round result. -/
def CheckedTaxonomyRoundOutcome.ofSubsumptionDecision
    (decision : SubsumptionDecision ontology sub sup) :
    CheckedTaxonomyRoundOutcome conceptCount roleCount
      (EntailsSub ontology sub sup) :=
  match decision with
  | .entailed proof => .holds proof
  | .notEntailed counterexample => .refutes counterexample

theorem CheckedTaxonomyRoundOutcome.conclusive_semantics
    (outcome : CheckedTaxonomyRoundOutcome conceptCount roleCount statement) :
    (match outcome with | .frontier .. => False | _ => True) →
      outcome.Semantics := by
  cases outcome with
  | holds proof => exact fun _ => proof
  | refutes proof => exact fun _ => proof
  | frontier document hconcepts hroles hcheck => simp

/-- Checked mode-6 frontiers cannot persist through the production doubling
schedule.  Therefore one round proves the cell proposition or its negation. -/
theorem checked_taxonomy_doubling_decides
    (run : Nat → CheckedTaxonomyRoundOutcome conceptCount roleCount statement)
    (hnodes : ∀ round document hconcepts hroles hcheck,
      run round = .frontier document hconcepts hroles hcheck →
        document.node_count = 8 * 2 ^ round) :
    ∃ round, (run round).Semantics := by
  classical
  by_contra hconclusive
  have hnone : ∀ round, ¬(run round).Semantics := not_exists.mp hconclusive
  have hfrontier : ∀ round, ∃ document hconcepts hroles hcheck,
      run round = .frontier document hconcepts hroles hcheck := by
    intro round
    generalize houtcome : run round = outcome
    cases outcome with
    | holds proof =>
        exact False.elim (hnone round (by
          rw [houtcome]
          exact proof))
    | refutes proof =>
        exact False.elim (hnone round (by
          rw [houtcome]
          exact proof))
    | frontier document hconcepts hroles hcheck =>
        exact ⟨document, hconcepts, hroles, hcheck, rfl⟩
  choose document hconcepts hroles hchecks heq using hfrontier
  obtain ⟨round, hrejected⟩ :=
    mode6_doubling_eventually_rejects_checked_frontier
      document _ _
      (fun round => hnodes round (document round) (hconcepts round)
        (hroles round) (hchecks round) (heq round))
      hconcepts hroles
  exact hrejected (hchecks round)

/-- Totality of the two-level production taxonomy search used by Rust. At a
fixed node budget, rejected blocker certificates add a fresh forbidden fold
until a checked cell outcome remains. Checked frontiers alone advance the
outer doubling schedule. Consequently one retry at one budget proves either
the cell statement or its negation. -/
theorem checked_taxonomy_fresh_fold_producer_decides
    (producer : ∀ budget, FreshFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount statement))
    (hnodes : ∀ budget retry document hconcepts hroles hcheck,
      (producer budget).run retry = .done
        (.frontier document hconcepts hroles hcheck) →
      document.node_count = 8 * 2 ^ budget) :
    ∃ budget retry outcome,
      (producer budget).run retry = .done outcome ∧ outcome.Semantics := by
  have hsettles : ∀ budget, ∃ retry outcome,
      (producer budget).run retry = .done outcome := by
    intro budget
    exact (producer budget).eventually_done
  choose retry settled hsettled using hsettles
  have hsettledNodes : ∀ budget document hconcepts hroles hcheck,
      settled budget = .frontier document hconcepts hroles hcheck →
        document.node_count = 8 * 2 ^ budget := by
    intro budget document hconcepts hroles hcheck houtcome
    exact hnodes budget (retry budget) document hconcepts hroles hcheck
      (by rw [hsettled budget, houtcome])
  obtain ⟨budget, hsemantics⟩ :=
    checked_taxonomy_doubling_decides settled hsettledNodes
  exact ⟨budget, retry budget, settled budget, hsettled budget, hsemantics⟩

theorem checked_taxonomy_fold_assignment_producer_decides
    (producer : ∀ budget, FoldAssignmentProducer (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount statement))
    (hnodes : ∀ budget retry document hconcepts hroles hcheck,
      (producer budget).run retry = .done
        (.frontier document hconcepts hroles hcheck) →
      document.node_count = 8 * 2 ^ budget) :
    ∃ budget retry outcome,
      (producer budget).run retry = .done outcome ∧ outcome.Semantics := by
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
    checked_taxonomy_doubling_decides settled hsettledNodes
  exact ⟨budget, retry budget, settled budget, hsettled budget, hsemantics⟩

/-- Eliminate the proved two-level search into any proof-carrying decision
type. `Nonempty` keeps the elimination constructive at the public boundary
while the selected terminating budget and retry remain implementation detail. -/
theorem checked_taxonomy_fresh_fold_producer_decision
    (producer : ∀ budget, FreshFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount statement))
    (hnodes : ∀ budget retry document hconcepts hroles hcheck,
      (producer budget).run retry = .done
        (.frontier document hconcepts hroles hcheck) →
      document.node_count = 8 * 2 ^ budget)
    (ofHolds : statement → Decision)
    (ofRefutes : ¬statement → Decision) : Nonempty Decision := by
  classical
  have hresult : Nonempty { selected :
      Nat × Nat × CheckedTaxonomyRoundOutcome conceptCount roleCount statement //
    (producer selected.1).run selected.2.1 = .done selected.2.2 ∧
      selected.2.2.Semantics } := by
    rcases checked_taxonomy_fresh_fold_producer_decides producer hnodes with
      ⟨budget, retry, outcome, hrun, hsemantics⟩
    exact ⟨⟨(budget, retry, outcome), hrun, hsemantics⟩⟩
  let selected := Classical.choice hresult
  have hsemantics := selected.property.2
  generalize houtcome : selected.1.2.2 = outcome at hsemantics
  cases outcome with
  | holds proof => exact ⟨ofHolds hsemantics⟩
  | refutes proof => exact ⟨ofRefutes hsemantics⟩
  | frontier document hconcepts hroles hcheck =>
      simp only [CheckedTaxonomyRoundOutcome.Semantics] at hsemantics

theorem checked_taxonomy_fold_assignment_producer_decision
    (producer : ∀ budget, FoldAssignmentProducer (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount statement))
    (hnodes : ∀ budget retry document hconcepts hroles hcheck,
      (producer budget).run retry = .done
        (.frontier document hconcepts hroles hcheck) →
      document.node_count = 8 * 2 ^ budget)
    (ofHolds : statement → Decision)
    (ofRefutes : ¬statement → Decision) : Nonempty Decision := by
  classical
  rcases checked_taxonomy_fold_assignment_producer_decides producer hnodes with
    ⟨budget, retry, outcome, hrun, hsemantics⟩
  cases outcome with
  | holds proof => exact ⟨ofHolds hsemantics⟩
  | refutes proof => exact ⟨ofRefutes hsemantics⟩
  | frontier document hconcepts hroles hcheck =>
      simp only [CheckedTaxonomyRoundOutcome.Semantics] at hsemantics

theorem checked_taxonomy_scheduled_fold_assignment_producer_decision
    (producer : ∀ budget, FoldAssignmentProducer (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount statement))
    (hscheduled : ∀ budget retry document hconcepts hroles hcheck,
      (producer budget).run retry = .done
        (.frontier document hconcepts hroles hcheck) →
      document.checkScheduled budget = true)
    (ofHolds : statement → Decision)
    (ofRefutes : ¬statement → Decision) : Nonempty Decision := by
  apply checked_taxonomy_fold_assignment_producer_decision producer _ ofHolds ofRefutes
  intro budget retry document hconcepts hroles hcheck hrun
  exact document.checkScheduled_node_count budget
    (hscheduled budget retry document hconcepts hroles hcheck hrun)

/-- Constructor-guarded production form of complete-assignment learning. -/
theorem checked_taxonomy_scheduled_guarded_fold_assignment_producer_decision
    (producer : ∀ budget, GuardedFoldAssignmentProducer
      (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount statement))
    (hscheduled : ∀ budget retry document hconcepts hroles hcheck,
      (producer budget).toFoldAssignmentProducer.run retry = .done
        (.frontier document hconcepts hroles hcheck) →
      document.checkScheduled budget = true)
    (ofHolds : statement → Decision)
    (ofRefutes : ¬statement → Decision) : Nonempty Decision := by
  exact checked_taxonomy_scheduled_fold_assignment_producer_decision
    (fun budget => (producer budget).toFoldAssignmentProducer)
    hscheduled ofHolds ofRefutes

/-- Production complete-assignment search in which every rejected assignment
is both fresh and generated from the current source-major Cartesian blocker
options. -/
theorem checked_taxonomy_scheduled_cartesian_fold_assignment_producer_decision
    (producer : ∀ budget, CartesianFoldAssignmentRuntime
      (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount statement))
    (hscheduled : ∀ budget retry document hconcepts hroles hcheck,
      (producer budget).toProducer.toGuarded.toFoldAssignmentProducer.run retry = .done
        (.frontier document hconcepts hroles hcheck) →
      document.checkScheduled budget = true)
    (ofHolds : statement → Decision)
    (ofRefutes : ¬statement → Decision) : Nonempty Decision := by
  exact checked_taxonomy_scheduled_guarded_fold_assignment_producer_decision
    (fun budget => (producer budget).toProducer.toGuarded)
    hscheduled ofHolds ofRefutes

/-- Serialized-frontier form of the producer theorem. The exact doubling
dimension is extracted from an executable schedule check rather than supplied
as a free equality premise. -/
theorem checked_taxonomy_scheduled_fresh_fold_producer_decision
    (producer : ∀ budget, FreshFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount statement))
    (hscheduled : ∀ budget retry document hconcepts hroles hcheck,
      (producer budget).run retry = .done
        (.frontier document hconcepts hroles hcheck) →
      document.checkScheduled budget = true)
    (ofHolds : statement → Decision)
    (ofRefutes : ¬statement → Decision) : Nonempty Decision := by
  apply checked_taxonomy_fresh_fold_producer_decision producer _ ofHolds ofRefutes
  intro budget retry document hconcepts hroles hcheck hrun
  exact document.checkScheduled_node_count budget
    (hscheduled budget retry document hconcepts hroles hcheck hrun)

/-- Rust-branch taxonomy form: checker rejection is represented by a guarded
attempt whose type already records the successful fresh-fold insertion. -/
theorem checked_taxonomy_scheduled_guarded_fold_producer_decision
    (producer : ∀ budget, GuardedFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount statement))
    (hscheduled : ∀ budget retry document hconcepts hroles hcheck,
      (producer budget).toFreshFoldProducer.run retry = .done
        (.frontier document hconcepts hroles hcheck) →
      document.checkScheduled budget = true)
    (ofHolds : statement → Decision)
    (ofRefutes : ¬statement → Decision) : Nonempty Decision := by
  exact checked_taxonomy_scheduled_fresh_fold_producer_decision
    (fun budget => (producer budget).toFreshFoldProducer)
    hscheduled ofHolds ofRefutes

/-- All checked searches used to construct one production taxonomy.  Each
field is indexed by the exact source-level query that its result decides. -/
structure CertifiedHTProductionTaxonomyRoute
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (named : List (Fin conceptCount)) where
  conceptRun : ∀ concept, concept ∈ named → Nat →
    CheckedTaxonomyRoundOutcome conceptCount roleCount
      (UnsatisfiableConcept ontology concept)
  conceptNodes : ∀ concept hnamed round document hconcepts hroles hcheck,
    conceptRun concept hnamed round =
        .frontier document hconcepts hroles hcheck →
      document.node_count = 8 * 2 ^ round
  subsumptionRun : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named → Nat →
    CheckedTaxonomyRoundOutcome conceptCount roleCount
      (EntailsSub ontology sub sup)
  subsumptionNodes : ∀ sub hsub sup hsup round document hconcepts hroles hcheck,
    subsumptionRun sub hsub sup hsup round =
        .frontier document hconcepts hroles hcheck →
      document.node_count = 8 * 2 ^ round

/-- Every production taxonomy route decides every required cell and therefore
constructs a complete exact named taxonomy. -/
theorem CertifiedHTProductionTaxonomyRoute.decides
    (route : CertifiedHTProductionTaxonomyRoute conceptCount roleCount
      variableCount ontology named) :
    Nonempty (CompleteTaxonomyCertificate ontology named) := by
  classical
  refine ⟨{
    concept := ?_
    subsumption := ?_
  }⟩
  · intro concept hnamed
    have hround : Nonempty { round //
        (route.conceptRun concept hnamed round).Semantics } := by
      rcases checked_taxonomy_doubling_decides
          (route.conceptRun concept hnamed)
          (route.conceptNodes concept hnamed) with ⟨round, hsemantics⟩
      exact ⟨⟨round, hsemantics⟩⟩
    let selected := Classical.choice hround
    let round := selected.1
    have hsemantics := selected.2
    generalize houtcome : route.conceptRun concept hnamed round = outcome at hsemantics
    cases outcome with
    | holds proof => exact .unsatisfiable hsemantics
    | refutes proof => exact .satisfiable hsemantics
    | frontier document hconcepts hroles hcheck =>
      simp only [CheckedTaxonomyRoundOutcome.Semantics] at hsemantics

  · intro sub hsub sup hsup
    have hround : Nonempty { round //
        (route.subsumptionRun sub hsub sup hsup round).Semantics } := by
      rcases checked_taxonomy_doubling_decides
          (route.subsumptionRun sub hsub sup hsup)
          (route.subsumptionNodes sub hsub sup hsup) with ⟨round, hsemantics⟩
      exact ⟨⟨round, hsemantics⟩⟩
    let selected := Classical.choice hround
    let round := selected.1
    have hsemantics := selected.2
    generalize houtcome : route.subsumptionRun sub hsub sup hsup round = outcome at hsemantics
    cases outcome with
    | holds proof => exact .entailed hsemantics
    | refutes proof => exact .notEntailed hsemantics
    | frontier document hconcepts hroles hcheck =>
        simp only [CheckedTaxonomyRoundOutcome.Semantics] at hsemantics

/-- Production equality-free taxonomy route with Rust's concrete inner
learned-fold loop represented explicitly for every concept and subsumption
cell. The route no longer assumes that a single search attempt per node budget
has already settled. -/
structure CertifiedHTFreshFoldProductionTaxonomyRoute
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (named : List (Fin conceptCount)) where
  conceptProducer : ∀ concept, concept ∈ named → ∀ budget,
    GuardedFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount
        (UnsatisfiableConcept ontology concept))
  conceptScheduled : ∀ concept hnamed budget retry document hconcepts hroles hcheck,
    (conceptProducer concept hnamed budget).toFreshFoldProducer.run retry =
        .done (.frontier document hconcepts hroles hcheck) →
      document.checkScheduled budget = true
  subsumptionProducer : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named →
    ∀ budget, GuardedFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount
        (EntailsSub ontology sub sup))
  subsumptionScheduled :
    ∀ sub hsub sup hsup budget retry document hconcepts hroles hcheck,
      (subsumptionProducer sub hsub sup hsup budget).toFreshFoldProducer.run retry =
          .done (.frontier document hconcepts hroles hcheck) →
        document.checkScheduled budget = true

theorem CertifiedHTFreshFoldProductionTaxonomyRoute.decides
    (route : CertifiedHTFreshFoldProductionTaxonomyRoute conceptCount roleCount
      variableCount ontology named) :
    Nonempty (CompleteTaxonomyCertificate ontology named) := by
  classical
  refine ⟨{ concept := ?_, subsumption := ?_ }⟩
  · intro concept hnamed
    exact Classical.choice (checked_taxonomy_scheduled_guarded_fold_producer_decision
      (route.conceptProducer concept hnamed)
      (route.conceptScheduled concept hnamed)
      ConceptDecision.unsatisfiable ConceptDecision.satisfiable)
  · intro sub hsub sup hsup
    exact Classical.choice (checked_taxonomy_scheduled_guarded_fold_producer_decision
      (route.subsumptionProducer sub hsub sup hsup)
      (route.subsumptionScheduled sub hsub sup hsup)
      SubsumptionDecision.entailed SubsumptionDecision.notEntailed)

/-- Cardinality-aware production taxonomy searches.  The semantic index keeps
the normalized number restrictions in every cell. -/
structure CertifiedHTCardinalityProductionTaxonomyRoute
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (named : List (Fin conceptCount)) where
  conceptRun : ∀ concept, concept ∈ named → Nat →
    CheckedTaxonomyRoundOutcome conceptCount roleCount
      (UnsatisfiableConceptWithCardinality ontology definitions concept)
  conceptNodes : ∀ concept hnamed round document hconcepts hroles hcheck,
    conceptRun concept hnamed round =
        .frontier document hconcepts hroles hcheck →
      document.node_count = 8 * 2 ^ round
  subsumptionRun : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named → Nat →
    CheckedTaxonomyRoundOutcome conceptCount roleCount
      (EntailsSubWithCardinality ontology definitions sub sup)
  subsumptionNodes : ∀ sub hsub sup hsup round document hconcepts hroles hcheck,
    subsumptionRun sub hsub sup hsup round =
        .frontier document hconcepts hroles hcheck →
      document.node_count = 8 * 2 ^ round

theorem CertifiedHTCardinalityProductionTaxonomyRoute.decides
    (route : CertifiedHTCardinalityProductionTaxonomyRoute conceptCount roleCount
      variableCount ontology definitions named) :
    Nonempty (CompleteCardinalityTaxonomyCertificate ontology definitions named) := by
  classical
  refine ⟨{ concept := ?_, subsumption := ?_ }⟩
  · intro concept hnamed
    have hround : Nonempty { round //
        (route.conceptRun concept hnamed round).Semantics } := by
      rcases checked_taxonomy_doubling_decides
          (route.conceptRun concept hnamed)
          (route.conceptNodes concept hnamed) with ⟨round, hsemantics⟩
      exact ⟨⟨round, hsemantics⟩⟩
    let selected := Classical.choice hround
    let round := selected.1
    have hsemantics := selected.2
    generalize houtcome : route.conceptRun concept hnamed round = outcome at hsemantics
    cases outcome with
    | holds proof => exact .unsatisfiable hsemantics
    | refutes proof => exact .satisfiable hsemantics
    | frontier document hconcepts hroles hcheck =>
        simp only [CheckedTaxonomyRoundOutcome.Semantics] at hsemantics
  · intro sub hsub sup hsup
    have hround : Nonempty { round //
        (route.subsumptionRun sub hsub sup hsup round).Semantics } := by
      rcases checked_taxonomy_doubling_decides
          (route.subsumptionRun sub hsub sup hsup)
          (route.subsumptionNodes sub hsub sup hsup) with ⟨round, hsemantics⟩
      exact ⟨⟨round, hsemantics⟩⟩
    let selected := Classical.choice hround
    let round := selected.1
    have hsemantics := selected.2
    generalize houtcome : route.subsumptionRun sub hsub sup hsup round = outcome at hsemantics
    cases outcome with
    | holds proof => exact .entailed hsemantics
    | refutes proof => exact .notEntailed hsemantics
    | frontier document hconcepts hroles hcheck =>
        simp only [CheckedTaxonomyRoundOutcome.Semantics] at hsemantics

/-- Native-ABox production taxonomy searches.  Every cell is interpreted
jointly with the same complete ABox rather than against the TBox alone. -/
structure CertifiedHTNativeABoxProductionTaxonomyRoute
    (conceptCount roleCount variableCount : Nat)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (named : List (Fin conceptCount)) where
  conceptRun : ∀ concept, concept ∈ named → Nat →
    CheckedTaxonomyRoundOutcome conceptCount roleCount
      (abox.UnsatisfiableConceptWith ontology concept)
  conceptNodes : ∀ concept hnamed round document hconcepts hroles hcheck,
    conceptRun concept hnamed round =
        .frontier document hconcepts hroles hcheck →
      document.node_count = 8 * 2 ^ round
  subsumptionRun : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named → Nat →
    CheckedTaxonomyRoundOutcome conceptCount roleCount
      (abox.EntailsSubWith ontology sub sup)
  subsumptionNodes : ∀ sub hsub sup hsup round document hconcepts hroles hcheck,
    subsumptionRun sub hsub sup hsup round =
        .frontier document hconcepts hroles hcheck →
      document.node_count = 8 * 2 ^ round

theorem CertifiedHTNativeABoxProductionTaxonomyRoute.decides
    (route : CertifiedHTNativeABoxProductionTaxonomyRoute conceptCount roleCount
      variableCount abox ontology named) :
    Nonempty (CompleteNativeABoxTaxonomyCertificate abox ontology named) := by
  classical
  refine ⟨{ concept := ?_, subsumption := ?_ }⟩
  · intro concept hnamed
    have hround : Nonempty { round //
        (route.conceptRun concept hnamed round).Semantics } := by
      rcases checked_taxonomy_doubling_decides
          (route.conceptRun concept hnamed)
          (route.conceptNodes concept hnamed) with ⟨round, hsemantics⟩
      exact ⟨⟨round, hsemantics⟩⟩
    let selected := Classical.choice hround
    let round := selected.1
    have hsemantics := selected.2
    generalize houtcome : route.conceptRun concept hnamed round = outcome at hsemantics
    cases outcome with
    | holds proof => exact .unsatisfiable hsemantics
    | refutes proof => exact .satisfiable hsemantics
    | frontier document hconcepts hroles hcheck =>
        simp only [CheckedTaxonomyRoundOutcome.Semantics] at hsemantics

  · intro sub hsub sup hsup
    have hround : Nonempty { round //
        (route.subsumptionRun sub hsub sup hsup round).Semantics } := by
      rcases checked_taxonomy_doubling_decides
          (route.subsumptionRun sub hsub sup hsup)
          (route.subsumptionNodes sub hsub sup hsup) with ⟨round, hsemantics⟩
      exact ⟨⟨round, hsemantics⟩⟩
    let selected := Classical.choice hround
    let round := selected.1
    have hsemantics := selected.2
    generalize houtcome : route.subsumptionRun sub hsub sup hsup round = outcome at hsemantics
    cases outcome with
    | holds proof => exact .entailed hsemantics
    | refutes proof => exact .notEntailed hsemantics
    | frontier document hconcepts hroles hcheck =>
        simp only [CheckedTaxonomyRoundOutcome.Semantics] at hsemantics

/-- The fourth production family combines first-class cardinalities with the
complete native ABox in every taxonomy query. -/
structure CertifiedHTNativeABoxCardinalityProductionTaxonomyRoute
    (conceptCount roleCount variableCount : Nat)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (named : List (Fin conceptCount)) where
  conceptRun : ∀ concept, concept ∈ named → Nat →
    CheckedTaxonomyRoundOutcome conceptCount roleCount
      (abox.UnsatisfiableConceptWithCardinality ontology definitions concept)
  conceptNodes : ∀ concept hnamed round document hconcepts hroles hcheck,
    conceptRun concept hnamed round =
        .frontier document hconcepts hroles hcheck →
      document.node_count = 8 * 2 ^ round
  subsumptionRun : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named → Nat →
    CheckedTaxonomyRoundOutcome conceptCount roleCount
      (abox.EntailsSubWithCardinality ontology definitions sub sup)
  subsumptionNodes : ∀ sub hsub sup hsup round document hconcepts hroles hcheck,
    subsumptionRun sub hsub sup hsup round =
        .frontier document hconcepts hroles hcheck →
      document.node_count = 8 * 2 ^ round

theorem CertifiedHTNativeABoxCardinalityProductionTaxonomyRoute.decides
    (route : CertifiedHTNativeABoxCardinalityProductionTaxonomyRoute
      conceptCount roleCount variableCount abox ontology definitions named) :
    Nonempty (CompleteNativeABoxCardinalityTaxonomyCertificate
      abox ontology definitions named) := by
  classical
  refine ⟨{ concept := ?_, subsumption := ?_ }⟩
  · intro concept hnamed
    have hround : Nonempty { round //
        (route.conceptRun concept hnamed round).Semantics } := by
      rcases checked_taxonomy_doubling_decides
          (route.conceptRun concept hnamed)
          (route.conceptNodes concept hnamed) with ⟨round, hsemantics⟩
      exact ⟨⟨round, hsemantics⟩⟩
    let selected := Classical.choice hround
    let round := selected.1
    have hsemantics := selected.2
    generalize houtcome : route.conceptRun concept hnamed round = outcome at hsemantics
    cases outcome with
    | holds proof => exact .unsatisfiable hsemantics
    | refutes proof => exact .satisfiable hsemantics
    | frontier document hconcepts hroles hcheck =>
        simp only [CheckedTaxonomyRoundOutcome.Semantics] at hsemantics
  · intro sub hsub sup hsup
    have hround : Nonempty { round //
        (route.subsumptionRun sub hsub sup hsup round).Semantics } := by
      rcases checked_taxonomy_doubling_decides
          (route.subsumptionRun sub hsub sup hsup)
          (route.subsumptionNodes sub hsub sup hsup) with ⟨round, hsemantics⟩
      exact ⟨⟨round, hsemantics⟩⟩
    let selected := Classical.choice hround
    let round := selected.1
    have hsemantics := selected.2
    generalize houtcome : route.subsumptionRun sub hsub sup hsup round = outcome at hsemantics
    cases outcome with
    | holds proof => exact .entailed hsemantics
    | refutes proof => exact .notEntailed hsemantics
    | frontier document hconcepts hroles hcheck =>
        simp only [CheckedTaxonomyRoundOutcome.Semantics] at hsemantics

/-! ## Explicit learned-fold production routes for every taxonomy family -/

structure CertifiedHTFreshFoldCardinalityProductionTaxonomyRoute
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (named : List (Fin conceptCount)) where
  conceptProducer : ∀ concept, concept ∈ named → ∀ budget,
    GuardedFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount
        (UnsatisfiableConceptWithCardinality ontology definitions concept))
  conceptScheduled : ∀ concept hnamed budget retry document hconcepts hroles hcheck,
    (conceptProducer concept hnamed budget).toFreshFoldProducer.run retry =
        .done (.frontier document hconcepts hroles hcheck) →
      document.checkScheduled budget = true
  subsumptionProducer : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named →
    ∀ budget, GuardedFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount
        (EntailsSubWithCardinality ontology definitions sub sup))
  subsumptionScheduled :
    ∀ sub hsub sup hsup budget retry document hconcepts hroles hcheck,
      (subsumptionProducer sub hsub sup hsup budget).toFreshFoldProducer.run retry =
          .done (.frontier document hconcepts hroles hcheck) →
        document.checkScheduled budget = true

theorem CertifiedHTFreshFoldCardinalityProductionTaxonomyRoute.decides
    (route : CertifiedHTFreshFoldCardinalityProductionTaxonomyRoute
      conceptCount roleCount variableCount ontology definitions named) :
    Nonempty (CompleteCardinalityTaxonomyCertificate ontology definitions named) := by
  classical
  refine ⟨{ concept := ?_, subsumption := ?_ }⟩
  · intro concept hnamed
    exact Classical.choice (checked_taxonomy_scheduled_guarded_fold_producer_decision
      (route.conceptProducer concept hnamed) (route.conceptScheduled concept hnamed)
      CardinalityConceptDecision.unsatisfiable
      CardinalityConceptDecision.satisfiable)
  · intro sub hsub sup hsup
    exact Classical.choice (checked_taxonomy_scheduled_guarded_fold_producer_decision
      (route.subsumptionProducer sub hsub sup hsup)
      (route.subsumptionScheduled sub hsub sup hsup)
      CardinalitySubsumptionDecision.entailed
      CardinalitySubsumptionDecision.notEntailed)

structure CertifiedHTFreshFoldNativeABoxProductionTaxonomyRoute
    (conceptCount roleCount variableCount : Nat)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (named : List (Fin conceptCount)) where
  conceptProducer : ∀ concept, concept ∈ named → ∀ budget,
    GuardedFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount
        (abox.UnsatisfiableConceptWith ontology concept))
  conceptScheduled : ∀ concept hnamed budget retry document hconcepts hroles hcheck,
    (conceptProducer concept hnamed budget).toFreshFoldProducer.run retry =
        .done (.frontier document hconcepts hroles hcheck) →
      document.checkScheduled budget = true
  subsumptionProducer : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named →
    ∀ budget, GuardedFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount
        (abox.EntailsSubWith ontology sub sup))
  subsumptionScheduled :
    ∀ sub hsub sup hsup budget retry document hconcepts hroles hcheck,
      (subsumptionProducer sub hsub sup hsup budget).toFreshFoldProducer.run retry =
          .done (.frontier document hconcepts hroles hcheck) →
        document.checkScheduled budget = true

theorem CertifiedHTFreshFoldNativeABoxProductionTaxonomyRoute.decides
    (route : CertifiedHTFreshFoldNativeABoxProductionTaxonomyRoute
      conceptCount roleCount variableCount abox ontology named) :
    Nonempty (CompleteNativeABoxTaxonomyCertificate abox ontology named) := by
  classical
  refine ⟨{ concept := ?_, subsumption := ?_ }⟩
  · intro concept hnamed
    exact Classical.choice (checked_taxonomy_scheduled_guarded_fold_producer_decision
      (route.conceptProducer concept hnamed) (route.conceptScheduled concept hnamed)
      NativeABoxConceptDecision.unsatisfiable
      NativeABoxConceptDecision.satisfiable)
  · intro sub hsub sup hsup
    exact Classical.choice (checked_taxonomy_scheduled_guarded_fold_producer_decision
      (route.subsumptionProducer sub hsub sup hsup)
      (route.subsumptionScheduled sub hsub sup hsup)
      NativeABoxSubsumptionDecision.entailed
      NativeABoxSubsumptionDecision.notEntailed)

structure CertifiedHTFreshFoldNativeABoxCardinalityProductionTaxonomyRoute
    (conceptCount roleCount variableCount : Nat)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (named : List (Fin conceptCount)) where
  conceptProducer : ∀ concept, concept ∈ named → ∀ budget,
    GuardedFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount
        (abox.UnsatisfiableConceptWithCardinality ontology definitions concept))
  conceptScheduled : ∀ concept hnamed budget retry document hconcepts hroles hcheck,
    (conceptProducer concept hnamed budget).toFreshFoldProducer.run retry =
        .done (.frontier document hconcepts hroles hcheck) →
      document.checkScheduled budget = true
  subsumptionProducer : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named →
    ∀ budget, GuardedFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount
        (abox.EntailsSubWithCardinality ontology definitions sub sup))
  subsumptionScheduled :
    ∀ sub hsub sup hsup budget retry document hconcepts hroles hcheck,
      (subsumptionProducer sub hsub sup hsup budget).toFreshFoldProducer.run retry =
          .done (.frontier document hconcepts hroles hcheck) →
        document.checkScheduled budget = true

theorem CertifiedHTFreshFoldNativeABoxCardinalityProductionTaxonomyRoute.decides
    (route : CertifiedHTFreshFoldNativeABoxCardinalityProductionTaxonomyRoute
      conceptCount roleCount variableCount abox ontology definitions named) :
    Nonempty (CompleteNativeABoxCardinalityTaxonomyCertificate
      abox ontology definitions named) := by
  classical
  refine ⟨{ concept := ?_, subsumption := ?_ }⟩
  · intro concept hnamed
    exact Classical.choice (checked_taxonomy_scheduled_guarded_fold_producer_decision
      (route.conceptProducer concept hnamed) (route.conceptScheduled concept hnamed)
      NativeABoxCardinalityConceptDecision.unsatisfiable
      NativeABoxCardinalityConceptDecision.satisfiable)
  · intro sub hsub sup hsup
    exact Classical.choice (checked_taxonomy_scheduled_guarded_fold_producer_decision
      (route.subsumptionProducer sub hsub sup hsup)
      (route.subsumptionScheduled sub hsub sup hsup)
      NativeABoxCardinalitySubsumptionDecision.entailed
      NativeABoxCardinalitySubsumptionDecision.notEntailed)

/-! ## Complete-assignment production routes

These are the production interfaces used by the current Rust search.  A
checker rejection excludes one complete simultaneous fold assignment, not the
individual pairs occurring in that assignment. -/

structure CertifiedHTFoldAssignmentProductionTaxonomyRoute
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (named : List (Fin conceptCount)) where
  conceptProducer : ∀ concept, concept ∈ named → ∀ budget,
    CartesianFoldAssignmentRuntime (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount
        (UnsatisfiableConcept ontology concept))
  conceptScheduled : ∀ concept hnamed budget retry document hconcepts hroles hcheck,
    (conceptProducer concept hnamed budget).toProducer.toGuarded.toFoldAssignmentProducer.run retry =
        .done (.frontier document hconcepts hroles hcheck) →
      document.checkScheduled budget = true
  subsumptionProducer : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named →
    ∀ budget, CartesianFoldAssignmentRuntime (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount
        (EntailsSub ontology sub sup))
  subsumptionScheduled :
    ∀ sub hsub sup hsup budget retry document hconcepts hroles hcheck,
      (subsumptionProducer sub hsub sup hsup budget).toProducer.toGuarded.toFoldAssignmentProducer.run retry =
          .done (.frontier document hconcepts hroles hcheck) →
        document.checkScheduled budget = true

theorem CertifiedHTFoldAssignmentProductionTaxonomyRoute.decides
    (route : CertifiedHTFoldAssignmentProductionTaxonomyRoute conceptCount
      roleCount variableCount ontology named) :
    Nonempty (CompleteTaxonomyCertificate ontology named) := by
  classical
  refine ⟨{ concept := ?_, subsumption := ?_ }⟩
  · intro concept hnamed
    exact Classical.choice (checked_taxonomy_scheduled_cartesian_fold_assignment_producer_decision
      (route.conceptProducer concept hnamed)
      (route.conceptScheduled concept hnamed)
      ConceptDecision.unsatisfiable ConceptDecision.satisfiable)
  · intro sub hsub sup hsup
    exact Classical.choice (checked_taxonomy_scheduled_cartesian_fold_assignment_producer_decision
      (route.subsumptionProducer sub hsub sup hsup)
      (route.subsumptionScheduled sub hsub sup hsup)
      SubsumptionDecision.entailed SubsumptionDecision.notEntailed)

structure CertifiedHTFoldAssignmentCardinalityProductionTaxonomyRoute
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (named : List (Fin conceptCount)) where
  conceptProducer : ∀ concept, concept ∈ named → ∀ budget,
    CartesianFoldAssignmentRuntime (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount
        (UnsatisfiableConceptWithCardinality ontology definitions concept))
  conceptScheduled : ∀ concept hnamed budget retry document hconcepts hroles hcheck,
    (conceptProducer concept hnamed budget).toProducer.toGuarded.toFoldAssignmentProducer.run retry =
        .done (.frontier document hconcepts hroles hcheck) →
      document.checkScheduled budget = true
  subsumptionProducer : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named →
    ∀ budget, CartesianFoldAssignmentRuntime (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount
        (EntailsSubWithCardinality ontology definitions sub sup))
  subsumptionScheduled :
    ∀ sub hsub sup hsup budget retry document hconcepts hroles hcheck,
      (subsumptionProducer sub hsub sup hsup budget).toProducer.toGuarded.toFoldAssignmentProducer.run retry =
          .done (.frontier document hconcepts hroles hcheck) →
        document.checkScheduled budget = true

theorem CertifiedHTFoldAssignmentCardinalityProductionTaxonomyRoute.decides
    (route : CertifiedHTFoldAssignmentCardinalityProductionTaxonomyRoute
      conceptCount roleCount variableCount ontology definitions named) :
    Nonempty (CompleteCardinalityTaxonomyCertificate ontology definitions named) := by
  classical
  refine ⟨{ concept := ?_, subsumption := ?_ }⟩
  · intro concept hnamed
    exact Classical.choice (checked_taxonomy_scheduled_cartesian_fold_assignment_producer_decision
      (route.conceptProducer concept hnamed)
      (route.conceptScheduled concept hnamed)
      CardinalityConceptDecision.unsatisfiable
      CardinalityConceptDecision.satisfiable)
  · intro sub hsub sup hsup
    exact Classical.choice (checked_taxonomy_scheduled_cartesian_fold_assignment_producer_decision
      (route.subsumptionProducer sub hsub sup hsup)
      (route.subsumptionScheduled sub hsub sup hsup)
      CardinalitySubsumptionDecision.entailed
      CardinalitySubsumptionDecision.notEntailed)

structure CertifiedHTFoldAssignmentNativeABoxProductionTaxonomyRoute
    (conceptCount roleCount variableCount : Nat)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (named : List (Fin conceptCount)) where
  conceptProducer : ∀ concept, concept ∈ named → ∀ budget,
    CartesianFoldAssignmentRuntime (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount
        (abox.UnsatisfiableConceptWith ontology concept))
  conceptScheduled : ∀ concept hnamed budget retry document hconcepts hroles hcheck,
    (conceptProducer concept hnamed budget).toProducer.toGuarded.toFoldAssignmentProducer.run retry =
        .done (.frontier document hconcepts hroles hcheck) →
      document.checkScheduled budget = true
  subsumptionProducer : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named →
    ∀ budget, CartesianFoldAssignmentRuntime (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount
        (abox.EntailsSubWith ontology sub sup))
  subsumptionScheduled :
    ∀ sub hsub sup hsup budget retry document hconcepts hroles hcheck,
      (subsumptionProducer sub hsub sup hsup budget).toProducer.toGuarded.toFoldAssignmentProducer.run retry =
          .done (.frontier document hconcepts hroles hcheck) →
        document.checkScheduled budget = true

theorem CertifiedHTFoldAssignmentNativeABoxProductionTaxonomyRoute.decides
    (route : CertifiedHTFoldAssignmentNativeABoxProductionTaxonomyRoute
      conceptCount roleCount variableCount abox ontology named) :
    Nonempty (CompleteNativeABoxTaxonomyCertificate abox ontology named) := by
  classical
  refine ⟨{ concept := ?_, subsumption := ?_ }⟩
  · intro concept hnamed
    exact Classical.choice (checked_taxonomy_scheduled_cartesian_fold_assignment_producer_decision
      (route.conceptProducer concept hnamed)
      (route.conceptScheduled concept hnamed)
      NativeABoxConceptDecision.unsatisfiable
      NativeABoxConceptDecision.satisfiable)
  · intro sub hsub sup hsup
    exact Classical.choice (checked_taxonomy_scheduled_cartesian_fold_assignment_producer_decision
      (route.subsumptionProducer sub hsub sup hsup)
      (route.subsumptionScheduled sub hsub sup hsup)
      NativeABoxSubsumptionDecision.entailed
      NativeABoxSubsumptionDecision.notEntailed)

structure CertifiedHTFoldAssignmentNativeABoxCardinalityProductionTaxonomyRoute
    (conceptCount roleCount variableCount : Nat)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (named : List (Fin conceptCount)) where
  conceptProducer : ∀ concept, concept ∈ named → ∀ budget,
    CartesianFoldAssignmentRuntime (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount
        (abox.UnsatisfiableConceptWithCardinality ontology definitions concept))
  conceptScheduled : ∀ concept hnamed budget retry document hconcepts hroles hcheck,
    (conceptProducer concept hnamed budget).toProducer.toGuarded.toFoldAssignmentProducer.run retry =
        .done (.frontier document hconcepts hroles hcheck) →
      document.checkScheduled budget = true
  subsumptionProducer : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named →
    ∀ budget, CartesianFoldAssignmentRuntime (Fin (8 * 2 ^ budget))
      (CheckedTaxonomyRoundOutcome conceptCount roleCount
        (abox.EntailsSubWithCardinality ontology definitions sub sup))
  subsumptionScheduled :
    ∀ sub hsub sup hsup budget retry document hconcepts hroles hcheck,
      (subsumptionProducer sub hsub sup hsup budget).toProducer.toGuarded.toFoldAssignmentProducer.run retry =
          .done (.frontier document hconcepts hroles hcheck) →
        document.checkScheduled budget = true

theorem CertifiedHTFoldAssignmentNativeABoxCardinalityProductionTaxonomyRoute.decides
    (route : CertifiedHTFoldAssignmentNativeABoxCardinalityProductionTaxonomyRoute
      conceptCount roleCount variableCount abox ontology definitions named) :
    Nonempty (CompleteNativeABoxCardinalityTaxonomyCertificate
      abox ontology definitions named) := by
  classical
  refine ⟨{ concept := ?_, subsumption := ?_ }⟩
  · intro concept hnamed
    exact Classical.choice (checked_taxonomy_scheduled_cartesian_fold_assignment_producer_decision
      (route.conceptProducer concept hnamed)
      (route.conceptScheduled concept hnamed)
      NativeABoxCardinalityConceptDecision.unsatisfiable
      NativeABoxCardinalityConceptDecision.satisfiable)
  · intro sub hsub sup hsup
    exact Classical.choice (checked_taxonomy_scheduled_cartesian_fold_assignment_producer_decision
      (route.subsumptionProducer sub hsub sup hsup)
      (route.subsumptionScheduled sub hsub sup hsup)
      NativeABoxCardinalitySubsumptionDecision.entailed
      NativeABoxCardinalitySubsumptionDecision.notEntailed)
#print axioms CheckedTaxonomyRoundOutcome.conclusive_semantics
#print axioms checked_taxonomy_doubling_decides
#print axioms checked_taxonomy_fresh_fold_producer_decides
#print axioms checked_taxonomy_fold_assignment_producer_decides
#print axioms checked_taxonomy_fresh_fold_producer_decision
#print axioms checked_taxonomy_fold_assignment_producer_decision
#print axioms checked_taxonomy_scheduled_fold_assignment_producer_decision
#print axioms checked_taxonomy_scheduled_guarded_fold_assignment_producer_decision
#print axioms checked_taxonomy_scheduled_cartesian_fold_assignment_producer_decision
#print axioms checked_taxonomy_scheduled_fresh_fold_producer_decision
#print axioms checked_taxonomy_scheduled_guarded_fold_producer_decision
#print axioms CertifiedHTProductionTaxonomyRoute.decides
#print axioms CertifiedHTFreshFoldProductionTaxonomyRoute.decides
#print axioms CertifiedHTCardinalityProductionTaxonomyRoute.decides
#print axioms CertifiedHTNativeABoxProductionTaxonomyRoute.decides
#print axioms CertifiedHTNativeABoxCardinalityProductionTaxonomyRoute.decides
#print axioms CertifiedHTFreshFoldCardinalityProductionTaxonomyRoute.decides
#print axioms CertifiedHTFreshFoldNativeABoxProductionTaxonomyRoute.decides
#print axioms CertifiedHTFreshFoldNativeABoxCardinalityProductionTaxonomyRoute.decides
#print axioms CertifiedHTFoldAssignmentProductionTaxonomyRoute.decides
#print axioms CertifiedHTFoldAssignmentCardinalityProductionTaxonomyRoute.decides
#print axioms CertifiedHTFoldAssignmentNativeABoxProductionTaxonomyRoute.decides
#print axioms CertifiedHTFoldAssignmentNativeABoxCardinalityProductionTaxonomyRoute.decides

end ContextCalculus.Hypertableau
