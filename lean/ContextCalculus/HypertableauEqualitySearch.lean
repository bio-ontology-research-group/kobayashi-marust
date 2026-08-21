import ContextCalculus.HypertableauEqualityRuntimeSearch
import ContextCalculus.HypertableauFrontierWire
import ContextCalculus.HypertableauEqualityNormalization
import ContextCalculus.HypertableauRegularProduction

/-!
# Checked bounded equality-aware HT outcomes

KM's bounded equality-aware decision search has three operational outcomes.
A saturated open leaf becomes conclusive only after the finite quotient-model
checker accepts it. A closed tree becomes conclusive only after its refutation
checker accepts it. Exhausting the node budget remains a frontier.
-/

namespace ContextCalculus.Hypertableau

abbrev EqualityHasNonemptyModel
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role),
    Nonempty Domain ∧ I.models ontology

inductive CheckedEqualityDecisionOutcome
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) : Type where
  | sat
      {nodeCount : Nat}
      (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
      (hontology : certificate.base.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hcheck : certificate.checkEqSat = true)
  | closed
      {nodeCount : Nat}
      (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
      (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
      (hontology : certificate.base.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hempty : certificate.EmptyRoot)
      (hcheck : tree.checkClosed certificate = true)
  | frontier
      (document : WireAddressFrontier)
      (hconcepts : document.concept_count = conceptCount)
      (hroles : document.role_count = roleCount)
      (hcheck : document.check = true)

def CheckedEqualityDecisionOutcome.Semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedEqualityDecisionOutcome
      conceptCount roleCount variableCount ontology) : Prop :=
  match outcome with
  | .sat .. => EqualityHasNonemptyModel ontology
  | .closed .. => ¬EqualityHasNonemptyModel ontology
  | .frontier .. => False

def CheckedEqualityDecisionOutcome.SourceSemantics
    {target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (source : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (outcome : CheckedEqualityDecisionOutcome
      conceptCount roleCount variableCount target) : Prop :=
  match outcome with
  | .sat .. => EqualityHasNonemptyModel source
  | .closed .. => ¬EqualityHasNonemptyModel source
  | .frontier .. => False

theorem CheckedEqualityDecisionOutcome.source_semantics_of_equivalent
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedEqualityDecisionOutcome
      conceptCount roleCount variableCount target)
    (equivalent : ModelEquivalent source target)
    (hsemantics : outcome.Semantics) :
    outcome.SourceSemantics source := by
  cases outcome with
  | sat certificate hontology hnonempty hcheck =>
      simp only [CheckedEqualityDecisionOutcome.Semantics,
        CheckedEqualityDecisionOutcome.SourceSemantics,
        EqualityHasNonemptyModel] at hsemantics ⊢
      rcases hsemantics with ⟨Domain, I, hdomain, htarget⟩
      exact ⟨Domain, I, hdomain, (equivalent Domain I).mpr htarget⟩
  | closed certificate tree hontology hnonempty hempty hcheck =>
      simp only [CheckedEqualityDecisionOutcome.Semantics,
        CheckedEqualityDecisionOutcome.SourceSemantics,
        EqualityHasNonemptyModel] at hsemantics ⊢
      rintro ⟨Domain, I, hdomain, hsource⟩
      exact hsemantics ⟨Domain, I, hdomain, (equivalent Domain I).mp hsource⟩
  | frontier document hconcepts hroles hcheck =>
      exact hsemantics

theorem CheckedEqualityDecisionOutcome.sat_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {nodeCount : Nat}
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hontology : certificate.base.ontology = ontology)
    (hnonempty : 0 < nodeCount)
    (hcheck : certificate.checkEqSat = true) :
    EqualityHasNonemptyModel ontology := by
  letI : Nonempty (Fin nodeCount) := ⟨⟨0, hnonempty⟩⟩
  refine ⟨certificate.state.QuotientDomain, certificate.state.quotientCanonical, ?_, ?_⟩
  · exact ⟨Quotient.mk certificate.state.nodeSetoid (Classical.choice inferInstance)⟩
  · simpa [hontology] using certificate.checkEqSat_models hcheck

theorem CheckedEqualityDecisionOutcome.closed_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {nodeCount : Nat}
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
    (hontology : certificate.base.ontology = ontology)
    (hnonempty : 0 < nodeCount)
    (hempty : certificate.EmptyRoot)
    (hcheck : tree.checkClosed certificate = true) :
    ¬EqualityHasNonemptyModel ontology := by
  letI : Nonempty (Fin nodeCount) := ⟨⟨0, hnonempty⟩⟩
  have hnot := tree.checkClosed_ontology_unsatisfiable certificate hempty hcheck
  simpa [EqualityHasNonemptyModel, hontology] using hnot

theorem CheckedEqualityDecisionOutcome.conclusive_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedEqualityDecisionOutcome
      conceptCount roleCount variableCount ontology) :
    (match outcome with | .frontier .. => False | _ => True) →
      outcome.Semantics := by
  cases outcome with
  | sat certificate hontology hnonempty hcheck =>
      intro _
      exact CheckedEqualityDecisionOutcome.sat_semantics
        certificate hontology hnonempty hcheck
  | closed certificate tree hontology hnonempty hempty hcheck =>
      intro _
      exact CheckedEqualityDecisionOutcome.closed_semantics
        certificate tree hontology hnonempty hempty hcheck
  | frontier document hconcepts hroles hcheck => simp

/-- Equality-aware iterative deepening uses the same checked rooted witness
addresses as equality-free search. Equality changes branch labels and the
blocking signature, but it neither changes canonical child slots nor permits
duplicate rooted addresses. Therefore checked full frontiers cannot persist
through KM's doubling schedule. -/
theorem checked_equality_doubling_decides
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (run : Nat →
      CheckedEqualityDecisionOutcome conceptCount roleCount variableCount ontology)
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
    | sat certificate hontology hnonempty hcheck =>
        exfalso
        exact hnone round (by
          rw [houtcome]
          exact CheckedEqualityDecisionOutcome.sat_semantics
            certificate hontology hnonempty hcheck)
    | closed certificate tree hontology hnonempty hempty hcheck =>
        exfalso
        exact hnone round (by
          rw [houtcome]
          exact CheckedEqualityDecisionOutcome.closed_semantics
            certificate tree hontology hnonempty hempty hcheck)
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

theorem checked_equality_doubling_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (run : Nat →
      CheckedEqualityDecisionOutcome conceptCount roleCount variableCount target)
    (hnodes : ∀ round document hconcepts hroles hcheck,
      run round = .frontier document hconcepts hroles hcheck →
        document.node_count = 8 * 2 ^ round) :
    ∃ round, (run round).SourceSemantics source := by
  obtain ⟨round, hsemantics⟩ := checked_equality_doubling_decides run hnodes
  exact ⟨round, (run round).source_semantics_of_equivalent equivalent hsemantics⟩

/-- Equality-aware production first learns away rejected blocker folds at each
fixed budget, then uses the checked address frontier to justify doubling. -/
theorem checked_equality_fold_learning_doubling_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (attempt : ∀ budget, Nat → FoldLearningOutcome (Fin (8 * 2 ^ budget))
      (CheckedEqualityDecisionOutcome conceptCount roleCount variableCount target))
    (forbidden : ∀ budget,
      Nat → Finset (Fin (8 * 2 ^ budget) × Fin (8 * 2 ^ budget)))
    (hlearn : ∀ budget retry folds,
      attempt budget retry = .rejected folds →
        forbidden budget (retry + 1) = forbidden budget retry ∪ folds ∧
          ∃ fold ∈ folds, fold ∉ forbidden budget retry)
    (hnodes : ∀ budget retry document hconcepts hroles hcheck,
      attempt budget retry = .done (.frontier document hconcepts hroles hcheck) →
        document.node_count = 8 * 2 ^ budget) :
    ∃ budget retry outcome,
      attempt budget retry = .done outcome ∧ outcome.SourceSemantics source := by
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
    checked_equality_doubling_decides_source equivalent settled hsettledNodes
  exact ⟨budget, retry budget, settled budget, hsettled budget, hsemantics⟩

theorem checked_equality_fresh_fold_producer_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (producer : ∀ budget, FreshFoldProducer (Fin (8 * 2 ^ budget))
      (CheckedEqualityDecisionOutcome conceptCount roleCount variableCount target))
    (hnodes : ∀ budget retry document hconcepts hroles hcheck,
      (producer budget).run retry = .done
        (.frontier document hconcepts hroles hcheck) →
        document.node_count = 8 * 2 ^ budget) :
    ∃ budget retry outcome,
      (producer budget).run retry = .done outcome ∧
        outcome.SourceSemantics source := by
  exact checked_equality_fold_learning_doubling_decides_source equivalent
    (fun budget => (producer budget).run)
    (fun budget => (producer budget).forbidden)
    (fun _ _ _ hrun => FreshFoldProducer.rejected_step _ hrun) hnodes

#print axioms CheckedEqualityDecisionOutcome.sat_semantics
#print axioms CheckedEqualityDecisionOutcome.closed_semantics
#print axioms CheckedEqualityDecisionOutcome.conclusive_semantics
#print axioms checked_equality_doubling_decides
#print axioms CheckedEqualityDecisionOutcome.source_semantics_of_equivalent
#print axioms checked_equality_doubling_decides_source
#print axioms checked_equality_fold_learning_doubling_decides_source
#print axioms checked_equality_fresh_fold_producer_decides_source

end ContextCalculus.Hypertableau
