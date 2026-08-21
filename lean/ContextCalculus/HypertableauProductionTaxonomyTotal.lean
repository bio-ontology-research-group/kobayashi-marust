import ContextCalculus.HypertableauTaxonomyCertificate
import ContextCalculus.HypertableauFrontierWire
import ContextCalculus.HypertableauCardinalityTaxonomyWire
import ContextCalculus.HypertableauNativeABoxTaxonomy
import ContextCalculus.HypertableauNativeABoxCardinalityTaxonomyWire

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
#print axioms CheckedTaxonomyRoundOutcome.conclusive_semantics
#print axioms checked_taxonomy_doubling_decides
#print axioms CertifiedHTProductionTaxonomyRoute.decides
#print axioms CertifiedHTCardinalityProductionTaxonomyRoute.decides
#print axioms CertifiedHTNativeABoxProductionTaxonomyRoute.decides
#print axioms CertifiedHTNativeABoxCardinalityProductionTaxonomyRoute.decides

end ContextCalculus.Hypertableau
