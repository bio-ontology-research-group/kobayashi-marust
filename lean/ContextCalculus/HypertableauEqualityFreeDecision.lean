import ContextCalculus.HypertableauBlockedSearch
import ContextCalculus.HypertableauFrontierWire

/-!
# Total checked equality-free HT decision

This module composes the three concrete outcomes of KM's equality-free
iterative search. SAT and UNSAT terminals carry the already proved finite
certificate checks. A frontier carries the checked rooted-address wire from
`HypertableauFrontierWire`. Since full checked frontiers cannot persist through
the doubling schedule, some round has a conclusive, semantically correct
terminal.
-/

namespace ContextCalculus.Hypertableau

abbrev HasNonemptyModel
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role),
    Nonempty Domain ∧ I.models ontology

inductive CheckedEqualityFreeRoundOutcome
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) : Type where
  | sat
      {nodeCount : Nat}
      (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
      (hontology : certificate.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hcheck : certificate.checkSat = true)
  | unsat
      {nodeCount : Nat}
      (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
      (tree : FiniteRefutationTree nodeCount conceptCount roleCount variableCount)
      (hontology : certificate.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hempty : certificate.EmptyRoot)
      (hcheck : tree.check certificate = true)
  | frontier
      (document : WireAddressFrontier)
      (hconcepts : document.concept_count = conceptCount)
      (hroles : document.role_count = roleCount)
      (hcheck : document.check = true)

def CheckedEqualityFreeRoundOutcome.Semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedEqualityFreeRoundOutcome conceptCount roleCount variableCount ontology) :
    Prop :=
  match outcome with
  | .sat .. => HasNonemptyModel ontology
  | .unsat .. => ¬HasNonemptyModel ontology
  | .frontier .. => False

theorem CheckedEqualityFreeRoundOutcome.sat_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {nodeCount : Nat}
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (hontology : certificate.ontology = ontology)
    (hnonempty : 0 < nodeCount)
    (hcheck : certificate.checkSat = true) :
    HasNonemptyModel ontology := by
  letI : Nonempty (Fin nodeCount) := ⟨⟨0, hnonempty⟩⟩
  rcases certificate.checkSat_satisfiable hcheck with ⟨interpretation, hmodels⟩
  exact ⟨Fin nodeCount, interpretation, inferInstance,
    by simpa [hontology] using hmodels⟩

theorem CheckedEqualityFreeRoundOutcome.unsat_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {nodeCount : Nat}
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (tree : FiniteRefutationTree nodeCount conceptCount roleCount variableCount)
    (hontology : certificate.ontology = ontology)
    (hnonempty : 0 < nodeCount)
    (hempty : certificate.EmptyRoot)
    (hcheck : tree.check certificate = true) :
    ¬HasNonemptyModel ontology := by
  letI : Nonempty (Fin nodeCount) := ⟨⟨0, hnonempty⟩⟩
  have hnot := tree.check_ontology_unsatisfiable certificate hempty hcheck
  simpa [HasNonemptyModel, hontology] using hnot

theorem CheckedEqualityFreeRoundOutcome.conclusive_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedEqualityFreeRoundOutcome conceptCount roleCount variableCount ontology) :
    (match outcome with | .frontier .. => False | _ => True) →
      outcome.Semantics := by
  cases outcome with
  | sat certificate hontology hnonempty hcheck =>
      intro _
      exact CheckedEqualityFreeRoundOutcome.sat_semantics
        certificate hontology hnonempty hcheck
  | unsat certificate tree hontology hnonempty hempty hcheck =>
      intro _
      exact CheckedEqualityFreeRoundOutcome.unsat_semantics
        certificate tree hontology hnonempty hempty hcheck
  | frontier document hconcepts hroles hcheck => simp

/-- Every round returns one checked outcome. If frontier node counts follow
KM's doubling schedule, some round is conclusive and its SAT/UNSAT meaning is
correct for the exact normalized ontology. -/
theorem checked_equality_free_doubling_decides
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (run : Nat →
      CheckedEqualityFreeRoundOutcome conceptCount roleCount variableCount ontology)
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
    | sat certificate hontology hnonempty hcheck =>
        exfalso
        exact hnone round (by
          rw [houtcome]
          exact CheckedEqualityFreeRoundOutcome.sat_semantics
            certificate hontology hnonempty hcheck)
    | unsat certificate tree hontology hnonempty hempty hcheck =>
        exfalso
        exact hnone round (by
          rw [houtcome]
          exact CheckedEqualityFreeRoundOutcome.unsat_semantics
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

#print axioms CheckedEqualityFreeRoundOutcome.sat_semantics
#print axioms CheckedEqualityFreeRoundOutcome.unsat_semantics
#print axioms CheckedEqualityFreeRoundOutcome.conclusive_semantics
#print axioms checked_equality_free_doubling_decides

end ContextCalculus.Hypertableau
