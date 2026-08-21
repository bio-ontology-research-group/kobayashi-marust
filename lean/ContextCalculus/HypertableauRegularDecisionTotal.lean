import ContextCalculus.HypertableauRegularDecisionWire
import ContextCalculus.HypertableauFrontierWire
import ContextCalculus.HypertableauEqualityFreeDecision

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

def CheckedRegularRoundOutcome.Semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedRegularRoundOutcome
      conceptCount roleCount variableCount ontology) : Prop :=
  match outcome with
  | .regularSat .. => HasNonemptyModel ontology
  | .finiteUnsat .. => ¬HasNonemptyModel ontology
  | .frontier .. => False

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

#print axioms CheckedRegularRoundOutcome.regularSat_semantics
#print axioms CheckedRegularRoundOutcome.finiteUnsat_semantics
#print axioms CheckedRegularRoundOutcome.conclusive_semantics
#print axioms checked_regular_doubling_decides

end ContextCalculus.Hypertableau
