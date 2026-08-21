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
    (hheads : ∀ clause ∈ certificate.residual, ∀ atom ∈ clause.head,
      PathLiftableHead atom)
    (hcoverClosed : certificate.CoverClosed)
    (hcoverEdge : ∀ role source target,
      certificate.coverRelation role source target →
        certificate.state.edge role source target) :
    CheckedRegularRoundOutcome conceptCount roleCount variableCount ontology :=
  .regularSat certificate hontology hnonempty
    (certificate.check_of_blocked_runtime_terminal runtime blocked fold hstate
      hterminal hwitnessRefines hredirectRefines hauthorized hguarded hheads
      hcoverClosed hcoverEdge)

def CheckedRegularRoundOutcome.Semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedRegularRoundOutcome
      conceptCount roleCount variableCount ontology) : Prop :=
  match outcome with
  | .regularSat .. => HasNonemptyModel ontology
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

#print axioms CheckedRegularRoundOutcome.regularSat_semantics
#print axioms CheckedRegularRoundOutcome.finiteUnsat_semantics
#print axioms CheckedRegularRoundOutcome.conclusive_semantics
#print axioms checked_regular_doubling_decides
#print axioms CheckedRegularRoundOutcome.source_semantics_of_equivalent
#print axioms checked_regular_doubling_decides_source

end ContextCalculus.Hypertableau
