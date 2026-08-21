import ContextCalculus.HypertableauNativeABoxDecision
import ContextCalculus.HypertableauCardinalityFrontierWire
import ContextCalculus.HypertableauEqualityNormalization

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
      (document : WireCardinalityAddressFrontier)
      (hconcepts : document.concept_count = conceptCount)
      (hroles : document.role_count = roleCount)
      (hdefinitions : document.definition_count = definitions.length)
      (hcheck : document.check = true)

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
    (maxWidth : Nat)
    (run : Nat → CheckedNativeABoxCardinalityOutcome Individual conceptCount
      roleCount variableCount abox target definitions)
    (hnodes : ∀ round document hconcepts hroles hdefinitions hcheck,
      run round = .frontier document hconcepts hroles hdefinitions hcheck →
        document.node_count = 8 * 2 ^ round)
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
    cardinality_doubling_eventually_rejects_checked_frontier
      document conceptCount roleCount definitions.length maxWidth
      (fun round ↦ hnodes round (document round) (hconcepts round)
        (hroles round) (hdefinitions round) (hchecks round) (heq round))
      hconcepts hroles hdefinitions
      (fun round ↦ hwidth round (document round) (hconcepts round)
        (hroles round) (hdefinitions round) (hchecks round) (heq round))
  exact hrejected (hchecks round)

#print axioms CheckedNativeABoxCardinalityOutcome.sat_semantics
#print axioms CheckedNativeABoxCardinalityOutcome.closed_semantics
#print axioms CheckedNativeABoxCardinalityOutcome.source_semantics_of_equivalent
#print axioms checked_native_abox_cardinality_doubling_decides_source

end ContextCalculus.Hypertableau
