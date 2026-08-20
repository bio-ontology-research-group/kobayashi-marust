import ContextCalculus.HypertableauCardinalityDistinct
import ContextCalculus.HypertableauCardinalityRefutationCertificate

/-!
# Finite distinct-aware cardinality certificates

The finite state adds an explicit list of apart node pairs to the existing
equality certificate.  Transition checks compare apart relations extensionally
over the finite node type, so list order and duplicates are irrelevant.
-/

namespace ContextCalculus.Hypertableau

structure FiniteDistinctEqCertificate
    (nodeCount conceptCount roleCount variableCount : Nat) where
  base : FiniteEqCertificate nodeCount conceptCount roleCount variableCount
  apart : List (Fin nodeCount × Fin nodeCount)

def FiniteDistinctEqCertificate.state
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) :
    DistinctEqState (Fin nodeCount) (Fin conceptCount) (Fin roleCount) where
  base := certificate.base.state
  apart left right := (left, right) ∈ certificate.apart

def FiniteDistinctEqCertificate.mergeTransitionB
    (current next : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (left right : Fin nodeCount) : Bool :=
  current.base.mergeTransitionB next.base left right &&
    decide (next.apart = current.apart)

def FiniteDistinctEqCertificate.transitionB
    (current next : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) : Bool :=
  current.base.transitionB next.base assignment atom &&
    decide (next.apart = current.apart)

theorem FiniteDistinctEqCertificate.transitionB_state
    (current next : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount))
    (hcheck : current.transitionB next assignment atom = true) :
    next.state = current.state.assertAtom assignment atom := by
  simp only [FiniteDistinctEqCertificate.transitionB, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  apply DistinctEqState.ext
  · exact current.base.transitionB_state next.base assignment atom hcheck.1
  · funext left right
    simp only [FiniteDistinctEqCertificate.state, DistinctEqState.assertAtom]
    rw [hcheck.2]

def FiniteDistinctEqCertificate.freshNodeB
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (target : Fin nodeCount) : Bool :=
  certificate.base.freshNodeB target &&
    decide (∀ node,
      (target, node) ∉ certificate.apart ∧ (node, target) ∉ certificate.apart)

theorem FiniteDistinctEqCertificate.freshNodeB_sound
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (target : Fin nodeCount)
    (hvalid : certificate.base.equalityClosureValidB = true)
    (hcheck : certificate.freshNodeB target = true) :
    certificate.state.Fresh target := by
  simp only [FiniteDistinctEqCertificate.freshNodeB, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  exact ⟨(certificate.base.freshNodeB_eq_true hvalid target).mp hcheck.1, hcheck.2⟩

def FiniteDistinctEqCertificate.materializeWitness
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (source target : Fin nodeCount) (role : Fin roleCount)
    (filler : Lit (Fin conceptCount)) :
    FiniteDistinctEqCertificate nodeCount conceptCount roleCount variableCount where
  base := certificate.base.materializeWitness source target role filler
  apart := certificate.apart

theorem FiniteDistinctEqCertificate.state_materializeWitness
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (source target : Fin nodeCount) (role : Fin roleCount)
    (filler : Lit (Fin conceptCount)) :
    (certificate.materializeWitness source target role filler).state =
      certificate.state.materializeWitness source target role filler := by
  apply DistinctEqState.ext
  · exact certificate.base.state_materializeWitness source target role filler
  · rfl

theorem FiniteDistinctEqCertificate.mergeTransitionB_state
    (current next : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (left right : Fin nodeCount)
    (hcheck : current.mergeTransitionB next left right = true) :
    next.state = current.state.merge left right := by
  simp only [FiniteDistinctEqCertificate.mergeTransitionB, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨hbase, hapart⟩
  apply DistinctEqState.ext
  · exact FiniteEqCertificate.mergeTransitionB_state _ _ left right hbase
  · funext candidateLeft candidateRight
    simp only [FiniteDistinctEqCertificate.state, DistinctEqState.merge]
    rw [hapart]

def FiniteDistinctEqCertificate.minimumTransitionB
    (current next : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (source : Fin nodeCount) (targets : Fin count → Fin nodeCount)
    (role : Fin roleCount) (filler : Fin conceptCount) : Bool :=
  current.base.minimumTransitionB next.base source targets role filler &&
    decide (∀ left right,
      ((left, right) ∈ next.apart) ↔
        (left, right) ∈ current.apart ∨
        ∃ first second, first ≠ second ∧
          left = targets first ∧ right = targets second)

theorem FiniteDistinctEqCertificate.minimumTransitionB_state
    (current next : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (source : Fin nodeCount) (targets : Fin count → Fin nodeCount)
    (role : Fin roleCount) (filler : Fin conceptCount)
    (hcheck : current.minimumTransitionB next source targets role filler = true) :
    next.state = current.state.materializeMinimum source targets role filler := by
  simp only [FiniteDistinctEqCertificate.minimumTransitionB, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨hbase, hapart⟩
  apply DistinctEqState.ext
  · exact FiniteEqCertificate.minimumTransitionB_state _ _ source targets role filler hbase
  · funext left right
    exact propext (hapart left right)

def FiniteDistinctEqCertificate.freshFamilyB
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (targets : Fin count → Fin nodeCount) : Bool :=
  certificate.base.freshFamilyB targets &&
    decide (∀ index node,
      (targets index, node) ∉ certificate.apart ∧
      (node, targets index) ∉ certificate.apart)

theorem FiniteDistinctEqCertificate.freshFamilyB_sound
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (targets : Fin count → Fin nodeCount)
    (hvalid : certificate.base.equalityClosureValidB = true)
    (hcheck : certificate.freshFamilyB targets = true) :
    certificate.state.FreshFamily targets := by
  simp only [FiniteDistinctEqCertificate.freshFamilyB, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  have hbase := certificate.base.freshFamilyB_sound targets hvalid hcheck.1
  exact ⟨hbase.1, fun index => ⟨hbase.2 index, fun node => hcheck.2 index node⟩⟩

inductive FiniteDistinctCardinalityRefutationTree
    (nodeCount conceptCount roleCount variableCount : Nat) : Nat → Type where
  | equality
      (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount) :
      FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount 0
  | clash : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount 0
  | equalityApart (left right : Fin nodeCount) :
      FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount 0
  | delay
      (child : FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount depth) :
      FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount (depth + 1)
  | maximum
      (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
      (source : Fin nodeCount)
      (witnesses : Fin (definition.bound + 1) → Fin nodeCount)
      (next : ∀ _ _ : Fin (definition.bound + 1),
        FiniteDistinctEqCertificate nodeCount conceptCount roleCount variableCount)
      (children : ∀ _ _ : Fin (definition.bound + 1),
        FiniteDistinctCardinalityRefutationTree
          nodeCount conceptCount roleCount variableCount depth) :
      FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount (depth + 1)
  | branch
      (clause : Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))
      (assignment : Fin variableCount → Fin nodeCount)
      (next : Fin clause.head.length →
        FiniteDistinctEqCertificate nodeCount conceptCount roleCount variableCount)
      (children : Fin clause.head.length → FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount depth) :
      FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount (depth + 1)
  | witness
      (source target : Fin nodeCount) (role : Fin roleCount)
      (filler : Lit (Fin conceptCount))
      (child : FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount depth) :
      FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount (depth + 1)
  | minimum
      (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
      (source : Fin nodeCount)
      (targets : Fin definition.bound → Fin nodeCount)
      (next : FiniteDistinctEqCertificate nodeCount conceptCount roleCount variableCount)
      (child : FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount depth) :
      FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount (depth + 1)

def FiniteDistinctCardinalityRefutationTree.check
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) :
    FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth → Bool
  | .equalityApart left right =>
      certificate.base.equalityClosureValidB &&
      certificate.base.closedRelatedB left right &&
      decide ((left, right) ∈ certificate.apart)
  | .equality tree => tree.check certificate.base
  | .clash => certificate.base.equalityClosureValidB && certificate.base.closedClashB
  | .delay child => child.check definitions certificate
  | .maximum definition source witnesses next children =>
      decide (definition ∈ definitions) &&
      decide (definition.kind = .maximum) &&
      decide ((source, .pos definition.marker) ∈ certificate.base.base.labels) &&
      decide (∀ index,
        (definition.role, source, witnesses index) ∈ certificate.base.base.edges) &&
      decide (∀ index,
        (witnesses index, .pos definition.filler) ∈ certificate.base.base.labels) &&
      decide (∀ left right, left ≠ right →
        certificate.mergeTransitionB (next left right)
          (witnesses left) (witnesses right) = true ∧
        (children left right).check definitions (next left right) = true)
  | .branch clause assignment next children =>
      certificate.base.equalityClosureValidB &&
      decide (clause ∈ certificate.base.base.ontology) &&
      clause.body.all (certificate.base.closedHoldsAtomB assignment) &&
      decide (∀ index,
        certificate.transitionB (next index) assignment (clause.head.get index) = true ∧
        (children index).check definitions (next index) = true)
  | .witness source target role filler child =>
      certificate.base.equalityClosureValidB &&
      decide ((role, filler, source) ∈ certificate.base.base.obligations) &&
      certificate.freshNodeB target &&
      child.check definitions
        (certificate.materializeWitness source target role filler)
  | .minimum definition source targets next child =>
      certificate.base.equalityClosureValidB &&
      decide (definition ∈ definitions) && decide (definition.kind = .minimum) &&
      decide ((source, .pos definition.marker) ∈ certificate.base.base.labels) &&
      certificate.freshFamilyB targets &&
      certificate.minimumTransitionB next source targets definition.role definition.filler &&
      child.check definitions next

theorem FiniteDistinctCardinalityRefutationTree.check_sound
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hcheck : tree.check definitions certificate = true) :
    DistinctCardinalityRefutes (Fin nodeCount) certificate.base.base.ontology
      definitions certificate.state := by
  induction tree generalizing certificate with
  | equality tree =>
      exact .equality certificate.state
        (tree.check_sound certificate.base (by
          simpa [FiniteDistinctCardinalityRefutationTree.check] using hcheck))
  | clash =>
      simp only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true] at hcheck
      exact .clash certificate.state
        (certificate.base.closedClashB_sound hcheck.1 hcheck.2)
  | equalityApart left right =>
      simp only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      exact .equalityApart certificate.state left right
        ((certificate.base.closedRelatedB_eq_true hcheck.1.1 left right).mp hcheck.1.2)
        hcheck.2
  | delay child ih =>
      exact ih certificate
        (by simpa [FiniteDistinctCardinalityRefutationTree.check] using hcheck)
  | maximum definition source witnesses next children ih =>
      simp only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with
        ⟨⟨⟨⟨⟨hdefinition, hkind⟩, hmarker⟩, hedge⟩, hfiller⟩, hchildren⟩
      apply DistinctCardinalityRefutes.maximum certificate.state definition
        hdefinition hkind source hmarker witnesses hedge hfiller
      intro left right hne
      rcases hchildren left right hne with ⟨htransition, hchild⟩
      rw [← certificate.mergeTransitionB_state (next left right)
        (witnesses left) (witnesses right) htransition]
      have hontology : (next left right).base.base.ontology =
          certificate.base.base.ontology := by
        simp only [FiniteDistinctEqCertificate.mergeTransitionB, Bool.and_eq_true,
          FiniteEqCertificate.mergeTransitionB, decide_eq_true_eq] at htransition
        exact htransition.1.1.1.1.1
      simpa only [hontology] using ih left right (next left right) hchild
  | branch clause assignment next children ih =>
      simp only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨⟨hvalid, hclause⟩, hbody⟩, hchildren⟩
      apply DistinctCardinalityRefutes.branch certificate.state clause hclause assignment
      · intro atom hatom
        exact (certificate.base.closedHoldsAtomB_eq_true hvalid assignment atom).mp
          (hbody atom hatom)
      · intro atom hatom
        rcases List.mem_iff_get.mp hatom with ⟨index, hindex⟩
        rw [← hindex]
        rcases hchildren index with ⟨htransition, hchild⟩
        rw [← certificate.transitionB_state (next index) assignment
          (clause.head.get index) htransition]
        have htransitionParts := htransition
        simp only [FiniteDistinctEqCertificate.transitionB, Bool.and_eq_true,
          decide_eq_true_eq] at htransitionParts
        have hbase := certificate.base.transitionB_base (next index).base assignment
          (clause.head.get index) htransitionParts.1
        have hontology : (next index).base.base.ontology =
            certificate.base.base.ontology := by
          rw [hbase]
          cases clause.head.get index <;> rfl
        simpa only [hontology] using ih index (next index) hchild
  | witness source target role filler child ih =>
      simp only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨⟨hvalid, hobligation⟩, hfresh⟩, hchild⟩
      apply DistinctCardinalityRefutes.witness certificate.state source target role filler
        hobligation (certificate.freshNodeB_sound target hvalid hfresh)
      rw [← certificate.state_materializeWitness source target role filler]
      exact ih (certificate.materializeWitness source target role filler) hchild
  | minimum definition source targets next child ih =>
      simp only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with
        ⟨⟨⟨⟨⟨⟨hvalid, hdefinition⟩, hkind⟩, hmarker⟩, hfresh⟩,
          htransition⟩, hchild⟩
      apply DistinctCardinalityRefutes.minimum certificate.state definition
        hdefinition hkind source hmarker targets
        (certificate.freshFamilyB_sound targets hvalid hfresh)
      rw [← certificate.minimumTransitionB_state next source targets definition.role
        definition.filler htransition]
      have hontology : next.base.base.ontology = certificate.base.base.ontology := by
        simp only [FiniteDistinctEqCertificate.minimumTransitionB, Bool.and_eq_true,
          FiniteEqCertificate.minimumTransitionB, decide_eq_true_eq] at htransition
        exact htransition.1.1.1.1.1
      simpa only [hontology] using ih next hchild

/-- Exact acceptance criterion for an equality-apart leaf. In particular, the
equality may be obtained transitively from the complete asserted equality
history; it need not be a single directly listed pair. -/
theorem FiniteDistinctCardinalityRefutationTree.check_equalityApart_iff
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (left right : Fin nodeCount) :
    (FiniteDistinctCardinalityRefutationTree.equalityApart left right).check
        definitions certificate = true ↔
      certificate.base.equalityClosureValidB = true ∧
      certificate.state.base.equiv left right ∧ certificate.state.apart left right := by
  simp only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
    decide_eq_true_eq, FiniteDistinctEqCertificate.state]
  constructor
  · rintro ⟨⟨hvalid, hrelated⟩, hapart⟩
    exact ⟨hvalid, (certificate.base.closedRelatedB_eq_true hvalid left right).mp hrelated,
      hapart⟩
  · rintro ⟨hvalid, hequiv, hapart⟩
    exact ⟨⟨hvalid, (certificate.base.closedRelatedB_eq_true hvalid left right).mpr hequiv⟩,
      hapart⟩

theorem FiniteDistinctCardinalityRefutationTree.check_unsatisfiable
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hcheck : tree.check definitions certificate = true) :
    ¬certificate.state.RealizableWithCardinality
      certificate.base.base.ontology definitions :=
  (tree.check_sound definitions certificate hcheck).sound

theorem FiniteDistinctCardinalityRefutationTree.check_ontology_unsatisfiable
    [Nonempty (Fin nodeCount)]
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hempty : certificate.base.EmptyRoot) (hapart : certificate.apart = [])
    (hcheck : tree.check definitions certificate = true) :
    ¬∃ (Domain : Type) (I : Interp Domain (Fin conceptCount) (Fin roleCount)),
      Nonempty Domain ∧ I.models certificate.base.base.ontology ∧
        I.modelsCardinalityDefs definitions := by
  rintro ⟨Domain, I, hdomain, hmodels, hcardinality⟩
  apply tree.check_unsatisfiable definitions certificate hcheck
  let value : Fin nodeCount → Domain := fun _ => Classical.choice hdomain
  refine ⟨Domain, I, value, hmodels, hcardinality, ?_, ?_⟩
  · rcases hempty with ⟨hlabels, hedges, hobligations⟩
    refine ⟨?_, ?_⟩
    · simp [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
        FiniteSatCertificate.state, State.RealizedBy, hlabels, hedges, hobligations]
    · intro left right _
      rfl
  · simp [FiniteDistinctEqCertificate.state, hapart]

theorem FiniteDistinctCardinalityRefutationTree.check_subsumption
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (sub sup : Fin conceptCount)
    (hroot : certificate.base.SubsumptionRoot root sub sup)
    (hapart : certificate.apart = [])
    (hcheck : tree.check definitions certificate = true) :
    EntailsSubWithCardinality certificate.base.base.ontology definitions sub sup := by
  intro Domain I hmodels hcardinality value hsub
  by_contra hsup
  apply tree.check_unsatisfiable definitions certificate hcheck
  refine ⟨Domain, I, fun _ => value, hmodels, hcardinality, ?_, ?_⟩
  · rcases hroot with ⟨hlabels, hedges, hobligations⟩
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro node lit hlabel
        simp only [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
          FiniteSatCertificate.state, hlabels, List.mem_cons, List.not_mem_nil,
          or_false, Prod.mk.injEq] at hlabel
        rcases hlabel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa [Interp.satLit, Lit.pos] using hsub
        · simpa [Interp.satLit, Lit.negated] using hsup
      · simp [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
          FiniteSatCertificate.state, hedges]
      · simp [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
          FiniteSatCertificate.state, hobligations]
    · intro left right _
      rfl
  · simp [FiniteDistinctEqCertificate.state, hapart]

theorem FiniteDistinctCardinalityRefutationTree.check_unsatisfiable_concept
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (concept : Fin conceptCount)
    (hroot : certificate.base.UnsatisfiableRoot root concept)
    (hapart : certificate.apart = [])
    (hcheck : tree.check definitions certificate = true) :
    UnsatisfiableConceptWithCardinality certificate.base.base.ontology
      definitions concept := by
  intro Domain I hmodels hcardinality value hconcept
  apply tree.check_unsatisfiable definitions certificate hcheck
  refine ⟨Domain, I, fun _ => value, hmodels, hcardinality, ?_, ?_⟩
  · rcases hroot with ⟨hlabels, hedges, hobligations⟩
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro node lit hlabel
        simp only [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
          FiniteSatCertificate.state, hlabels, List.mem_cons, List.not_mem_nil,
          or_false, Prod.mk.injEq] at hlabel
        rcases hlabel with ⟨rfl, rfl⟩
        simpa [Interp.satLit, Lit.pos] using hconcept
      · simp [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
          FiniteSatCertificate.state, hedges]
      · simp [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
          FiniteSatCertificate.state, hobligations]
    · intro left right _
      rfl
  · simp [FiniteDistinctEqCertificate.state, hapart]

namespace DistinctCardinalityCheckerTests

private def rootEq : FiniteEqCertificate 3 1 1 0 where
  base := {
    ontology := []
    labels := [(0, .pos 0)]
    edges := []
    obligations := []
  }
  equalities := []
  representative := fun node => node
  representativePath := fun _ => []

private def root : FiniteDistinctEqCertificate 3 1 1 0 :=
  { base := rootEq, apart := [] }

private def targets : Fin 2 → Fin 3
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2

private def activeEq : FiniteEqCertificate 3 1 1 0 where
  base := {
    ontology := []
    labels := [(0, .pos 0), (1, .pos 0), (2, .pos 0)]
    edges := [(0, 0, 1), (0, 0, 2)]
    obligations := []
  }
  equalities := []
  representative := fun node => node
  representativePath := fun _ => []

private def active : FiniteDistinctEqCertificate 3 1 1 0 :=
  { base := activeEq, apart := [(1, 2), (2, 1)] }

private def mergedEq (left right : Fin 2) : FiniteEqCertificate 3 1 1 0 where
  base := activeEq.base
  equalities := [(targets left, targets right)]
  representative := fun node => if node = 2 then 1 else node
  representativePath := fun node => if node = 2 then [1] else []

private def merged (left right : Fin 2) : FiniteDistinctEqCertificate 3 1 1 0 :=
  { base := mergedEq left right, apart := active.apart }

private def minimum : CardinalityDef (Fin 1) (Fin 1) :=
  minimumDefinition 0 2 0 0

private def maximum : CardinalityDef (Fin 1) (Fin 1) :=
  maximumDefinition 0 1 0 0

private def tree : FiniteDistinctCardinalityRefutationTree 3 1 1 0 2 :=
  .minimum minimum 0 targets active
    (.maximum maximum 0 targets merged
      (fun left right => .equalityApart (targets left) (targets right)))

example : tree.check [minimum, maximum] root = true := by native_decide

private def missingApart : FiniteDistinctEqCertificate 3 1 1 0 :=
  { active with apart := [(1, 2)] }

private def badTree : FiniteDistinctCardinalityRefutationTree 3 1 1 0 2 :=
  .minimum minimum 0 targets missingApart
    (.maximum maximum 0 targets merged
      (fun left right => .equalityApart (targets left) (targets right)))

example : badTree.check [minimum, maximum] root = false := by native_decide

private def transitiveEq : FiniteEqCertificate 3 1 1 0 where
  base := rootEq.base
  equalities := [(0, 1), (1, 2)]
  representative := fun _ => 0
  representativePath := fun node =>
    if node = 2 then [1, 0] else if node = 1 then [0] else []

private def transitiveApart : FiniteDistinctEqCertificate 3 1 1 0 :=
  { base := transitiveEq, apart := [(0, 2)] }

/-- Regression: equality-apart closure must detect a contradiction reached
through two equality generators, not only a directly asserted pair. -/
example :
    (FiniteDistinctCardinalityRefutationTree.equalityApart 0 2).check []
      transitiveApart = true := by native_decide

end DistinctCardinalityCheckerTests

#print axioms FiniteDistinctEqCertificate.mergeTransitionB_state
#print axioms FiniteDistinctEqCertificate.transitionB_state
#print axioms FiniteDistinctEqCertificate.freshNodeB_sound
#print axioms FiniteDistinctEqCertificate.minimumTransitionB_state
#print axioms FiniteDistinctEqCertificate.freshFamilyB_sound
#print axioms FiniteDistinctCardinalityRefutationTree.check_sound
#print axioms FiniteDistinctCardinalityRefutationTree.check_equalityApart_iff
#print axioms FiniteDistinctCardinalityRefutationTree.check_ontology_unsatisfiable
#print axioms FiniteDistinctCardinalityRefutationTree.check_subsumption
#print axioms FiniteDistinctCardinalityRefutationTree.check_unsatisfiable_concept

end ContextCalculus.Hypertableau
