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
      certificate.base.relatedB left right &&
      decide ((left, right) ∈ certificate.apart)
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
  | equalityApart left right =>
      simp only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      exact .equalityApart certificate.state left right
        (certificate.base.relatedB_sound left right hcheck.1.2)
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

end DistinctCardinalityCheckerTests

#print axioms FiniteDistinctEqCertificate.mergeTransitionB_state
#print axioms FiniteDistinctEqCertificate.minimumTransitionB_state
#print axioms FiniteDistinctEqCertificate.freshFamilyB_sound
#print axioms FiniteDistinctCardinalityRefutationTree.check_sound
#print axioms FiniteDistinctCardinalityRefutationTree.check_ontology_unsatisfiable
#print axioms FiniteDistinctCardinalityRefutationTree.check_subsumption
#print axioms FiniteDistinctCardinalityRefutationTree.check_unsatisfiable_concept

end ContextCalculus.Hypertableau
