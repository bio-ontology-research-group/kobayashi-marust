import ContextCalculus.HypertableauCardinalityDistinct
import ContextCalculus.HypertableauCardinalityRefutationCertificate
import Mathlib.Data.Fintype.Order

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

noncomputable def FiniteDistinctEqCertificate.canonicalizeEqualityClosure
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) :
    FiniteDistinctEqCertificate nodeCount conceptCount roleCount variableCount where
  base := certificate.base.canonicalizeEqualityClosure
  apart := certificate.apart

@[simp] theorem FiniteDistinctEqCertificate.canonicalizeEqualityClosure_state
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.canonicalizeEqualityClosure.state = certificate.state := rfl

theorem FiniteDistinctEqCertificate.canonicalizeEqualityClosure_valid
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.canonicalizeEqualityClosure.base.equalityClosureValidB = true :=
  certificate.base.canonicalizeEqualityClosure_valid

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

noncomputable def FiniteDistinctEqCertificate.canonicalAssertAtom
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) :
    FiniteDistinctEqCertificate nodeCount conceptCount roleCount variableCount where
  base := (certificate.base.assertAtom assignment atom).canonicalizeEqualityClosure
  apart := certificate.apart

theorem FiniteDistinctEqCertificate.transitionB_canonicalAssertAtom
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) :
    certificate.transitionB (certificate.canonicalAssertAtom assignment atom)
      assignment atom = true := by
  simp [FiniteDistinctEqCertificate.transitionB,
    FiniteDistinctEqCertificate.canonicalAssertAtom,
    certificate.base.transitionB_canonicalized_assertAtom]

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

theorem FiniteDistinctEqCertificate.freshNodeB_eq_true
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (target : Fin nodeCount) (hvalid : certificate.base.equalityClosureValidB = true) :
    certificate.freshNodeB target = true ↔ certificate.state.Fresh target := by
  simp only [FiniteDistinctEqCertificate.freshNodeB, Bool.and_eq_true,
    decide_eq_true_eq, DistinctEqState.Fresh, FiniteDistinctEqCertificate.state]
  constructor
  · rintro ⟨hbase, hapart⟩
    exact ⟨(certificate.base.freshNodeB_eq_true hvalid target).mp hbase, hapart⟩
  · rintro ⟨hbase, hapart⟩
    exact ⟨(certificate.base.freshNodeB_eq_true hvalid target).mpr hbase, hapart⟩

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

noncomputable def FiniteDistinctEqCertificate.canonicalMerge
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (left right : Fin nodeCount) :
    FiniteDistinctEqCertificate nodeCount conceptCount roleCount variableCount where
  base := certificate.base.canonicalMerge left right
  apart := certificate.apart

theorem FiniteDistinctEqCertificate.mergeTransitionB_canonicalMerge
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (left right : Fin nodeCount) :
    certificate.mergeTransitionB (certificate.canonicalMerge left right) left right = true := by
  simp [FiniteDistinctEqCertificate.mergeTransitionB,
    FiniteDistinctEqCertificate.canonicalMerge,
    certificate.base.mergeTransitionB_canonicalMerge]

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

noncomputable def FiniteDistinctEqCertificate.canonicalMinimum
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (source : Fin nodeCount) (targets : Fin count → Fin nodeCount)
    (role : Fin roleCount) (filler : Fin conceptCount) :
    FiniteDistinctEqCertificate nodeCount conceptCount roleCount variableCount where
  base := certificate.base.canonicalMinimum source targets role filler
  apart := certificate.apart ++
    ((Finset.univ : Finset { pair : Fin count × Fin count // pair.1 ≠ pair.2 }).toList.map
      fun pair => (targets pair.1.1, targets pair.1.2))

theorem FiniteDistinctEqCertificate.minimumTransitionB_canonicalMinimum
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (source : Fin nodeCount) (targets : Fin count → Fin nodeCount)
    (role : Fin roleCount) (filler : Fin conceptCount) :
    certificate.minimumTransitionB
      (certificate.canonicalMinimum source targets role filler)
      source targets role filler = true := by
  simp only [FiniteDistinctEqCertificate.minimumTransitionB, Bool.and_eq_true]
  constructor
  · exact certificate.base.minimumTransitionB_canonicalMinimum source targets role filler
  · simp only [decide_eq_true_eq]
    intro left right
    simp only [FiniteDistinctEqCertificate.canonicalMinimum, List.mem_append,
      List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    constructor
    · rintro (hold | ⟨pair, hpair⟩)
      · exact Or.inl hold
      · exact Or.inr ⟨pair.1.1, pair.1.2, pair.2,
          (congrArg Prod.fst hpair).symm, (congrArg Prod.snd hpair).symm⟩
    · rintro (hold | ⟨first, second, hne, rfl, rfl⟩)
      · exact Or.inl hold
      · exact Or.inr ⟨⟨(first, second), hne⟩, rfl⟩

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

theorem FiniteDistinctEqCertificate.freshFamilyB_eq_true
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (targets : Fin count → Fin nodeCount)
    (hvalid : certificate.base.equalityClosureValidB = true) :
    certificate.freshFamilyB targets = true ↔ certificate.state.FreshFamily targets := by
  simp only [FiniteDistinctEqCertificate.freshFamilyB, Bool.and_eq_true,
    decide_eq_true_eq, DistinctEqState.FreshFamily, FiniteDistinctEqCertificate.state]
  constructor
  · rintro ⟨hbase, hapart⟩
    have hfresh := (certificate.base.freshFamilyB_eq_true targets hvalid).mp hbase
    exact ⟨hfresh.1, fun index => ⟨hfresh.2 index, hapart index⟩⟩
  · rintro ⟨hinjective, hfresh⟩
    exact ⟨(certificate.base.freshFamilyB_eq_true targets hvalid).mpr
        ⟨hinjective, fun index => (hfresh index).1⟩,
      fun index => (hfresh index).2⟩

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

def FiniteDistinctCardinalityRefutationTree.pad
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth) :
    (extra : Nat) → FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount (depth + extra)
  | 0 => tree
  | extra + 1 => by
      simpa [Nat.add_assoc] using
        FiniteDistinctCardinalityRefutationTree.delay (tree.pad extra)

def FiniteDistinctCardinalityRefutationTree.padTo
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (hle : depth ≤ targetDepth) : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount targetDepth :=
  cast (congrArg (FiniteDistinctCardinalityRefutationTree
    nodeCount conceptCount roleCount variableCount) (Nat.add_sub_of_le hle))
    (tree.pad (targetDepth - depth))

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

theorem FiniteDistinctCardinalityRefutationTree.check_pad
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) (extra : Nat) :
    (tree.pad extra).check definitions certificate = tree.check definitions certificate := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      simpa [FiniteDistinctCardinalityRefutationTree.pad,
        FiniteDistinctCardinalityRefutationTree.check] using ih

theorem FiniteDistinctCardinalityRefutationTree.check_cast
    {sourceDepth targetDepth : Nat} (heq : sourceDepth = targetDepth)
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount sourceDepth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) :
    (cast (congrArg (FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount) heq) tree).check
        definitions certificate = tree.check definitions certificate := by
  subst targetDepth
  rfl

theorem FiniteDistinctCardinalityRefutationTree.check_padTo
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hle : depth ≤ targetDepth) :
    (tree.padTo (targetDepth := targetDepth) hle).check definitions certificate =
      tree.check definitions certificate := by
  unfold FiniteDistinctCardinalityRefutationTree.padTo
  exact (FiniteDistinctCardinalityRefutationTree.check_cast (Nat.add_sub_of_le hle)
    (tree.pad (targetDepth - depth)) definitions certificate).trans
      (tree.check_pad definitions certificate (targetDepth - depth))

theorem exists_uniform_checked_distinct_cardinality_trees
    {Index : Type} [Finite Index]
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : Index → FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hencode : ∀ index, ∃ depth,
      ∃ tree : FiniteDistinctCardinalityRefutationTree
          nodeCount conceptCount roleCount variableCount depth,
        tree.check definitions (certificate index) = true) :
    ∃ depth, ∃ trees : Index → FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount depth,
      ∀ index, (trees index).check definitions (certificate index) = true := by
  classical
  let childDepth : Index → Nat := fun index => (hencode index).choose
  obtain ⟨depth, hdepth⟩ := Finite.exists_le childDepth
  let rawTree (index : Index) : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount (childDepth index) :=
    (hencode index).choose_spec.choose
  let trees (index : Index) := (rawTree index).padTo (hdepth index)
  refine ⟨depth, trees, ?_⟩
  intro index
  change ((rawTree index).padTo (hdepth index)).check definitions
    (certificate index) = true
  rw [FiniteDistinctCardinalityRefutationTree.check_padTo]
  exact (hencode index).choose_spec.choose_spec

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

/-- Completeness of the distinct-aware cardinality checker relative to finite
semantic `DistinctCardinalityRefutes` derivations. -/
theorem DistinctCardinalityRefutes.exists_checked_tree
    {ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    {state : DistinctEqState (Fin nodeCount) (Fin conceptCount) (Fin roleCount)}
    (hrefutes : DistinctCardinalityRefutes
      (Fin nodeCount) ontology definitions state) :
    ∀ certificate : FiniteDistinctEqCertificate
        nodeCount conceptCount roleCount variableCount,
      certificate.base.base.ontology = ontology → certificate.state = state →
      certificate.base.equalityClosureValidB = true →
      ∃ depth, ∃ tree : FiniteDistinctCardinalityRefutationTree
          nodeCount conceptCount roleCount variableCount depth,
        tree.check definitions certificate = true := by
  induction hrefutes with
  | equality state tree =>
      intro certificate hontology hstate hvalid
      obtain ⟨encoded, hencoded⟩ := tree.exists_checked_tree certificate.base hontology
        (by exact congrArg DistinctEqState.base hstate) hvalid
      exact ⟨0, .equality encoded, by
        simpa [FiniteDistinctCardinalityRefutationTree.check] using hencoded⟩
  | clash state hclash =>
      intro certificate hontology hstate hvalid
      rcases hclash with
        ⟨positiveNode, negativeNode, concept, hequiv, hpositive, hnegative⟩
      have hclosed : certificate.base.closedClashB = true := by
        cases hvalue : certificate.base.closedClashB with
        | true => rfl
        | false =>
            have hfree := certificate.base.not_closedClashB_closedClashFree hvalid hvalue
            have hbase : certificate.base.state = state.base :=
              congrArg DistinctEqState.base hstate
            rw [hbase] at hfree
            exact (hfree positiveNode negativeNode concept hequiv
              ⟨hpositive, hnegative⟩).elim
      exact ⟨0, .clash, by
        simp [FiniteDistinctCardinalityRefutationTree.check, hvalid, hclosed]⟩
  | equalityApart state left right hequal hapart =>
      intro certificate hontology hstate hvalid
      refine ⟨0, .equalityApart left right, ?_⟩
      apply (FiniteDistinctCardinalityRefutationTree.check_equalityApart_iff
        definitions certificate left right).2
      rw [hstate]
      exact ⟨hvalid, hequal, hapart⟩
  | branch state clause hclause assignment hbody children ih =>
      intro certificate hontology hstate hvalid
      have hclause' : clause ∈ certificate.base.base.ontology := by
        simpa [hontology] using hclause
      have hbody' : ∀ atom ∈ clause.body,
          certificate.base.closedHoldsAtomB assignment atom = true := by
        intro atom hatom
        apply (certificate.base.closedHoldsAtomB_eq_true hvalid assignment atom).2
        have hbase : certificate.base.state = state.base :=
          congrArg DistinctEqState.base hstate
        rw [hbase]
        exact hbody atom hatom
      let next (index : Fin clause.head.length) :=
        certificate.canonicalAssertAtom assignment (clause.head.get index)
      obtain ⟨depth, encodedChildren, hencodedChildren⟩ :=
        exists_uniform_checked_distinct_cardinality_trees definitions next (fun index => by
          have hatom : clause.head.get index ∈ clause.head := List.get_mem _ _
          apply ih (clause.head.get index) hatom (next index)
          · have htransition := certificate.transitionB_canonicalAssertAtom assignment
                (clause.head.get index)
            have hbase := certificate.base.transitionB_base (next index).base assignment
              (clause.head.get index) (by
                have hparts : certificate.base.transitionB (next index).base assignment
                    (clause.head.get index) = true ∧
                    (next index).apart = certificate.apart := by
                  simpa [FiniteDistinctEqCertificate.transitionB, next] using htransition
                exact hparts.1)
            rw [hbase]
            cases clause.head.get index <;> simpa using hontology
          · calc
              (next index).state = certificate.state.assertAtom assignment
                  (clause.head.get index) :=
                certificate.transitionB_state (next index) assignment
                  (clause.head.get index) (by
                    simpa [next] using certificate.transitionB_canonicalAssertAtom
                      assignment (clause.head.get index))
              _ = state.assertAtom assignment (clause.head.get index) := by rw [hstate]
          · exact (certificate.base.assertAtom assignment
              (clause.head.get index)).canonicalizeEqualityClosure_valid)
      refine ⟨depth + 1, .branch clause assignment next encodedChildren, ?_⟩
      simp only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨hvalid, hclause'⟩, hbody'⟩, ?_⟩
      intro index
      exact ⟨(by simpa [next] using
          (certificate.transitionB_canonicalAssertAtom assignment
            (clause.head.get index))), hencodedChildren index⟩
  | witness state source target role filler hobligation hfresh child ih =>
      intro certificate hontology hstate hvalid
      have hobligation' : (role, filler, source) ∈ certificate.base.base.obligations := by
        change certificate.state.base.base.obligation role filler source
        rw [hstate]
        exact hobligation
      have hfresh' : certificate.freshNodeB target = true :=
        (certificate.freshNodeB_eq_true target hvalid).2 (by simpa [hstate] using hfresh)
      obtain ⟨depth, encodedChild, hencodedChild⟩ :=
        ih (certificate.materializeWitness source target role filler)
          (by simpa [hontology]) (by rw [certificate.state_materializeWitness, hstate]) hvalid
      exact ⟨depth + 1, .witness source target role filler encodedChild, by
        simp [FiniteDistinctCardinalityRefutationTree.check, hvalid, hobligation', hfresh',
          hencodedChild]⟩
  | maximum state definition hdefinition hkind source hmarker witnesses hedge hfiller
      children ih =>
      intro certificate hontology hstate hvalid
      let Pair := { pair : Fin (definition.bound + 1) × Fin (definition.bound + 1) //
        pair.1 ≠ pair.2 }
      let nextPair (pair : Pair) :=
        certificate.canonicalMerge (witnesses pair.1.1) (witnesses pair.1.2)
      obtain ⟨depth, encodedPair, hencodedPair⟩ :=
        exists_uniform_checked_distinct_cardinality_trees definitions nextPair (fun pair => by
          apply ih pair.1.1 pair.1.2 pair.2 (nextPair pair)
          · simp [nextPair, FiniteDistinctEqCertificate.canonicalMerge,
              FiniteEqCertificate.canonicalMerge,
              FiniteEqCertificate.canonicalizeEqualityClosure, hontology]
          · calc
              (nextPair pair).state = certificate.state.merge
                  (witnesses pair.1.1) (witnesses pair.1.2) :=
                certificate.mergeTransitionB_state (nextPair pair)
                  (witnesses pair.1.1) (witnesses pair.1.2)
                  (certificate.mergeTransitionB_canonicalMerge _ _)
              _ = state.merge (witnesses pair.1.1) (witnesses pair.1.2) := by rw [hstate]
          · exact certificate.base.canonicalMerge_valid _ _)
      let next (left right : Fin (definition.bound + 1)) :=
        if hne : left ≠ right then nextPair ⟨(left, right), hne⟩ else certificate
      let encodedChildren (left right : Fin (definition.bound + 1)) :
          FiniteDistinctCardinalityRefutationTree
            nodeCount conceptCount roleCount variableCount depth :=
        if hne : left ≠ right then encodedPair ⟨(left, right), hne⟩
        else FiniteDistinctCardinalityRefutationTree.clash.padTo (Nat.zero_le depth)
      have hmarker' : (source, .pos definition.marker) ∈ certificate.base.base.labels := by
        change certificate.state.base.base.label source (.pos definition.marker)
        rw [hstate]
        exact hmarker
      have hedge' : ∀ index,
          (definition.role, source, witnesses index) ∈ certificate.base.base.edges := by
        intro index
        change certificate.state.base.base.edge definition.role source (witnesses index)
        rw [hstate]
        exact hedge index
      have hfiller' : ∀ index,
          (witnesses index, .pos definition.filler) ∈ certificate.base.base.labels := by
        intro index
        change certificate.state.base.base.label (witnesses index) (.pos definition.filler)
        rw [hstate]
        exact hfiller index
      refine ⟨depth + 1, .maximum definition source witnesses next encodedChildren, ?_⟩
      simp only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq]
      refine ⟨⟨⟨⟨⟨hdefinition, hkind⟩, hmarker'⟩, hedge'⟩, hfiller'⟩, ?_⟩
      intro left right hne
      constructor
      · simpa [next, hne, nextPair] using certificate.mergeTransitionB_canonicalMerge
          (witnesses left) (witnesses right)
      · simp only [next, encodedChildren, dif_pos hne]
        exact hencodedPair ⟨(left, right), hne⟩
  | minimum state definition hdefinition hkind source hmarker targets hfresh child ih =>
      intro certificate hontology hstate hvalid
      let next := certificate.canonicalMinimum source targets definition.role definition.filler
      obtain ⟨depth, encodedChild, hencodedChild⟩ := ih next (by
          simp [next, FiniteDistinctEqCertificate.canonicalMinimum,
            FiniteEqCertificate.canonicalMinimum,
            FiniteEqCertificate.canonicalizeEqualityClosure, hontology]) (by
          calc
            next.state = certificate.state.materializeMinimum source targets
                definition.role definition.filler :=
              certificate.minimumTransitionB_state next source targets definition.role
                definition.filler (certificate.minimumTransitionB_canonicalMinimum
                  source targets definition.role definition.filler)
            _ = state.materializeMinimum source targets definition.role definition.filler := by
              rw [hstate]) (certificate.base.canonicalMinimum_valid source targets
            definition.role definition.filler)
      have hmarker' : (source, .pos definition.marker) ∈ certificate.base.base.labels := by
        change certificate.state.base.base.label source (.pos definition.marker)
        rw [hstate]
        exact hmarker
      have hfresh' : certificate.freshFamilyB targets = true :=
        (certificate.freshFamilyB_eq_true targets hvalid).2 (by simpa [hstate] using hfresh)
      refine ⟨depth + 1, .minimum definition source targets next encodedChild, ?_⟩
      simp [FiniteDistinctCardinalityRefutationTree.check, hvalid, hdefinition, hkind,
        hmarker', hfresh', next, certificate.minimumTransitionB_canonicalMinimum,
        hencodedChild]

theorem FiniteDistinctEqCertificate.refutes_iff_exists_checked_tree
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) :
    DistinctCardinalityRefutes (Fin nodeCount) certificate.base.base.ontology definitions
        certificate.state ↔
      ∃ depth, ∃ tree : FiniteDistinctCardinalityRefutationTree
          nodeCount conceptCount roleCount variableCount depth,
        tree.check definitions certificate.canonicalizeEqualityClosure = true := by
  constructor
  · intro hrefutes
    exact hrefutes.exists_checked_tree certificate.canonicalizeEqualityClosure rfl rfl
      certificate.canonicalizeEqualityClosure_valid
  · rintro ⟨depth, tree, hcheck⟩
    simpa using tree.check_sound definitions certificate.canonicalizeEqualityClosure hcheck

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
#print axioms DistinctCardinalityRefutes.exists_checked_tree
#print axioms FiniteDistinctEqCertificate.refutes_iff_exists_checked_tree
#print axioms FiniteDistinctCardinalityRefutationTree.check_ontology_unsatisfiable
#print axioms FiniteDistinctCardinalityRefutationTree.check_subsumption
#print axioms FiniteDistinctCardinalityRefutationTree.check_unsatisfiable_concept

end ContextCalculus.Hypertableau
