import ContextCalculus.HypertableauCardinalityRefutation
import ContextCalculus.HypertableauEqualityCertificate
import Mathlib.Data.Fintype.Order

/-!
# Finite cardinality-aware hypertableau refutations

The maximum node records all `n + 1` successors and a checked child for every
ordered pair.  Diagonal children are ignored.  Every unequal pair must extend
the equality history by exactly that merge and must itself refute.
-/

namespace ContextCalculus.Hypertableau

def FiniteEqCertificate.mergeTransitionB
    (current next : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (left right : Fin nodeCount) : Bool :=
  decide (next.base.ontology = current.base.ontology) &&
    decide (next.base.labels = current.base.labels) &&
    decide (next.base.edges = current.base.edges) &&
    decide (next.base.obligations = current.base.obligations) &&
    decide (next.equalities = (left, right) :: current.equalities)

noncomputable def FiniteEqCertificate.canonicalMerge
    (current : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (left right : Fin nodeCount) :
    FiniteEqCertificate nodeCount conceptCount roleCount variableCount :=
  ({ current with equalities := (left, right) :: current.equalities } :
    FiniteEqCertificate nodeCount conceptCount roleCount variableCount).canonicalizeEqualityClosure

theorem FiniteEqCertificate.mergeTransitionB_canonicalMerge
    (current : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (left right : Fin nodeCount) :
    current.mergeTransitionB (current.canonicalMerge left right) left right = true := by
  simp [FiniteEqCertificate.mergeTransitionB, FiniteEqCertificate.canonicalMerge,
    FiniteEqCertificate.canonicalizeEqualityClosure]

theorem FiniteEqCertificate.canonicalMerge_valid
    (current : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (left right : Fin nodeCount) :
    (current.canonicalMerge left right).equalityClosureValidB = true :=
  FiniteEqCertificate.canonicalizeEqualityClosure_valid _

theorem FiniteEqCertificate.mergeTransitionB_state
    (current next : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (left right : Fin nodeCount)
    (htransition : current.mergeTransitionB next left right = true) :
    next.state = current.state.merge left right := by
  simp only [FiniteEqCertificate.mergeTransitionB, Bool.and_eq_true,
    decide_eq_true_eq] at htransition
  rcases htransition with
    ⟨⟨⟨⟨hontology, hlabels⟩, hedges⟩, hobligations⟩, hequalities⟩
  apply EqState.ext
  · apply State.ext
    · funext node lit
      simp only [FiniteEqCertificate.state, FiniteSatCertificate.state, EqState.merge]
      rw [hlabels]
    · funext role source target
      simp only [FiniteEqCertificate.state, FiniteSatCertificate.state, EqState.merge]
      rw [hedges]
    · funext role filler node
      simp only [FiniteEqCertificate.state, FiniteSatCertificate.state, EqState.merge]
      rw [hobligations]
  · apply funext; intro x
    apply funext; intro y
    exact propext (by
      simp only [FiniteEqCertificate.state, EqState.merge, hequalities]
      exact eqvGen_cons_iff (left, right) current.equalities x y)

def FiniteEqCertificate.minimumTransitionB
    (current next : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (source : Fin nodeCount) (targets : Fin count → Fin nodeCount)
    (role : Fin roleCount) (filler : Fin conceptCount) : Bool :=
  decide (next.base.ontology = current.base.ontology) &&
  decide (next.base.labels = current.base.labels ++
    List.ofFn (fun index => (targets index, .pos filler))) &&
  decide (next.base.edges = current.base.edges ++
    List.ofFn (fun index => (role, source, targets index))) &&
  decide (next.base.obligations = current.base.obligations) &&
  decide (next.equalities = current.equalities)

noncomputable def FiniteEqCertificate.canonicalMinimum
    (current : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (source : Fin nodeCount) (targets : Fin count → Fin nodeCount)
    (role : Fin roleCount) (filler : Fin conceptCount) :
    FiniteEqCertificate nodeCount conceptCount roleCount variableCount :=
  ({ current with base := { current.base with
      labels := current.base.labels ++
        List.ofFn (fun index => (targets index, .pos filler))
      edges := current.base.edges ++
        List.ofFn (fun index => (role, source, targets index)) } } :
    FiniteEqCertificate nodeCount conceptCount roleCount variableCount).canonicalizeEqualityClosure

theorem FiniteEqCertificate.minimumTransitionB_canonicalMinimum
    (current : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (source : Fin nodeCount) (targets : Fin count → Fin nodeCount)
    (role : Fin roleCount) (filler : Fin conceptCount) :
    current.minimumTransitionB
      (current.canonicalMinimum source targets role filler)
      source targets role filler = true := by
  simp [FiniteEqCertificate.minimumTransitionB, FiniteEqCertificate.canonicalMinimum,
    FiniteEqCertificate.canonicalizeEqualityClosure]

theorem FiniteEqCertificate.canonicalMinimum_valid
    (current : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (source : Fin nodeCount) (targets : Fin count → Fin nodeCount)
    (role : Fin roleCount) (filler : Fin conceptCount) :
    (current.canonicalMinimum source targets role filler).equalityClosureValidB = true :=
  FiniteEqCertificate.canonicalizeEqualityClosure_valid _

theorem FiniteEqCertificate.minimumTransitionB_state
    (current next : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (source : Fin nodeCount) (targets : Fin count → Fin nodeCount)
    (role : Fin roleCount) (filler : Fin conceptCount)
    (htransition : current.minimumTransitionB next source targets role filler = true) :
    next.state = current.state.materializeMinimum source targets role filler := by
  simp only [FiniteEqCertificate.minimumTransitionB, Bool.and_eq_true,
    decide_eq_true_eq] at htransition
  rcases htransition with
    ⟨⟨⟨⟨hontology, hlabels⟩, hedges⟩, hobligations⟩, hequalities⟩
  apply EqState.ext
  · apply State.ext
    · funext node lit
      apply propext
      simp [FiniteEqCertificate.state, FiniteSatCertificate.state,
        EqState.materializeMinimum, State.materializeMinimum, hlabels, eq_comm]
    · funext candidateRole candidateSource candidateTarget
      apply propext
      simp [FiniteEqCertificate.state, FiniteSatCertificate.state,
        EqState.materializeMinimum, State.materializeMinimum, hedges, eq_comm]
    · funext candidateRole candidateFiller node
      simp [FiniteEqCertificate.state, FiniteSatCertificate.state,
        EqState.materializeMinimum, State.materializeMinimum, hobligations]
  · simp [FiniteEqCertificate.state, EqState.materializeMinimum, hequalities]

def FiniteEqCertificate.freshFamilyB
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (targets : Fin count → Fin nodeCount) : Bool :=
  decide (∀ left right, targets left = targets right → left = right) &&
    decide (∀ index, certificate.freshNodeB (targets index))

theorem FiniteEqCertificate.freshFamilyB_sound
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (targets : Fin count → Fin nodeCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (hcheck : certificate.freshFamilyB targets = true) :
    certificate.state.FreshFamily targets := by
  simp only [FiniteEqCertificate.freshFamilyB, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  exact ⟨(fun _ _ heq => hcheck.1 _ _ heq), fun index =>
    (certificate.freshNodeB_eq_true hvalid (targets index)).mp (hcheck.2 index)⟩

theorem FiniteEqCertificate.freshFamilyB_eq_true
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (targets : Fin count → Fin nodeCount)
    (hvalid : certificate.equalityClosureValidB = true) :
    certificate.freshFamilyB targets = true ↔ certificate.state.FreshFamily targets := by
  simp only [FiniteEqCertificate.freshFamilyB, Bool.and_eq_true, decide_eq_true_eq,
    EqState.FreshFamily]
  constructor
  · rintro ⟨hinjective, hfresh⟩
    exact ⟨hinjective, fun index =>
      (certificate.freshNodeB_eq_true hvalid (targets index)).mp (hfresh index)⟩
  · rintro ⟨hinjective, hfresh⟩
    exact ⟨hinjective, fun index =>
      (certificate.freshNodeB_eq_true hvalid (targets index)).mpr (hfresh index)⟩

inductive FiniteCardinalityEqRefutationTree
    (nodeCount conceptCount roleCount variableCount : Nat) : Nat → Type where
  | equality
      (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
      : FiniteCardinalityEqRefutationTree nodeCount conceptCount roleCount variableCount 0
  | clash : FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount 0
  | delay
      (child : FiniteCardinalityEqRefutationTree
        nodeCount conceptCount roleCount variableCount depth)
      : FiniteCardinalityEqRefutationTree
        nodeCount conceptCount roleCount variableCount (depth + 1)

  | maximum
      (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
      (source : Fin nodeCount)
      (witnesses : Fin (definition.bound + 1) → Fin nodeCount)
      (next : ∀ _ _ : Fin (definition.bound + 1),
        FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
      (children : ∀ _ _ : Fin (definition.bound + 1),
        FiniteCardinalityEqRefutationTree
          nodeCount conceptCount roleCount variableCount depth)
      : FiniteCardinalityEqRefutationTree
        nodeCount conceptCount roleCount variableCount (depth + 1)

  | branch
      (clause : Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))
      (assignment : Fin variableCount → Fin nodeCount)
      (next : Fin clause.head.length →
        FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
      (children : Fin clause.head.length → FiniteCardinalityEqRefutationTree
        nodeCount conceptCount roleCount variableCount depth)
      : FiniteCardinalityEqRefutationTree
        nodeCount conceptCount roleCount variableCount (depth + 1)
  | witness
      (source target : Fin nodeCount) (role : Fin roleCount)
      (filler : Lit (Fin conceptCount))
      (child : FiniteCardinalityEqRefutationTree
        nodeCount conceptCount roleCount variableCount depth)
      : FiniteCardinalityEqRefutationTree
        nodeCount conceptCount roleCount variableCount (depth + 1)
  | minimum
      (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
      (source : Fin nodeCount)
      (targets : Fin definition.bound → Fin nodeCount)
      (next : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
      (child : FiniteCardinalityEqRefutationTree
        nodeCount conceptCount roleCount variableCount depth)
      : FiniteCardinalityEqRefutationTree
        nodeCount conceptCount roleCount variableCount (depth + 1)

def FiniteCardinalityEqRefutationTree.pad
    (tree : FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount depth) :
    (extra : Nat) → FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount (depth + extra)
  | 0 => tree
  | extra + 1 => by
      simpa [Nat.add_assoc] using
        FiniteCardinalityEqRefutationTree.delay (tree.pad extra)

def FiniteCardinalityEqRefutationTree.padTo
    (tree : FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (hle : depth ≤ targetDepth) : FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount targetDepth :=
  cast (congrArg (FiniteCardinalityEqRefutationTree
    nodeCount conceptCount roleCount variableCount) (Nat.add_sub_of_le hle))
    (tree.pad (targetDepth - depth))

def FiniteCardinalityEqRefutationTree.check
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount) :
    FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount depth → Bool
  | .equality tree => tree.check certificate
  | .clash => certificate.equalityClosureValidB && certificate.closedClashB
  | .delay child => child.check definitions certificate
  | .maximum definition source witnesses next children =>
      decide (definition ∈ definitions) &&
      decide (definition.kind = .maximum) &&
      decide ((source, .pos definition.marker) ∈ certificate.base.labels) &&
      decide (∀ index, (definition.role, source, witnesses index) ∈ certificate.base.edges) &&
      decide (∀ index, (witnesses index, .pos definition.filler) ∈ certificate.base.labels) &&
      decide (∀ left right, left ≠ right →
        certificate.mergeTransitionB (next left right) (witnesses left) (witnesses right) = true ∧
        (children left right).check definitions (next left right) = true)
  | .branch clause assignment next children =>
      certificate.equalityClosureValidB &&
      decide (clause ∈ certificate.base.ontology) &&
      clause.body.all (certificate.closedHoldsAtomB assignment) &&
      decide (∀ index,
        certificate.transitionB (next index) assignment (clause.head.get index) = true ∧
        (children index).check definitions (next index) = true)
  | .witness source target role filler child =>
      certificate.equalityClosureValidB &&
      decide ((role, filler, source) ∈ certificate.base.obligations) &&
      certificate.freshNodeB target &&
      child.check definitions (certificate.materializeWitness source target role filler)
  | .minimum definition source targets next child =>
      certificate.equalityClosureValidB &&
      decide (definition ∈ definitions) && decide (definition.kind = .minimum) &&
      decide ((source, .pos definition.marker) ∈ certificate.base.labels) &&
      certificate.freshFamilyB targets &&
      certificate.minimumTransitionB next source targets definition.role definition.filler &&
      child.check definitions next

theorem FiniteCardinalityEqRefutationTree.check_pad
    (tree : FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (extra : Nat) :
    (tree.pad extra).check definitions certificate = tree.check definitions certificate := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      simpa [FiniteCardinalityEqRefutationTree.pad,
        FiniteCardinalityEqRefutationTree.check] using ih

theorem FiniteCardinalityEqRefutationTree.check_cast
    {sourceDepth targetDepth : Nat} (heq : sourceDepth = targetDepth)
    (tree : FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount sourceDepth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount) :
    (cast (congrArg (FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount) heq) tree).check
        definitions certificate = tree.check definitions certificate := by
  subst targetDepth
  rfl

theorem FiniteCardinalityEqRefutationTree.check_padTo
    (tree : FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hle : depth ≤ targetDepth) :
    (tree.padTo (targetDepth := targetDepth) hle).check definitions certificate =
      tree.check definitions certificate := by
  unfold FiniteCardinalityEqRefutationTree.padTo
  exact (FiniteCardinalityEqRefutationTree.check_cast (Nat.add_sub_of_le hle)
    (tree.pad (targetDepth - depth)) definitions certificate).trans
      (tree.check_pad definitions certificate (targetDepth - depth))

theorem exists_uniform_checked_cardinality_trees
    {Index : Type} [Finite Index]
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : Index →
      FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hencode : ∀ index, ∃ depth,
      ∃ tree : FiniteCardinalityEqRefutationTree
          nodeCount conceptCount roleCount variableCount depth,
        tree.check definitions (certificate index) = true) :
    ∃ depth, ∃ trees : Index → FiniteCardinalityEqRefutationTree
        nodeCount conceptCount roleCount variableCount depth,
      ∀ index, (trees index).check definitions (certificate index) = true := by
  classical
  let childDepth : Index → Nat := fun index => (hencode index).choose
  obtain ⟨depth, hdepth⟩ := Finite.exists_le childDepth
  let rawTree (index : Index) : FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount (childDepth index) :=
    (hencode index).choose_spec.choose
  let trees (index : Index) := (rawTree index).padTo (hdepth index)
  refine ⟨depth, trees, ?_⟩
  intro index
  change ((rawTree index).padTo (hdepth index)).check definitions
    (certificate index) = true
  rw [FiniteCardinalityEqRefutationTree.check_padTo]
  exact (hencode index).choose_spec.choose_spec

theorem FiniteCardinalityEqRefutationTree.check_sound
    (tree : FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hcheck : tree.check definitions certificate = true) :
    CardinalityEqRefutes (Fin nodeCount) certificate.base.ontology definitions
      certificate.state := by
  induction tree generalizing certificate with
  | equality tree =>
      exact .equality certificate.state
        (tree.check_sound certificate (by simpa [FiniteCardinalityEqRefutationTree.check] using hcheck))
  | clash =>
      simp only [FiniteCardinalityEqRefutationTree.check, Bool.and_eq_true] at hcheck
      exact .clash certificate.state
        (certificate.closedClashB_sound hcheck.1 hcheck.2)
  | delay child ih =>
      exact ih certificate (by simpa [FiniteCardinalityEqRefutationTree.check] using hcheck)
  | maximum definition source witnesses next children ih =>
      simp only [FiniteCardinalityEqRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with
        ⟨⟨⟨⟨⟨hdefinition, hkind⟩, hmarker⟩, hedge⟩, hfiller⟩, hchildren⟩
      apply CardinalityEqRefutes.maximum certificate.state definition hdefinition hkind
        source hmarker witnesses hedge hfiller
      intro left right hne
      rcases hchildren left right hne with ⟨htransition, hchild⟩
      rw [← certificate.mergeTransitionB_state (next left right)
        (witnesses left) (witnesses right) htransition]
      have hbase : (next left right).base = certificate.base := by
        simp only [FiniteEqCertificate.mergeTransitionB, Bool.and_eq_true,
          decide_eq_true_eq] at htransition
        rcases htransition with
          ⟨⟨⟨⟨hontology, hlabels⟩, hedges⟩, hobligations⟩, _⟩
        cases hnext : (next left right).base
        cases hcurrent : certificate.base
        simp only [hnext, hcurrent] at hontology hlabels hedges hobligations
        simp_all
      simpa only [hbase] using ih left right (next left right) hchild
  | branch clause assignment next children ih =>
      simp only [FiniteCardinalityEqRefutationTree.check, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨⟨hvalid, hclause⟩, hbody⟩, hchildren⟩
      apply CardinalityEqRefutes.branch certificate.state clause hclause assignment
      · intro atom hatom
        exact (certificate.closedHoldsAtomB_eq_true hvalid assignment atom).mp
          (hbody atom hatom)
      · intro atom hatom
        rcases List.mem_iff_get.mp hatom with ⟨index, hindex⟩
        rw [← hindex]
        rcases hchildren index with ⟨htransition, hchild⟩
        rw [← certificate.transitionB_state (next index) assignment
          (clause.head.get index) htransition]
        have hbase := certificate.transitionB_base (next index) assignment
          (clause.head.get index) htransition
        have hontology : (next index).base.ontology = certificate.base.ontology := by
          rw [hbase]
          cases clause.head.get index <;> rfl
        simpa only [hontology] using ih index (next index) hchild
  | witness source target role filler child ih =>
      simp only [FiniteCardinalityEqRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨⟨hvalid, hobligation⟩, hfresh⟩, hchild⟩
      apply CardinalityEqRefutes.witness certificate.state source target role filler
        hobligation ((certificate.freshNodeB_eq_true hvalid target).mp hfresh)
      rw [← certificate.state_materializeWitness source target role filler]
      exact ih (certificate.materializeWitness source target role filler) hchild
  | minimum definition source targets next child ih =>
      simp only [FiniteCardinalityEqRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with
        ⟨⟨⟨⟨⟨⟨hvalid, hdefinition⟩, hkind⟩, hmarker⟩, hfresh⟩,
          htransition⟩, hchild⟩
      apply CardinalityEqRefutes.minimum certificate.state definition hdefinition hkind
        source hmarker targets (certificate.freshFamilyB_sound targets hvalid hfresh)
      rw [← certificate.minimumTransitionB_state next source targets definition.role
        definition.filler htransition]
      have hontology : next.base.ontology = certificate.base.ontology := by
        simp only [FiniteEqCertificate.minimumTransitionB, Bool.and_eq_true,
          decide_eq_true_eq] at htransition
        exact htransition.1.1.1.1
      simpa only [hontology] using ih next hchild

/-- Completeness of the finite cardinality refutation checker relative to the
semantic derivation. Finite branch families are padded to a common depth, and
equality-changing transitions receive a canonical checked closure. -/
theorem CardinalityEqRefutes.exists_checked_tree
    {ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    {state : EqState (Fin nodeCount) (Fin conceptCount) (Fin roleCount)}
    (hrefutes : CardinalityEqRefutes (Fin nodeCount) ontology definitions state) :
    ∀ certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount,
      certificate.base.ontology = ontology → certificate.state = state →
      certificate.equalityClosureValidB = true →
      ∃ depth, ∃ tree : FiniteCardinalityEqRefutationTree
          nodeCount conceptCount roleCount variableCount depth,
        tree.check definitions certificate = true := by
  induction hrefutes with
  | equality state tree =>
      intro certificate hontology hstate hvalid
      obtain ⟨encoded, hencoded⟩ :=
        tree.exists_checked_tree certificate hontology hstate hvalid
      exact ⟨0, .equality encoded, by
        simpa [FiniteCardinalityEqRefutationTree.check] using hencoded⟩
  | clash state hclash =>
      intro certificate hontology hstate hvalid
      rcases hclash with
        ⟨positiveNode, negativeNode, concept, hequiv, hpositive, hnegative⟩
      have hclosed : certificate.closedClashB = true := by
        cases hvalue : certificate.closedClashB with
        | true => rfl
        | false =>
            have hfree := certificate.not_closedClashB_closedClashFree hvalid hvalue
            rw [hstate] at hfree
            exact (hfree positiveNode negativeNode concept hequiv
              ⟨hpositive, hnegative⟩).elim
      exact ⟨0, .clash, by
        simp [FiniteCardinalityEqRefutationTree.check, hvalid, hclosed]⟩
  | branch state clause hclause assignment hbody children ih =>
      intro certificate hontology hstate hvalid
      have hclause' : clause ∈ certificate.base.ontology := by simpa [hontology] using hclause
      have hbody' : ∀ atom ∈ clause.body,
          certificate.closedHoldsAtomB assignment atom = true := by
        intro atom hatom
        apply (certificate.closedHoldsAtomB_eq_true hvalid assignment atom).2
        rw [hstate]
        exact hbody atom hatom
      let next (index : Fin clause.head.length) :=
        (certificate.assertAtom assignment
          (clause.head.get index)).canonicalizeEqualityClosure
      obtain ⟨depth, encodedChildren, hencodedChildren⟩ :=
        exists_uniform_checked_cardinality_trees definitions next (fun index => by
          have hatom : clause.head.get index ∈ clause.head := List.get_mem _ _
          apply ih (clause.head.get index) hatom (next index)
          · have htransition := certificate.transitionB_canonicalized_assertAtom
                assignment (clause.head.get index)
            have hbase := certificate.transitionB_base (next index) assignment
              (clause.head.get index) (by simpa [next] using htransition)
            rw [hbase]
            cases clause.head.get index <;> simpa using hontology
          · simp only [next, FiniteEqCertificate.canonicalizeEqualityClosure_state,
              certificate.state_assertAtom, hstate]
          · exact (certificate.assertAtom assignment
              (clause.head.get index)).canonicalizeEqualityClosure_valid)
      refine ⟨depth + 1, .branch clause assignment next encodedChildren, ?_⟩
      simp only [FiniteCardinalityEqRefutationTree.check, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨hvalid, hclause'⟩, hbody'⟩, ?_⟩
      intro index
      exact ⟨by
        simp [next, certificate.transitionB_canonicalized_assertAtom],
        hencodedChildren index⟩
  | witness state source target role filler hobligation hfresh child ih =>
      intro certificate hontology hstate hvalid
      have hobligation' : (role, filler, source) ∈ certificate.base.obligations := by
        change certificate.state.base.obligation role filler source
        rw [hstate]
        exact hobligation
      have hfresh' : certificate.freshNodeB target = true :=
        (certificate.freshNodeB_eq_true hvalid target).2 (by simpa [hstate] using hfresh)
      obtain ⟨depth, encodedChild, hencodedChild⟩ :=
        ih (certificate.materializeWitness source target role filler)
          (by simpa [hontology]) (by rw [certificate.state_materializeWitness, hstate]) hvalid
      exact ⟨depth + 1, .witness source target role filler encodedChild, by
        simp [FiniteCardinalityEqRefutationTree.check, hvalid, hobligation', hfresh',
          hencodedChild]⟩
  | maximum state definition hdefinition hkind source hmarker witnesses hedge hfiller
      children ih =>
      intro certificate hontology hstate hvalid
      let Pair := { pair : Fin (definition.bound + 1) × Fin (definition.bound + 1) //
        pair.1 ≠ pair.2 }
      let nextPair (pair : Pair) :=
        certificate.canonicalMerge (witnesses pair.1.1) (witnesses pair.1.2)
      obtain ⟨depth, encodedPair, hencodedPair⟩ :=
        exists_uniform_checked_cardinality_trees definitions nextPair (fun pair => by
          apply ih pair.1.1 pair.1.2 pair.2 (nextPair pair)
          · simp [nextPair, FiniteEqCertificate.canonicalMerge,
              FiniteEqCertificate.canonicalizeEqualityClosure, hontology]
          · calc
              (nextPair pair).state = certificate.state.merge
                  (witnesses pair.1.1) (witnesses pair.1.2) :=
                certificate.mergeTransitionB_state (nextPair pair)
                  (witnesses pair.1.1) (witnesses pair.1.2)
                  (certificate.mergeTransitionB_canonicalMerge _ _)
              _ = state.merge (witnesses pair.1.1) (witnesses pair.1.2) := by rw [hstate]
          · exact certificate.canonicalMerge_valid _ _)
      let next (left right : Fin (definition.bound + 1)) :=
        if hne : left ≠ right then nextPair ⟨(left, right), hne⟩ else certificate
      let encodedChildren (left right : Fin (definition.bound + 1)) :
          FiniteCardinalityEqRefutationTree
            nodeCount conceptCount roleCount variableCount depth :=
        if hne : left ≠ right then encodedPair ⟨(left, right), hne⟩
        else FiniteCardinalityEqRefutationTree.clash.padTo (Nat.zero_le depth)
      have hmarker' : (source, .pos definition.marker) ∈ certificate.base.labels := by
        change certificate.state.base.label source (.pos definition.marker)
        rw [hstate]
        exact hmarker
      have hedge' : ∀ index,
          (definition.role, source, witnesses index) ∈ certificate.base.edges := by
        intro index
        change certificate.state.base.edge definition.role source (witnesses index)
        rw [hstate]
        exact hedge index
      have hfiller' : ∀ index,
          (witnesses index, .pos definition.filler) ∈ certificate.base.labels := by
        intro index
        change certificate.state.base.label (witnesses index) (.pos definition.filler)
        rw [hstate]
        exact hfiller index
      refine ⟨depth + 1,
        .maximum definition source witnesses next encodedChildren, ?_⟩
      simp only [FiniteCardinalityEqRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq]
      refine ⟨⟨⟨⟨⟨hdefinition, hkind⟩, hmarker'⟩, hedge'⟩, hfiller'⟩, ?_⟩
      intro left right hne
      constructor
      · simp [next, hne, nextPair, certificate.mergeTransitionB_canonicalMerge]
      · simp only [next, encodedChildren, dif_pos hne]
        exact hencodedPair ⟨(left, right), hne⟩
  | minimum state definition hdefinition hkind source hmarker targets hfresh child ih =>
      intro certificate hontology hstate hvalid
      let next := certificate.canonicalMinimum source targets definition.role definition.filler
      obtain ⟨depth, encodedChild, hencodedChild⟩ := ih next (by
          simp [next, FiniteEqCertificate.canonicalMinimum,
            FiniteEqCertificate.canonicalizeEqualityClosure, hontology]) (by
          calc
            next.state = certificate.state.materializeMinimum source targets
                definition.role definition.filler :=
              certificate.minimumTransitionB_state next source targets definition.role
                definition.filler (certificate.minimumTransitionB_canonicalMinimum
                  source targets definition.role definition.filler)
            _ = state.materializeMinimum source targets definition.role definition.filler := by
              rw [hstate]) (certificate.canonicalMinimum_valid source targets
            definition.role definition.filler)
      have hmarker' : (source, .pos definition.marker) ∈ certificate.base.labels := by
        change certificate.state.base.label source (.pos definition.marker)
        rw [hstate]
        exact hmarker
      have hfresh' : certificate.freshFamilyB targets = true :=
        (certificate.freshFamilyB_eq_true targets hvalid).2 (by simpa [hstate] using hfresh)
      refine ⟨depth + 1, .minimum definition source targets next encodedChild, ?_⟩
      simp [FiniteCardinalityEqRefutationTree.check, hvalid, hdefinition, hkind,
        hmarker', hfresh', next, certificate.minimumTransitionB_canonicalMinimum,
        hencodedChild]

theorem FiniteEqCertificate.cardinalityRefutes_iff_exists_checked_tree
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) :
    CardinalityEqRefutes (Fin nodeCount) certificate.base.ontology definitions
        certificate.state ↔
      ∃ depth, ∃ tree : FiniteCardinalityEqRefutationTree
          nodeCount conceptCount roleCount variableCount depth,
        tree.check definitions certificate.canonicalizeEqualityClosure = true := by
  constructor
  · intro hrefutes
    exact hrefutes.exists_checked_tree certificate.canonicalizeEqualityClosure rfl rfl
      certificate.canonicalizeEqualityClosure_valid
  · rintro ⟨depth, tree, hcheck⟩
    simpa using tree.check_sound definitions certificate.canonicalizeEqualityClosure hcheck

theorem FiniteCardinalityEqRefutationTree.check_unsatisfiable
    (tree : FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hcheck : tree.check definitions certificate = true) :
    ¬certificate.state.RealizableWithCardinality certificate.base.ontology definitions :=
  (tree.check_sound definitions certificate hcheck).sound

theorem FiniteCardinalityEqRefutationTree.check_ontology_unsatisfiable
    [Nonempty (Fin nodeCount)]
    (tree : FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hempty : certificate.EmptyRoot)
    (hcheck : tree.check definitions certificate = true) :
    ¬∃ (Domain : Type) (I : Interp Domain (Fin conceptCount) (Fin roleCount)),
      Nonempty Domain ∧ I.models certificate.base.ontology ∧
        I.modelsCardinalityDefs definitions := by
  rintro ⟨Domain, I, hdomain, hmodels, hcardinality⟩
  apply tree.check_unsatisfiable definitions certificate hcheck
  let value : Fin nodeCount → Domain := fun _ => Classical.choice hdomain
  refine ⟨Domain, I, value, hmodels, hcardinality, ?_⟩
  rcases hempty with ⟨hlabels, hedges, hobligations⟩
  refine ⟨?_, ?_⟩
  · simp [FiniteEqCertificate.state, FiniteSatCertificate.state, State.RealizedBy,
      hlabels, hedges, hobligations]
  · intro left right _
    rfl

theorem FiniteCardinalityEqRefutationTree.check_subsumption
    (tree : FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (sub sup : Fin conceptCount)
    (hroot : certificate.SubsumptionRoot root sub sup)
    (hcheck : tree.check definitions certificate = true) :
    EntailsSubWithCardinality certificate.base.ontology definitions sub sup := by
  intro Domain I hmodels hcardinality value hsub
  by_contra hsup
  apply tree.check_unsatisfiable definitions certificate hcheck
  refine ⟨Domain, I, fun _ => value, hmodels, hcardinality, ?_, ?_⟩
  · rcases hroot with ⟨hlabels, hedges, hobligations⟩
    refine ⟨?_, ?_, ?_⟩
    · intro node lit hlabel
      simp only [FiniteEqCertificate.state, FiniteSatCertificate.state, hlabels,
        List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hlabel
      rcases hlabel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa [Interp.satLit, Lit.pos] using hsub
      · simpa [Interp.satLit, Lit.negated] using hsup
    · simp [FiniteEqCertificate.state, FiniteSatCertificate.state, hedges]
    · simp [FiniteEqCertificate.state, FiniteSatCertificate.state, hobligations]
  · intro left right _
    rfl

theorem FiniteCardinalityEqRefutationTree.check_unsatisfiable_concept
    (tree : FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (concept : Fin conceptCount)
    (hroot : certificate.UnsatisfiableRoot root concept)
    (hcheck : tree.check definitions certificate = true) :
    UnsatisfiableConceptWithCardinality certificate.base.ontology definitions concept := by
  intro Domain I hmodels hcardinality value hconcept
  apply tree.check_unsatisfiable definitions certificate hcheck
  refine ⟨Domain, I, fun _ => value, hmodels, hcardinality, ?_, ?_⟩
  · rcases hroot with ⟨hlabels, hedges, hobligations⟩
    refine ⟨?_, ?_, ?_⟩
    · intro node lit hlabel
      simp only [FiniteEqCertificate.state, FiniteSatCertificate.state, hlabels,
        List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hlabel
      rcases hlabel with ⟨rfl, rfl⟩
      simpa [Interp.satLit, Lit.pos] using hconcept
    · simp [FiniteEqCertificate.state, FiniteSatCertificate.state, hedges]
    · simp [FiniteEqCertificate.state, FiniteSatCertificate.state, hobligations]
  · intro left right _
    rfl

#print axioms FiniteEqCertificate.mergeTransitionB_state
#print axioms FiniteEqCertificate.minimumTransitionB_state
#print axioms FiniteEqCertificate.freshFamilyB_sound
#print axioms FiniteCardinalityEqRefutationTree.check_sound
#print axioms CardinalityEqRefutes.exists_checked_tree
#print axioms FiniteEqCertificate.cardinalityRefutes_iff_exists_checked_tree
#print axioms FiniteCardinalityEqRefutationTree.check_ontology_unsatisfiable
#print axioms FiniteCardinalityEqRefutationTree.check_subsumption
#print axioms FiniteCardinalityEqRefutationTree.check_unsatisfiable_concept

end ContextCalculus.Hypertableau
