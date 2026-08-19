import ContextCalculus.HypertableauCardinalityRefutation
import ContextCalculus.HypertableauEqualityCertificate

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
#print axioms FiniteCardinalityEqRefutationTree.check_sound
#print axioms FiniteCardinalityEqRefutationTree.check_ontology_unsatisfiable
#print axioms FiniteCardinalityEqRefutationTree.check_subsumption
#print axioms FiniteCardinalityEqRefutationTree.check_unsatisfiable_concept

end ContextCalculus.Hypertableau
