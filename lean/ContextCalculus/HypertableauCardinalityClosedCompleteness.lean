import ContextCalculus.HypertableauCardinalityRuntimeSearch

/-!
# Completeness of the quotient-closed cardinality refutation checker

The production cardinality search reasons over complete equality closure.
This module proves the converse of its checker soundness theorem: every finite
`ClosedDistinctCardinalityRefutes` derivation can be serialized as an accepted
`FiniteDistinctCardinalityRefutationTree`.
-/

namespace ContextCalculus.Hypertableau

theorem FiniteDistinctCardinalityRefutationTree.checkClosed_pad
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) (extra : Nat) :
    (tree.pad extra).checkClosed definitions certificate =
      tree.checkClosed definitions certificate := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      simpa [FiniteDistinctCardinalityRefutationTree.pad,
        FiniteDistinctCardinalityRefutationTree.checkClosed] using ih

theorem FiniteDistinctCardinalityRefutationTree.checkClosed_cast
    {sourceDepth targetDepth : Nat} (heq : sourceDepth = targetDepth)
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount sourceDepth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) :
    (cast (congrArg (FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount) heq) tree).checkClosed
        definitions certificate = tree.checkClosed definitions certificate := by
  subst targetDepth
  rfl

theorem FiniteDistinctCardinalityRefutationTree.checkClosed_padTo
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hle : depth ≤ targetDepth) :
    (tree.padTo (targetDepth := targetDepth) hle).checkClosed definitions certificate =
      tree.checkClosed definitions certificate := by
  unfold FiniteDistinctCardinalityRefutationTree.padTo
  exact (FiniteDistinctCardinalityRefutationTree.checkClosed_cast
    (Nat.add_sub_of_le hle) (tree.pad (targetDepth - depth)) definitions
    certificate).trans (tree.checkClosed_pad definitions certificate
      (targetDepth - depth))

theorem exists_uniform_checked_closed_cardinality_trees
    {Index : Type} [Finite Index]
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : Index → FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hencode : ∀ index, ∃ depth,
      ∃ tree : FiniteDistinctCardinalityRefutationTree
          nodeCount conceptCount roleCount variableCount depth,
        tree.checkClosed definitions (certificate index) = true) :
    ∃ depth, ∃ trees : Index → FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount depth,
      ∀ index, (trees index).checkClosed definitions (certificate index) = true := by
  classical
  let childDepth : Index → Nat := fun index => (hencode index).choose
  obtain ⟨depth, hdepth⟩ := Finite.exists_le childDepth
  let rawTree (index : Index) : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount (childDepth index) :=
    (hencode index).choose_spec.choose
  let trees (index : Index) := (rawTree index).padTo (hdepth index)
  refine ⟨depth, trees, ?_⟩
  intro index
  change ((rawTree index).padTo (hdepth index)).checkClosed definitions
    (certificate index) = true
  rw [FiniteDistinctCardinalityRefutationTree.checkClosed_padTo]
  exact (hencode index).choose_spec.choose_spec

/-- Completeness of the production quotient-closed cardinality checker for
finite semantic refutations. -/
theorem ClosedDistinctCardinalityRefutes.exists_checkClosed_tree
    {ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    {state : DistinctEqState (Fin nodeCount) (Fin conceptCount) (Fin roleCount)}
    (hrefutes : ClosedDistinctCardinalityRefutes
      (Fin nodeCount) ontology definitions state) :
    ∀ certificate : FiniteDistinctEqCertificate
        nodeCount conceptCount roleCount variableCount,
      certificate.base.base.ontology = ontology → certificate.state = state →
      certificate.base.equalityClosureValidB = true →
      ∃ depth, ∃ tree : FiniteDistinctCardinalityRefutationTree
          nodeCount conceptCount roleCount variableCount depth,
        tree.checkClosed definitions certificate = true := by
  induction hrefutes with
  | equality state tree =>
      intro certificate hontology hstate hvalid
      obtain ⟨encoded, hencoded⟩ := tree.exists_checkClosed_tree certificate.base
        hontology (congrArg DistinctEqState.base hstate) hvalid
      exact ⟨0, .equality encoded, by
        simpa [FiniteDistinctCardinalityRefutationTree.checkClosed] using hencoded⟩
  | clash state hclash =>
      intro certificate hontology hstate hvalid
      rcases hclash with
        ⟨positiveNode, negativeNode, concept, hequiv, hpositive, hnegative⟩
      have hclosed : certificate.base.closedClashB = true := by
        cases hvalue : certificate.base.closedClashB with
        | true => rfl
        | false =>
            have hfree := certificate.base.not_closedClashB_closedClashFree
              hvalid hvalue
            have hbase : certificate.base.state = state.base :=
              congrArg DistinctEqState.base hstate
            rw [hbase] at hfree
            exact (hfree positiveNode negativeNode concept hequiv
              ⟨hpositive, hnegative⟩).elim
      exact ⟨0, .clash, by
        simp [FiniteDistinctCardinalityRefutationTree.checkClosed, hvalid,
          hclosed]⟩
  | equalityApart state left right hequal hapart =>
      intro certificate hontology hstate hvalid
      refine ⟨0, .equalityApart left right, ?_⟩
      have hequal' : certificate.state.base.equiv left right := by
        rw [hstate]
        exact hequal
      have hapart' : (left, right) ∈ certificate.apart := by
        change certificate.state.apart left right
        rw [hstate]
        exact hapart
      simp [FiniteDistinctCardinalityRefutationTree.checkClosed, hvalid,
        (certificate.base.closedRelatedB_eq_true hvalid left right).2 hequal',
        hapart']
  | branch state clause hclause assignment hbody children ih =>
      intro certificate hontology hstate hvalid
      have hclause' : clause ∈ certificate.base.base.ontology := by
        simpa [hontology] using hclause
      have hbody' : ∀ atom ∈ clause.body,
          certificate.base.quotientClosedHoldsAtomB assignment atom = true := by
        intro atom hatom
        apply (certificate.base.quotientClosedHoldsAtomB_eq_true hvalid
          assignment atom).2
        have hbase : certificate.base.state = state.base :=
          congrArg DistinctEqState.base hstate
        rw [hbase]
        exact hbody atom hatom
      let next (index : Fin clause.head.length) :=
        certificate.canonicalAssertAtom assignment (clause.head.get index)
      obtain ⟨depth, encodedChildren, hencodedChildren⟩ :=
        exists_uniform_checked_closed_cardinality_trees definitions next
          (fun index => by
            have hatom : clause.head.get index ∈ clause.head := List.get_mem _ _
            apply ih (clause.head.get index) hatom (next index)
            · have htransition := certificate.transitionB_canonicalAssertAtom
                  assignment (clause.head.get index)
              have hbase := certificate.base.transitionB_base (next index).base
                assignment (clause.head.get index) (by
                  have hparts : certificate.base.transitionB (next index).base
                      assignment (clause.head.get index) = true ∧
                      (next index).apart = certificate.apart := by
                    simpa [FiniteDistinctEqCertificate.transitionB, next] using
                      htransition
                  exact hparts.1)
              rw [hbase]
              cases clause.head.get index <;> simpa using hontology
            · calc
                (next index).state = certificate.state.assertAtom assignment
                    (clause.head.get index) :=
                  certificate.transitionB_state (next index) assignment
                    (clause.head.get index) (by
                      simpa [next] using
                        certificate.transitionB_canonicalAssertAtom assignment
                          (clause.head.get index))
                _ = state.assertAtom assignment (clause.head.get index) := by
                  rw [hstate]
            · exact (certificate.base.assertAtom assignment
                (clause.head.get index)).canonicalizeEqualityClosure_valid)
      refine ⟨depth + 1, .branch clause assignment next encodedChildren, ?_⟩
      simp only [FiniteDistinctCardinalityRefutationTree.checkClosed,
        Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨hvalid, hclause'⟩, hbody'⟩, ?_⟩
      intro index
      refine ⟨?_, hencodedChildren index⟩
      simpa [next] using
        (certificate.transitionB_canonicalAssertAtom assignment
          (clause.head.get index))
  | witness state source target role filler hobligation hfresh child ih =>
      intro certificate hontology hstate hvalid
      have hobligation' :
          (role, filler, source) ∈ certificate.base.base.obligations := by
        change certificate.state.base.base.obligation role filler source
        rw [hstate]
        exact hobligation
      have hfresh' : certificate.freshNodeB target = true :=
        (certificate.freshNodeB_eq_true target hvalid).2
          (by simpa [hstate] using hfresh)
      obtain ⟨depth, encodedChild, hencodedChild⟩ :=
        ih (certificate.materializeWitness source target role filler)
          (by simpa [hontology])
          (by rw [certificate.state_materializeWitness, hstate]) hvalid
      exact ⟨depth + 1, .witness source target role filler encodedChild, by
        simp [FiniteDistinctCardinalityRefutationTree.checkClosed, hvalid,
          hobligation', hfresh', hencodedChild]⟩
  | maximum state definition hdefinition hkind source hmarker witnesses hedge
      hfiller children ih =>
      intro certificate hontology hstate hvalid
      have hbase : certificate.base.state = state.base := by
        simpa [FiniteDistinctEqCertificate.state] using
          congrArg DistinctEqState.base hstate
      let Pair := { pair : Fin (definition.bound + 1) ×
          Fin (definition.bound + 1) // pair.1 ≠ pair.2 }
      let nextPair (pair : Pair) :=
        certificate.canonicalMerge (witnesses pair.1.1) (witnesses pair.1.2)
      obtain ⟨depth, encodedPair, hencodedPair⟩ :=
        exists_uniform_checked_closed_cardinality_trees definitions nextPair
          (fun pair => by
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
                _ = state.merge (witnesses pair.1.1)
                    (witnesses pair.1.2) := by rw [hstate]
            · exact certificate.base.canonicalMerge_valid _ _)
      let next (left right : Fin (definition.bound + 1)) :=
        if hne : left ≠ right then nextPair ⟨(left, right), hne⟩ else certificate
      let encodedChildren (left right : Fin (definition.bound + 1)) :
          FiniteDistinctCardinalityRefutationTree
            nodeCount conceptCount roleCount variableCount depth :=
        if hne : left ≠ right then encodedPair ⟨(left, right), hne⟩
        else FiniteDistinctCardinalityRefutationTree.clash.padTo
          (Nat.zero_le depth)
      have hmarker' : certificate.base.closedLabelB source
          (.pos definition.marker) = true := by
        apply (certificate.base.closedLabelB_eq_true_iff hvalid _ _).2
        rw [hbase]
        exact hmarker
      have hedge' : ∀ index, certificate.base.closedEdgeB definition.role
          source (witnesses index) = true := by
        intro index
        apply (certificate.base.closedEdgeB_eq_true_iff hvalid _ _ _).2
        rw [hbase]
        exact hedge index
      have hfiller' : ∀ index, certificate.base.closedLabelB
          (witnesses index) (.pos definition.filler) = true := by
        intro index
        apply (certificate.base.closedLabelB_eq_true_iff hvalid _ _).2
        rw [hbase]
        exact hfiller index
      refine ⟨depth + 1,
        .maximum definition source witnesses next encodedChildren, ?_⟩
      simp only [FiniteDistinctCardinalityRefutationTree.checkClosed,
        Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
        decide_eq_true_eq]
      refine ⟨⟨⟨⟨hvalid, hdefinition⟩, hkind⟩, hmarker'⟩, ?_⟩
      intro index _
      refine ⟨⟨hedge' index, hfiller' index⟩, ?_⟩
      intro other _
      by_cases hne : index ≠ other
      · simp [hne, next, encodedChildren, nextPair,
          certificate.mergeTransitionB_canonicalMerge,
          hencodedPair ⟨(index, other), hne⟩]
      · simp [not_ne_iff.mp hne]
  | minimum state definition hdefinition hkind source hmarker targets hfresh
      child ih =>
      intro certificate hontology hstate hvalid
      have hbase : certificate.base.state = state.base := by
        simpa [FiniteDistinctEqCertificate.state] using
          congrArg DistinctEqState.base hstate
      let next := certificate.canonicalMinimum source targets definition.role
        definition.filler
      obtain ⟨depth, encodedChild, hencodedChild⟩ := ih next (by
          simp [next, FiniteDistinctEqCertificate.canonicalMinimum,
            FiniteEqCertificate.canonicalMinimum,
            FiniteEqCertificate.canonicalizeEqualityClosure, hontology]) (by
          calc
            next.state = certificate.state.materializeMinimum source targets
                definition.role definition.filler :=
              certificate.minimumTransitionB_state next source targets
                definition.role definition.filler
                (certificate.minimumTransitionB_canonicalMinimum source targets
                  definition.role definition.filler)
            _ = state.materializeMinimum source targets definition.role
                definition.filler := by rw [hstate])
          (certificate.base.canonicalMinimum_valid source targets
            definition.role definition.filler)
      have hmarker' : certificate.base.closedLabelB source
          (.pos definition.marker) = true := by
        apply (certificate.base.closedLabelB_eq_true_iff hvalid _ _).2
        rw [hbase]
        exact hmarker
      have hfresh' : certificate.freshFamilyB targets = true :=
        (certificate.freshFamilyB_eq_true targets hvalid).2
          (by simpa [hstate] using hfresh)
      refine ⟨depth + 1, .minimum definition source targets next encodedChild, ?_⟩
      simp [FiniteDistinctCardinalityRefutationTree.checkClosed, hvalid,
        hdefinition, hkind, hmarker', hfresh', next,
        certificate.minimumTransitionB_canonicalMinimum, hencodedChild]

#print axioms ClosedDistinctCardinalityRefutes.exists_checkClosed_tree

end ContextCalculus.Hypertableau
