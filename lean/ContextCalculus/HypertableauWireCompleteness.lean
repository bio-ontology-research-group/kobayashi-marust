import ContextCalculus.HypertableauWire

/-!
# Completeness of the ordinary hypertableau wire format

The JSON decoder stores branch clauses by ontology index and assignments as
ordered node-id lists. This module proves that every finite refutation tree
accepted by the semantic checker has an exact representation in that external
format. The proof follows the checker's mutually recursive tree/children
structure, including the state change beneath every branch and witness.
-/

namespace ContextCalculus.Hypertableau

def FiniteRefutationChildren.trees :
    FiniteRefutationChildren nodeCount conceptCount roleCount variableCount →
      List (FiniteRefutationTree nodeCount conceptCount roleCount variableCount)
  | .nil => []
  | .cons _ child rest => child :: rest.trees

mutual
  theorem FiniteRefutationTree.exists_wire_of_check
      (tree : FiniteRefutationTree nodeCount conceptCount roleCount variableCount) :
      ∀ (checked decoded :
          FiniteSatCertificate nodeCount conceptCount roleCount variableCount),
        checked.ontology = decoded.ontology → tree.check checked = true →
        ∃ wire : WireRefutationTree,
          WireRefutationTree.decode decoded wire = Except.ok tree := by
    cases tree with
    | clash =>
        intro checked decoded hontology hcheck
        refine ⟨WireRefutationTree.clash, ?_⟩
        rw [WireRefutationTree.decode.eq_1]
        rfl
    | branch clause assignment children =>
        intro checked decoded hontology hcheck
        simp only [FiniteRefutationTree.check, Bool.and_eq_true,
          List.all_eq_true, decide_eq_true_eq] at hcheck
        rcases hcheck with ⟨⟨⟨hclause, _⟩, _⟩, hchildren⟩
        obtain ⟨wires, hwiresLength, hwiresDecode, hbuild⟩ :=
          children.exists_wires_of_check checked decoded assignment clause.head
            hontology hchildren
        have hlookup :
            decoded.ontology[checked.ontology.idxOf clause]? = some clause := by
          rw [← hontology]
          exact List.getElem?_idxOf hclause
        refine ⟨WireRefutationTree.branch (checked.ontology.idxOf clause)
          (encodeAssignment assignment) wires, ?_⟩
        rw [WireRefutationTree.decode.eq_2]
        rw [hlookup, decodeAssignment_encode]
        simp [hwiresLength, hwiresDecode]
        change (FiniteRefutationTree.branch clause assignment <$>
          buildChildren clause.head children.trees) =
            Except.ok (FiniteRefutationTree.branch clause assignment children)
        rw [hbuild]
        rfl
    | witness source target role filler child =>
        intro checked decoded hontology hcheck
        simp only [FiniteRefutationTree.check, Bool.and_eq_true,
          decide_eq_true_eq] at hcheck
        rcases hcheck with ⟨⟨_, _⟩, hchild⟩
        have hnextOntology :
            (checked.materializeWitness source target role filler).ontology =
              decoded.ontology := by simpa using hontology
        obtain ⟨wire, hwire⟩ := child.exists_wire_of_check
          (checked.materializeWitness source target role filler) decoded
          hnextOntology hchild
        refine ⟨WireRefutationTree.witness source.val target.val role.val
          (WireLit.encode filler) wire, ?_⟩
        rw [WireRefutationTree.decode.eq_3]
        simp only [checkedFin_value, WireLit.decode_encode, hwire]
        rfl

  theorem FiniteRefutationChildren.exists_wires_of_check
      (children :
        FiniteRefutationChildren nodeCount conceptCount roleCount variableCount) :
      ∀ (checked decoded :
          FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
        (assignment : Fin variableCount → Fin nodeCount)
        (heads :
          List (Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount))),
        checked.ontology = decoded.ontology →
        children.check checked assignment heads = true →
        ∃ wires : List WireRefutationTree,
          wires.length = heads.length ∧
          wires.mapM (WireRefutationTree.decode decoded) =
            Except.ok children.trees ∧
          buildChildren heads children.trees = Except.ok children := by
    cases children with
    | nil =>
        intro checked decoded assignment heads hontology hcheck
        simp only [FiniteRefutationChildren.check, List.isEmpty_iff] at hcheck
        subst heads
        exact ⟨[], rfl, rfl, rfl⟩
    | cons atom child rest =>
        intro checked decoded assignment heads hontology hcheck
        cases heads with
        | nil => simp [FiniteRefutationChildren.check] at hcheck
        | cons head heads =>
            simp only [FiniteRefutationChildren.check, Bool.and_eq_true,
              decide_eq_true_eq] at hcheck
            rcases hcheck with ⟨⟨hatom, hchild⟩, hrest⟩
            subst atom
            have hnextOntology :
                (checked.assertAtom assignment head).ontology = decoded.ontology := by
              simpa using hontology
            obtain ⟨wire, hwire⟩ := child.exists_wire_of_check
              (checked.assertAtom assignment head) decoded hnextOntology hchild
            obtain ⟨wires, hwiresLength, hwiresDecode, hbuild⟩ :=
              rest.exists_wires_of_check checked decoded assignment heads
                hontology hrest
            refine ⟨wire :: wires, by simp [hwiresLength], ?_, ?_⟩
            · simp only [List.mapM_cons, hwire, hwiresDecode]
              rfl
            · simp only [FiniteRefutationChildren.trees, buildChildren, hbuild]
              rfl
end

/-- Every accepted finite ordinary HT refutation is exactly representable by
the untrusted JSON tree format consumed by the executable Lean checker. -/
theorem FiniteRefutationTree.wire_complete
    (certificate :
      FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (tree : FiniteRefutationTree nodeCount conceptCount roleCount variableCount)
    (hcheck : tree.check certificate = true) :
    ∃ wire : WireRefutationTree,
      WireRefutationTree.decode certificate wire = Except.ok tree :=
  tree.exists_wire_of_check certificate certificate rfl hcheck

#print axioms FiniteRefutationTree.exists_wire_of_check
#print axioms FiniteRefutationChildren.exists_wires_of_check
#print axioms FiniteRefutationTree.wire_complete

end ContextCalculus.Hypertableau
