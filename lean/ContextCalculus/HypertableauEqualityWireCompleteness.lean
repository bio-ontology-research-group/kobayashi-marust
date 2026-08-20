import ContextCalculus.HypertableauEqualityWire
import Mathlib.Data.List.OfFn

/-!
# Lossless equality-aware hypertableau state encoding

Equality-aware branch trees carry a complete finite equality certificate at
every child. This module constructs its external representation and proves
that the existing bounds-checking decoder returns the exact original state.
-/

namespace ContextCalculus.Hypertableau

def WireLabel.encode (entry : Fin nodeCount × Lit (Fin conceptCount)) : WireLabel where
  node := entry.1.val
  literal := WireLit.encode entry.2

@[simp] theorem WireLabel.decode_encode_list
    (labels : List (Fin nodeCount × Lit (Fin conceptCount))) :
    (labels.map WireLabel.encode).mapM (fun label => do
      return (← checkedFin "node" nodeCount label.node,
        ← label.literal.decode conceptCount)) = Except.ok labels := by
  induction labels with
  | nil => rfl
  | cons label labels ih =>
      rcases label with ⟨node, literal⟩
      simp only [List.map_cons, List.mapM_cons, WireLabel.encode,
        checkedFin_value, WireLit.decode_encode, ih]
      rfl

def WireEdge.encode
    (entry : Fin roleCount × Fin nodeCount × Fin nodeCount) : WireEdge where
  role := entry.1.val
  source := entry.2.1.val
  target := entry.2.2.val

@[simp] theorem WireEdge.decode_encode_list
    (edges : List (Fin roleCount × Fin nodeCount × Fin nodeCount)) :
    (edges.map WireEdge.encode).mapM (fun edge => do
      return (← checkedFin "role" roleCount edge.role,
        ← checkedFin "node" nodeCount edge.source,
        ← checkedFin "node" nodeCount edge.target)) = Except.ok edges := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      rcases edge with ⟨role, source, target⟩
      simp only [List.map_cons, List.mapM_cons, WireEdge.encode,
        checkedFin_value, ih]
      rfl

def WireObligation.encode
    (entry : Fin roleCount × Lit (Fin conceptCount) × Fin nodeCount) :
    WireObligation where
  role := entry.1.val
  filler := WireLit.encode entry.2.1
  node := entry.2.2.val

@[simp] theorem WireObligation.decode_encode_list
    (obligations :
      List (Fin roleCount × Lit (Fin conceptCount) × Fin nodeCount)) :
    (obligations.map WireObligation.encode).mapM (fun obligation => do
      return (← checkedFin "role" roleCount obligation.role,
        ← obligation.filler.decode conceptCount,
        ← checkedFin "node" nodeCount obligation.node)) =
      Except.ok obligations := by
  induction obligations with
  | nil => rfl
  | cons obligation obligations ih =>
      rcases obligation with ⟨role, filler, node⟩
      simp only [List.map_cons, List.mapM_cons, WireObligation.encode,
        checkedFin_value, WireLit.decode_encode, ih]
      rfl

def WireEquality.encode (entry : Fin nodeCount × Fin nodeCount) : WireEquality where
  left := entry.1.val
  right := entry.2.val

@[simp] theorem WireEquality.decode_encode_list
    (equalities : List (Fin nodeCount × Fin nodeCount)) :
    (equalities.map WireEquality.encode).mapM (fun equality => do
      return (← checkedFin "equality node" nodeCount equality.left,
        ← checkedFin "equality node" nodeCount equality.right)) =
      Except.ok equalities := by
  induction equalities with
  | nil => rfl
  | cons equality equalities ih =>
      rcases equality with ⟨left, right⟩
      simp only [List.map_cons, List.mapM_cons, WireEquality.encode,
        checkedFin_value, ih]
      rfl

def encodeNodeVector (values : Fin nodeCount → Fin nodeCount) : List Nat :=
  List.ofFn fun index => (values index).val

@[simp] theorem decodeNodeVector_encode (kind : String)
    (values : Fin nodeCount → Fin nodeCount) :
    decodeNodeVector kind nodeCount (encodeNodeVector values) = Except.ok values := by
  unfold decodeNodeVector encodeNodeVector
  have hencoded :
      List.ofFn (fun index => (values index).val) =
        (List.ofFn values).map Fin.val := by
    simpa [Function.comp_def] using
      (List.map_ofFn (f := values) (g := Fin.val)).symm
  rw [hencoded, checkedFin_value_list]
  change (if h : (List.ofFn values).length = nodeCount then
      Except.ok (fun index => (List.ofFn values).get (h.symm ▸ index))
    else Except.error _) = Except.ok values
  split <;> rename_i h
  · congr
    funext index
    rw [List.get_ofFn]
    apply congrArg values
    have heq : h = List.length_ofFn (f := values) := Subsingleton.elim _ _
    rw [heq]
    exact finCast_transport_back _ _
  · exact (h (by simp)).elim

def encodeNodePaths (paths : Fin nodeCount → List (Fin nodeCount)) :
    List (List Nat) :=
  List.ofFn fun index => (paths index).map Fin.val

@[simp] theorem decodeNodePaths_encode
    (paths : Fin nodeCount → List (Fin nodeCount)) :
    decodeNodePaths nodeCount (encodeNodePaths paths) = Except.ok paths := by
  unfold decodeNodePaths encodeNodePaths
  have hencoded :
      List.ofFn (fun index => (paths index).map Fin.val) =
        (List.ofFn paths).map (List.map Fin.val) := by
    simpa [Function.comp_def] using
      (List.map_ofFn (f := paths) (g := List.map Fin.val)).symm
  rw [hencoded]
  have hdecoded :
      ((List.ofFn paths).map (List.map Fin.val)).mapM
          (fun path => path.mapM (checkedFin "path node" nodeCount)) =
        Except.ok (List.ofFn paths) := by
    induction List.ofFn paths with
    | nil => rfl
    | cons path rest ih =>
        simp only [List.map_cons, List.mapM_cons, checkedFin_value_list, ih]
        rfl
  rw [hdecoded]
  change (if h : (List.ofFn paths).length = nodeCount then
      Except.ok (fun index => (List.ofFn paths).get (h.symm ▸ index))
    else Except.error _) = Except.ok paths
  split <;> rename_i h
  · congr
    funext index
    rw [List.get_ofFn]
    apply congrArg paths
    have heq : h = List.length_ofFn (f := paths) := Subsingleton.elim _ _
    rw [heq]
    exact finCast_transport_back _ _
  · exact (h (by simp)).elim

def WireEqState.encode
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount) :
    WireEqState where
  labels := certificate.base.labels.map WireLabel.encode
  edges := certificate.base.edges.map WireEdge.encode
  obligations := certificate.base.obligations.map WireObligation.encode
  equalities := certificate.equalities.map WireEquality.encode
  representatives := encodeNodeVector certificate.representative
  representative_paths := encodeNodePaths certificate.representativePath

@[simp] theorem WireEqState.decode_encode
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount) :
    (WireEqState.encode certificate).decode nodeCount conceptCount roleCount
        variableCount certificate.base.ontology = Except.ok certificate := by
  rcases certificate with ⟨⟨ontology, labels, edges, obligations⟩,
    equalities, representative, representativePath⟩
  simp only [WireEqState.encode, WireEqState.decode,
    WireLabel.decode_encode_list, WireEdge.decode_encode_list,
    WireObligation.decode_encode_list, WireEquality.decode_encode_list,
    decodeNodeVector_encode, decodeNodePaths_encode]
  rfl

theorem WireEqState.decode_encode_of_ontology
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (hontology : certificate.base.ontology = ontology) :
    (WireEqState.encode certificate).decode nodeCount conceptCount roleCount
        variableCount ontology = Except.ok certificate := by
  subst ontology
  exact WireEqState.decode_encode certificate

def FiniteEqRefutationChildren.entries :
    FiniteEqRefutationChildren nodeCount conceptCount roleCount variableCount →
      List (FiniteEqCertificate nodeCount conceptCount roleCount variableCount ×
        FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
  | .nil => []
  | .cons _ next child rest => (next, child) :: rest.entries

mutual
  theorem FiniteEqRefutationTree.exists_wire_of_check
      (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount) :
      ∀ (checked :
          FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
        (ontology :
          List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))),
        checked.base.ontology = ontology → tree.check checked = true →
        ∃ wire : WireEqRefutationTree,
          wire.decode nodeCount conceptCount roleCount variableCount ontology =
            Except.ok tree := by
    cases tree with
    | clash =>
        intro checked ontology hontology hcheck
        refine ⟨WireEqRefutationTree.clash, ?_⟩
        rw [WireEqRefutationTree.decode.eq_1]
        rfl
    | branch clause assignment children =>
        intro checked ontology hontology hcheck
        simp only [FiniteEqRefutationTree.check, Bool.and_eq_true,
          List.all_eq_true, decide_eq_true_eq] at hcheck
        rcases hcheck with ⟨⟨⟨_, hclause⟩, _⟩, hchildren⟩
        obtain ⟨wires, hwiresLength, hwiresDecode, hbuild⟩ :=
          children.exists_wires_of_check checked ontology assignment clause.head
            hontology hchildren
        have hlookup : ontology[checked.base.ontology.idxOf clause]? = some clause := by
          rw [← hontology]
          exact List.getElem?_idxOf hclause
        refine ⟨WireEqRefutationTree.branch
          (checked.base.ontology.idxOf clause) (encodeAssignment assignment) wires, ?_⟩
        rw [WireEqRefutationTree.decode.eq_2, hlookup, decodeAssignment_encode]
        simp [hwiresLength]
        rw [hwiresDecode]
        change (FiniteEqRefutationTree.branch clause assignment <$>
          buildEqChildren clause.head children.entries) =
            Except.ok (FiniteEqRefutationTree.branch clause assignment children)
        rw [hbuild]
        rfl
    | witness source target role filler child =>
        intro checked ontology hontology hcheck
        simp only [FiniteEqRefutationTree.check, Bool.and_eq_true,
          decide_eq_true_eq] at hcheck
        rcases hcheck with ⟨⟨⟨_, _⟩, _⟩, hchild⟩
        have hnextOntology :
            (checked.materializeWitness source target role filler).base.ontology =
              ontology := by simpa using hontology
        obtain ⟨wire, hwire⟩ := child.exists_wire_of_check
          (checked.materializeWitness source target role filler) ontology
          hnextOntology hchild
        refine ⟨WireEqRefutationTree.witness source.val target.val role.val
          (WireLit.encode filler) wire, ?_⟩
        rw [WireEqRefutationTree.decode.eq_3]
        simp only [checkedFin_value, WireLit.decode_encode, hwire]
        rfl

  theorem FiniteEqRefutationChildren.exists_wires_of_check
      (children :
        FiniteEqRefutationChildren nodeCount conceptCount roleCount variableCount) :
      ∀ (checked :
          FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
        (ontology :
          List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
        (assignment : Fin variableCount → Fin nodeCount)
        (heads :
          List (Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount))),
        checked.base.ontology = ontology →
        children.check checked assignment heads = true →
        ∃ wires : List (WireEqState × WireEqRefutationTree),
          wires.length = heads.length ∧
          wires.mapM (fun child => do
            let state ← child.1.decode nodeCount conceptCount roleCount
              variableCount ontology
            Prod.mk state <$> child.2.decode nodeCount conceptCount roleCount
              variableCount ontology) = Except.ok children.entries ∧
          buildEqChildren heads children.entries = Except.ok children := by
    cases children with
    | nil =>
        intro checked ontology assignment heads hontology hcheck
        simp only [FiniteEqRefutationChildren.check, List.isEmpty_iff] at hcheck
        subst heads
        exact ⟨[], rfl, rfl, rfl⟩
    | cons atom next child rest =>
        intro checked ontology assignment heads hontology hcheck
        cases heads with
        | nil => simp [FiniteEqRefutationChildren.check] at hcheck
        | cons head heads =>
            simp only [FiniteEqRefutationChildren.check, Bool.and_eq_true,
              decide_eq_true_eq] at hcheck
            rcases hcheck with ⟨⟨⟨hatom, htransition⟩, hchild⟩, hrest⟩
            subst atom
            have hnextOntology : next.base.ontology = ontology := by
              have hbase := checked.transitionB_base next assignment head htransition
              calc
                next.base.ontology = checked.base.ontology := by
                  have hfields := congrArg FiniteSatCertificate.ontology hbase
                  cases head <;>
                    simpa [FiniteEqCertificate.assertAtom] using hfields
                _ = ontology := hontology
            obtain ⟨wire, hwire⟩ := child.exists_wire_of_check next ontology
              hnextOntology hchild
            obtain ⟨wires, hwiresLength, hwiresDecode, hbuild⟩ :=
              rest.exists_wires_of_check checked ontology assignment heads
                hontology hrest
            refine ⟨(WireEqState.encode next, wire) :: wires,
              by simp [hwiresLength], ?_, ?_⟩
            · simp only [List.mapM_cons]
              rw [WireEqState.decode_encode_of_ontology next ontology hnextOntology,
                hwire, hwiresDecode]
              rfl
            · simp only [FiniteEqRefutationChildren.entries, buildEqChildren, hbuild]
              rfl
end

/-- Every accepted finite equality-aware HT refutation is exactly
representable by the version-2 JSON tree format. -/
theorem FiniteEqRefutationTree.wire_complete
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
    (hcheck : tree.check certificate = true) :
    ∃ wire : WireEqRefutationTree,
      wire.decode nodeCount conceptCount roleCount variableCount
        certificate.base.ontology = Except.ok tree :=
  tree.exists_wire_of_check certificate certificate.base.ontology rfl hcheck

#print axioms WireLabel.decode_encode_list
#print axioms WireEdge.decode_encode_list
#print axioms WireObligation.decode_encode_list
#print axioms WireEquality.decode_encode_list
#print axioms decodeNodeVector_encode
#print axioms decodeNodePaths_encode
#print axioms WireEqState.decode_encode
#print axioms FiniteEqRefutationTree.exists_wire_of_check
#print axioms FiniteEqRefutationChildren.exists_wires_of_check
#print axioms FiniteEqRefutationTree.wire_complete

end ContextCalculus.Hypertableau
