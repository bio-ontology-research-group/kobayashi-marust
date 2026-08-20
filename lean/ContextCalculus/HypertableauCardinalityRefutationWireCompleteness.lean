import ContextCalculus.HypertableauCardinalityRefutationWire
import ContextCalculus.HypertableauEqualityWireCompleteness
import Mathlib.Data.List.OfFn

/-!
# Cardinality-refutation wire completeness

The cardinality wire represents dependent finite vectors as JSON lists. These
lemmas prove that exact-length decoding reconstructs the original functions,
including nested square matrices. They form the data boundary used by branch,
minimum, and maximum refutation constructors.
-/

namespace ContextCalculus.Hypertableau

theorem mapM_eq_ok_map_of_forall
    (values : List α) (decode : α → Except ε β) (encode : α → β)
    (hdecode : ∀ value ∈ values, decode value = Except.ok (encode value)) :
    values.mapM decode = Except.ok (values.map encode) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [List.mapM_cons, hdecode value (by simp), ih]
      · rfl
      · intro item hitem
        exact hdecode item (by simp [hitem])

@[simp] theorem FiniteEqCertificate.ontology_assertAtom
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) :
    (certificate.assertAtom assignment atom).base.ontology =
      certificate.base.ontology := by
  cases atom <;> rfl

def encodeExactVector (values : Fin expected → α) : List α := List.ofFn values

@[simp] theorem decodeExactVector_encode (kind : String)
    (values : Fin expected → α) :
    decodeExactVector kind expected (encodeExactVector values) = Except.ok values := by
  unfold decodeExactVector encodeExactVector
  split <;> rename_i h
  · congr
    funext index
    rw [List.get_ofFn]
    apply congrArg values
    have heq : h = List.length_ofFn (f := values) := Subsingleton.elim _ _
    rw [heq]
    exact finCast_transport_back _ _
  · exact (h (by simp)).elim

@[simp] theorem decodeExactVector_encode_list (kind : String)
    (values : List (Fin expected → α)) :
    (values.map encodeExactVector).mapM (decodeExactVector kind expected) =
      Except.ok values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.map_cons, List.mapM_cons, decodeExactVector_encode, ih]
      rfl

def encodeCheckedNodeVector (values : Fin expected → Fin nodeCount) : List Nat :=
  List.ofFn fun index => (values index).val

@[simp] theorem decodeCheckedNodeVector_encode (kind : String)
    (values : Fin expected → Fin nodeCount) :
    (do
      let decoded ← (encodeCheckedNodeVector values).mapM
        (checkedFin kind nodeCount)
      decodeExactVector kind expected decoded) = Except.ok values := by
  unfold encodeCheckedNodeVector
  have hencoded :
      List.ofFn (fun index => (values index).val) =
        (List.ofFn values).map Fin.val := by
    simpa [Function.comp_def, encodeExactVector] using
      (List.map_ofFn (f := values) (g := Fin.val)).symm
  rw [hencoded, checkedFin_value_list]
  change decodeExactVector kind expected (List.ofFn values) = Except.ok values
  exact decodeExactVector_encode kind values

def encodeExactMatrix (values : Fin width → Fin width → α) :
    List (List α) :=
  List.ofFn fun row => List.ofFn fun column => values row column

@[simp] theorem decodeExactMatrix_encode (rowKind columnKind : String)
    (values : Fin width → Fin width → α) :
    (do
      let rows ← (encodeExactMatrix values).mapM fun row =>
        decodeExactVector columnKind width row
      decodeExactVector rowKind width rows) = Except.ok values := by
  unfold encodeExactMatrix
  have hencoded :
      List.ofFn (fun row => List.ofFn fun column => values row column) =
        (List.ofFn values).map encodeExactVector := by
    simpa [Function.comp_def, encodeExactVector] using
      (List.map_ofFn (f := values) (g := encodeExactVector)).symm
  rw [hencoded]
  rw [decodeExactVector_encode_list]
  change decodeExactVector rowKind width (List.ofFn values) = Except.ok values
  exact decodeExactVector_encode rowKind values

def FiniteCardinalityEqRefutationTree.canonical :
    (depth : Nat) → FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount depth
  | 0 => .clash
  | depth + 1 => .delay (canonical depth)

def WireCardinalityEqRefutationTree.canonical :
    Nat → WireCardinalityEqRefutationTree
  | 0 => .clash
  | depth + 1 => .delay (canonical depth)

@[simp] theorem WireCardinalityEqRefutationTree.decodeAtDepth_canonical
    (depth : Nat)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) :
    (WireCardinalityEqRefutationTree.canonical depth).decodeAtDepth
        nodeCount conceptCount roleCount variableCount ontology definitions depth =
      Except.ok (FiniteCardinalityEqRefutationTree.canonical depth) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp only [WireCardinalityEqRefutationTree.canonical,
        WireCardinalityEqRefutationTree.decodeAtDepth,
        FiniteCardinalityEqRefutationTree.canonical, ih]
      rfl

theorem decodeEqStateTreeVector_encode
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (next : Fin width →
      FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (wires : Fin width → WireCardinalityEqRefutationTree)
    (trees : Fin width → FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (hontology : ∀ index, (next index).base.ontology = ontology)
    (htrees : ∀ index,
      (wires index).decodeAtDepth nodeCount conceptCount roleCount variableCount
        ontology definitions depth = Except.ok (trees index)) :
    (List.ofFn fun index => (WireEqState.encode (next index), wires index)).mapM
        (fun child => do
          let state ← child.1.decode nodeCount conceptCount roleCount variableCount ontology
          let tree ← child.2.decodeAtDepth nodeCount conceptCount roleCount variableCount
            ontology definitions depth
          return (state, tree)) =
      Except.ok (List.ofFn fun index => (next index, trees index)) := by
  induction width with
  | zero => rfl
  | succ width ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.mapM_cons]
      rw [WireEqState.decode_encode_of_ontology (next 0) ontology
        (hontology 0), htrees 0]
      have htail := ih (fun index => next index.succ)
        (fun index => wires index.succ) (fun index => trees index.succ)
        (fun index => hontology index.succ) (fun index => htrees index.succ)
      rw [htail]
      rfl

theorem decodeEqStateTreeRows_encode
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (next : Fin rows → Fin columns →
      FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (wires : Fin rows → Fin columns → WireCardinalityEqRefutationTree)
    (trees : Fin rows → Fin columns → FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (hontology : ∀ row column, (next row column).base.ontology = ontology)
    (htrees : ∀ row column,
      (wires row column).decodeAtDepth nodeCount conceptCount roleCount variableCount
        ontology definitions depth = Except.ok (trees row column)) :
    (List.ofFn fun row => List.ofFn fun column =>
        (WireEqState.encode (next row column), wires row column)).mapM
      (fun row => do
        let decodedRow ← row.mapM (fun child => do
          let state ← child.1.decode nodeCount conceptCount roleCount variableCount ontology
          let tree ← child.2.decodeAtDepth nodeCount conceptCount roleCount variableCount
            ontology definitions depth
          return (state, tree))
        decodeExactVector "maximum child row" columns decodedRow) =
      Except.ok (List.ofFn fun row => fun column =>
        (next row column, trees row column)) := by
  induction rows with
  | zero => rfl
  | succ rows ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.mapM_cons]
      rw [decodeEqStateTreeVector_encode ontology (next 0) (wires 0) (trees 0)
        definitions (hontology 0) (htrees 0)]
      change (do
        let first ← decodeExactVector "maximum child row" columns
          (encodeExactVector fun column => (next 0 column, trees 0 column))
        let rest ← List.mapM _ _
        pure (first :: rest)) = _
      rw [decodeExactVector_encode]
      have htail := ih (fun row column => next row.succ column)
        (fun row column => wires row.succ column)
        (fun row column => trees row.succ column)
        (fun row column => hontology row.succ column)
        (fun row column => htrees row.succ column)
      rw [htail]
      rfl

/-- Every accepted cardinality refutation has a wire representation that
decodes to an accepted refutation at the same declared depth. Maximum-rule
diagonal cells are canonicalized because the checker intentionally ignores
them; all semantically relevant off-diagonal cells preserve their checked
successors. -/
theorem FiniteCardinalityEqRefutationTree.exists_checked_wire
    (tree : FiniteCardinalityEqRefutationTree
      nodeCount conceptCount roleCount variableCount depth) :
    ∀ (certificate : FiniteEqCertificate
        nodeCount conceptCount roleCount variableCount)
      (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
      (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))),
      certificate.base.ontology = ontology →
      tree.check definitions certificate = true →
      ∃ wire : WireCardinalityEqRefutationTree,
        ∃ decoded : FiniteCardinalityEqRefutationTree
            nodeCount conceptCount roleCount variableCount depth,
        WireCardinalityEqRefutationTree.decodeAtDepth
            nodeCount conceptCount roleCount variableCount
            ontology definitions depth wire = Except.ok decoded ∧
        FiniteCardinalityEqRefutationTree.check definitions certificate decoded = true := by
  induction tree with
  | equality eqTree =>
      intro certificate ontology definitions hontology hcheck
      obtain ⟨wire, hwire⟩ := eqTree.exists_wire_of_check certificate
        certificate.base.ontology rfl hcheck
      refine ⟨WireCardinalityEqRefutationTree.equality wire,
        FiniteCardinalityEqRefutationTree.equality eqTree, ?_, hcheck⟩
      simp only [WireCardinalityEqRefutationTree.decodeAtDepth]
      rw [← hontology, hwire]
      rfl
  | clash =>
      intro certificate ontology definitions hontology hcheck
      exact ⟨WireCardinalityEqRefutationTree.clash,
        FiniteCardinalityEqRefutationTree.clash, rfl, hcheck⟩
  | delay child ih =>
      intro certificate ontology definitions hontology hcheck
      obtain ⟨wire, decoded, hdecode, hdecoded⟩ :=
        ih certificate ontology definitions hontology hcheck
      exact ⟨WireCardinalityEqRefutationTree.delay wire,
        FiniteCardinalityEqRefutationTree.delay decoded,
        by simp only [WireCardinalityEqRefutationTree.decodeAtDepth, hdecode]; rfl,
        hdecoded⟩
  | branch clause assignment next children ih =>
      intro certificate ontology definitions hontology hcheck
      simp only [FiniteCardinalityEqRefutationTree.check, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨⟨hvalid, hclause⟩, hbody⟩, hall⟩
      have hnextOntology : ∀ index, (next index).base.ontology = ontology := by
        intro index
        have htransition := (hall index).1
        have hbase := certificate.transitionB_base (next index) assignment
          (clause.head.get index) htransition
        calc
          (next index).base.ontology = certificate.base.ontology := by
            have hfields := congrArg FiniteSatCertificate.ontology hbase
            simpa only [FiniteEqCertificate.ontology_assertAtom] using hfields
          _ = ontology := hontology
      have hex := fun index => ih index (next index) ontology definitions
        (hnextOntology index) (hall index).2
      choose wires decoded hdecode hdecoded using hex
      have hlookup : ontology[certificate.base.ontology.idxOf clause]? = some clause := by
        rw [← hontology]
        exact List.getElem?_idxOf hclause
      refine ⟨WireCardinalityEqRefutationTree.branch
          (certificate.base.ontology.idxOf clause)
          (encodeAssignment assignment)
          (List.ofFn fun index => (WireEqState.encode (next index), wires index)),
        FiniteCardinalityEqRefutationTree.branch clause assignment next decoded, ?_, ?_⟩
      · simp only [WireCardinalityEqRefutationTree.decodeAtDepth]
        rw [hlookup, decodeAssignment_encode]
        rw [decodeEqStateTreeVector_encode ontology next wires decoded definitions
          hnextOntology hdecode]
        change (do
          let childVector ← decodeExactVector "cardinality branch children"
            clause.head.length (encodeExactVector fun index => (next index, decoded index))
          pure (FiniteCardinalityEqRefutationTree.branch clause assignment
            (fun index => (childVector index).1)
            (fun index => (childVector index).2))) = _
        rw [decodeExactVector_encode]
        rfl
      · simp only [FiniteCardinalityEqRefutationTree.check, Bool.and_eq_true,
          List.all_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨hvalid, hclause⟩, hbody⟩, fun index =>
          ⟨(hall index).1, hdecoded index⟩⟩
  | witness source target role filler child ih =>
      intro certificate ontology definitions hontology hcheck
      simp only [FiniteCardinalityEqRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨⟨hvalid, hobligation⟩, hfresh⟩, hchild⟩
      have hnextOntology :
          (certificate.materializeWitness source target role filler).base.ontology =
            ontology := by simpa using hontology
      obtain ⟨wire, decoded, hdecode, hdecoded⟩ := ih
        (certificate.materializeWitness source target role filler) ontology definitions
        hnextOntology hchild
      refine ⟨WireCardinalityEqRefutationTree.witness source.val target.val role.val
          (WireLit.encode filler) wire,
        FiniteCardinalityEqRefutationTree.witness source target role filler decoded, ?_, ?_⟩
      · simp only [WireCardinalityEqRefutationTree.decodeAtDepth,
          checkedFin_value, WireLit.decode_encode, hdecode]
        rfl
      · simpa only [FiniteCardinalityEqRefutationTree.check, Bool.and_eq_true,
          decide_eq_true_eq] using ⟨⟨⟨hvalid, hobligation⟩, hfresh⟩, hdecoded⟩
  | minimum definition source targets next child ih =>
      intro certificate ontology definitions hontology hcheck
      simp only [FiniteCardinalityEqRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with
        ⟨⟨⟨⟨⟨⟨hvalid, hdefinition⟩, hkind⟩, hmarker⟩, hfresh⟩,
          htransition⟩, hchild⟩
      have hnextOntology : next.base.ontology = ontology := by
        have hfields := htransition
        simp only [FiniteEqCertificate.minimumTransitionB, Bool.and_eq_true,
          decide_eq_true_eq] at hfields
        exact hfields.1.1.1.1.trans hontology
      obtain ⟨wire, decoded, hdecode, hdecoded⟩ :=
        ih next ontology definitions hnextOntology hchild
      have hlookup : definitions[definitions.idxOf definition]? = some definition :=
        List.getElem?_idxOf hdefinition
      refine ⟨WireCardinalityEqRefutationTree.minimum
          (definitions.idxOf definition) source.val
          (encodeCheckedNodeVector targets) (WireEqState.encode next) wire,
        FiniteCardinalityEqRefutationTree.minimum definition source targets next decoded,
        ?_, ?_⟩
      · simp only [WireCardinalityEqRefutationTree.decodeAtDepth]
        simp only [hlookup]
        have hencoded : encodeCheckedNodeVector targets =
            (List.ofFn targets).map Fin.val := by
          simpa [encodeCheckedNodeVector, Function.comp_def] using
            (List.map_ofFn (f := targets) (g := Fin.val)).symm
        rw [hencoded, checkedFin_value_list]
        change (do
          let targetVector ← decodeExactVector "minimum targets" definition.bound
            (encodeExactVector targets)
          let decodedSource ← checkedFin "node" nodeCount source.val
          let decodedNext ← WireEqState.decode nodeCount conceptCount roleCount
            variableCount ontology (WireEqState.encode next)
          let decodedChild ← wire.decodeAtDepth nodeCount conceptCount roleCount
            variableCount ontology definitions _
          pure (FiniteCardinalityEqRefutationTree.minimum definition decodedSource
            targetVector decodedNext decodedChild)) = _
        rw [decodeExactVector_encode, checkedFin_value,
          WireEqState.decode_encode_of_ontology next ontology hnextOntology, hdecode]
        rfl
      · simpa only [FiniteCardinalityEqRefutationTree.check, Bool.and_eq_true,
          decide_eq_true_eq] using
          ⟨⟨⟨⟨⟨⟨hvalid, hdefinition⟩, hkind⟩, hmarker⟩, hfresh⟩,
            htransition⟩, hdecoded⟩
  | @maximum childDepth definition source witnesses next children ih =>
      intro certificate ontology definitions hontology hcheck
      simp only [FiniteCardinalityEqRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with
        ⟨⟨⟨⟨⟨hdefinition, hkind⟩, hmarker⟩, hedges⟩, hlabels⟩, hall⟩
      have hex : ∀ (left right : Fin (definition.bound + 1)),
          ∃ state : FiniteEqCertificate nodeCount conceptCount roleCount variableCount,
          ∃ wire : WireCardinalityEqRefutationTree,
          ∃ decoded : FiniteCardinalityEqRefutationTree
              nodeCount conceptCount roleCount variableCount childDepth,
          state.base.ontology = ontology ∧
          wire.decodeAtDepth nodeCount conceptCount roleCount variableCount
              ontology definitions childDepth = Except.ok decoded ∧
          (left ≠ right →
            state = next left right ∧ decoded.check definitions state = true) := by
        intro left right
        by_cases hne : left ≠ right
        · have hpair := hall left right hne
          have hfields := hpair.1
          simp only [FiniteEqCertificate.mergeTransitionB, Bool.and_eq_true,
            decide_eq_true_eq] at hfields
          have hnextOntology : (next left right).base.ontology = ontology :=
            hfields.1.1.1.1.trans hontology
          obtain ⟨wire, decoded, hdecode, hdecoded⟩ :=
            ih left right (next left right) ontology definitions hnextOntology hpair.2
          exact ⟨next left right, wire, decoded, hnextOntology, hdecode,
            fun _ => ⟨rfl, hdecoded⟩⟩
        · have heq : left = right := Classical.not_not.mp hne
          exact ⟨certificate, WireCardinalityEqRefutationTree.canonical _,
            FiniteCardinalityEqRefutationTree.canonical _, hontology,
            WireCardinalityEqRefutationTree.decodeAtDepth_canonical _ ontology definitions,
            fun h => (h heq).elim⟩
      choose states wires decoded hstates hdecode hrelevant using hex
      have hlookup : definitions[definitions.idxOf definition]? = some definition :=
        List.getElem?_idxOf hdefinition
      refine ⟨WireCardinalityEqRefutationTree.maximum
          (definitions.idxOf definition) source.val
          (encodeCheckedNodeVector witnesses)
          (List.ofFn fun left => List.ofFn fun right =>
            (WireEqState.encode (states left right), wires left right)),
        FiniteCardinalityEqRefutationTree.maximum definition source witnesses states decoded,
        ?_, ?_⟩
      · simp only [WireCardinalityEqRefutationTree.decodeAtDepth]
        simp only [hlookup]
        have hencoded : encodeCheckedNodeVector witnesses =
            (List.ofFn witnesses).map Fin.val := by
          simpa [encodeCheckedNodeVector, Function.comp_def] using
            (List.map_ofFn (f := witnesses) (g := Fin.val)).symm
        rw [hencoded, checkedFin_value_list]
        change (do
          let witnessVector ← decodeExactVector "cardinality witnesses"
            (definition.bound + 1) (encodeExactVector witnesses)
          let decodedRows ← List.mapM _ _
          let childMatrix : Fin (definition.bound + 1) → Fin (definition.bound + 1) →
              (FiniteEqCertificate nodeCount conceptCount roleCount variableCount ×
                FiniteCardinalityEqRefutationTree nodeCount conceptCount roleCount
                  variableCount childDepth) ←
            decodeExactVector "maximum child rows"
            (definition.bound + 1) decodedRows
          let decodedSource ← checkedFin "node" nodeCount source.val
          pure (FiniteCardinalityEqRefutationTree.maximum definition decodedSource
            witnessVector (fun left right => (childMatrix left right).1)
            (fun left right => (childMatrix left right).2))) = _
        rw [decodeExactVector_encode, checkedFin_value]
        rw [decodeEqStateTreeRows_encode ontology states wires decoded definitions
          hstates hdecode]
        change (do
          let childMatrix : Fin (definition.bound + 1) → Fin (definition.bound + 1) →
              (FiniteEqCertificate nodeCount conceptCount roleCount variableCount ×
                FiniteCardinalityEqRefutationTree nodeCount conceptCount roleCount
                  variableCount childDepth) ←
            decodeExactVector "maximum child rows"
            (definition.bound + 1) (encodeExactVector fun left right =>
              (states left right, decoded left right))
          pure (FiniteCardinalityEqRefutationTree.maximum definition source witnesses
            (fun left right => (childMatrix left right).1)
            (fun left right => (childMatrix left right).2))) = _
        rw [decodeExactVector_encode]
        rfl
      · simp only [FiniteCardinalityEqRefutationTree.check, Bool.and_eq_true,
          decide_eq_true_eq]
        refine ⟨⟨⟨⟨⟨hdefinition, hkind⟩, hmarker⟩, hedges⟩, hlabels⟩, ?_⟩
        intro left right hne
        rcases hrelevant left right hne with ⟨hstate, hchecked⟩
        exact ⟨by rw [hstate]; exact (hall left right hne).1, hchecked⟩

#print axioms decodeExactVector_encode
#print axioms decodeExactVector_encode_list
#print axioms decodeCheckedNodeVector_encode
#print axioms decodeExactMatrix_encode
#print axioms WireCardinalityEqRefutationTree.decodeAtDepth_canonical
#print axioms FiniteCardinalityEqRefutationTree.exists_checked_wire

end ContextCalculus.Hypertableau
