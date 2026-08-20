import ContextCalculus.HypertableauCardinalityDistinctWire
import ContextCalculus.HypertableauCardinalityRefutationWireCompleteness

/-!
# Distinct-cardinality refutation wire completeness

Distinct-cardinality states extend equality states with a directed `apart`
relation. This file proves lossless state encoding and the dependent vector and
matrix decoding boundary needed by recursive refutation-tree representability.
-/

namespace ContextCalculus.Hypertableau

def WireApart.encode (pair : Fin nodeCount × Fin nodeCount) : WireApart where
  left := pair.1.val
  right := pair.2.val

@[simp] theorem WireApart.decode_encode_list
    (apart : List (Fin nodeCount × Fin nodeCount)) :
    (apart.map WireApart.encode).mapM (fun pair => do
      return (← checkedFin "apart node" nodeCount pair.left,
        ← checkedFin "apart node" nodeCount pair.right)) = Except.ok apart := by
  induction apart with
  | nil => rfl
  | cons pair apart ih =>
      rcases pair with ⟨left, right⟩
      simp only [List.map_cons, List.mapM_cons, WireApart.encode,
        checkedFin_value, ih]
      rfl

def WireDistinctEqState.encode
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) : WireDistinctEqState where
  base := WireEqState.encode certificate.base
  apart := certificate.apart.map WireApart.encode

@[simp] theorem WireDistinctEqState.decode_encode
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) :
    (WireDistinctEqState.encode certificate).decode nodeCount conceptCount roleCount
        variableCount certificate.base.base.ontology = Except.ok certificate := by
  rcases certificate with ⟨base, apart⟩
  simp only [WireDistinctEqState.encode, WireDistinctEqState.decode,
    WireEqState.decode_encode, WireApart.decode_encode_list]
  rfl

theorem WireDistinctEqState.decode_encode_of_ontology
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (hontology : certificate.base.base.ontology = ontology) :
    (WireDistinctEqState.encode certificate).decode nodeCount conceptCount roleCount
        variableCount ontology = Except.ok certificate := by
  subst ontology
  exact WireDistinctEqState.decode_encode certificate

def FiniteDistinctCardinalityRefutationTree.canonical :
    (depth : Nat) → FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth
  | 0 => .clash
  | depth + 1 => .delay (canonical depth)

def WireDistinctCardinalityRefutationTree.canonical :
    Nat → WireDistinctCardinalityRefutationTree
  | 0 => .clash
  | depth + 1 => .delay (canonical depth)

@[simp] theorem WireDistinctCardinalityRefutationTree.decodeAtDepth_canonical
    (depth : Nat)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) :
    (WireDistinctCardinalityRefutationTree.canonical depth).decodeAtDepth
        nodeCount conceptCount roleCount variableCount ontology definitions depth =
      Except.ok (FiniteDistinctCardinalityRefutationTree.canonical depth) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp only [WireDistinctCardinalityRefutationTree.canonical,
        WireDistinctCardinalityRefutationTree.decodeAtDepth,
        FiniteDistinctCardinalityRefutationTree.canonical, ih]
      rfl

theorem decodeDistinctStateTreeVector_encode
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (next : Fin width →
      FiniteDistinctEqCertificate nodeCount conceptCount roleCount variableCount)
    (wires : Fin width → WireDistinctCardinalityRefutationTree)
    (trees : Fin width → FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (hontology : ∀ index, (next index).base.base.ontology = ontology)
    (htrees : ∀ index,
      (wires index).decodeAtDepth nodeCount conceptCount roleCount variableCount
        ontology definitions depth = Except.ok (trees index)) :
    (List.ofFn fun index =>
      (WireDistinctEqState.encode (next index), wires index)).mapM
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
      rw [WireDistinctEqState.decode_encode_of_ontology (next 0) ontology
        (hontology 0), htrees 0]
      have htail := ih (fun index => next index.succ)
        (fun index => wires index.succ) (fun index => trees index.succ)
        (fun index => hontology index.succ) (fun index => htrees index.succ)
      rw [htail]
      rfl

theorem decodeDistinctStateTreeRows_encode
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (next : Fin rows → Fin columns →
      FiniteDistinctEqCertificate nodeCount conceptCount roleCount variableCount)
    (wires : Fin rows → Fin columns → WireDistinctCardinalityRefutationTree)
    (trees : Fin rows → Fin columns → FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (hontology : ∀ row column, (next row column).base.base.ontology = ontology)
    (htrees : ∀ row column,
      (wires row column).decodeAtDepth nodeCount conceptCount roleCount variableCount
        ontology definitions depth = Except.ok (trees row column)) :
    (List.ofFn fun row => List.ofFn fun column =>
      (WireDistinctEqState.encode (next row column), wires row column)).mapM
        (fun row => do
          let decodedRow ← row.mapM (fun child => do
            let state ← child.1.decode nodeCount conceptCount roleCount variableCount ontology
            let tree ← child.2.decodeAtDepth nodeCount conceptCount roleCount variableCount
              ontology definitions depth
            return (state, tree))
          decodeExactVector "distinct maximum child row" columns decodedRow) =
      Except.ok (List.ofFn fun row => fun column =>
        (next row column, trees row column)) := by
  induction rows with
  | zero => rfl
  | succ rows ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.mapM_cons]
      rw [decodeDistinctStateTreeVector_encode ontology (next 0) (wires 0) (trees 0)
        definitions (hontology 0) (htrees 0)]
      change (do
        let first ← decodeExactVector "distinct maximum child row" columns
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

/-- Every accepted distinct-cardinality refutation has a bounded wire
representation that decodes to an accepted refutation at the same depth. -/
theorem FiniteDistinctCardinalityRefutationTree.exists_checked_wire
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth) :
    ∀ (certificate : FiniteDistinctEqCertificate
        nodeCount conceptCount roleCount variableCount)
      (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
      (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))),
      certificate.base.base.ontology = ontology →
      tree.check definitions certificate = true →
      ∃ wire : WireDistinctCardinalityRefutationTree,
        ∃ decoded : FiniteDistinctCardinalityRefutationTree
          nodeCount conceptCount roleCount variableCount depth,
        wire.decodeAtDepth nodeCount conceptCount roleCount variableCount
            ontology definitions depth = Except.ok decoded ∧
        decoded.check definitions certificate = true := by
  induction tree with
  | equality eqTree =>
      intro certificate ontology definitions hontology hcheck
      obtain ⟨wire, hwire⟩ := eqTree.exists_wire_of_check certificate.base
        certificate.base.base.ontology rfl hcheck
      refine ⟨.equality wire, .equality eqTree, ?_, hcheck⟩
      simp only [WireDistinctCardinalityRefutationTree.decodeAtDepth]
      rw [← hontology, hwire]
      rfl
  | clash =>
      intro certificate ontology definitions hontology hcheck
      exact ⟨.clash, .clash, rfl, hcheck⟩
  | equalityApart left right =>
      intro certificate ontology definitions hontology hcheck
      exact ⟨.equality_apart left.val right.val, .equalityApart left right,
        by simp only [WireDistinctCardinalityRefutationTree.decodeAtDepth,
          checkedFin_value]; rfl, hcheck⟩
  | delay child ih =>
      intro certificate ontology definitions hontology hcheck
      obtain ⟨wire, decoded, hdecode, hdecoded⟩ :=
        ih certificate ontology definitions hontology hcheck
      exact ⟨.delay wire, .delay decoded,
        by simp only [WireDistinctCardinalityRefutationTree.decodeAtDepth, hdecode]; rfl,
        hdecoded⟩
  | branch clause assignment next children ih =>
      intro certificate ontology definitions hontology hcheck
      simp only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨⟨hvalid, hclause⟩, hbody⟩, hall⟩
      have hnextOntology : ∀ index, (next index).base.base.ontology = ontology := by
        intro index
        have htransition := (hall index).1
        simp only [FiniteDistinctEqCertificate.transitionB, Bool.and_eq_true,
          decide_eq_true_eq] at htransition
        have hbase := certificate.base.transitionB_base (next index).base assignment
          (clause.head.get index) htransition.1
        calc
          (next index).base.base.ontology = certificate.base.base.ontology := by
            have hfields := congrArg FiniteSatCertificate.ontology hbase
            simpa only [FiniteEqCertificate.ontology_assertAtom] using hfields
          _ = ontology := hontology
      have hex := fun index => ih index (next index) ontology definitions
        (hnextOntology index) (hall index).2
      choose wires decoded hdecode hdecoded using hex
      have hlookup : ontology[certificate.base.base.ontology.idxOf clause]? = some clause := by
        rw [← hontology]
        exact List.getElem?_idxOf hclause
      refine ⟨.branch (certificate.base.base.ontology.idxOf clause)
          (encodeAssignment assignment)
          (List.ofFn fun index => (WireDistinctEqState.encode (next index), wires index)),
        .branch clause assignment next decoded, ?_, ?_⟩
      · simp only [WireDistinctCardinalityRefutationTree.decodeAtDepth]
        rw [hlookup, decodeAssignment_encode]
        rw [decodeDistinctStateTreeVector_encode ontology next wires decoded definitions
          hnextOntology hdecode]
        change (do
          let childVector ← decodeExactVector "distinct branch children"
            clause.head.length (encodeExactVector fun index => (next index, decoded index))
          pure (FiniteDistinctCardinalityRefutationTree.branch clause assignment
            (fun index => (childVector index).1)
            (fun index => (childVector index).2))) = _
        rw [decodeExactVector_encode]
        rfl
      · simp only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
          List.all_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨hvalid, hclause⟩, hbody⟩, fun index =>
          ⟨(hall index).1, hdecoded index⟩⟩
  | witness source target role filler child ih =>
      intro certificate ontology definitions hontology hcheck
      simp only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨⟨hvalid, hobligation⟩, hfresh⟩, hchild⟩
      have hnextOntology :
          (certificate.materializeWitness source target role filler).base.base.ontology =
            ontology := by simpa using hontology
      obtain ⟨wire, decoded, hdecode, hdecoded⟩ := ih
        (certificate.materializeWitness source target role filler) ontology definitions
        hnextOntology hchild
      refine ⟨.witness source.val target.val role.val (WireLit.encode filler) wire,
        .witness source target role filler decoded, ?_, ?_⟩
      · simp only [WireDistinctCardinalityRefutationTree.decodeAtDepth,
          checkedFin_value, WireLit.decode_encode, hdecode]
        rfl
      · simpa only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
          decide_eq_true_eq] using ⟨⟨⟨hvalid, hobligation⟩, hfresh⟩, hdecoded⟩
  | minimum definition source targets next child ih =>
      intro certificate ontology definitions hontology hcheck
      simp only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with
        ⟨⟨⟨⟨⟨⟨hvalid, hdefinition⟩, hkind⟩, hmarker⟩, hfresh⟩,
          htransition⟩, hchild⟩
      have hnextOntology : next.base.base.ontology = ontology := by
        have hfields := htransition
        simp only [FiniteDistinctEqCertificate.minimumTransitionB,
          FiniteEqCertificate.minimumTransitionB, Bool.and_eq_true,
          decide_eq_true_eq] at hfields
        exact hfields.1.1.1.1.1.trans hontology
      obtain ⟨wire, decoded, hdecode, hdecoded⟩ :=
        ih next ontology definitions hnextOntology hchild
      have hlookup : definitions[definitions.idxOf definition]? = some definition :=
        List.getElem?_idxOf hdefinition
      refine ⟨.minimum (definitions.idxOf definition) source.val
          (encodeCheckedNodeVector targets) (WireDistinctEqState.encode next) wire,
        .minimum definition source targets next decoded, ?_, ?_⟩
      · simp only [WireDistinctCardinalityRefutationTree.decodeAtDepth, hlookup]
        have hencoded : encodeCheckedNodeVector targets =
            (List.ofFn targets).map Fin.val := by
          simpa [encodeCheckedNodeVector, Function.comp_def] using
            (List.map_ofFn (f := targets) (g := Fin.val)).symm
        rw [hencoded, checkedFin_value_list]
        change (do
          let targetVector ← decodeExactVector "minimum targets" definition.bound
            (encodeExactVector targets)
          let decodedSource ← checkedFin "node" nodeCount source.val
          let decodedNext ← WireDistinctEqState.decode nodeCount conceptCount roleCount
            variableCount ontology (WireDistinctEqState.encode next)
          let decodedChild ← wire.decodeAtDepth nodeCount conceptCount roleCount
            variableCount ontology definitions _
          pure (FiniteDistinctCardinalityRefutationTree.minimum definition decodedSource
            targetVector decodedNext decodedChild)) = _
        rw [decodeExactVector_encode, checkedFin_value,
          WireDistinctEqState.decode_encode_of_ontology next ontology hnextOntology, hdecode]
        rfl
      · simpa only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
          decide_eq_true_eq] using
          ⟨⟨⟨⟨⟨⟨hvalid, hdefinition⟩, hkind⟩, hmarker⟩, hfresh⟩,
            htransition⟩, hdecoded⟩
  | @maximum childDepth definition source witnesses next children ih =>
      intro certificate ontology definitions hontology hcheck
      simp only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with
        ⟨⟨⟨⟨⟨hdefinition, hkind⟩, hmarker⟩, hedges⟩, hlabels⟩, hall⟩
      have hex : ∀ (left right : Fin (definition.bound + 1)),
          ∃ state : FiniteDistinctEqCertificate nodeCount conceptCount roleCount variableCount,
          ∃ wire : WireDistinctCardinalityRefutationTree,
          ∃ decoded : FiniteDistinctCardinalityRefutationTree
              nodeCount conceptCount roleCount variableCount childDepth,
          state.base.base.ontology = ontology ∧
          wire.decodeAtDepth nodeCount conceptCount roleCount variableCount
              ontology definitions childDepth = Except.ok decoded ∧
          (left ≠ right → state = next left right ∧
            decoded.check definitions state = true) := by
        intro left right
        by_cases hne : left ≠ right
        · have hpair := hall left right hne
          have hfields := hpair.1
          simp only [FiniteDistinctEqCertificate.mergeTransitionB,
            FiniteEqCertificate.mergeTransitionB, Bool.and_eq_true,
            decide_eq_true_eq] at hfields
          have hnextOntology : (next left right).base.base.ontology = ontology :=
            hfields.1.1.1.1.1.trans hontology
          obtain ⟨wire, decoded, hdecode, hdecoded⟩ :=
            ih left right (next left right) ontology definitions hnextOntology hpair.2
          exact ⟨next left right, wire, decoded, hnextOntology, hdecode,
            fun _ => ⟨rfl, hdecoded⟩⟩
        · have heq : left = right := Classical.not_not.mp hne
          exact ⟨certificate, WireDistinctCardinalityRefutationTree.canonical _,
            FiniteDistinctCardinalityRefutationTree.canonical _, hontology,
            WireDistinctCardinalityRefutationTree.decodeAtDepth_canonical _ ontology definitions,
            fun h => (h heq).elim⟩
      choose states wires decoded hstates hdecode hrelevant using hex
      have hlookup : definitions[definitions.idxOf definition]? = some definition :=
        List.getElem?_idxOf hdefinition
      refine ⟨.maximum (definitions.idxOf definition) source.val
          (encodeCheckedNodeVector witnesses)
          (List.ofFn fun left => List.ofFn fun right =>
            (WireDistinctEqState.encode (states left right), wires left right)),
        .maximum definition source witnesses states decoded, ?_, ?_⟩
      · simp only [WireDistinctCardinalityRefutationTree.decodeAtDepth, hlookup]
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
              (FiniteDistinctEqCertificate nodeCount conceptCount roleCount variableCount ×
                FiniteDistinctCardinalityRefutationTree nodeCount conceptCount roleCount
                  variableCount childDepth) ←
            decodeExactVector "distinct maximum child rows"
              (definition.bound + 1) decodedRows
          let decodedSource ← checkedFin "node" nodeCount source.val
          pure (FiniteDistinctCardinalityRefutationTree.maximum definition decodedSource
            witnessVector (fun left right => (childMatrix left right).1)
            (fun left right => (childMatrix left right).2))) = _
        rw [decodeExactVector_encode, checkedFin_value]
        rw [decodeDistinctStateTreeRows_encode ontology states wires decoded definitions
          hstates hdecode]
        change (do
          let childMatrix : Fin (definition.bound + 1) → Fin (definition.bound + 1) →
              (FiniteDistinctEqCertificate nodeCount conceptCount roleCount variableCount ×
                FiniteDistinctCardinalityRefutationTree nodeCount conceptCount roleCount
                  variableCount childDepth) ←
            decodeExactVector "distinct maximum child rows" (definition.bound + 1)
              (encodeExactVector fun left right => (states left right, decoded left right))
          pure (FiniteDistinctCardinalityRefutationTree.maximum definition source witnesses
            (fun left right => (childMatrix left right).1)
            (fun left right => (childMatrix left right).2))) = _
        rw [decodeExactVector_encode]
        rfl
      · simp only [FiniteDistinctCardinalityRefutationTree.check, Bool.and_eq_true,
          decide_eq_true_eq]
        refine ⟨⟨⟨⟨⟨hdefinition, hkind⟩, hmarker⟩, hedges⟩, hlabels⟩, ?_⟩
        intro left right hne
        rcases hrelevant left right hne with ⟨hstate, hchecked⟩
        exact ⟨by rw [hstate]; exact (hall left right hne).1, hchecked⟩

#print axioms WireDistinctEqState.decode_encode
#print axioms WireDistinctCardinalityRefutationTree.decodeAtDepth_canonical
#print axioms decodeDistinctStateTreeRows_encode
#print axioms FiniteDistinctCardinalityRefutationTree.exists_checked_wire

end ContextCalculus.Hypertableau
