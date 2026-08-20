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

#print axioms decodeExactVector_encode
#print axioms decodeExactVector_encode_list
#print axioms decodeCheckedNodeVector_encode
#print axioms decodeExactMatrix_encode
#print axioms WireCardinalityEqRefutationTree.decodeAtDepth_canonical

end ContextCalculus.Hypertableau
