import ContextCalculus.HypertableauCertificate
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

/-!
# Checked finite-model folding for blocked hypertableau branches

A tableau blocker is a search device, not a trusted semantic premise.  This
module treats a finite fold plan as untrusted data, materializes the blocker's
outgoing edges at the blocked node, and then runs the existing exhaustive SAT
checker on the resulting ordinary finite graph.  Consequently, an incorrect
blocker choice can only make the checker reject; it cannot justify a verdict.
-/

namespace ContextCalculus.Hypertableau

/-! ## Finite blocking signatures -/

/-- Signed HT literals are equivalent to a concept paired with its polarity. -/
def litEquiv (Concept : Type*) : Lit Concept ≃ Concept × Bool where
  toFun lit := (lit.concept, lit.neg)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv lit := by cases lit; rfl
  right_inv pair := by cases pair; rfl

noncomputable instance [Fintype Concept] : Fintype (Lit Concept) :=
  Fintype.ofEquiv (Concept × Bool) (litEquiv Concept).symm

/-- The complete signed concept label used by equality and subset blocking. -/
noncomputable def State.labelSet [Fintype Concept]
    (state : State Node Concept Role) (node : Node) : Finset (Lit Concept) :=
  by classical exact Finset.univ.filter fun lit => state.label node lit

@[simp] theorem State.mem_labelSet [Fintype Concept] [DecidableEq Concept]
    (state : State Node Concept Role) (node : Node) (lit : Lit Concept) :
    lit ∈ state.labelSet node ↔ state.label node lit := by
  classical
  simp [State.labelSet]

theorem State.labelSet_subset [Fintype Concept] [DecidableEq Concept]
    (state : State Node Concept Role) (node : Node) :
    state.labelSet node ⊆ Finset.univ := by
  intro lit _
  simp

/-- `blocker` carries every signed label of `blocked`, the semantic condition
checked by KM's default anywhere-subset blocking mode. -/
def State.Blocks (state : State Node Concept Role) (blocker blocked : Node) : Prop :=
  ∀ lit, state.label blocked lit → state.label blocker lit

theorem State.blocks_of_labelSet_eq
    [Fintype Concept] [DecidableEq Concept]
    (state : State Node Concept Role) {blocker blocked : Node}
    (hequal : state.labelSet blocker = state.labelSet blocked) :
    state.Blocks blocker blocked := by
  intro lit hlabel
  rw [← state.mem_labelSet] at hlabel
  rw [← hequal] at hlabel
  exact (state.mem_labelSet blocker lit).mp hlabel

/-- Folding a labelled node onto a blocker preserves every signed concept fact
in the canonical interpretation. Role and witness obligations are validated
separately by `FiniteFoldCertificate.check`. -/
theorem State.blocks_preserve_canonical_label
    (state : State Node Concept Role) (hclash : state.ClashFree)
    {blocker blocked : Node} (hblocks : state.Blocks blocker blocked)
    {lit : Lit Concept} (hlabel : state.label blocked lit) :
    state.canonical.satLit lit blocker :=
  state.canonical_satLit hclash blocker lit (hblocks lit hlabel)

/-- A path with one more node than there are possible signed labels contains an
earlier exact-label blocker. This is the finite pigeonhole bound underlying
termination of equality/subset blocking on the certified finite signature. -/
theorem State.exists_blocker_on_long_path
    [Fintype Concept] [DecidableEq Concept]
    (state : State Node Concept Role)
    (path : Fin (2 ^ Fintype.card (Lit Concept) + 1) → Node) :
    ∃ earlier later,
      earlier < later ∧ state.Blocks (path earlier) (path later) := by
  classical
  let positions : Finset (Fin (2 ^ Fintype.card (Lit Concept) + 1)) := Finset.univ
  let signatures : Finset (Finset (Lit Concept)) := Finset.univ.powerset
  have hcard : signatures.card < positions.card := by
    simp [positions, signatures, Finset.card_powerset]
  obtain ⟨left, _, right, _, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun position => state.labelSet (path position)) (fun position _ => by
        exact Finset.mem_powerset.mpr (state.labelSet_subset (path position)))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨left, right, hlt, state.blocks_of_labelSet_eq heq⟩
  · exact ⟨right, left, hgt, state.blocks_of_labelSet_eq heq.symm⟩

/-- `(blocked, blocker)` pairs supplied by an untrusted finite-model producer. -/
structure FiniteFoldCertificate
    (nodeCount conceptCount roleCount variableCount : Nat) where
  base : FiniteSatCertificate nodeCount conceptCount roleCount variableCount
  folds : List (Fin nodeCount × Fin nodeCount)

/-- Copy every outgoing blocker edge to its blocked unfolding position. -/
def FiniteFoldCertificate.foldedEdges
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount) :
    List (Fin roleCount × Fin nodeCount × Fin nodeCount) :=
  certificate.base.edges ++ certificate.folds.flatMap fun fold =>
    certificate.base.edges.filterMap fun edge =>
      if edge.2.1 = fold.2 then some (edge.1, fold.1, edge.2.2) else none

/-- The ordinary finite SAT certificate obtained after materializing a fold. -/
def FiniteFoldCertificate.materialize
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount) :
    FiniteSatCertificate nodeCount conceptCount roleCount variableCount := {
  certificate.base with edges := certificate.foldedEdges
}

@[simp] theorem FiniteFoldCertificate.materialize_ontology
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.ontology = certificate.base.ontology := rfl

@[simp] theorem FiniteFoldCertificate.materialize_labels
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.labels = certificate.base.labels := rfl

@[simp] theorem FiniteFoldCertificate.materialize_obligations
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.obligations = certificate.base.obligations := rfl

theorem FiniteFoldCertificate.base_edge_mem_foldedEdges
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount)
    (edge : Fin roleCount × Fin nodeCount × Fin nodeCount)
    (hedge : edge ∈ certificate.base.edges) :
    edge ∈ certificate.foldedEdges := by
  exact List.mem_append_left _ hedge

/-- Executable acceptance condition for an untrusted finite fold. -/
def FiniteFoldCertificate.check
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount) : Bool :=
  certificate.materialize.checkSat

/-- Fold checking is exact for the materialized finite endpoint invariant. In
particular, proving a runtime fold guarded, clash-free, witness-complete, and
saturated is sufficient to prove executable acceptance rather than merely
semantic model existence. -/
theorem FiniteFoldCertificate.check_eq_true_iff_materialize_valid
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount) :
    certificate.check = true ↔ certificate.materialize.Valid := by
  exact certificate.materialize.checkSat_eq_true_iff_valid

theorem FiniteFoldCertificate.check_complete
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.materialize.Valid) :
    certificate.check = true :=
  certificate.materialize.checkSat_complete hvalid

/-- Concrete acceptance contract for a blocked terminal. These are exactly the
four properties the Rust terminal enumerator must establish; there is no
additional hidden checker premise. -/
theorem FiniteFoldCertificate.check_complete_of
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount)
    (hguarded : ∀ clause ∈ certificate.base.ontology, clause.GuardedBody)
    (hclash : certificate.materialize.state.ClashFree)
    (hwitness : ∀ obligation ∈ certificate.base.obligations,
      ∃ witness,
        (obligation.1, obligation.2.2, witness) ∈ certificate.foldedEdges ∧
        (witness, obligation.2.1) ∈ certificate.base.labels)
    (hsaturated : certificate.materialize.state.SaturatedFor
      certificate.base.ontology) :
    certificate.check = true := by
  apply certificate.check_complete
  exact ⟨hguarded, hclash, hwitness, hsaturated⟩

/-- A checked fold constructs a model of the exact, unchanged ontology.  No
property of `folds` occurs among the assumptions. -/
theorem FiniteFoldCertificate.check_satisfiable
    (certificate : FiniteFoldCertificate nodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.check = true) :
    ∃ I : Interp (Fin nodeCount) (Fin conceptCount) (Fin roleCount),
      I.models certificate.base.ontology := by
  simpa [FiniteFoldCertificate.check] using
    certificate.materialize.checkSat_satisfiable hcheck

namespace FoldTests

private def cyclicBase : FiniteSatCertificate 3 2 1 1 where
  ontology := [
    { body := [], head := [.concept (.pos 0) 0] },
    { body := [.concept (.pos 0) 0], head := [.exists_ 0 (.pos 1) 0] }
  ]
  labels := [
    (0, .pos 0),
    (1, .pos 0), (1, .pos 1),
    (2, .pos 0), (2, .pos 1)
  ]
  edges := [(0, 0, 1), (0, 1, 2)]
  obligations := [(0, .pos 1, 0), (0, .pos 1, 1), (0, .pos 1, 2)]

example : cyclicBase.checkSat = false := by native_decide

private def cyclicFold : FiniteFoldCertificate 3 2 1 1 where
  base := cyclicBase
  folds := [(2, 1)]

example : cyclicFold.materialize.edges =
    [(0, 0, 1), (0, 1, 2), (0, 2, 2)] := by native_decide

example : cyclicFold.check = true := by native_decide

end FoldTests

#print axioms FiniteFoldCertificate.check_satisfiable
#print axioms FiniteFoldCertificate.check_eq_true_iff_materialize_valid
#print axioms FiniteFoldCertificate.check_complete
#print axioms FiniteFoldCertificate.check_complete_of
#print axioms State.blocks_preserve_canonical_label
#print axioms State.exists_blocker_on_long_path

end ContextCalculus.Hypertableau
