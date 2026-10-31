import ContextCalculus.HypertableauWire

/-!
# Checked subset-blocking unravellings of production hypertableau runs

The native hypertableau worker (`engine/src/hypertableau.rs`) blocks a node
`w` by an earlier node `w'` with `L(w) ⊆ L(w')` in its production blocking
modes 1 and 5, admitting the pair only when no gained literal is relevant
(`SubsetGain`, docs/HYBRID-CB-HT.md section 9). Since v1.5.5 it computes that
relation incrementally (`checked_subset_incremental`). The certified runs use
a different blocking (mode 6), so no earlier certificate covers a subset-blocked
answer.

This module checks such an answer from the production terminal itself. The
certificate carries the terminal completion graph (descendants of blocked
nodes removed), the predecessor relation, the blocking pairs the engine used,
and the query seed at the root. Lean builds the unravelled model of section 9:
the position of a blocked node `w` takes the label and the obligations of its
blocker `w'`, keeps its own incoming edges and its edges to other kept nodes,
and receives copies of the edges between `w'` and the successors of `w'`. The
checker then verifies

* every pair is a subset pair (`L(w) ⊆ L(w')`, with `w'` itself unblocked);
* the root carries every seed literal in the unravelled model;
* the unravelled model satisfies every clause of the certificate's ontology
  under every assignment, has a witness for every existential obligation, and
  has no complementary labels (`FiniteSatCertificate.checkSat`).

For every blocked node listed in `predecessorFolds` (wire field
`predecessor`, since 2026-10-31) the blocked position also receives copies of
the edges between `w'` and its own predecessor `p'` (the classical
unravelling, one level further up; the predecessor fold): a blocker
that witnesses an existential through the inverse edge to `p'` passes that
witness on to `w`'s position. The copied edges make the blocked position a
second neighbour of `p'` with the label of `w'`, so a clause that counts
neighbours of `p'` (two neighbour variables and an equality head, for example
a functional role) can fail at `p'`; `checkSat` evaluates every clause under
every assignment, so such a fold is rejected, never accepted. The old folds
(an empty `predecessorFolds`, with or without relabelling) stay available,
and the engine selects the predecessor fold per pair.

The blocking pairs and the predecessor relation are untrusted: they only
decide which graph is materialized, and `check_sound` has no premise about
them. In particular the relevance condition on gained literals (`SubsetGain`)
is not part of the trusted base; what it is meant to guarantee, that the
unravelling is a model, is checked directly.
-/

namespace ContextCalculus.Hypertableau

open Lean

/-- A production terminal, its predecessor relation and its subset-blocking
pairs. -/
structure SubsetUnravelling (nodeCount conceptCount roleCount variableCount : Nat) where
  base : FiniteSatCertificate nodeCount conceptCount roleCount variableCount
  /-- `(child, parent)` for every successor created by an existential. -/
  parents : List (Fin nodeCount × Fin nodeCount)
  /-- `(blocked, blocker)`. -/
  folds : List (Fin nodeCount × Fin nodeCount)
  root : Fin nodeCount
  seed : List (Lit (Fin conceptCount))
  /-- `true`: a blocked position takes its blocker's label and obligations
  (the construction of docs/HYBRID-CB-HT.md section 9); `false`: it keeps its
  own label and obligations and only receives the blocker's successor edges
  (the fold of `HypertableauBlockingCertificate`). -/
  relabel : Bool
  /-- Blocked nodes whose position also receives copies of the edges
  between their blocker and the blocker's own predecessor (the predecessor
  fold); the others receive only the blocker's successor edges. -/
  predecessorFolds : List (Fin nodeCount) := []

namespace SubsetUnravelling

variable (u : SubsetUnravelling nodeCount conceptCount roleCount variableCount)

def isBlocked (node : Fin nodeCount) : Bool :=
  u.folds.any fun fold => decide (fold.1 = node)

/-- Is `other` a neighbour of the blocker `fold.2` whose edges the blocked
position `fold.1` copies: a successor of the blocker, and for a predecessor
fold also a predecessor of the blocker? -/
def copiedNeighbour (fold : Fin nodeCount × Fin nodeCount) (other : Fin nodeCount) : Prop :=
  (other, fold.2) ∈ u.parents ∨ (fold.1 ∈ u.predecessorFolds ∧ (fold.2, other) ∈ u.parents)

instance (fold : Fin nodeCount × Fin nodeCount) (other : Fin nodeCount) :
    Decidable (u.copiedNeighbour fold other) := by
  unfold copiedNeighbour; infer_instance

/-- Without predecessor folds the copied neighbours are exactly the
blocker's successors: the successor fold of the earlier wire is unchanged. -/
theorem copiedNeighbour_of_predecessorFolds_nil (hnil : u.predecessorFolds = [])
    (fold : Fin nodeCount × Fin nodeCount) (other : Fin nodeCount) :
    u.copiedNeighbour fold other ↔ (other, fold.2) ∈ u.parents := by
  simp [copiedNeighbour, hnil]

/-- A predecessor fold copies the edges to the blocker's predecessor. -/
theorem copiedNeighbour_predecessor {fold : Fin nodeCount × Fin nodeCount} {other : Fin nodeCount}
    (hfold : fold.1 ∈ u.predecessorFolds) (hparent : (fold.2, other) ∈ u.parents) :
    u.copiedNeighbour fold other :=
  Or.inr ⟨hfold, hparent⟩

/-- The edges between a blocker and its own successors (and, for a
predecessor fold, its own predecessor), redirected to the blocked
position. -/
def copiedEdges (fold : Fin nodeCount × Fin nodeCount) :
    List (Fin roleCount × Fin nodeCount × Fin nodeCount) :=
  u.base.edges.flatMap fun edge =>
    (if edge.2.1 = fold.2 ∧ u.copiedNeighbour fold edge.2.2 then [(edge.1, fold.1, edge.2.2)] else []) ++
    (if edge.2.2 = fold.2 ∧ u.copiedNeighbour fold edge.2.1 then [(edge.1, edge.2.1, fold.1)] else [])

/-- The unravelled finite model. -/
def materialize : FiniteSatCertificate nodeCount conceptCount roleCount variableCount where
  ontology := u.base.ontology
  labels :=
    if u.relabel then
      (u.base.labels.filter fun label => !u.isBlocked label.1) ++
        u.folds.flatMap fun fold =>
          (u.base.labels.filter fun label => decide (label.1 = fold.2)).map
            fun label => (fold.1, label.2)
    else u.base.labels
  edges := u.base.edges ++ u.folds.flatMap u.copiedEdges
  obligations :=
    if u.relabel then
      u.base.obligations ++
        u.folds.flatMap fun fold =>
          (u.base.obligations.filter fun obligation => decide (obligation.2.2 = fold.2)).map
            fun obligation => (obligation.1, obligation.2.1, fold.1)
    else u.base.obligations

/-- Every pair is a subset pair whose blocker is not blocked. -/
def checkFolds : Bool :=
  u.folds.all fun fold =>
    decide (fold.1 ≠ fold.2) && !u.isBlocked fold.2 &&
      u.base.labels.all fun label =>
        !decide (label.1 = fold.1) || decide ((fold.2, label.2) ∈ u.base.labels)

def check : Bool :=
  u.checkFolds &&
    u.seed.all (fun literal => decide ((u.root, literal) ∈ u.materialize.labels)) &&
    u.materialize.checkSat

@[simp] theorem materialize_ontology : u.materialize.ontology = u.base.ontology := rfl

/-- **Soundness.** An accepted unravelling is a finite model of the exact
ontology of the certificate in which the root satisfies every seed literal. No
property of `folds`, `parents` or `predecessorFolds` is assumed, so the
statement covers the successor fold, the predecessor fold and the own-label
fold alike. -/
theorem check_sound (hcheck : u.check = true) :
    ∃ I : Interp (Fin nodeCount) (Fin conceptCount) (Fin roleCount),
      I.models u.base.ontology ∧ ∀ literal ∈ u.seed, I.satLit literal u.root := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨_, hseed⟩, hsat⟩
  have hvalid := u.materialize.checkSat_sound hsat
  refine ⟨u.materialize.state.canonical, ?_, ?_⟩
  · simpa using u.materialize.checkSat_models hsat
  · intro literal hliteral
    exact u.materialize.state.canonical_satLit hvalid.2.1 u.root literal (hseed literal hliteral)

/-- The seed conjunction is satisfiable together with the ontology. -/
theorem check_seed_satisfiable (hcheck : u.check = true) :
    ∃ (Domain : Type) (I : Interp Domain (Fin conceptCount) (Fin roleCount)) (value : Domain),
      I.models u.base.ontology ∧ ∀ literal ∈ u.seed, I.satLit literal value := by
  rcases u.check_sound hcheck with ⟨I, hmodels, hseed⟩
  exact ⟨Fin nodeCount, I, u.root, hmodels, hseed⟩

/-- With seed `[A]`, `A` is satisfiable. -/
theorem check_not_unsatisfiable (hcheck : u.check = true) {concept : Fin conceptCount}
    (hseed : Lit.pos concept ∈ u.seed) :
    ¬UnsatisfiableConcept u.base.ontology concept := by
  intro hunsat
  rcases u.check_sound hcheck with ⟨I, hmodels, hseedHolds⟩
  exact hunsat _ I hmodels u.root (hseedHolds _ hseed)

/-- With seed `[A, ¬B]`, `A ⊑ B` is not entailed. -/
theorem check_not_entailsSub (hcheck : u.check = true) {sub sup : Fin conceptCount}
    (hsub : Lit.pos sub ∈ u.seed) (hsup : Lit.negated sup ∈ u.seed) :
    ¬EntailsSub u.base.ontology sub sup := by
  intro hentails
  rcases u.check_sound hcheck with ⟨I, hmodels, hseedHolds⟩
  have hA := hseedHolds _ hsub
  have hB := hseedHolds _ hsup
  simp only [Interp.satLit, Lit.pos, Lit.negated, Bool.false_eq_true, if_false, if_true] at hA hB
  exact hB (hentails _ I hmodels u.root hA)

end SubsetUnravelling

/-! ## Wire format -/

structure WireSubsetPair where
  source : Nat
  target : Nat
deriving FromJson, ToJson, Repr

/-- `base` is a version-1 SAT certificate of the terminal graph (its
`evidence` field is ignored), `parents` holds `(child, parent)` pairs and
`folds` `(blocked, blocker)` pairs. -/
structure WireSubsetUnravelling where
  version : Nat
  base : WireCertificate
  parents : List WireSubsetPair
  folds : List WireSubsetPair
  root : Nat
  seed : List WireLit
  /-- Absent means `true`. -/
  relabel : Option Bool := none
  /-- `predecessorFolds` (blocked nodes); absent means none (the fold
  before 2026-10-31). -/
  predecessor : Option (List Nat) := none
deriving FromJson, ToJson, Repr

structure DecodedSubsetUnravelling where
  nodeCount : Nat
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  unravelling : SubsetUnravelling nodeCount conceptCount roleCount variableCount

def WireSubsetPair.decode (nodeCount : Nat) (pair : WireSubsetPair) :
    Except String (Fin nodeCount × Fin nodeCount) := do
  return (← checkedFin "node" nodeCount pair.source, ← checkedFin "node" nodeCount pair.target)

def WireSubsetUnravelling.decode (wire : WireSubsetUnravelling) :
    Except String DecodedSubsetUnravelling := do
  if wire.version != 1 then
    throw s!"unsupported subset-unravelling version {wire.version}"
  let decoded ← wire.base.decodeBase
  let parents ← wire.parents.mapM (WireSubsetPair.decode decoded.nodeCount)
  let folds ← wire.folds.mapM (WireSubsetPair.decode decoded.nodeCount)
  let root ← checkedFin "node" decoded.nodeCount wire.root
  let seed ← wire.seed.mapM (WireLit.decode decoded.conceptCount)
  let predecessorFolds ← (wire.predecessor.getD []).mapM (checkedFin "node" decoded.nodeCount)
  return {
    nodeCount := decoded.nodeCount
    conceptCount := decoded.conceptCount
    roleCount := decoded.roleCount
    variableCount := decoded.variableCount
    unravelling := {
      base := decoded.certificate, parents, folds, root, seed
      relabel := wire.relabel.getD true
      predecessorFolds }
  }

def WireSubsetUnravelling.check (wire : WireSubsetUnravelling) : Except String Bool := do
  return (← wire.decode).unravelling.check

/-- **Wire soundness.** An accepted document decodes to a terminal whose
unravelling is a finite model of the decoded ontology with the seed at the
root. -/
theorem WireSubsetUnravelling.check_sound (wire : WireSubsetUnravelling)
    (hcheck : wire.check = .ok true) :
    ∃ decoded, wire.decode = .ok decoded ∧
      ∃ I : Interp (Fin decoded.nodeCount) (Fin decoded.conceptCount) (Fin decoded.roleCount),
        I.models decoded.unravelling.base.ontology ∧
          ∀ literal ∈ decoded.unravelling.seed, I.satLit literal decoded.unravelling.root := by
  unfold WireSubsetUnravelling.check at hcheck
  generalize hdecode : wire.decode = result at hcheck
  cases result with
  | error message => simp at hcheck
  | ok decoded =>
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hcheck
      exact ⟨decoded, rfl, decoded.unravelling.check_sound hcheck⟩

namespace SubsetUnravellingTests

/-- `A ⊑ ∃r.A` over the path `0 → 2 → 1`. Node 1 (label `A`) is
subset-blocked by its predecessor 2 (label `A`, `B`); the unravelled position
of 1 takes `{A, B}` and a copy of the edge `2 → 1`, a loop at 1. -/
private def base : FiniteSatCertificate 3 2 1 2 where
  ontology := [
    { body := [.concept (.pos 0) 0], head := [.exists_ 0 (.pos 0) 0] }
  ]
  labels := [(0, .pos 0), (0, .pos 1), (1, .pos 0), (2, .pos 0), (2, .pos 1)]
  edges := [(0, 0, 1), (0, 1, 2)]
  obligations := [(0, .pos 0, 0), (0, .pos 0, 1), (0, .pos 0, 2)]

private def folded : SubsetUnravelling 3 2 1 2 where
  base := {
    base with
    labels := [(0, .pos 0), (0, .pos 1), (1, .pos 0), (2, .pos 0), (2, .pos 1)]
    edges := [(0, 0, 2), (0, 2, 1)]
    obligations := [(0, .pos 0, 0), (0, .pos 0, 2)]
  }
  parents := [(2, 0), (1, 2)]
  folds := [(1, 2)]
  root := 0
  seed := [.pos 0]
  relabel := true

example : folded.check = true := by native_decide

/-- Without relabelling, node 1 keeps its own obligations, and this terminal
lists none for it although `A ⊑ ∃r.A` fires there: rejected. -/
example : ({ folded with relabel := false } : SubsetUnravelling 3 2 1 2).check = false := by
  native_decide

/-- A pair that is not a subset pair is rejected. -/
example : ({ folded with folds := [(2, 1)] } : SubsetUnravelling 3 2 1 2).check = false := by
  native_decide

/-- A clause the unravelling violates is rejected whatever the folds say. -/
example : ({ folded with
    base := { folded.base with
      ontology := folded.base.ontology ++ [{ body := [.concept (.pos 0) 0], head := [.concept (.negated 1) 0] }] } } :
    SubsetUnravelling 3 2 1 2).check = false := by
  native_decide

/-- The inverse-witness shape of docs/HYBRID-CB-HT.md section 9. Concepts
`A = 0`, `B = 1`, `C = 2`; roles `s = 0` and its inverse `r = 1`. Node 0
(`B`, `C`) has the `s`-successor 1 (`A`), which has the `s`-successor 2
(`A`); node 2 is blocked by 1. Node 1 witnesses `A ⊑ ∃r.C` through the
inverse edge to its predecessor 0. The successor fold gives node 2's
position that obligation without a witness (node 1 lacks `C`); the
predecessor fold also copies `r(1, 0)` and `s(0, 1)` to node 2. -/
private def inverseOntology : List (Clause (Fin 3) (Fin 3) (Fin 2)) := [
  { body := [.concept (.pos 1) 0], head := [.exists_ 0 (.pos 0) 0] },
  { body := [.concept (.pos 0) 0], head := [.exists_ 0 (.pos 0) 0] },
  { body := [.concept (.pos 0) 0], head := [.exists_ 1 (.pos 2) 0] },
  { body := [.role 0 0 1], head := [.role 1 1 0] },
  { body := [.role 1 0 1], head := [.role 0 1 0] }
]

private def inverseWitness : SubsetUnravelling 3 3 2 3 where
  base := {
    ontology := inverseOntology
    labels := [(0, .pos 1), (0, .pos 2), (1, .pos 0), (2, .pos 0)]
    edges := [(0, 0, 1), (1, 1, 0), (0, 1, 2), (1, 2, 1)]
    obligations := [(0, .pos 0, 0), (0, .pos 0, 1), (1, .pos 2, 1)]
  }
  parents := [(1, 0), (2, 1)]
  folds := [(2, 1)]
  root := 0
  seed := [.pos 1]
  relabel := true

/-- The successor fold is not a model here. -/
example : inverseWitness.check = false := by native_decide

/-- The predecessor fold is. -/
example : ({ inverseWitness with predecessorFolds := [2] } : SubsetUnravelling 3 3 2 3).check = true := by
  native_decide

/-- A functional `s` (`s(x, y) ∧ s(x, z) → y = z`) is satisfied by the
terminal, but the predecessor fold gives node 0 the two `s`-successors 1 and
2: the counting clause fails at the copied predecessor and the fold is
rejected. -/
example : ({ inverseWitness with
    predecessorFolds := [2]
    base := { inverseWitness.base with
      ontology := inverseOntology ++ [{ body := [.role 0 0 1, .role 0 0 2], head := [.eq 1 2] }] } } :
    SubsetUnravelling 3 3 2 3).check = false := by
  native_decide

end SubsetUnravellingTests

#print axioms SubsetUnravelling.check_sound
#print axioms SubsetUnravelling.copiedNeighbour_of_predecessorFolds_nil
#print axioms SubsetUnravelling.check_not_unsatisfiable
#print axioms SubsetUnravelling.check_not_entailsSub
#print axioms WireSubsetUnravelling.check_sound

end ContextCalculus.Hypertableau
