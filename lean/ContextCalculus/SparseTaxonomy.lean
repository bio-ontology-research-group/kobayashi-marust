import ContextCalculus.KMConcreteWorkerAdapters
import Std.Data.TreeMap
import Std.Data.TreeMap.Lemmas
import Std.Data.TreeSet
import Std.Data.TreeSet.Lemmas

/-!
# Sparse taxonomy publication for the reference stage (v1.6.1)

The v1.6.0 reference stage publishes the dense `TaxonomyAnswer`: one cell per
(sub, sup) pair of requested names.  That list is quadratic in the number of
requested names, while the answer itself is sparse: a satisfiable class has
few named subsumers and an unsatisfiable class has all of them.

This module defines a sparse publication (`SparseTaxonomy`: one row per
requested name, with an unsatisfiability flag and the list of requested
superclasses) together with its dense expansion `SparseTaxonomy.dense`, and
proves that the sparse EL and ALC reference answers expand to exactly the
v1.6.0 reference answers (`sparseReferenceAnswer_dense`, `ofMatrix_dense`).
The executable `sparseElReference` and `sparseAlcReference` therefore
publish, through `dense`, the very publication of `elReferenceExecution` and
`alcReferenceExecution` (`sparseElReference_agrees`,
`sparseAlcReference_agrees`), and every v1.6.0 theorem about those
executions covers the sparse output.

The EL readout computes the reference closure once and reads every row from
the closure's fact list through one index from subject to requested
superclasses (`superIndex`), so it never builds a named x named list.
-/

/- The release fixes both the namespace `ContextCalculus.SparseTaxonomy` and the
structure name `SparseTaxonomy`, so the duplicated-namespace linter is off. -/
set_option linter.dupNamespace false

namespace ContextCalculus.SparseTaxonomy

open ContextCalculus
open ContextCalculus.KMConcreteWorkerAdapters
open Std

structure SparseRow where
  sub : Nat
  unsat : Bool
  sups : List Nat
deriving DecidableEq, Repr

structure SparseTaxonomy where
  named : List Nat
  rows : List SparseRow
deriving DecidableEq, Repr

def SparseRow.bit (row : SparseRow) (sup : Nat) : Bool :=
  row.unsat || row.sups.contains sup

/-- The dense answer a sparse publication denotes. -/
def SparseTaxonomy.dense (t : SparseTaxonomy) : TaxonomyAnswer :=
  { named := t.named
    cells := t.rows.flatMap fun row =>
      t.named.map fun sup => { sub := row.sub, sup, answer := row.bit sup } }

/-- Sparse readout of a dense bit function (used for ALC, which is small).
Rows never set `unsat`: the bit function already holds every superclass of an
unsatisfiable class, and the Rust caller derives unsatisfiability from the bit
of its bottom probe. -/
def ofMatrix (named : List Nat) (f : Nat → Nat → Bool) : SparseTaxonomy :=
  { named
    rows := named.map fun sub =>
      { sub, unsat := false, sups := named.filter (f sub) } }

/-! ### Dense expansion of a matrix readout -/

private theorem contains_filter_of_mem {named : List Nat} {p : Nat → Bool}
    {sup : Nat} (hsup : sup ∈ named) :
    (named.filter p).contains sup = p sup := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hsup, h⟩⟩

theorem ofMatrix_dense (named : List Nat) (f : Nat → Nat → Bool) :
    (ofMatrix named f).dense = matrixAnswer named f := by
  simp only [ofMatrix, SparseTaxonomy.dense, matrixAnswer, matrixCells,
    List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro sub _hsub
  apply List.map_congr_left
  intro sup hsup
  simp only [SparseRow.bit, Bool.false_or, contains_filter_of_mem hsup]

/-! ### The EL readout: one closure, one pass over its fact list -/

/-- The index step: record `p.2` as a superclass of `p.1` when it is requested. -/
def superIndexStep (requested : TreeSet Nat) (table : TreeMap Nat (List Nat))
    (p : Nat × Nat) : TreeMap Nat (List Nat) :=
  if requested.contains p.2 then
    table.alter p.1 fun old => some (p.2 :: old.getD [])
  else table

/-- Requested superclasses of every subject, read in one pass over the
closure's fact list (`O(|facts| log |facts|)`). -/
def superIndex (requested : TreeSet Nat) (facts : List (Nat × Nat)) :
    TreeMap Nat (List Nat) :=
  facts.foldl (superIndexStep requested) ∅

private theorem mem_superIndexStep (requested : TreeSet Nat)
    (table : TreeMap Nat (List Nat)) (p : Nat × Nat) (k y : Nat) :
    y ∈ (superIndexStep requested table p).getD k [] ↔
      y ∈ table.getD k [] ∨ (p = (k, y) ∧ requested.contains y = true) := by
  unfold superIndexStep
  split
  · next hreq =>
      rw [TreeMap.getD_alter]
      split
      · next hcmp =>
          have hk : p.1 = k := LawfulEqCmp.compare_eq_iff_eq.mp hcmp
          rcases p with ⟨a, b⟩
          simp only at hk hreq ⊢
          subst hk
          simp only [TreeMap.getD_eq_getD_getElem?, Option.getD_some,
            List.mem_cons, Prod.mk.injEq, true_and]
          constructor
          · rintro (rfl | h)
            · exact Or.inr ⟨rfl, hreq⟩
            · exact Or.inl h
          · rintro (h | ⟨rfl, _⟩)
            · exact Or.inr h
            · exact Or.inl rfl
      · next hcmp =>
          constructor
          · exact Or.inl
          · rintro (h | ⟨rfl, _⟩)
            · exact h
            · exact absurd (Std.ReflCmp.compare_self) hcmp
  · next hreq =>
      constructor
      · exact Or.inl
      · rintro (h | ⟨rfl, hy⟩)
        · exact h
        · exact absurd hy hreq

private theorem mem_foldl_superIndexStep (requested : TreeSet Nat) (k y : Nat) :
    ∀ (facts : List (Nat × Nat)) (table : TreeMap Nat (List Nat)),
      y ∈ (facts.foldl (superIndexStep requested) table).getD k [] ↔
        y ∈ table.getD k [] ∨ ((k, y) ∈ facts ∧ requested.contains y = true)
  | [], table => by simp
  | p :: facts, table => by
      rw [List.foldl_cons, mem_foldl_superIndexStep requested k y facts,
        mem_superIndexStep]
      constructor
      · rintro ((h | ⟨rfl, hy⟩) | ⟨hmem, hy⟩)
        · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_self, hy⟩
        · exact Or.inr ⟨List.mem_cons_of_mem _ hmem, hy⟩
      · rintro (h | ⟨hmem, hy⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hmem with h | h
          · exact Or.inl (Or.inr ⟨h.symm, hy⟩)
          · exact Or.inr ⟨h, hy⟩

theorem mem_superIndex (requested : TreeSet Nat) (facts : List (Nat × Nat))
    (k y : Nat) :
    y ∈ (superIndex requested facts).getD k [] ↔
      (k, y) ∈ facts ∧ requested.contains y = true := by
  rw [superIndex, mem_foldl_superIndexStep]
  simp

/-- One sparse row of the EL reference answer. -/
def sparseRowOf (c : ELReference.State) (bottom : Nat)
    (index : TreeMap Nat (List Nat)) (sub : Nat) : SparseRow :=
  if c.hasSub sub bottom then { sub, unsat := true, sups := [] }
  else { sub, unsat := false, sups := index.getD sub [] }

/-- Sparse EL reference answer: one closure, rows read from the closure's
fact list, never a named x named list. -/
def sparseReferenceAnswer (recognized : ELCommonSourceRecognizer.RecognizedEL)
    (named : List Nat) : SparseTaxonomy :=
  let c := ELReference.closure recognized.top recognized.bottom named
    recognized.ontology
  let index := superIndex (TreeSet.ofList named) c.subs
  { named, rows := named.map (sparseRowOf c recognized.bottom index) }

/-- The reference bit of a requested subject is the disjunction of two fact
memberships in the closure: this is the closure's readout theorem composed with
the materialization characterisation of EL entailment. -/
private theorem referenceBitOf_iff_mem
    (recognized : ELCommonSourceRecognizer.RecognizedEL) (named : List Nat)
    {sub : Nat} (hsub : sub ∈ named) (sup : Nat) :
    ELReference.referenceBitOf
        (ELReference.closure recognized.top recognized.bottom named
          recognized.ontology) recognized.bottom sub sup = true ↔
      (sub, recognized.bottom) ∈
          (ELReference.closure recognized.top recognized.bottom named
            recognized.ontology).subs ∨
        (sub, sup) ∈
          (ELReference.closure recognized.top recognized.bottom named
            recognized.ontology).subs := by
  rw [← ELReference.referenceBit_eq,
    ELReference.referenceBit_exact_of_named recognized.top recognized.bottom
      named recognized.ontology hsub sup,
    ELCompletion.entails_iff_materialized_on
      (ELReference.closure_closedOn recognized.top recognized.bottom named
        recognized.ontology)
      (ELReference.closure_sound recognized.top recognized.bottom named
        recognized.ontology)
      (ELReference.mem_universe_of_named hsub)]
  rfl

theorem sparseRowOf_bit (recognized : ELCommonSourceRecognizer.RecognizedEL)
    (named : List Nat) {sub sup : Nat} (hsub : sub ∈ named) (hsup : sup ∈ named) :
    let c := ELReference.closure recognized.top recognized.bottom named
      recognized.ontology
    (sparseRowOf c recognized.bottom (superIndex (TreeSet.ofList named) c.subs)
        sub).bit sup =
      ELReference.referenceBitOf c recognized.bottom sub sup := by
  intro c
  have hiff := referenceBitOf_iff_mem recognized named hsub
  unfold sparseRowOf
  split
  · next hbot =>
      simp [SparseRow.bit, ELReference.referenceBitOf, hbot]
  · next hbot =>
      have hbot' : ELReference.referenceBitOf c recognized.bottom sub
          recognized.bottom = false := by
        simp [ELReference.referenceBitOf, hbot]
      have hnot : (sub, recognized.bottom) ∉ c.subs := by
        intro hmem
        have := (hiff recognized.bottom).mpr (Or.inl hmem)
        rw [hbot'] at this
        exact Bool.false_ne_true this
      apply Bool.eq_iff_iff.mpr
      rw [hiff sup]
      simp only [SparseRow.bit, Bool.false_or,
        mem_superIndex, TreeSet.contains_ofList, List.elem_eq_mem,
        decide_eq_true_eq]
      constructor
      · exact fun h => Or.inr h.1
      · rintro (h | h)
        · exact absurd h hnot
        · exact ⟨h, hsup⟩

theorem sparseReferenceAnswer_dense
    (recognized : ELCommonSourceRecognizer.RecognizedEL) (named : List Nat) :
    (sparseReferenceAnswer recognized named).dense =
      referenceAnswer recognized named := by
  simp only [sparseReferenceAnswer, referenceAnswer, SparseTaxonomy.dense,
    matrixAnswer, matrixCells, List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro sub hsub
  apply List.map_congr_left
  intro sup hsup
  have hrow : (sparseRowOf
      (ELReference.closure recognized.top recognized.bottom named
        recognized.ontology) recognized.bottom
      (superIndex (TreeSet.ofList named)
        (ELReference.closure recognized.top recognized.bottom named
          recognized.ontology).subs) sub).sub = sub := by
    unfold sparseRowOf; split <;> rfl
  rw [hrow, sparseRowOf_bit recognized named hsub hsup]

/-! ### The executable stages -/

/-- What the binary runs for `--procedure el`. -/
def sparseElReference (source : RequestedTaxonomySource) : Option SparseTaxonomy :=
  match ELCommonSourceRecognizer.recognizeEL source.named source.ontology with
  | none => none
  | some recognized =>
      if ELReference.nodupFast source.named then
        some (sparseReferenceAnswer recognized source.named)
      else none

/-- What the binary runs for `--procedure alc` (budget check stays in the
binary, as in v1.6.0). -/
def sparseAlcReference (source : RequestedTaxonomySource) : Option SparseTaxonomy :=
  match ALCCommonSourceRecognizer.recognizeALC source.named source.ontology with
  | none => none
  | some recognized =>
      if ELReference.nodupFast source.named then
        some (ofMatrix source.named
          (alcReferenceBitOf recognized
            (ALCReference.saturateC recognized.ontology)))
      else none

/-- The sparse EL output is exactly what the v1.6.0 reference execution
publishes, so every v1.6.0 theorem about `elReferenceExecution` covers it. -/
theorem sparseElReference_agrees (source : RequestedTaxonomySource)
    (t : SparseTaxonomy) (h : sparseElReference source = some t) :
    elReferenceExecution.run source =
      .publish { source, answer := t.dense, evidence := .elReference ⟨1⟩ } := by
  unfold sparseElReference at h
  split at h
  · cases h
  · next recognized hrecognized =>
      split at h
      · next hfast =>
          cases h
          have hnodup : source.named.Nodup := (ELReference.nodupFast_iff _).mp hfast
          simp [elReferenceExecution, hrecognized, hnodup,
            sparseReferenceAnswer_dense]
      · cases h

/-- The sparse ALC output with its exact v1.6.0 evidence. -/
theorem sparseAlcReference_agrees_exact (source : RequestedTaxonomySource)
    (t : SparseTaxonomy) (h : sparseAlcReference source = some t) :
    alcReferenceExecution.run source =
      .publish { source, answer := t.dense, evidence := .alcReference ⟨1⟩ } := by
  unfold sparseAlcReference at h
  split at h
  · cases h
  · next recognized hrecognized =>
      split at h
      · next hfast =>
          cases h
          have hnodup : source.named.Nodup := (ELReference.nodupFast_iff _).mp hfast
          simp [alcReferenceExecution, hrecognized, hnodup, ofMatrix_dense,
            alcReferenceAnswer]
      · cases h

theorem sparseAlcReference_agrees (source : RequestedTaxonomySource)
    (t : SparseTaxonomy) (h : sparseAlcReference source = some t) :
    ∃ evidence, alcReferenceExecution.run source =
      .publish { source, answer := t.dense, evidence } :=
  ⟨_, sparseAlcReference_agrees_exact source t h⟩

theorem sparseElReference_correct (source : RequestedTaxonomySource)
    (t : SparseTaxonomy) (h : sparseElReference source = some t) :
    RequestedCorrect source t.dense :=
  requestedExactAccept_sound source t.dense _
    (elReferenceExecution.accepted source _ (sparseElReference_agrees source t h))

theorem sparseAlcReference_correct (source : RequestedTaxonomySource)
    (t : SparseTaxonomy) (h : sparseAlcReference source = some t) :
    RequestedCorrect source t.dense :=
  requestedExactAccept_sound source t.dense _
    (alcReferenceExecution.accepted source _
      (sparseAlcReference_agrees_exact source t h))

/-- Totality on the fragment: the sparse stage answers whenever v1.6.0's
reference execution does. -/
theorem sparseElReference_complete (source : RequestedTaxonomySource)
    (hrecognized : (ELCommonSourceRecognizer.recognizeEL source.named
      source.ontology).isSome = true)
    (hnodup : source.named.Nodup) :
    (sparseElReference source).isSome = true := by
  rcases Option.isSome_iff_exists.mp hrecognized with ⟨recognized, hsome⟩
  simp [sparseElReference, hsome, (ELReference.nodupFast_iff _).mpr hnodup]

/-- Totality of the sparse ALC stage on the recognised ALC fragment. -/
theorem sparseAlcReference_complete (source : RequestedTaxonomySource)
    (hrecognized : (ALCCommonSourceRecognizer.recognizeALC source.named
      source.ontology).isSome = true)
    (hnodup : source.named.Nodup) :
    (sparseAlcReference source).isSome = true := by
  rcases Option.isSome_iff_exists.mp hrecognized with ⟨recognized, hsome⟩
  simp [sparseAlcReference, hsome, (ELReference.nodupFast_iff _).mpr hnodup]

#print axioms ofMatrix_dense
#print axioms mem_superIndex
#print axioms sparseRowOf_bit
#print axioms sparseReferenceAnswer_dense
#print axioms sparseElReference_agrees
#print axioms sparseAlcReference_agrees_exact
#print axioms sparseAlcReference_agrees
#print axioms sparseElReference_correct
#print axioms sparseAlcReference_correct
#print axioms sparseElReference_complete
#print axioms sparseAlcReference_complete

end ContextCalculus.SparseTaxonomy
