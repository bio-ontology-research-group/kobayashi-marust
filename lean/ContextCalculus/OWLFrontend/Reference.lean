import ContextCalculus.OWLFrontend.ELTranslateCorrect
import ContextCalculus.OWLFrontend.ALCTranslateCorrect
import ContextCalculus.SparseTaxonomy

/-!
# The OWL reference procedure and its capstone

`docs/V1.6.2-FRONTEND-PLAN.md`, section 7. `owlReference O requested`
translates an OWL ontology with the EL route if it is OWL EL, else with the
ALC route if it is OWL ALC, runs the matching v1.6.0 reference procedure on
the normal forms, and reads out one sparse row per requested IRI (the v1.6.1
row format). The two theorems at the end are stated on the OWL 2 direct
semantics of the ontology alone:

- `owlReference_sound`: every published row is exact for `OWL.EntailsSub`;
- `owlReference_complete`: on OWL EL and OWL ALC the procedure publishes.

Unsatisfiability and inconsistency follow by the probe reading
(`OWL.unsatisfiable_iff_entailsSub_fresh`,
`OWL.inconsistent_iff_entailsSub_fresh`): request fresh IRIs.

Requested IRI `named[i]` has index `i` in both translations, so the rows
range over `List.range named.length`.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus
open ContextCalculus.SparseTaxonomy

/-- A published OWL answer: the requested IRIs and one sparse row per IRI,
row `i` about `named[i]`, superclasses by index. -/
structure OWLAnswer where
  named : List OWL.IRI
  rows : List SparseRow
deriving Repr

/-- The answer's bit for the pair of requested indices `(i, j)`. -/
def OWLAnswer.bit (a : OWLAnswer) (i j : Nat) : Bool :=
  match a.rows[i]? with
  | some row => row.bit j
  | none => false

/-- EL route: one closure, sparse readout. -/
def owlELReference (O : OWL.Ontology) (requested : List OWL.IRI) : Option OWLAnswer :=
  (translateEL O requested).map fun T =>
    { named := T.named
      rows := (sparseReferenceAnswer ⟨T.top, T.bottom, T.ontology⟩
        (List.range T.named.length)).rows }

/-- The ALC bit on indices, `false` outside the concept range. -/
def alcIndexBit (T : ALCTranslation)
    (G : Finset (Finset (Fin T.conceptCount))) (i j : Nat) : Bool :=
  if hi : i < T.conceptCount then
    if hj : j < T.conceptCount then ALCReference.alcBitOf G ⟨i, hi⟩ ⟨j, hj⟩
    else false
  else false

/-- ALC route: one type elimination, dense readout (the ALC signatures the
procedure can finish are small). -/
def owlALCReference (O : OWL.Ontology) (requested : List OWL.IRI) : Option OWLAnswer :=
  (translateALC O requested).map fun T =>
    let G := ALCReference.saturateC T.ontology
    { named := T.named
      rows := (ofMatrix (List.range T.named.length) (alcIndexBit T G)).rows }

/-- The OWL reference procedure: EL first, then ALC. -/
def owlReference (O : OWL.Ontology) (requested : List OWL.IRI) : Option OWLAnswer :=
  match owlELReference O requested with
  | some a => some a
  | none => owlALCReference O requested

/-! ### Exactness of each route -/

theorem owlELReference_sound {O : OWL.Ontology} {requested : List OWL.IRI}
    {a : OWLAnswer} (h : owlELReference O requested = some a) :
    a.named = requested.eraseDups ∧
      ∀ i j (hi : i < a.named.length) (hj : j < a.named.length),
        (a.bit i j = true ↔ OWL.EntailsSub O a.named[i] a.named[j]) := by
  unfold owlELReference at h
  rcases hT : translateEL O requested with _ | T
  · simp [hT] at h
  · simp only [hT, Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨translateEL_named hT, ?_⟩
    intro i j hi hj
    have hiR : i ∈ List.range T.named.length := List.mem_range.mpr hi
    have hjR : j ∈ List.range T.named.length := List.mem_range.mpr hj
    change OWLAnswer.bit _ i j = true ↔ OWL.EntailsSub O T.named[i] T.named[j]
    rw [translateEL_correct hT i j hi hj]
    simp only [OWLAnswer.bit, sparseReferenceAnswer, List.getElem?_map,
      List.getElem?_range hi, Option.map_some]
    rw [sparseRowOf_bit ⟨T.top, T.bottom, T.ontology⟩ (List.range T.named.length)
      hiR hjR]
    exact ELReference.referenceBit_exact_of_named T.top T.bottom
      (List.range T.named.length) T.ontology hiR j

theorem owlALCReference_sound {O : OWL.Ontology} {requested : List OWL.IRI}
    {a : OWLAnswer} (h : owlALCReference O requested = some a) :
    a.named = requested.eraseDups ∧
      ∀ i j (hi : i < a.named.length) (hj : j < a.named.length),
        (a.bit i j = true ↔ OWL.EntailsSub O a.named[i] a.named[j]) := by
  unfold owlALCReference at h
  rcases hT : translateALC O requested with _ | T
  · simp [hT] at h
  · simp only [hT, Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨translateALC_named hT, ?_⟩
    intro i j hi hj
    change OWLAnswer.bit _ i j = true ↔ OWL.EntailsSub O T.named[i] T.named[j]
    rw [translateALC_correct hT i j hi hj, ← ALCReference.alcBit_iff_entailsSub]
    have hjR : j ∈ List.range T.named.length := List.mem_range.mpr hj
    have hi' : i < T.conceptCount := Nat.lt_of_lt_of_le hi T.hnamed
    have hj' : j < T.conceptCount := Nat.lt_of_lt_of_le hj T.hnamed
    simp only [OWLAnswer.bit, ofMatrix, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, SparseRow.bit, Bool.false_or, List.contains_iff_mem,
      List.mem_filter, hjR, true_and, alcIndexBit, hi', hj', dite_true]
    rfl

/-! ### The capstone -/

/-- Every answer the OWL reference procedure publishes is exact under the
OWL 2 direct semantics, for every requested pair. -/
theorem owlReference_sound {O : OWL.Ontology} {requested : List OWL.IRI}
    {a : OWLAnswer} (h : owlReference O requested = some a) :
    a.named = requested.eraseDups ∧
      ∀ i j (hi : i < a.named.length) (hj : j < a.named.length),
        (a.bit i j = true ↔ OWL.EntailsSub O a.named[i] a.named[j]) := by
  unfold owlReference at h
  split at h
  · next a' hEL =>
      cases h
      exact owlELReference_sound hEL
  · exact owlALCReference_sound h

/-- On OWL EL and OWL ALC ontologies the OWL reference procedure publishes,
for every requested list. -/
theorem owlReference_complete {O : OWL.Ontology} (requested : List OWL.IRI)
    (h : O.isEL = true ∨ O.isALC = true) :
    (owlReference O requested).isSome = true := by
  unfold owlReference
  rcases h with hEL | hALC
  · have hs := translateEL_isSome (requested := requested) hEL
    split
    · rfl
    · next hnone =>
        simp [owlELReference, Option.map_eq_none_iff] at hnone
        rw [hnone] at hs
        exact absurd hs (by simp)
  · split
    · rfl
    · have hs := translateALC_isSome (requested := requested) hALC
      simpa [owlALCReference, Option.isSome_map] using hs

#print axioms owlELReference_sound
#print axioms owlALCReference_sound
#print axioms owlReference_sound
#print axioms owlReference_complete

end ContextCalculus.OWLFrontend
