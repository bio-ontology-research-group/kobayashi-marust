import ContextCalculus.OWLFrontend.SRITranslateCorrect
import ContextCalculus.OWLFrontend.Reference
import ContextCalculus.SRI.Fast
import ContextCalculus.SRI.Transitivity

/-!
# The v1.6.3 OWL route: SHI through the SRI normal form

`docs/V1.6.3-HT-PLAN.md`. `owlSRIReference` translates the ontology to the
SRI normal form (`translateSRI`), checks that every role chain is an
inclusion or a transitivity axiom, removes transitivity (`encTrans`),
classifies the requested names with the fast procedure (`classifyF`) and
reads out one sparse row per requested IRI, in the format of the EL and
ALC routes. An unsatisfiable name gets a row with `unsat := true` and no
listed subsumers.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus
open ContextCalculus.SparseTaxonomy
open ContextCalculus.SRI
open ContextCalculus.SRI.Proc

/-- Chains are inclusions or transitivity (`IsSHI`), as a Boolean. -/
def chainOK {n m : Nat} : SRI.Clause (Fin n) (Fin m) → Bool
  | .chain body S => body.length == 1 || body == [S, S]
  | _ => true

def isSHIB {n m : Nat} (O : SRI.Ontology (Fin n) (Fin m)) : Bool :=
  O.all chainOK

theorem isSHI_of_isSHIB {n m : Nat} {O : SRI.Ontology (Fin n) (Fin m)}
    (h : isSHIB O = true) : IsSHI O := by
  intro body S hc
  have := List.all_eq_true.1 h _ hc
  simp only [chainOK, Bool.or_eq_true, beq_iff_eq] at this
  exact this

/-- The requested indices `0 .. named.length - 1`, as names of the
encoding. -/
def sriRequest (T : SRITranslation) (k : Nat) : List (Fin (T.conceptCount + k)) :=
  List.ofFn fun i : Fin T.named.length =>
    Fin.castAdd k ⟨i.val, Nat.lt_of_lt_of_le i.isLt T.hnamed⟩

/-- The row of one classified name: unsatisfiable, or its subsumers among
the requested indices. -/
def sriRow (T : SRITranslation) {k : Nat}
    (p : Fin (T.conceptCount + k) × Option (List (Fin (T.conceptCount + k)))) : SparseRow :=
  match p.2 with
  | none => { sub := p.1.val, unsat := true, sups := [] }
  | some L =>
    { sub := p.1.val, unsat := false,
      sups := (L.map Fin.val).filter (· < T.named.length) }

/-- One row per requested index. -/
def sriRows (T : SRITranslation) {k : Nat}
    (cls : List (Fin (T.conceptCount + k) × Option (List (Fin (T.conceptCount + k))))) :
    List SparseRow :=
  cls.map (sriRow T)

/-- The SHI route. -/
def owlSRIReference (O : OWL.Ontology) (requested : List OWL.IRI) : Option OWLAnswer :=
  match translateSRI O requested with
  | none => none
  | some T =>
      if isSHIB T.ontology then
        let E := encTrans T.ontology
        some { named := T.named,
               rows := sriRows T (classifyF E.2 (sriRequest T E.1)) }
      else none

/-! ### Exactness -/

/-- The bits of the answer over any ALCHI ontology on the encoded names. -/
theorem sri_bit (T : SRITranslation) {k : Nat}
    {O' : SRI.Ontology (Fin (T.conceptCount + k)) (Fin T.roleCount)} (hA : IsALCHI O')
    (i j : Nat) (hi : i < T.named.length) (hj : j < T.named.length) :
    OWLAnswer.bit { named := T.named, rows := sriRows T (classifyF O' (sriRequest T k)) } i j
        = true ↔
      SRI.EntailsSub O' (Fin.castAdd k ⟨i, Nat.lt_of_lt_of_le hi T.hnamed⟩)
        (Fin.castAdd k ⟨j, Nat.lt_of_lt_of_le hj T.hnamed⟩) := by
  obtain ⟨g, hg⟩ : ∃ g : Fin (T.conceptCount + k) → Option (List (Fin (T.conceptCount + k))),
      classifyF O' (sriRequest T k) = (sriRequest T k).map fun a => (a, g a) := ⟨_, rfl⟩
  have hiC : i < T.conceptCount := Nat.lt_of_lt_of_le hi T.hnamed
  have hjC : j < T.conceptCount := Nat.lt_of_lt_of_le hj T.hnamed
  have hmem : (Fin.castAdd k ⟨i, hiC⟩, g (Fin.castAdd k ⟨i, hiC⟩)) ∈
      classifyF O' (sriRequest T k) := by
    rw [hg]
    refine List.mem_map_of_mem ?_
    simp only [sriRequest, List.mem_ofFn]
    exact ⟨⟨i, hi⟩, rfl⟩
  obtain ⟨-, hnone, hsome⟩ := classifyF_spec hA _ hmem
  have hrow : OWLAnswer.bit { named := T.named, rows := sriRows T (classifyF O' (sriRequest T k)) } i j
      = (sriRow T (Fin.castAdd k ⟨i, hiC⟩, g (Fin.castAdd k ⟨i, hiC⟩))).bit j := by
    simp only [OWLAnswer.bit, sriRows]
    rw [hg, List.map_map, List.getElem?_map]
    simp only [sriRequest, List.getElem?_ofFn, hi, dite_true, Option.map_some, Function.comp]
  rw [hrow]
  cases hga : g (Fin.castAdd k ⟨i, hiC⟩) with
  | none =>
    simp only [sriRow, SparseRow.bit, Bool.true_or, true_iff]
    intro D _ I hI x hx
    exact absurd hx (hnone.1 hga D I hI x)
  | some L =>
    simp only [sriRow, SparseRow.bit, Bool.false_or, List.contains_iff_mem, List.mem_filter,
      List.mem_map, decide_eq_true_eq]
    rw [← hsome L hga]
    constructor
    · rintro ⟨⟨b, hb, hbj⟩, -⟩
      have : Fin.castAdd k ⟨j, hjC⟩ = b := Fin.ext (by simp [hbj])
      rw [this]; exact hb
    · intro h
      exact ⟨⟨_, h, rfl⟩, by simpa using hj⟩

/-- Every answer of the SHI route is exact under the OWL 2 direct semantics,
for every requested pair. -/
theorem owlSRIReference_sound {O : OWL.Ontology} {requested : List OWL.IRI}
    {a : OWLAnswer} (h : owlSRIReference O requested = some a) :
    a.named = requested.eraseDups ∧
      ∀ i j (hi : i < a.named.length) (hj : j < a.named.length),
        (a.bit i j = true ↔ OWL.EntailsSub O a.named[i] a.named[j]) := by
  unfold owlSRIReference at h
  split at h
  · exact absurd h (by simp)
  next T hT =>
    split at h
    · next hS =>
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨translateSRI_named hT, ?_⟩
      intro i j hi hj
      rw [translateSRI_correct hT i j hi hj, encTrans_correct (isSHI_of_isSHIB hS)]
      exact sri_bit T (encTrans_isALCHI T.ontology) i j hi hj
    · exact absurd h (by simp)

#print axioms owlSRIReference_sound

end ContextCalculus.OWLFrontend
