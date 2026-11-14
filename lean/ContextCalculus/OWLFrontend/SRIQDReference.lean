import ContextCalculus.OWLFrontend.SRIQDCorrect
import ContextCalculus.OWLFrontend.SRIQReference
import ContextCalculus.SRIQD.CellPartsProc

/-!
# The SHIQ(D) route (v1.7.0 stage C4, part D)

`owlSHIQDReference O requested`: translate (`translateSRIQD`), check the
simple-role restriction on the object part (`isSHIQB`), check that the
data atoms are in the supported sub-language (`allSupported`), remove
transitivity (`encTransQD`), split the data theory of the map into parts by
the readings of the datatypes outside the map on the small finite value
types (`SRIQD/CellParts*.lean`), and publish a subsumption when every part
entails it (`aliveD` per part, `entailsParts_iff`). Without datatypes
outside the map there is one part. The answer rows are read as in the SHIQ
route.

`owlSHIQDReference_sound`: every published bit is OWL entailment at the
OWL 2 datatype map `owl2MapP pat`, for every reading `pat` of
`xsd:pattern`.

`owlSHIQReference_sound_at`: the SHIQ route's answers are entailment at
any datatype map, in particular at the OWL 2 map (`entailsSubAt_iff`).
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD
open ContextCalculus.SparseTaxonomy

/-- The requested indices of the encoding with `k` new names. -/
def sriqdRequest (T : SRIQDTranslation) (hle : T.named.length ≤ T.obj.conceptCount) (k : Nat) :
    List (Fin (T.obj.conceptCount + k)) :=
  List.ofFn fun i : Fin T.named.length => Fin.castAdd k ⟨i.val, Nat.lt_of_lt_of_le i.isLt hle⟩

/-- The answer rows: `b` is a subsumer of `a` when every alive set in `gs`
(one per part) puts `b` in every root record that contains `a`. -/
def sriqdRows (T : SRIQDTranslation) (hle : T.named.length ≤ T.obj.conceptCount) {k : Nat}
    (gs : List (Finset (SRIQ.Proc.QRec (T.obj.conceptCount + k) T.obj.roleCount))) :
    List SparseRow :=
  sriRowsN T.named.length ((sriqdRequest T hle k).map fun a => (a, some
    ((List.finRange (T.obj.conceptCount + k)).filter fun b =>
      gs.all fun G => decide (∀ ρ ∈ G, ρ.2 = none → a ∈ ρ.1 → b ∈ ρ.1))))

/-- All data atoms of the table are in the supported sub-language. -/
def allSupported (T : SRIQDTranslation) : Bool :=
  (List.finRange T.tab.length).all fun p => drSupported (spec T.tab p)

/-- The data bound of the encoding and the small-cell threshold. -/
def partBound (T : SRIQDTranslation) : Nat :=
  ContextCalculus.SRIQD.dbnd (ContextCalculus.SRIQD.Proc.encTransQD T.ontology).2 *
    (ContextCalculus.SRIQD.allG (allFrees (spec T.tab)).length).length

/-- The alive records of every part of the data theory. -/
def partAlive (T : SRIQDTranslation) :
    List (Finset (SRIQ.Proc.QRec (T.obj.conceptCount + (ContextCalculus.SRIQD.Proc.encTransQD
      T.ontology).1) T.obj.roleCount)) :=
  let sp := spec T.tab
  let as := allBases sp
  let cs := cellsOf as
  let L := partBound T
  (ContextCalculus.SRIQD.partsOf (cellSize as) (allFrees sp).length
      (cs.filter fun c => ContextCalculus.SRIQD.small (cellSize as) L c)).map fun x =>
    ContextCalculus.SRIQD.Proc.aliveD (ContextCalculus.SRIQD.Proc.encTransQD T.ontology).2
      (ContextCalculus.SRIQD.partCard cs (cellSize as) L (owlE sp)
        (ContextCalculus.SRIQD.toPart (allFrees sp).length x))

/-- **The SHIQ(D) route.** The data theory of the OWL 2 map is split into
parts by the readings of the datatypes outside the map on the small finite
value types; a subsumption is published when every part entails it. -/
def owlSHIQDReference (O : OWL.Ontology) (requested : List OWL.IRI) : Option OWLAnswer :=
  match translateSRIQD O requested with
  | none => none
  | some T =>
    if h : (isSHIQB (ContextCalculus.SRIQD.objPart T.ontology) && allSupported T) = true ∧
        T.named.length ≤ T.obj.conceptCount then
      some { named := T.named, rows := sriqdRows T h.2 (partAlive T) }
    else none

theorem translateSRIQD_named {O : OWL.Ontology} {requested : List OWL.IRI} {T : SRIQDTranslation}
    (h : translateSRIQD O requested = some T) : T.named = requested.eraseDups := by
  unfold translateSRIQD at h
  split_ifs at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h; rfl
  · cases h

/-- The bits of the rows. -/
theorem sriqd_bit (T : SRIQDTranslation) (hle : T.named.length ≤ T.obj.conceptCount) {k : Nat}
    {α : Type} (xs : List α)
    (f : α → Finset (SRIQ.Proc.QRec (T.obj.conceptCount + k) T.obj.roleCount))
    (i j : Nat) (hi : i < T.named.length) (hj : j < T.named.length) :
    OWLAnswer.bit { named := T.named, rows := sriqdRows T hle (xs.map f) } i j = true ↔
      ∀ x ∈ xs, ∀ ρ ∈ f x, ρ.2 = none → Fin.castAdd k ⟨i, Nat.lt_of_lt_of_le hi hle⟩ ∈ ρ.1 →
        Fin.castAdd k ⟨j, Nat.lt_of_lt_of_le hj hle⟩ ∈ ρ.1 := by
  have hrow : OWLAnswer.bit { named := T.named, rows := sriqdRows T hle (xs.map f) } i j =
      (sriRowN T.named.length (Fin.castAdd k ⟨i, Nat.lt_of_lt_of_le hi hle⟩,
        some ((List.finRange (T.obj.conceptCount + k)).filter fun b =>
          (xs.map f).all fun G => decide (∀ ρ ∈ G, ρ.2 = none →
            Fin.castAdd k ⟨i, Nat.lt_of_lt_of_le hi hle⟩ ∈ ρ.1 → b ∈ ρ.1)))).bit j := by
    simp only [OWLAnswer.bit, sriqdRows, sriRowsN, List.getElem?_map, sriqdRequest,
      List.getElem?_ofFn, hi, dite_true, Option.map_some]
  rw [hrow]
  simp only [sriRowN, SparseRow.bit, Bool.false_or, List.contains_iff_mem, List.mem_filter,
    List.mem_map, List.mem_finRange, true_and, List.all_eq_true, decide_eq_true_eq,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · rintro ⟨⟨b, hb, hbj⟩, -⟩
    have : Fin.castAdd k ⟨j, Nat.lt_of_lt_of_le hj hle⟩ = b := Fin.ext (by simp [hbj])
    rw [this]; exact hb
  · intro h
    exact ⟨⟨_, h, rfl⟩, by simpa using hj⟩

/-- **Soundness of the SHIQ(D) route.** Every published bit is entailment at
the OWL 2 datatype map, for every reading of `xsd:pattern`, also with
datatypes outside the map. -/
theorem owlSHIQDReference_sound (pat : String → String → Prop) {O : OWL.Ontology}
    {requested : List OWL.IRI} {a : OWLAnswer} (h : owlSHIQDReference O requested = some a) :
    a.named = requested.eraseDups ∧
      ∀ i j (hi : i < a.named.length) (hj : j < a.named.length),
        (a.bit i j = true ↔ EntailsSubAt (owl2MapP pat) O a.named[i] a.named[j]) := by
  unfold owlSHIQDReference at h
  split at h
  · cases h
  next T hT =>
    split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨translateSRIQD_named hT, fun i j hi hj => ?_⟩
      obtain ⟨hc1, hle⟩ := hc
      rw [Bool.and_eq_true] at hc1
      have hS : ContextCalculus.SRIQD.Proc.IsSHIQD T.ontology := isSHIQ_of_isSHIQB hc1.1
      have hsup : ∀ p, drSupported (spec T.tab p) = true := fun p =>
        List.all_eq_true.1 hc1.2 p (List.mem_finRange p)
      have heq : owlTheory pat (spec T.tab) = ContextCalculus.SRIQD.cellTheory
          (cellOf (allBases (spec T.tab))) (owlE (spec T.tab)) := by
        funext V atom
        exact propext (owlTheory_iff pat hsup V atom)
      unfold partAlive
      rw [sriqd_bit T hle _ _ i j hi hj]
      change _ ↔ EntailsSubAt (owl2MapP pat) O T.named[i] T.named[j]
      rw [translateSRIQD_correct pat hT hi hj (Nat.lt_of_lt_of_le hi hle) (Nat.lt_of_lt_of_le hj hle),
        ContextCalculus.SRIQD.Proc.encTransQD_correct hS, heq,
        ← ContextCalculus.SRIQD.entailsParts_iff (cellSpec _) (le_refl _) (le_refl _)
          (ContextCalculus.SRIQD.Proc.encTransQD_isALCHIQ T.ontology)]
      simp only [ContextCalculus.SRIQD.entailsParts, List.all_eq_true,
        ContextCalculus.SRIQD.Proc.entailsQD, decide_eq_true_eq]
      rfl
    · cases h

/-- The SHIQ route's answers are entailment at every datatype map. -/
theorem owlSHIQReference_sound_at (DM : DatatypeMap) {O : OWL.Ontology} {requested : List OWL.IRI}
    {a : OWLAnswer} (h : owlSHIQReference O requested = some a) :
    a.named = requested.eraseDups ∧
      ∀ i j (hi : i < a.named.length) (hj : j < a.named.length),
        (a.bit i j = true ↔ EntailsSubAt DM O a.named[i] a.named[j]) := by
  obtain ⟨h1, h2⟩ := owlSHIQReference_sound h
  have hS : O.isSHIQ = true := by
    unfold owlSHIQReference at h
    split at h
    · cases h
    · next T hT => exact translateSRIQ_isSHIQ hT
  exact ⟨h1, fun i j hi hj => (h2 i j hi hj).trans (entailsSubAt_iff hS DM _ _).symm⟩

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.owlSHIQDReference_sound
#print axioms ContextCalculus.OWLFrontend.owlSHIQReference_sound_at
