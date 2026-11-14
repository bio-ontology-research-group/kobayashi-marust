import ContextCalculus.OWLFrontend.SRIQDCorrect
import ContextCalculus.OWLFrontend.SRIQReference

/-!
# The SHIQ(D) route (v1.7.0 stage C4, part D)

`owlSHIQDReference O requested`: translate (`translateSRIQD`), check the
simple-role restriction on the object part (`isSHIQB`), check that the
data atoms are in the supported sub-theory of the OWL 2 datatype map with
an oracle (`owlCheck`), remove transitivity (`encTransQD`), and classify
with the oracle `owlCard` (`classifyQD`). The answer rows are read as in
the SHIQ route.

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

/-- The answer rows from `classifyQD` on an ontology over the encoded names. -/
def sriqdRows (T : SRIQDTranslation) (hle : T.named.length ≤ T.obj.conceptCount) {k : Nat}
    (O' : ContextCalculus.SRIQD.Ontology (Fin (T.obj.conceptCount + k)) (Fin T.obj.roleCount)
      (Fin T.dps.length) (Fin T.tab.length))
    (card : Finset (Fin T.tab.length) → Option Nat) : List SparseRow :=
  sriRowsN T.named.length
    ((ContextCalculus.SRIQD.Proc.classifyQD O' card (sriqdRequest T hle k)).map fun p => (p.1, some p.2))

/-- **The SHIQ(D) route.** -/
def owlSHIQDReference (O : OWL.Ontology) (requested : List OWL.IRI) : Option OWLAnswer :=
  match translateSRIQD O requested with
  | none => none
  | some T =>
    if h : (isSHIQB (ContextCalculus.SRIQD.objPart T.ontology) && owlCheck (spec T.tab)) = true ∧
        T.named.length ≤ T.obj.conceptCount then
      let E := ContextCalculus.SRIQD.Proc.encTransQD T.ontology
      some { named := T.named, rows := sriqdRows T h.2 E.2 (owlCardC (spec T.tab)) }
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

/-- The bits of the rows over any ALCHIQ ontology on the encoded names. -/
theorem sriqd_bit (T : SRIQDTranslation) (hle : T.named.length ≤ T.obj.conceptCount) {k : Nat}
    {Θ : ContextCalculus.SRIQD.DataTheory (Fin T.tab.length)}
    {card : Finset (Fin T.tab.length) → Option Nat} (hspec : ContextCalculus.SRIQD.OracleSpec Θ card)
    {O' : ContextCalculus.SRIQD.Ontology (Fin (T.obj.conceptCount + k)) (Fin T.obj.roleCount)
      (Fin T.dps.length) (Fin T.tab.length)} (hA : ContextCalculus.SRIQD.IsALCHIQ O')
    (i j : Nat) (hi : i < T.named.length) (hj : j < T.named.length) :
    OWLAnswer.bit { named := T.named, rows := sriqdRows T hle O' card } i j = true ↔
      ContextCalculus.SRIQD.EntailsSub Θ O'
        (Fin.castAdd k ⟨i, Nat.lt_of_lt_of_le hi hle⟩) (Fin.castAdd k ⟨j, Nat.lt_of_lt_of_le hj hle⟩) := by
  have hrow : OWLAnswer.bit { named := T.named, rows := sriqdRows T hle O' card } i j =
      (sriRowN T.named.length (Fin.castAdd k ⟨i, Nat.lt_of_lt_of_le hi hle⟩,
        some ((List.finRange (T.obj.conceptCount + k)).filter fun b =>
          decide (∀ ρ ∈ ContextCalculus.SRIQD.Proc.aliveD O' card, ρ.2 = none →
            Fin.castAdd k ⟨i, Nat.lt_of_lt_of_le hi hle⟩ ∈ ρ.1 → b ∈ ρ.1)))).bit j := by
    simp only [OWLAnswer.bit, sriqdRows, sriRowsN, ContextCalculus.SRIQD.Proc.classifyQD,
      List.map_map, List.getElem?_map, sriqdRequest, List.getElem?_ofFn, hi, dite_true,
      Option.map_some, Function.comp]
  rw [hrow]
  simp only [sriRowN, SparseRow.bit, Bool.false_or, List.contains_iff_mem, List.mem_filter,
    List.mem_map, decide_eq_true_eq, List.mem_finRange, true_and]
  rw [← ContextCalculus.SRIQD.Proc.entailsQD_iff hspec hA]
  simp only [ContextCalculus.SRIQD.Proc.entailsQD, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨b, hb, hbj⟩, -⟩
    have : Fin.castAdd k ⟨j, Nat.lt_of_lt_of_le hj hle⟩ = b := Fin.ext (by simp [hbj])
    rw [this]; exact hb
  · intro h
    exact ⟨⟨_, h, rfl⟩, by simpa using hj⟩

/-- **Soundness of the SHIQ(D) route.** Every published bit is entailment at
the OWL 2 datatype map, for every reading of `xsd:pattern`. -/
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
      have hspec := owlCardC_eq (spec T.tab) ▸ oracleSpec_owl pat hc1.2
      rw [sriqd_bit T hle hspec (ContextCalculus.SRIQD.Proc.encTransQD_isALCHIQ T.ontology) i j hi hj,
        ← ContextCalculus.SRIQD.Proc.encTransQD_correct hS,
        translateSRIQD_correct pat hT hi hj]
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
