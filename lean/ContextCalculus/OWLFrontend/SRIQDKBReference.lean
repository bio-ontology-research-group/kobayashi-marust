import ContextCalculus.OWLFrontend.SRIQDKBCorrect
import ContextCalculus.OWLFrontend.SRIQDComplete

/-!
# The SHIQ(D) knowledge-base route: consistency (v1.7.0 stage C4)

`owlSHIQDKBConsistent O hint` decides whether an ontology of the SHIQ(D)
knowledge-base part (`Ontology.isSHIQDKB`) has a model at the OWL 2
datatype map: translate (`translateSRIQDKB`), check the simple-role
restrictions on the object part (`isSHIQB`, `negSimpleB`) and the
supported data sub-language (`drSupported`), and ask whether some part of
the data theory accepts the translated knowledge base (`consistentParts`,
with the split selector `splitCell` of the SHIQ(D) route). The optional
hint is a realisation in the text format of the SHIQ knowledge-base route
(`RawHint`), handed to every part.

`owlSHIQDKBConsistent_sound`: every answer is consistency at
`owl2MapP pat`, for every reading `pat` of `xsd:pattern` and every hint.
`owlSHIQDKBConsistent_isSome_iff`: the route answers exactly on the SHIQ(D)
knowledge-base part with the checks passed.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD

/-! ## The translation succeeds -/

theorem objOntK_isSHIQKB {O : Ontology} (hO : O.isSHIQDKB = true) (base : String) :
    (objOntK O base).isSHIQKB = true := by
  have hO' : ∀ ax ∈ O.axioms, ax.isSHIQDKB = true := by
    simpa [Ontology.isSHIQDKB, List.all_eq_true] using hO
  simp only [Ontology.isSHIQKB, List.all_eq_true]
  intro ax hax
  obtain ⟨ax', hax', rfl⟩ := List.mem_map.1 hax
  obtain ⟨ax0, h0, hax'0⟩ := List.mem_flatMap.1 hax'
  exact isSHIQKB_absAxK _ (rwK_ok (hO' ax0 h0) hax'0)

theorem nameIxK_isSome {T : SRIQKBTranslation} {a : IRI} (ha : a ∈ T.named) :
    (nameIxK T a).isSome = true := by
  unfold nameIxK
  rw [dif_pos (List.idxOf_lt_length_of_mem ha)]
  rfl

/-- The translation succeeds on the SHIQ(D) knowledge-base part. -/
theorem translateSRIQDKB_isSome {O : Ontology} (requested extra : List IRI)
    (hO : O.isSHIQDKB = true) : (translateSRIQDKB O requested extra).isSome = true := by
  have hT := translateSRIQKB_isSome (requested := requested ++
    freshNames (SRIQKB.defBase O requested) (tableK O)) (extra := extra)
    (objOntK_isSHIQKB hO (SRIQKB.defBase O requested))
  obtain ⟨Tobj, hTobj⟩ := Option.isSome_iff_exists.1 hT
  have hTn := (translateSRIQKB_spec hTobj).2.1
  have hfr : ∀ e ∈ tableK O, fName (SRIQKB.defBase O requested) (tableK O) e ∈ Tobj.named ∧
      wName (SRIQKB.defBase O requested) (tableK O) e ∈ Tobj.named := by
    intro e he
    rw [hTn]
    constructor <;> refine List.mem_eraseDups.2 (List.mem_append_right _ ?_) <;>
      exact List.mem_flatMap.2 ⟨e, he, by simp⟩
  have hp : ∀ e ∈ tableK O, e.p ∈ dpropsK O := fun e he =>
    List.mem_dedup.2 (List.mem_append_left _ (List.mem_map_of_mem he))
  have hsp : ∀ pq ∈ O.axioms.flatMap subPairs, pq.1 ∈ dpropsK O ∧ pq.2 ∈ dpropsK O :=
    fun pq hpq =>
    ⟨List.mem_dedup.2 (List.mem_append_right _ (List.mem_flatMap.2 ⟨pq, hpq, by simp⟩)),
      List.mem_dedup.2 (List.mem_append_right _ (List.mem_flatMap.2 ⟨pq, hpq, by simp⟩))⟩
  unfold translateSRIQDKB
  rw [if_pos hO]
  dsimp only
  rw [hTobj]
  dsimp only
  have hdc := SRIQKB.collect_isSome
      (f := dataClauseOfK Tobj (SRIQKB.defBase O requested) (tableK O) (dpropsK O))
      (xs := (tableK O).zipIdx) (by
    rintro ⟨e, k⟩ hek
    have hk := List.mem_zipIdx_iff_getElem?.1 hek
    have he : e ∈ tableK O := List.mem_of_getElem? hk
    have hk' : k < (tableK O).length := (List.getElem?_eq_some_iff.1 hk).1
    obtain ⟨F, hF⟩ := Option.isSome_iff_exists.1 (nameIxK_isSome (T := Tobj) (hfr e he).1)
    obtain ⟨W, hW⟩ := Option.isSome_iff_exists.1 (nameIxK_isSome (T := Tobj) (hfr e he).2)
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (dpIx_isSome (hp e he))
    unfold dataClauseOfK
    simp only [hF, hW, hu, dif_pos hk']
    rfl)
  have hsc := SRIQKB.collect_isSome (f := subClauseOfK Tobj (dpropsK O) (tableK O))
      (xs := O.axioms.flatMap subPairs) (by
    intro pq hpq
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (dpIx_isSome (hsp pq hpq).1)
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (dpIx_isSome (hsp pq hpq).2)
    unfold subClauseOfK
    simp only [hu, hw]
    rfl)
  obtain ⟨dc, hdc⟩ := Option.isSome_iff_exists.1 hdc
  obtain ⟨sc, hsc⟩ := Option.isSome_iff_exists.1 hsc
  rw [hdc, hsc]
  rfl

theorem translateSRIQDKB_isSHIQDKB {O : Ontology} {requested extra : List IRI}
    {T : SRIQDKBTranslation} (h : translateSRIQDKB O requested extra = some T) :
    O.isSHIQDKB = true := by
  unfold translateSRIQDKB at h
  split_ifs at h with hO
  exact hO

/-! ## The route -/

/-- The checks: simple roles in the counting clauses and in the negative
property assertions of the object part, and supported data atoms. -/
def kbdOK (T : SRIQDKBTranslation) : Bool :=
  isSHIQB (ContextCalculus.SRIQD.objPart T.ontology) &&
    negSimpleB (ContextCalculus.SRIQD.objPart T.ontology) (ContextCalculus.SRIQD.objABox T.abox) &&
    (List.finRange T.tab.length).all fun p => drSupported (spec T.tab p)

/-- The small-cell threshold of the knowledge base. -/
def kbdBound (T : SRIQDKBTranslation) : Nat :=
  ContextCalculus.SRIQD.dbnd (ContextCalculus.SRIQD.Proc.encO
      (ContextCalculus.SRIQD.Proc.encTransQD T.ontology).2
      (ContextCalculus.SRIQD.Proc.encABoxD T.ontology T.abox)) *
    (ContextCalculus.SRIQD.allG (allFrees (spec T.tab)).length).length

/-- Some part of the data theory accepts the translated knowledge base. -/
def kbdConsistent (T : SRIQDKBTranslation) (hint : Option RawHint) : Bool :=
  let sp := spec T.tab
  let as := allBases sp
  let cs := cellsOf as
  ContextCalculus.SRIQD.consistentParts T.ontology T.abox cs (cellSize as)
    (ContextCalculus.SRIQD.splitCell cs (cellSize as) (kbdBound T) (owlE sp)) (owlE sp)
    (hint.bind fun h => h.toHint _ _ _)

/-- **Consistency of a SHIQ(D) knowledge base** at the OWL 2 datatype map. -/
def owlSHIQDKBConsistent (O : OWL.Ontology) (hint : Option RawHint) : Option Bool :=
  match translateSRIQDKB O [] [] with
  | none => none
  | some T => if kbdOK T then some (kbdConsistent T hint) else none

/-- `O` has a model at the datatype map `DM`. -/
def ConsistentAt (DM : DatatypeMap) (O : Ontology) : Prop :=
  ∃ (Dom : Type) (_ : Nonempty Dom) (I : Interp DM Dom), OWL.Model O I

theorem consistentAt_iff_not (DM : DatatypeMap) (O : Ontology) :
    ConsistentAt DM O ↔ ¬ InconsistentAt DM O := by
  constructor
  · rintro ⟨Dom, hn, I, hI⟩ h
    exact h Dom I hI
  · intro h
    by_contra hc
    exact h fun Dom hn I hI => hc ⟨Dom, hn, I, hI⟩

/-- The translated knowledge base is consistent iff some part accepts it,
when the checks pass. -/
theorem kbdConsistent_iff (pat : String → String → Prop) {T : SRIQDKBTranslation}
    (hok : kbdOK T = true) (hint : Option RawHint) :
    kbdConsistent T hint = true ↔
      ContextCalculus.SRIQD.ConsistentKB (owlTheory pat (spec T.tab)) T.ontology T.abox := by
  simp only [kbdOK, Bool.and_eq_true] at hok
  obtain ⟨⟨h1, h2⟩, h3⟩ := hok
  have hS : ContextCalculus.SRIQD.Proc.IsSHIQDKB T.ontology T.abox := isSHIQKB_of_checks h1 h2
  have hsup : ∀ p, drSupported (spec T.tab p) = true := fun p =>
    List.all_eq_true.1 h3 p (List.mem_finRange p)
  have heq : owlTheory pat (spec T.tab) = ContextCalculus.SRIQD.cellTheory
      (cellOf (allBases (spec T.tab))) (owlE (spec T.tab)) := by
    funext V atom
    exact propext (owlTheory_iff pat hsup V atom)
  rw [heq]
  exact ContextCalculus.SRIQD.consistentParts_iff (cellSpec _) (le_refl (kbdBound T))
    ContextCalculus.SRIQD.splitCell_ok.1 ContextCalculus.SRIQD.splitCell_ok.2 hS (le_refl _) _

/-- **Exactness of the consistency route**, at the OWL 2 datatype map, for
every reading of `xsd:pattern` and every hint. -/
theorem owlSHIQDKBConsistent_sound (pat : String → String → Prop) {O : OWL.Ontology}
    {hint : Option RawHint} {v : Bool} (h : owlSHIQDKBConsistent O hint = some v) :
    v = true ↔ ConsistentAt (owl2MapP pat) O := by
  unfold owlSHIQDKBConsistent at h
  split at h
  · cases h
  next T hT =>
    split at h
    · next hok =>
      simp only [Option.some.injEq] at h
      subst h
      rw [kbdConsistent_iff pat hok, ← translateSRIQDKB_consistent pat hT]
      rfl
    · cases h

/-- The checks of the knowledge-base route on the translation. -/
def SHIQDKBChecks (O : OWL.Ontology) : Prop :=
  ∀ T, translateSRIQDKB O [] [] = some T → kbdOK T = true

/-- **When the consistency route answers.** Exactly on the SHIQ(D)
knowledge-base part with the checks passed, for every hint. -/
theorem owlSHIQDKBConsistent_isSome_iff (O : OWL.Ontology) (hint : Option RawHint) :
    (owlSHIQDKBConsistent O hint).isSome = true ↔ O.isSHIQDKB = true ∧ SHIQDKBChecks O := by
  constructor
  · intro h
    unfold owlSHIQDKBConsistent at h
    split at h
    · simp at h
    · next T hT =>
      split at h
      · next hok =>
        refine ⟨translateSRIQDKB_isSHIQDKB hT, fun T' hT' => ?_⟩
        rw [hT] at hT'
        cases hT'
        exact hok
      · simp at h
  · rintro ⟨hO, hc⟩
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 (translateSRIQDKB_isSome [] [] hO)
    unfold owlSHIQDKBConsistent
    rw [hT]
    dsimp only
    rw [if_pos (hc T hT)]
    rfl

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.translateSRIQDKB_isSome
#print axioms ContextCalculus.OWLFrontend.owlSHIQDKBConsistent_sound
#print axioms ContextCalculus.OWLFrontend.owlSHIQDKBConsistent_isSome_iff
