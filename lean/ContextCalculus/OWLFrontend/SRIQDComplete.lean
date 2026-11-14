import ContextCalculus.OWLFrontend.SRIQDReference
import ContextCalculus.OWLFrontend.SRIQComplete

/-!
# When the SHIQ(D) route publishes (v1.7.0 stage C4, part D)

`translateSRIQD_isSome`: the translation succeeds on the SHIQ(D) part.
`owlSHIQDReference_isSome_iff`: the route publishes exactly on the SHIQ(D)
part when the translated object part passes the simple-role check
(`isSHIQB`) and the data atoms are in the supported sub-language
(`allSupported`).
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD

theorem objOnt_isSHIQ {O : Ontology} (hO : O.isSHIQD = true) (base : String) :
    (objOnt O base).isSHIQ = true := by
  have hO' : ∀ ax ∈ O.axioms, ax.isSHIQD = true := by
    simpa [Ontology.isSHIQD, List.all_eq_true] using hO
  simp only [Ontology.isSHIQ, List.all_eq_true]
  intro ax hax
  obtain ⟨ax', hax', rfl⟩ := List.mem_map.1 hax
  obtain ⟨ax0, h0, hax'0⟩ := List.mem_flatMap.1 hax'
  have hrw := rw_isSHIQD (hO' ax0 h0) hax'0
  exact isSHIQ_absAx _ hrw.1 hrw.2

theorem nameIx_isSome {T : SRIQTranslation} {a : IRI} (ha : a ∈ T.named) :
    (nameIx T a).isSome = true := by
  unfold nameIx
  rw [dif_pos (List.idxOf_lt_length_of_mem ha)]
  rfl

theorem dpIx_isSome {dps : List IRI} {p : IRI} (hp : p ∈ dps) : (dpIx dps p).isSome = true := by
  unfold dpIx
  rw [dif_pos (List.idxOf_lt_length_of_mem hp)]
  rfl

/-- The translation succeeds on the SHIQ(D) part. -/
theorem translateSRIQD_isSome {O : Ontology} (requested : List IRI) (hO : O.isSHIQD = true) :
    (translateSRIQD O requested).isSome = true := by
  have hT := translateSRIQ_isSome (requested := requested ++
    freshNames (SRIQKB.defBase O requested) (table O)) (objOnt_isSHIQ hO (SRIQKB.defBase O requested))
  obtain ⟨Tobj, hTobj⟩ := Option.isSome_iff_exists.1 hT
  have hTn := translateSRIQ_named hTobj
  have hfr : ∀ e ∈ table O, fName (SRIQKB.defBase O requested) (table O) e ∈ Tobj.named ∧
      wName (SRIQKB.defBase O requested) (table O) e ∈ Tobj.named := by
    intro e he
    rw [hTn]
    constructor <;> refine List.mem_eraseDups.2 (List.mem_append_right _ ?_) <;>
      exact List.mem_flatMap.2 ⟨e, he, by simp⟩
  have hp : ∀ e ∈ table O, e.p ∈ dprops O := fun e he =>
    List.mem_dedup.2 (List.mem_append_left _ (List.mem_map_of_mem he))
  have hsp : ∀ pq ∈ O.axioms.flatMap subPairs, pq.1 ∈ dprops O ∧ pq.2 ∈ dprops O := fun pq hpq =>
    ⟨List.mem_dedup.2 (List.mem_append_right _ (List.mem_flatMap.2 ⟨pq, hpq, by simp⟩)),
      List.mem_dedup.2 (List.mem_append_right _ (List.mem_flatMap.2 ⟨pq, hpq, by simp⟩))⟩
  unfold translateSRIQD
  rw [if_pos hO]
  dsimp only
  rw [hTobj]
  dsimp only
  have hdc := SRIQKB.collect_isSome
      (f := dataClauseOf Tobj (SRIQKB.defBase O requested) (table O) (dprops O))
      (xs := (table O).zipIdx) (by
    rintro ⟨e, k⟩ hek
    have hk := List.mem_zipIdx_iff_getElem?.1 hek
    have he : e ∈ table O := List.mem_of_getElem? hk
    have hk' : k < (table O).length := (List.getElem?_eq_some_iff.1 hk).1
    obtain ⟨F, hF⟩ := Option.isSome_iff_exists.1 (nameIx_isSome (T := Tobj) (hfr e he).1)
    obtain ⟨W, hW⟩ := Option.isSome_iff_exists.1 (nameIx_isSome (T := Tobj) (hfr e he).2)
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (dpIx_isSome (hp e he))
    unfold dataClauseOf
    simp only [hF, hW, hu, dif_pos hk']
    rfl)
  have hsc := SRIQKB.collect_isSome (f := subClauseOf Tobj (dprops O) (table O))
      (xs := O.axioms.flatMap subPairs) (by
    intro pq hpq
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (dpIx_isSome (hsp pq hpq).1)
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (dpIx_isSome (hsp pq hpq).2)
    unfold subClauseOf
    simp only [hu, hw]
    rfl)
  obtain ⟨dc, hdc⟩ := Option.isSome_iff_exists.1 hdc
  obtain ⟨sc, hsc⟩ := Option.isSome_iff_exists.1 hsc
  rw [hdc, hsc]
  rfl

theorem translateSRIQD_isSHIQD {O : Ontology} {requested : List IRI} {T : SRIQDTranslation}
    (h : translateSRIQD O requested = some T) : O.isSHIQD = true := by
  unfold translateSRIQD at h
  split_ifs at h with hO
  exact hO

theorem translateSRIQD_named_le {O : Ontology} {requested : List IRI} {T : SRIQDTranslation}
    (h : translateSRIQD O requested = some T) : T.named.length ≤ T.obj.conceptCount := by
  unfold translateSRIQD at h
  split_ifs at h with hO
  dsimp only at h
  split at h
  · cases h
  rename_i Tobj hTobj
  split at h
  · cases h
    have hTn := translateSRIQ_named hTobj
    have : (requested ++ freshNames (SRIQKB.defBase O requested) (table O)).eraseDups =
        requested.eraseDups ++ _ := List.eraseDups_append
    have hle : requested.eraseDups.length ≤ Tobj.named.length := by
      rw [hTn, this, List.length_append]; omega
    exact hle.trans Tobj.hnamed
  · cases h

/-- The checks of the SHIQ(D) route on the translation. -/
def SHIQDChecks (O : OWL.Ontology) (requested : List OWL.IRI) : Prop :=
  ∀ T, translateSRIQD O requested = some T →
    isSHIQB (ContextCalculus.SRIQD.objPart T.ontology) = true ∧ allSupported T = true

/-- **When the SHIQ(D) route publishes.** Exactly on the SHIQ(D) part with
the checks passed. -/
theorem owlSHIQDReference_isSome_iff {O : OWL.Ontology} (requested : List OWL.IRI) :
    (owlSHIQDReference O requested).isSome = true ↔
      O.isSHIQD = true ∧ SHIQDChecks O requested := by
  constructor
  · intro h
    unfold owlSHIQDReference at h
    split at h
    · simp at h
    · next T hT =>
      split at h
      · next hc =>
        refine ⟨translateSRIQD_isSHIQD hT, fun T' hT' => ?_⟩
        rw [hT] at hT'
        cases hT'
        rw [Bool.and_eq_true] at hc
        exact hc.1
      · simp at h
  · rintro ⟨hO, hc⟩
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 (translateSRIQD_isSome requested hO)
    unfold owlSHIQDReference
    rw [hT]
    dsimp only
    obtain ⟨h1, h2⟩ := hc T hT
    rw [dif_pos ⟨by rw [h1, h2]; rfl, translateSRIQD_named_le hT⟩]
    rfl

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.translateSRIQD_isSome
#print axioms ContextCalculus.OWLFrontend.owlSHIQDReference_isSome_iff
