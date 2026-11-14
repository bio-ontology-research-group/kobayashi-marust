import ContextCalculus.OWLFrontend.SRIQTranslateCorrect

/-!
# The SHIQ translation at the level of models (v1.7.0 stage C4, part D)

`translateSRIQ_correct` relates entailments. The SHIQ(D) route adds data
clauses on some requested names, so it needs the two model maps behind
that theorem (`translateSRIQ_models`):

* a model of the translated clauses gives an OWL model of the ontology
  with the same extension for every requested IRI;
* an OWL model of the ontology (for any datatype map) gives a model of the
  translated clauses with the same extension for every requested IRI.

The proof is the one of `SRIQT.correct_core`, with the models kept.
-/

namespace ContextCalculus.OWLFrontend.SRIQT

open ContextCalculus.OWL
open SRIT (lower raise lower_raise)

/-- The model maps on the states of the pipeline. -/
theorem models_core (O : Ontology) (hSRI : O.isSHIQ = true) (b : EL.St) (F : St)
    (L : List IRI) (hb : EL.WF (EL.setTopBottom b))
    (hidxS : ∀ (i : Nat) (h : i < L.length), b.cmap[L[i]]? = some i)
    (hF : O.axioms.foldl transAxiom (start b) = F) :
    (∀ (D : Type) [Nonempty D] (J : SRI.Interp D (Fin F.b.cdefs.size) (Fin F.b.rdefs.size)),
      SRIQ.models J (F.out.reverse.filterMap (toFin F.b.cdefs.size F.b.rdefs.size)) →
      ∃ R : OWL.Interp OWL.DatatypeMap.trivial D, OWL.Model O R ∧
        ∀ (i : Nat) (hi : i < L.length) (hi' : i < F.b.cdefs.size) x,
          R.cls L[i] x ↔ J.c ⟨i, hi'⟩ x) ∧
    (∀ (DM : OWL.DatatypeMap) (D : Type) (I : OWL.Interp DM D), OWL.Model O I →
      ∃ J : SRI.Interp D (Fin F.b.cdefs.size) (Fin F.b.rdefs.size),
        SRIQ.models J (F.out.reverse.filterMap (toFin F.b.cdefs.size F.b.rdefs.size)) ∧
        ∀ (i : Nat) (hi : i < L.length) (hi' : i < F.b.cdefs.size) x,
          J.c ⟨i, hi'⟩ x ↔ I.cls L[i] x) := by
  have hS := start_wf hb
  have hLe : Le (start b) F := hF ▸ foldl_trans_le O.axioms (start b)
  have hFwf : WF F := hF ▸ foldl_trans_wf O.axioms (start b) hS
  have hA : ∀ ax ∈ O.axioms, ax.isSHIQ = true := by
    simpa [Ontology.isSHIQ, List.all_eq_true] using hSRI
  have hidx : ∀ k (hk : k < L.length), F.b.cmap[L[k]]? = some k := fun k hk =>
    hLe.b.cmap _ _ (hidxS k hk)
  constructor
  · intro D _ J hJ
    let K := raise F.b.cdefs.size F.b.rdefs.size J
    have hK : ∀ c ∈ F.out, SRIQ.satClause K c := (fin_models hFwf).2 J hJ
    have hT : ∀ x, K.c F.b.top x := by
      intro y
      obtain ⟨b', hb', hy⟩ := hK _ (hLe.out _ (start_top_mem b)) y (by simp)
      simp only [List.mem_singleton] at hb'
      rw [hb', ← hLe.b.top] at hy; exact hy
    have hB : ∀ x, ¬ K.c F.b.bottom x := by
      intro y hy
      obtain ⟨b', hb', _⟩ := hK _ (hLe.out _ (start_bottom_mem b)) y (by
        intro k hk; simp only [List.mem_singleton] at hk; rw [hk, ← hLe.b.bottom]
        exact hy)
      simp at hb'
    refine ⟨restrict F K, fun ax hax => ?_, fun i hi hi' x => ?_⟩
    · obtain ⟨s', _, hle⟩ := foldl_trans_mem O.axioms (start b) hS ax hax
      exact transAxiom_restrict F K hK hT hB s' ax (hF ▸ hle) (hA ax hax)
    · rw [restrict_cls (hidx i hi)]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hi', h⟩⟩
  · intro DM D I hI
    have hgood : Good I F F := by
      have := foldl_trans_good I F O.axioms (start b) hS (hF ▸ Le.rfl)
        (fun ax hax => ⟨hA ax hax, hI ax hax⟩) (by
          intro c hc
          simp only [start, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · intro y hy
            exact absurd (hy _ (by simp [start])) (extend_bottom I F hS hLe y)
          · intro y _
            exact ⟨_, by simp [start], extend_top I F hS hLe y⟩)
      rwa [hF] at this
    refine ⟨lower _ _ (extend I F), (fin_models hFwf).1 _ hgood, fun i hi hi' x => ?_⟩
    show (extend I F).c i x ↔ _
    rw [extend_c I F (hFwf.b.cmap _ _ (hidx i hi)), EL.ext_cls]

end ContextCalculus.OWLFrontend.SRIQT

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL SRIQT

theorem translateSRIQ_isSHIQ {O : OWL.Ontology} {requested : List OWL.IRI} {T : SRIQTranslation}
    (h : translateSRIQ O requested = some T) : O.isSHIQ = true := by
  simp only [translateSRIQ] at h
  split at h
  · assumption
  · exact absurd h (by simp)

/-- **The model maps of the SHIQ translation.** -/
theorem translateSRIQ_models {O : OWL.Ontology} {requested : List OWL.IRI} {T : SRIQTranslation}
    (h : translateSRIQ O requested = some T) :
    (∀ (D : Type) [Nonempty D] (J : SRI.Interp D (Fin T.conceptCount) (Fin T.roleCount)),
      SRIQ.models J T.ontology →
      ∃ R : OWL.Interp OWL.DatatypeMap.trivial D, OWL.Model O R ∧
        ∀ (i : Nat) (hi : i < T.named.length) x,
          R.cls T.named[i] x ↔ J.c ⟨i, Nat.lt_of_lt_of_le hi T.hnamed⟩ x) ∧
    (∀ (DM : OWL.DatatypeMap) (D : Type) (I : OWL.Interp DM D), OWL.Model O I →
      ∃ J : SRI.Interp D (Fin T.conceptCount) (Fin T.roleCount), SRIQ.models J T.ontology ∧
        ∀ (i : Nat) (hi : i < T.named.length) x,
          J.c ⟨i, Nat.lt_of_lt_of_le hi T.hnamed⟩ x ↔ I.cls T.named[i] x) := by
  simp only [translateSRIQ] at h
  split at h
  case isFalse => exact absurd h (by simp)
  rename_i hSRI
  split at h
  case isFalse => exact absurd h (by simp)
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨b, hb, _, hidx, hF⟩ := SRIQT.run_spec O requested
  obtain ⟨h1, h2⟩ := models_core O hSRI b _ _ hb hidx hF
  exact ⟨fun D _ J hJ => h1 D J hJ |>.imp fun R hR => ⟨hR.1, fun i hi x => hR.2 i hi _ x⟩,
    fun DM D I hI => h2 DM D I hI |>.imp fun J hJ => ⟨hJ.1, fun i hi x => hJ.2 i hi _ x⟩⟩

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.translateSRIQ_models
