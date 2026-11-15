import ContextCalculus.OWLFrontend.SRIQDKBLemmas
import ContextCalculus.OWLFrontend.SRIQDCorrect

/-!
# Correctness of the SHIQ(D) knowledge-base translation (v1.7.0 stage C4)

`translateSRIQDKB_consistent`: an ontology of the SHIQ(D) knowledge-base
part has a model at the OWL 2 datatype map `owl2MapP pat` iff the
translated `SRIQD` knowledge base is consistent over the data theory of
the map, for every reading `pat` of `xsd:pattern`. The proof is the one of
`translateSRIQD_correct`, with the knowledge-base model maps
`translateSRIQKB_up` and `translateSRIQKB_down` in place of
`translateSRIQ_models`.
-/

namespace ContextCalculus.OWLFrontend.SHIQD

open ContextCalculus.OWL

theorem mem_tableK {O : Ontology} {e : DExpr} :
    e ∈ tableK O ↔ ∃ ax ∈ rwAxiomsK O, e ∈ axDexprsK ax := by
  simp [tableK, List.mem_dedup, List.mem_flatMap]

theorem tableK_kind2 {O : Ontology} {e : DExpr} (he : e ∈ tableK O) : e.kind = 2 → 1 ≤ e.n := by
  obtain ⟨ax, -, he⟩ := mem_tableK.1 he
  cases ax <;> simp only [axDexprsK, axDexprs, List.mem_append, List.mem_flatMap,
    List.not_mem_nil] at he
  all_goals first
    | (rcases he with he | he <;> exact dexprs_kind2 _ e he)
    | (obtain ⟨c, -, he⟩ := he; exact dexprs_kind2 _ e he)
    | exact dexprs_kind2 _ e he

theorem rwOK_isSHIQDKB {ax : Axiom} (h : RwOK ax) : ax.isSHIQDKB = true := by
  rcases h with ⟨h1, -⟩ | ⟨c, a, rfl, hc, ha⟩ | ⟨h1, h2, h3⟩
  · cases ax <;> simp_all [Axiom.isSHIQDKB, Axiom.isSHIQD, Axiom.isSHI, Axiom.isSRI]
  · simp [Axiom.isSHIQDKB, hc, ha]
  · cases ax <;> simp_all [Axiom.isSHIQDKB, Axiom.isSHIQKB, Axiom.isAssertion]

end ContextCalculus.OWLFrontend.SHIQD

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD

/-- **The model maps of the SHIQ(D) knowledge-base translation**, with each
requested IRI standing for its index, and (stage H5) the data of the model
built from a data model: its data properties read through the value
bijection `eqv` of the theory, its atoms the data ranges of the table. -/
theorem translateSRIQDKB_mapsRD (pat : String → String → Prop) {O : Ontology}
    {requested extra : List IRI} {T : SRIQDKBTranslation}
    (h : translateSRIQDKB O requested extra = some T) :
    (∀ (Dom : Type) [Nonempty Dom] (I : Interp (owl2MapP pat) Dom), OWL.Model O I →
      ∃ (V : Type) (atom : Fin T.tab.length → V → Prop), owlTheory pat (spec T.tab) V atom ∧
        ∃ (K : ContextCalculus.SRIQD.DInterp Dom V (Fin T.obj.conceptCount) (Fin T.obj.roleCount)
            (Fin T.dps.length)) (ind : Fin T.obj.inds.length → Dom),
          ContextCalculus.SRIQD.models atom K T.ontology ∧
          ContextCalculus.SRIQD.satABox atom K ind T.abox ∧
          (∀ (i : Nat) (hi : i < T.obj.named.length), T.obj.named[i] ∈ requested → ∀ y,
            K.c ⟨i, Nat.lt_of_lt_of_le hi T.obj.hnamed⟩ y ↔ I.cls T.obj.named[i] y) ∧
          ∀ (r : ObjProp), r.isBasic = true → ∀ k, (EL.propIRI r, k) ∈ T.obj.rnames →
            ∀ R, SRIT.finRT T.obj.roleCount (SRIT.mkRT r k) = some R →
            ∀ x y, K.rt R x y ↔ I.prop r x y) ∧
    (∀ (Dom V : Type) [Nonempty Dom] (atom : Fin T.tab.length → V → Prop),
      owlTheory pat (spec T.tab) V atom →
      ∀ (K : ContextCalculus.SRIQD.DInterp Dom V (Fin T.obj.conceptCount) (Fin T.obj.roleCount)
          (Fin T.dps.length)) (ind : Fin T.obj.inds.length → Dom),
        ContextCalculus.SRIQD.models atom K T.ontology →
        ContextCalculus.SRIQD.satABox atom K ind T.abox →
        ∃ I : Interp (owl2MapP pat) Dom, OWL.Model O I ∧
          (∀ (i : Nat) (hi : i < T.obj.named.length), T.obj.named[i] ∈ requested → ∀ y,
            I.cls T.obj.named[i] y ↔ K.c ⟨i, Nat.lt_of_lt_of_le hi T.obj.hnamed⟩ y) ∧
          (∀ (r : ObjProp), r.isBasic = true → ∀ k, (EL.propIRI r, k) ∈ T.obj.rnames →
            ∀ R, SRIT.finRT T.obj.roleCount (SRIT.mkRT r k) = some R →
            ∀ x y, I.prop r x y ↔ K.rt R x y) ∧
          ∃ eqv : V ≃ Val, (∀ j v, atom j v ↔ (spec T.tab j).ext (owl2MapP pat) I.dtype (eqv v)) ∧
            ∀ (name : IRI) (y : Dom) (w : Val), I.dprop name y w ↔
              ∃ u : Fin T.dps.length, T.dps[u] = name ∧ K.d u y (eqv.symm w)) := by
  classical
  unfold translateSRIQDKB at h
  split_ifs at h with hO
  dsimp only at h
  split at h
  · cases h
  rename_i Tobj hTobj
  split at h
  swap
  · cases h
  rename_i _ _ dc sc hdc hsc
  cases h
  have hnamed_of_ix : ∀ a (F : Fin Tobj.conceptCount), nameIxK Tobj a = some F →
      ∃ hF : F.val < Tobj.named.length, Tobj.named[F.val] = a := by
    intro a F hF
    unfold nameIxK at hF
    split_ifs at hF with hlt
    cases hF
    exact ⟨hlt, List.getElem_idxOf hlt⟩
  have hdp_of_ix : ∀ p (u : Fin (dpropsK O).length), dpIx (dpropsK O) p = some u → (dpropsK O)[u] = p := by
    intro p u hu
    unfold dpIx at hu
    split_ifs at hu with hlt
    cases hu
    exact List.getElem_idxOf hlt
  have hdps_nd : (dpropsK O).Nodup := List.nodup_dedup _
  -- the data clauses
  have hdc_mem : ∀ cl ∈ dc, ∃ e ∈ (tableK O), ∃ (F W : Fin Tobj.conceptCount) (u : Fin (dpropsK O).length)
      (jj : Fin (tableK O).length), (tableK O)[jj] = e ∧ nameIxK Tobj (fName (SRIQKB.defBase O requested) (tableK O) e) = some F ∧
      nameIxK Tobj (wName (SRIQKB.defBase O requested) (tableK O) e) = some W ∧ dpIx (dpropsK O) e.p = some u ∧
      cl ∈ entryClauses (m := Tobj.roleCount) e F W u jj := by
    intro cl hcl
    obtain ⟨⟨e, k⟩, hek, l, hf, hcl⟩ := SRIQKB.collect_mem hdc cl hcl
    have hk := List.mem_zipIdx_iff_getElem?.1 hek
    simp only at hk
    unfold dataClauseOfK at hf
    split at hf
    · rename_i F W u hF hW hu
      split_ifs at hf with hk'
      cases hf
      refine ⟨e, ?_, F, W, u, ⟨k, hk'⟩, ?_, hF, hW, hu, hcl⟩
      · exact List.mem_of_getElem? hk
      · simpa [hk'] using hk
    · cases hf
  have hdc_all : ∀ e ∈ (tableK O), ∃ (F W : Fin Tobj.conceptCount) (u : Fin (dpropsK O).length)
      (jj : Fin (tableK O).length), (tableK O)[jj] = e ∧ nameIxK Tobj (fName (SRIQKB.defBase O requested) (tableK O) e) = some F ∧
      nameIxK Tobj (wName (SRIQKB.defBase O requested) (tableK O) e) = some W ∧ dpIx (dpropsK O) e.p = some u ∧
      ∀ cl ∈ entryClauses (m := Tobj.roleCount) e F W u jj, cl ∈ dc := by
    intro e he
    have hek : (e, (tableK O).idxOf e) ∈ (tableK O).zipIdx := List.mem_zipIdx_iff_getElem?.2 (by
      rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem he), List.getElem_idxOf])
    obtain ⟨l, hf, hl⟩ := SRIQKB.collect_some hdc _ hek
    unfold dataClauseOfK at hf
    split at hf
    · rename_i F W u hF hW hu
      split_ifs at hf with hk'
      cases hf
      exact ⟨F, W, u, ⟨_, hk'⟩, List.getElem_idxOf hk', hF, hW, hu, hl⟩
    · cases hf
  -- the sub-property clauses
  have hsc_mem : ∀ cl ∈ sc, ∃ pq ∈ O.axioms.flatMap subPairs, ∃ (u w : Fin (dpropsK O).length),
      (dpropsK O)[u] = pq.1 ∧ (dpropsK O)[w] = pq.2 ∧ cl = .dSub u w := by
    intro cl hcl
    obtain ⟨pq, hpq, l, hf, hcl⟩ := SRIQKB.collect_mem hsc cl hcl
    unfold subClauseOfK at hf
    split at hf
    · rename_i u w hu hw
      cases hf
      rw [List.mem_singleton] at hcl
      exact ⟨pq, hpq, u, w, hdp_of_ix _ _ hu, hdp_of_ix _ _ hw, hcl⟩
    · cases hf
  have hsc_all : ∀ pq ∈ O.axioms.flatMap subPairs, ∃ (u w : Fin (dpropsK O).length),
      (dpropsK O)[u] = pq.1 ∧ (dpropsK O)[w] = pq.2 ∧ ContextCalculus.SRIQD.Clause.dSub u w ∈ sc := by
    intro pq hpq
    obtain ⟨l, hf, hl⟩ := SRIQKB.collect_some hsc pq hpq
    unfold subClauseOfK at hf
    split at hf
    · rename_i u w hu hw
      cases hf
      exact ⟨u, w, hdp_of_ix _ _ hu, hdp_of_ix _ _ hw, hl _ (List.mem_singleton_self _)⟩
    · cases hf
  -- the object part
  have hobj_sub : ∀ c ∈ Tobj.ontology, c ∈ ContextCalculus.SRIQD.objPart
      (Tobj.ontology.map ContextCalculus.SRIQD.Clause.obj ++ dc ++ sc) := fun c hc =>
    ContextCalculus.SRIQD.mem_objPart.2
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hc)))
  have hobj_dc : ∀ c, ContextCalculus.SRIQD.Clause.obj c ∈ dc → c ∈ ContextCalculus.SRIQD.objPart
      (Tobj.ontology.map ContextCalculus.SRIQD.Clause.obj ++ dc ++ sc) := fun c hc =>
    ContextCalculus.SRIQD.mem_objPart.2 (List.mem_append_left _ (List.mem_append_right _ hc))
  have hobj_char : ∀ c ∈ ContextCalculus.SRIQD.objPart
      (Tobj.ontology.map ContextCalculus.SRIQD.Clause.obj ++ dc ++ sc),
      c ∈ Tobj.ontology ∨ ∃ e ∈ tableK O, ∃ F W : Fin Tobj.conceptCount,
        nameIxK Tobj (fName (SRIQKB.defBase O requested) (tableK O) e) = some F ∧
        nameIxK Tobj (wName (SRIQKB.defBase O requested) (tableK O) e) = some W ∧ c = .gci [] [F, W] := by
    intro c hc
    rcases List.mem_append.1 (ContextCalculus.SRIQD.mem_objPart.1 hc) with h | h
    · rcases List.mem_append.1 h with h | h
      · obtain ⟨c', hc', he⟩ := List.mem_map.1 h
        cases he
        exact Or.inl hc'
      · obtain ⟨e, he, F, W, u, jj, -, hF, hW, -, hcl⟩ := hdc_mem _ h
        right
        refine ⟨e, he, F, W, hF, hW, ?_⟩
        unfold entryClauses at hcl
        rcases List.mem_cons.1 hcl with he' | hcl
        · cases he'; rfl
        · split at hcl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl <;>
            rcases hcl with he' | he' <;> cases he'
    · obtain ⟨-, -, u, w, -, -, he⟩ := hsc_mem _ h
      cases he
  have hmem_rw : ∀ ax0 ∈ O.axioms, ∀ ax ∈ rwAxiomK ax0,
      absAxK (fName (SRIQKB.defBase O requested) (tableK O)) ax ∈
        (objOntK O (SRIQKB.defBase O requested)).axioms := fun ax0 h0 ax hax =>
    List.mem_map_of_mem (List.mem_flatMap.2 ⟨ax0, h0, hax⟩)
  have hdex_tab : ∀ ax0 ∈ O.axioms, ∀ ax ∈ rwAxiomK ax0, ∀ e ∈ axDexprsK ax, e ∈ tableK O :=
    fun ax0 h0 ax hax e he => mem_tableK.2 ⟨ax, List.mem_flatMap.2 ⟨ax0, h0, hax⟩, he⟩
  have hfresh_ax : ∀ ax ∈ O.axioms, ∀ a ∈ ax.classNames, ∀ n,
      a ≠ SRIQKB.defName (SRIQKB.defBase O requested) n :=
    fun ax hax a ha n => SRIQKB.fresh_ax hax ha n
  have hobjKB : ∀ ax ∈ (objOntK O (SRIQKB.defBase O requested)).axioms, ax.isSHIQKB = true := by
    have := (translateSRIQKB_spec hTobj).1
    simpa [Ontology.isSHIQKB, List.all_eq_true] using this
  have hO' : ∀ ax ∈ O.axioms, ax.isSHIQDKB = true := by
    simpa [Ontology.isSHIQDKB, List.all_eq_true] using hO
  have hNsw : ∀ {DM : DatatypeMap} {Dom : Type} (I : Interp DM Dom) {ax : Axiom},
      ax.isSHIQDKB = true → ∀ N N' : List IRI, I.sat N ax ↔ I.sat N' ax := by
    intro DM Dom I ax hax N N'
    exact sat_congr_clsK rfl rfl rfl rfl hax (fun _ _ => rfl) N N'
  refine ⟨?_, ?_⟩
  · intro Dom hD I hI
    let isF : IRI → Prop := fun a => ∃ e ∈ tableK O, fName (SRIQKB.defBase O requested) (tableK O) e = a
    let isW : IRI → Prop := fun a => ∃ e ∈ tableK O, wName (SRIQKB.defBase O requested) (tableK O) e = a
    let I' : Interp (owl2MapP pat) Dom :=
      { cls := fun a y => if isF a then ∃ e ∈ tableK O, fName (SRIQKB.defBase O requested) (tableK O) e = a ∧ I.ext e.toCE y
          else if isW a then ∃ e ∈ tableK O, wName (SRIQKB.defBase O requested) (tableK O) e = a ∧ ¬ I.ext e.toCE y
          else I.cls a y,
        role := I.role, ind := I.ind, dprop := I.dprop, dtype := I.dtype }
    have hI'ext : ∀ e : DExpr, I'.ext e.toCE = I.ext e.toCE := fun e =>
      ext_congr_cls (I := I') (J := I) rfl rfl rfl e.toCE (toCE_isALCIQD e) (by simp [toCE_names])
    have hI'F : ∀ e ∈ tableK O, ∀ y, I'.cls (fName (SRIQKB.defBase O requested) (tableK O) e) y ↔ I.ext e.toCE y := by
      intro e he y
      show (if isF _ then _ else _) ↔ _
      rw [if_pos ⟨e, he, rfl⟩]
      constructor
      · rintro ⟨e', he', hn, h⟩
        rw [fName_inj he' he hn] at h
        exact h
      · intro h; exact ⟨e, he, rfl, h⟩
    have hI'W : ∀ e ∈ tableK O, ∀ y, I'.cls (wName (SRIQKB.defBase O requested) (tableK O) e) y ↔ ¬ I.ext e.toCE y := by
      intro e he y
      show (if isF _ then _ else _) ↔ _
      rw [if_neg (fun ⟨e', _, hn⟩ => fName_ne_wName e' e hn), if_pos ⟨e, he, rfl⟩]
      constructor
      · rintro ⟨e', he', hn, h⟩
        rw [wName_inj he' he hn] at h
        exact h
      · intro h; exact ⟨e, he, rfl, h⟩
    have hI'old : ∀ a, (∀ n, a ≠ SRIQKB.defName (SRIQKB.defBase O requested) n) → I'.cls a = I.cls a := by
      intro a ha
      funext y
      show (if isF a then _ else _) = _
      rw [if_neg (fun ⟨e, _, hn⟩ => ha _ hn.symm), if_neg (fun ⟨e, _, hn⟩ => ha _ hn.symm)]
    have hI'O : OWL.Model O I' := fun ax hax =>
      (sat_congr_clsK (I := I) (J := I') rfl rfl rfl rfl (hO' ax hax)
        (fun a ha => (hI'old a (hfresh_ax ax hax a ha)).symm) _ _).1 (hI ax hax)
    have hI'obj : OWL.Model (objOntK O (SRIQKB.defBase O requested)) I' := by
      intro ax hax
      obtain ⟨ax', hax', rfl⟩ := List.mem_map.1 hax
      obtain ⟨ax0, h0, hax'0⟩ := List.mem_flatMap.1 hax'
      have hrw := rwK_ok (hO' ax0 h0) hax'0
      refine (sat_absAxK hrw (fun e he y => ?_) _).2 ?_
      · rw [hI'F e (hdex_tab ax0 h0 ax' hax'0 e he) y, hI'ext]
      · exact (hNsw I' (rwOK_isSHIQDKB hrw) _ _).1
          (((sat_rwAxiomK I' (hO' ax0 h0) _).1 (hI'O ax0 h0)).1 ax' hax'0)
    obtain ⟨J, hJ, hA, hJc, hJr⟩ := translateSRIQKB_upR hTobj I' hI'obj
    let K : ContextCalculus.SRIQD.DInterp Dom Val (Fin Tobj.conceptCount) (Fin Tobj.roleCount)
        (Fin (dpropsK O).length) :=
      { toInterp := J, d := fun u y v => I.dprop (dpropsK O)[u] y v }
    let atom : Fin (tableK O).length → Val → Prop := fun p v =>
      (spec (tableK O) p).ext (owl2MapP pat) I.dtype v
    have hΘ : owlTheory pat (spec (tableK O)) Val atom := ⟨Equiv.refl _, I.dtype, fun _ _ => Iff.rfl⟩
    have hKc : ∀ (F : Fin Tobj.conceptCount) (hF : F.val < Tobj.named.length) y,
        K.c F y ↔ I'.cls Tobj.named[F.val] y := fun F hF y => hJc F.val hF y
    have hK : ContextCalculus.SRIQD.models atom K
        (Tobj.ontology.map ContextCalculus.SRIQD.Clause.obj ++ dc ++ sc) := by
      refine ContextCalculus.SRIQD.models_iff.2 ⟨fun c hc => ?_, fun cl hcl y => ?_⟩
      · rcases hobj_char c hc with h | ⟨e, he, F, W, hF, hW, rfl⟩
        · exact hJ c h
        · intro y _
          obtain ⟨hFl, hFn⟩ := hnamed_of_ix _ F hF
          obtain ⟨hWl, hWn⟩ := hnamed_of_ix _ W hW
          by_cases hy : I.ext e.toCE y
          · refine ⟨F, List.mem_cons_self, (hKc F hFl y).2 ?_⟩
            rw [hFn]; exact (hI'F e he y).2 hy
          · refine ⟨W, List.mem_cons_of_mem _ List.mem_cons_self, (hKc W hWl y).2 ?_⟩
            rw [hWn]; exact (hI'W e he y).2 hy
      rcases List.mem_append.1 hcl with hcl | hcl
      · rcases List.mem_append.1 hcl with hcl | hcl
        · obtain ⟨c, -, rfl⟩ := List.mem_map.1 hcl
          trivial
        · obtain ⟨e, he, F, W, u, jj, hjj, hF, hW, hu, hcl'⟩ := hdc_mem cl hcl
          obtain ⟨hFl, hFn⟩ := hnamed_of_ix _ F hF
          obtain ⟨hWl, hWn⟩ := hnamed_of_ix _ W hW
          have hpos : posK e (K.d u y) (atom jj) ↔ I.ext e.toCE y := by
            refine posK_iff_ext I e y (Equiv.refl _) _ _ (fun v => ?_) (fun v => ?_)
            · show I.dprop (dpropsK O)[u] y v ↔ _
              rw [hdp_of_ix _ _ hu]; rfl
            · show (spec (tableK O) jj).ext (owl2MapP pat) I.dtype v ↔ e.R.ext (owl2MapP pat) I.dtype v
              simp only [spec, hjj]
          have hneg := negK_iff_not e (tableK_kind2 he) (K.d u y) (atom jj)
          have hall := (entryClauses_dLocal (m := Tobj.roleCount) atom (fun a => K.c a y)
            (fun u => K.d u y) e F W u jj).2 ⟨fun hc => ?_, fun hc => ?_⟩
          · exact hall cl hcl'
          · have := (hKc F hFl y).1 hc
            rw [hFn, hI'F e he y] at this
            exact hpos.2 this
          · have := (hKc W hWl y).1 hc
            rw [hWn, hI'W e he y] at this
            exact hneg.2 (fun h => this (hpos.1 h))
      · obtain ⟨pq, hpq, u, w, hu, hw, rfl⟩ := hsc_mem cl hcl
        obtain ⟨ax0, h0, hpq0⟩ := List.mem_flatMap.1 hpq
        intro v hv
        have := ((sat_rwAxiomK I (hO' ax0 h0) _).1 (hI ax0 h0)).2 pq hpq0 y v
        show I.dprop (dpropsK O)[w] y v
        rw [hw]
        exact this (by rw [← hu]; exact hv)
    refine ⟨Val, atom, hΘ, K, _, hK, ContextCalculus.SRIQD.satABox_map_obj.2 hA,
      fun i hi hreq y => (hKc ⟨i, _⟩ hi y).trans ?_, fun r hr k hk R hfin x y => ?_⟩
    · rw [hI'old _ fun n => SRIQKB.fresh_req hreq n]
    · exact (hJr r hr k hk R hfin x y).trans
        (Iff.of_eq (congrFun (congrFun (Interp.prop_congr (I := I') (J := I) rfl r) x) y))
  · intro Dom V hD atom hΘ K ind hK hA
    obtain ⟨eqv, dtype, hatom⟩ := hΘ
    have hKm := ContextCalculus.SRIQD.models_iff.1 hK
    obtain ⟨R, hR, -, hRc, hRr⟩ := translateSRIQKB_downR hTobj K.toInterp ind
      (fun c hc => hKm.1 c (hobj_sub c hc)) (ContextCalculus.SRIQD.satABox_map_obj.1 hA)
    let I : Interp (owl2MapP pat) Dom :=
      { cls := R.cls, role := R.role, ind := R.ind,
        dprop := fun p y w => ∃ u : Fin (dpropsK O).length, (dpropsK O)[u] = p ∧ K.d u y (eqv.symm w),
        dtype := dtype }
    have hIobj : OWL.Model (objOntK O (SRIQKB.defBase O requested)) I := fun ax hax =>
      (sat_congr_mapK (I := R) (J := I) rfl rfl rfl (hobjKB ax hax) _ _).1 (hR ax hax)
    have hIc : ∀ (F : Fin Tobj.conceptCount) (hF : F.val < Tobj.named.length) y,
        I.cls Tobj.named[F.val] y ↔ K.c F y := fun F hF y => hRc F.val hF y
    have hdpK : ∀ (u : Fin (dpropsK O).length) y v, I.dprop (dpropsK O)[u] y (eqv v) ↔ K.d u y v := by
      intro u y v
      constructor
      · rintro ⟨u', hu', hd⟩
        have : u' = u := Fin.ext ((List.Nodup.getElem_inj_iff hdps_nd).1 hu')
        subst this
        simpa using hd
      · intro hd
        exact ⟨u, rfl, by simpa using hd⟩
    have hdcK : ∀ cl ∈ dc, ∀ y, ContextCalculus.SRIQD.dLocal atom (fun a => K.c a y)
        (fun u => K.d u y) cl := fun cl hcl y =>
      hKm.2 cl (List.mem_append_left _ (List.mem_append_right _ hcl)) y
    have hH : ∀ e ∈ tableK O, ∀ y, I.cls (fName (SRIQKB.defBase O requested) (tableK O) e) y ↔ I.ext e.toCE y := by
      intro e he y
      obtain ⟨F, W, u, jj, hjj, hF, hW, hu, hcl⟩ := hdc_all e he
      obtain ⟨hFl, hFn⟩ := hnamed_of_ix _ F hF
      obtain ⟨hWl, hWn⟩ := hnamed_of_ix _ W hW
      have hloc := (entryClauses_dLocal atom (fun a => K.c a y) (fun u => K.d u y) e F W u jj).1
        (fun cl hcl' => hdcK cl (hcl cl hcl') y)
      have hpos : posK e (K.d u y) (atom jj) ↔ I.ext e.toCE y := by
        refine posK_iff_ext I e y eqv _ _ (fun v => ?_) (fun v => ?_)
        · rw [← hdp_of_ix _ _ hu]
          exact (hdpK u y v).symm
        · rw [hatom]
          show (spec (tableK O) jj).ext (owl2MapP pat) dtype (eqv v) ↔ e.R.ext (owl2MapP pat) dtype (eqv v)
          simp only [spec, hjj]
      have hneg := negK_iff_not e (tableK_kind2 he) (K.d u y) (atom jj)
      have hFc : I.cls (fName (SRIQKB.defBase O requested) (tableK O) e) y ↔ K.c F y := by
        rw [← hFn]; exact hIc F hFl y
      have hWc : I.cls (wName (SRIQKB.defBase O requested) (tableK O) e) y ↔ K.c W y := by
        rw [← hWn]; exact hIc W hWl y
      have hor : I.cls (fName (SRIQKB.defBase O requested) (tableK O) e) y ∨
          I.cls (wName (SRIQKB.defBase O requested) (tableK O) e) y := by
        have hg0 := hKm.1 (.gci [] [F, W])
          (hobj_dc _ (hcl _ (by unfold entryClauses; exact List.mem_cons_self)))
        simp only [SRIQ.satClause, List.not_mem_nil, false_implies, implies_true,
          forall_const] at hg0
        obtain ⟨b, hb, hby⟩ := hg0 y
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact Or.inl (hFc.2 hby)
        · exact Or.inr (hWc.2 hby)
      constructor
      · intro h; exact hpos.1 (hloc.1 (hFc.1 h))
      · intro h
        rcases hor with hf | hw
        · exact hf
        · exact absurd (hpos.2 h) (hneg.1 (hloc.2 (hWc.1 hw)))
    have hIO : OWL.Model O I := by
      intro ax0 h0
      refine (sat_rwAxiomK I (hO' ax0 h0) _).2 ⟨fun ax hax => ?_, fun pq hpq y v hv => ?_⟩
      · have hrw := rwK_ok (hO' ax0 h0) hax
        have := (sat_absAxK hrw (fun e he y => hH e (hdex_tab ax0 h0 ax hax e he) y) _).1
          (hIobj _ (hmem_rw ax0 h0 ax hax))
        exact (hNsw I (rwOK_isSHIQDKB hrw) _ _).1 this
      · obtain ⟨u, w, hu, hw, hmem⟩ := hsc_all pq (List.mem_flatMap.2 ⟨ax0, h0, hpq⟩)
        have hloc := hKm.2 _ (List.mem_append_right _ hmem) y
        rw [← hu] at hv
        rw [← hw]
        have h1 := (hdpK u y (eqv.symm v)).1 (by simpa using hv)
        have h2 := hloc (eqv.symm v) h1
        simpa using (hdpK w y (eqv.symm v)).2 h2
    refine ⟨I, hIO, fun i hi _ y => hIc ⟨i, _⟩ hi y, fun r hr k hk R' hfin x y => ?_,
      eqv, hatom, fun _ _ _ => Iff.rfl⟩
    have h := hRr r hr k hk R' hfin x y
    cases r <;> exact h

/-- **The model maps of the SHIQ(D) knowledge-base translation**, with each
requested IRI standing for its index. -/
theorem translateSRIQDKB_mapsR (pat : String → String → Prop) {O : Ontology}
    {requested extra : List IRI} {T : SRIQDKBTranslation}
    (h : translateSRIQDKB O requested extra = some T) :
    (∀ (Dom : Type) [Nonempty Dom] (I : Interp (owl2MapP pat) Dom), OWL.Model O I →
      ∃ (V : Type) (atom : Fin T.tab.length → V → Prop), owlTheory pat (spec T.tab) V atom ∧
        ∃ (K : ContextCalculus.SRIQD.DInterp Dom V (Fin T.obj.conceptCount) (Fin T.obj.roleCount)
            (Fin T.dps.length)) (ind : Fin T.obj.inds.length → Dom),
          ContextCalculus.SRIQD.models atom K T.ontology ∧
          ContextCalculus.SRIQD.satABox atom K ind T.abox ∧
          (∀ (i : Nat) (hi : i < T.obj.named.length), T.obj.named[i] ∈ requested → ∀ y,
            K.c ⟨i, Nat.lt_of_lt_of_le hi T.obj.hnamed⟩ y ↔ I.cls T.obj.named[i] y) ∧
          ∀ (r : ObjProp), r.isBasic = true → ∀ k, (EL.propIRI r, k) ∈ T.obj.rnames →
            ∀ R, SRIT.finRT T.obj.roleCount (SRIT.mkRT r k) = some R →
            ∀ x y, K.rt R x y ↔ I.prop r x y) ∧
    (∀ (Dom V : Type) [Nonempty Dom] (atom : Fin T.tab.length → V → Prop),
      owlTheory pat (spec T.tab) V atom →
      ∀ (K : ContextCalculus.SRIQD.DInterp Dom V (Fin T.obj.conceptCount) (Fin T.obj.roleCount)
          (Fin T.dps.length)) (ind : Fin T.obj.inds.length → Dom),
        ContextCalculus.SRIQD.models atom K T.ontology →
        ContextCalculus.SRIQD.satABox atom K ind T.abox →
        ∃ I : Interp (owl2MapP pat) Dom, OWL.Model O I ∧
          (∀ (i : Nat) (hi : i < T.obj.named.length), T.obj.named[i] ∈ requested → ∀ y,
            I.cls T.obj.named[i] y ↔ K.c ⟨i, Nat.lt_of_lt_of_le hi T.obj.hnamed⟩ y) ∧
          ∀ (r : ObjProp), r.isBasic = true → ∀ k, (EL.propIRI r, k) ∈ T.obj.rnames →
            ∀ R, SRIT.finRT T.obj.roleCount (SRIT.mkRT r k) = some R →
            ∀ x y, I.prop r x y ↔ K.rt R x y) := by
  obtain ⟨h1, h2⟩ := translateSRIQDKB_mapsRD pat h
  refine ⟨h1, fun Dom V _ atom hΘ K ind hK hA => ?_⟩
  obtain ⟨I, hI, hc, hr, -⟩ := h2 Dom V atom hΘ K ind hK hA
  exact ⟨I, hI, hc, hr⟩

theorem translateSRIQDKB_maps (pat : String → String → Prop) {O : Ontology}
    {requested extra : List IRI} {T : SRIQDKBTranslation}
    (h : translateSRIQDKB O requested extra = some T) :
    (∀ (Dom : Type) [Nonempty Dom] (I : Interp (owl2MapP pat) Dom), OWL.Model O I →
      ∃ (V : Type) (atom : Fin T.tab.length → V → Prop), owlTheory pat (spec T.tab) V atom ∧
        ∃ (K : ContextCalculus.SRIQD.DInterp Dom V (Fin T.obj.conceptCount) (Fin T.obj.roleCount)
            (Fin T.dps.length)) (ind : Fin T.obj.inds.length → Dom),
          ContextCalculus.SRIQD.models atom K T.ontology ∧
          ContextCalculus.SRIQD.satABox atom K ind T.abox ∧
          ∀ (i : Nat) (hi : i < T.obj.named.length), T.obj.named[i] ∈ requested → ∀ y,
            K.c ⟨i, Nat.lt_of_lt_of_le hi T.obj.hnamed⟩ y ↔ I.cls T.obj.named[i] y) ∧
    (∀ (Dom V : Type) [Nonempty Dom] (atom : Fin T.tab.length → V → Prop),
      owlTheory pat (spec T.tab) V atom →
      ∀ (K : ContextCalculus.SRIQD.DInterp Dom V (Fin T.obj.conceptCount) (Fin T.obj.roleCount)
          (Fin T.dps.length)) (ind : Fin T.obj.inds.length → Dom),
        ContextCalculus.SRIQD.models atom K T.ontology →
        ContextCalculus.SRIQD.satABox atom K ind T.abox →
        ∃ I : Interp (owl2MapP pat) Dom, OWL.Model O I ∧
          ∀ (i : Nat) (hi : i < T.obj.named.length), T.obj.named[i] ∈ requested → ∀ y,
            I.cls T.obj.named[i] y ↔ K.c ⟨i, Nat.lt_of_lt_of_le hi T.obj.hnamed⟩ y)  := by
  obtain ⟨h1, h2⟩ := translateSRIQDKB_mapsR pat h
  refine ⟨fun Dom _ I hI => ?_, fun Dom V _ atom hΘ K ind hK hA => ?_⟩
  · obtain ⟨V, atom, hΘ, K, ind, hK, hA, hc, -⟩ := h1 Dom I hI
    exact ⟨V, atom, hΘ, K, ind, hK, hA, hc⟩
  · obtain ⟨I, hI, hc, -⟩ := h2 Dom V atom hΘ K ind hK hA
    exact ⟨I, hI, hc⟩

/-- **Consistency through the SHIQ(D) knowledge-base translation.** -/
theorem translateSRIQDKB_consistent (pat : String → String → Prop) {O : Ontology}
    {requested extra : List IRI} {T : SRIQDKBTranslation}
    (h : translateSRIQDKB O requested extra = some T) :
    (∃ (Dom : Type) (_ : Nonempty Dom) (I : Interp (owl2MapP pat) Dom), OWL.Model O I) ↔
      ContextCalculus.SRIQD.ConsistentKB (owlTheory pat (spec T.tab)) T.ontology T.abox := by
  obtain ⟨hup, hdown⟩ := translateSRIQDKB_maps pat h
  constructor
  · rintro ⟨Dom, hD, I, hI⟩
    obtain ⟨V, atom, hΘ, K, ind, hK, hA, -⟩ := hup Dom I hI
    exact ⟨Dom, V, hD, atom, hΘ, K, ind, hK, hA⟩
  · rintro ⟨Dom, V, hD, atom, hΘ, K, ind, hK, hA⟩
    obtain ⟨I, hI, -⟩ := hdown Dom V atom hΘ K ind hK hA
    exact ⟨Dom, hD, I, hI⟩

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.translateSRIQDKB_maps
#print axioms ContextCalculus.OWLFrontend.translateSRIQDKB_mapsR
#print axioms ContextCalculus.OWLFrontend.translateSRIQDKB_mapsRD
#print axioms ContextCalculus.OWLFrontend.translateSRIQDKB_consistent
