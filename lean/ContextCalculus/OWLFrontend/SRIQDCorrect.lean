import ContextCalculus.OWLFrontend.SRIQDEntries
import ContextCalculus.OWLFrontend.SRIQKBTranslateCorrect

/-!
# Correctness of the SHIQ(D) translation at the OWL 2 datatype map (v1.7.0 stage C4, part D)

`translateSRIQD_correct`: for requested IRIs `A`, `B` (positions `i`, `j`),
`O` entails `SubClassOf(A B)` at `owl2MapP pat` iff the `SRIQD` ontology
entails `i ⊑ j` over the data theory of the map with the table's data
ranges as atoms (`owlTheory pat (spec T.tab)`), for every reading `pat` of
`xsd:pattern`.
-/

namespace ContextCalculus.OWLFrontend.SHIQD

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes

theorem dexprs_kind2 : ∀ (c : ClassExpr), ∀ e ∈ dexprs c, e.kind = 2 → 1 ≤ e.n
  | .and cs, e, he, hk => by
    rw [dexprs] at he
    obtain ⟨⟨c, hc⟩, -, he⟩ := List.mem_flatMap.1 he
    exact dexprs_kind2 c e he hk
  | .or cs, e, he, hk => by
    rw [dexprs] at he
    obtain ⟨⟨c, hc⟩, -, he⟩ := List.mem_flatMap.1 he
    exact dexprs_kind2 c e he hk
  | .not c, e, he, hk => by rw [dexprs] at he; exact dexprs_kind2 c e he hk
  | .some _ c, e, he, hk => by rw [dexprs] at he; exact dexprs_kind2 c e he hk
  | .all _ c, e, he, hk => by rw [dexprs] at he; exact dexprs_kind2 c e he hk
  | .min _ _ c, e, he, hk => by rw [dexprs] at he; exact dexprs_kind2 c e he hk
  | .max _ _ c, e, he, hk => by rw [dexprs] at he; exact dexprs_kind2 c e he hk
  | .exact _ _ c, e, he, hk => by rw [dexprs] at he; exact dexprs_kind2 c e he hk
  | .dataSome .., e, he, hk | .dataAll .., e, he, hk | .dataHasValue .., e, he, hk => by
    rw [dexprs] at he; simp at he; subst he; simp at hk
  | .dataMin 0 .., e, he, _ => by rw [dexprs] at he; simp at he
  | .dataMin (k + 1) .., e, he, _ => by rw [dexprs] at he; simp at he; subst he; simp
  | .dataMax .., e, he, hk => by rw [dexprs] at he; simp at he; subst he; simp at hk
  | .dataExact 0 .., e, he, hk => by rw [dexprs] at he; simp at he; subst he; simp at hk
  | .dataExact (k + 1) .., e, he, hk => by
    rw [dexprs] at he; simp at he
    rcases he with rfl | rfl
    · simp
    · simp at hk
  | .cls _, e, he, _ | .thing, e, he, _ | .nothing, e, he, _ | .oneOf _, e, he, _
  | .hasValue .., e, he, _ | .hasSelf _, e, he, _ => by simp [dexprs] at he
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

theorem mem_table {O : Ontology} {e : DExpr} :
    e ∈ table O ↔ ∃ ax ∈ rwAxioms O, e ∈ axDexprs ax := by
  simp [table, List.mem_dedup, List.mem_flatMap]

theorem table_kind2 {O : Ontology} {e : DExpr} (he : e ∈ table O) : e.kind = 2 → 1 ≤ e.n := by
  obtain ⟨ax, -, he⟩ := mem_table.1 he
  cases ax <;> simp only [axDexprs, List.mem_append, List.mem_flatMap, List.not_mem_nil] at he
  all_goals first
    | (rcases he with he | he <;> exact dexprs_kind2 _ e he)
    | (obtain ⟨c, -, he⟩ := he; exact dexprs_kind2 _ e he)
    | exact dexprs_kind2 _ e he

theorem rw_isSHIQD {ax0 ax : Axiom} (h0 : ax0.isSHIQD = true) (h : ax ∈ rwAxiom ax0) :
    ax.isSHIQD = true ∧ isDataPropAx ax = false := by
  cases ax0 <;> simp only [rwAxiom, List.mem_singleton, List.not_mem_nil] at h
  all_goals (subst h; simp_all [Axiom.isSHIQD, ClassExpr.isALCIQD, isDataPropAx, Axiom.isSHI, Axiom.isSRI])

/-! ## Fresh names -/

section Names

variable {base : String} {tab : List DExpr}

theorem fName_ne_wName (e e' : DExpr) : fName base tab e ≠ wName base tab e' := by
  intro h
  have := SRIQKB.defName_inj h
  omega

theorem fName_inj {e e' : DExpr} (he : e ∈ tab) (he' : e' ∈ tab)
    (h : fName base tab e = fName base tab e') : e = e' := by
  have h1 := SRIQKB.defName_inj h
  have h2 : tab.idxOf e = tab.idxOf e' := by omega
  rw [← List.getElem_idxOf (List.idxOf_lt_length_of_mem he),
    ← List.getElem_idxOf (List.idxOf_lt_length_of_mem he')]
  simp only [h2]

theorem wName_inj {e e' : DExpr} (he : e ∈ tab) (he' : e' ∈ tab)
    (h : wName base tab e = wName base tab e') : e = e' := by
  have h1 := SRIQKB.defName_inj h
  have h2 : tab.idxOf e = tab.idxOf e' := by omega
  rw [← List.getElem_idxOf (List.idxOf_lt_length_of_mem he),
    ← List.getElem_idxOf (List.idxOf_lt_length_of_mem he')]
  simp only [h2]

end Names

theorem toCE_isALCIQD (e : DExpr) : e.toCE.isALCIQD = true := by
  rcases e with ⟨k, n, p, R⟩
  match k with
  | 0 | 1 | 2 | 3 => simp [DExpr.toCE, ClassExpr.isALCIQD, DataProp.isNamed]

theorem toCE_names (e : DExpr) : e.toCE.names = [] := by
  rcases e with ⟨k, n, p, R⟩
  match k with
  | 0 | 1 | 2 | 3 => simp [DExpr.toCE, ClassExpr.names]

end ContextCalculus.OWLFrontend.SHIQD

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD

/-- **Correctness of the SHIQ(D) translation.** -/
theorem translateSRIQD_correct (pat : String → String → Prop) {O : Ontology}
    {requested : List IRI} {T : SRIQDTranslation} (h : translateSRIQD O requested = some T)
    {i j : Nat} (hi : i < T.named.length) (hj : j < T.named.length)
    (hi' : i < T.obj.conceptCount) (hj' : j < T.obj.conceptCount) :
    EntailsSubAt (owl2MapP pat) O T.named[i] T.named[j] ↔
      ContextCalculus.SRIQD.EntailsSub (owlTheory pat (spec T.tab)) T.ontology
        ⟨i, hi'⟩ ⟨j, hj'⟩ := by
  classical
  unfold translateSRIQD at h
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
  -- names
  have hTn : Tobj.named = (requested ++ freshNames (SRIQKB.defBase O requested) (table O)).eraseDups := translateSRIQ_named hTobj
  have hpre : ∀ k (hk : k < requested.eraseDups.length), ∃ hk2 : k < Tobj.named.length,
      Tobj.named[k] = requested.eraseDups[k] := by
    intro k hk
    have e1 : Tobj.named = requested.eraseDups ++
        ((freshNames (SRIQKB.defBase O requested) (table O)).removeAll requested).eraseDups := by
      rw [hTn, List.eraseDups_append]
    have hk2 : k < Tobj.named.length := by rw [e1, List.length_append]; omega
    refine ⟨hk2, ?_⟩
    simp only [e1]
    rw [List.getElem_append_left hk]
  have hreqfresh : ∀ k (hk : k < requested.eraseDups.length) (n : Nat),
      requested.eraseDups[k] ≠ SRIQKB.defName (SRIQKB.defBase O requested) n := fun k hk n =>
    SRIQKB.fresh_req (List.mem_eraseDups.1 (List.getElem_mem hk)) n
  have hnamed_of_ix : ∀ a (F : Fin Tobj.conceptCount), nameIx Tobj a = some F →
      ∃ hF : F.val < Tobj.named.length, Tobj.named[F.val] = a := by
    intro a F hF
    unfold nameIx at hF
    split_ifs at hF with hlt
    cases hF
    exact ⟨hlt, List.getElem_idxOf hlt⟩
  have hdp_of_ix : ∀ p (u : Fin (dprops O).length), dpIx (dprops O) p = some u → (dprops O)[u] = p := by
    intro p u hu
    unfold dpIx at hu
    split_ifs at hu with hlt
    cases hu
    exact List.getElem_idxOf hlt
  have hdps_nd : (dprops O).Nodup := List.nodup_dedup _
  -- the data clauses
  have hdc_mem : ∀ cl ∈ dc, ∃ e ∈ (table O), ∃ (F W : Fin Tobj.conceptCount) (u : Fin (dprops O).length)
      (jj : Fin (table O).length), (table O)[jj] = e ∧ nameIx Tobj (fName (SRIQKB.defBase O requested) (table O) e) = some F ∧
      nameIx Tobj (wName (SRIQKB.defBase O requested) (table O) e) = some W ∧ dpIx (dprops O) e.p = some u ∧
      cl ∈ entryClauses (m := Tobj.roleCount) e F W u jj := by
    intro cl hcl
    obtain ⟨⟨e, k⟩, hek, l, hf, hcl⟩ := SRIQKB.collect_mem hdc cl hcl
    have hk := List.mem_zipIdx_iff_getElem?.1 hek
    simp only at hk
    unfold dataClauseOf at hf
    split at hf
    · rename_i F W u hF hW hu
      split_ifs at hf with hk'
      cases hf
      refine ⟨e, ?_, F, W, u, ⟨k, hk'⟩, ?_, hF, hW, hu, hcl⟩
      · exact List.mem_of_getElem? hk
      · simpa [hk'] using hk
    · cases hf
  have hdc_all : ∀ e ∈ (table O), ∃ (F W : Fin Tobj.conceptCount) (u : Fin (dprops O).length)
      (jj : Fin (table O).length), (table O)[jj] = e ∧ nameIx Tobj (fName (SRIQKB.defBase O requested) (table O) e) = some F ∧
      nameIx Tobj (wName (SRIQKB.defBase O requested) (table O) e) = some W ∧ dpIx (dprops O) e.p = some u ∧
      ∀ cl ∈ entryClauses (m := Tobj.roleCount) e F W u jj, cl ∈ dc := by
    intro e he
    have hek : (e, (table O).idxOf e) ∈ (table O).zipIdx := List.mem_zipIdx_iff_getElem?.2 (by
      rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem he), List.getElem_idxOf])
    obtain ⟨l, hf, hl⟩ := SRIQKB.collect_some hdc _ hek
    unfold dataClauseOf at hf
    split at hf
    · rename_i F W u hF hW hu
      split_ifs at hf with hk'
      cases hf
      exact ⟨F, W, u, ⟨_, hk'⟩, List.getElem_idxOf hk', hF, hW, hu, hl⟩
    · cases hf
  -- the sub-property clauses
  have hsc_mem : ∀ cl ∈ sc, ∃ pq ∈ O.axioms.flatMap subPairs, ∃ (u w : Fin (dprops O).length),
      (dprops O)[u] = pq.1 ∧ (dprops O)[w] = pq.2 ∧ cl = .dSub u w := by
    intro cl hcl
    obtain ⟨pq, hpq, l, hf, hcl⟩ := SRIQKB.collect_mem hsc cl hcl
    unfold subClauseOf at hf
    split at hf
    · rename_i u w hu hw
      cases hf
      rw [List.mem_singleton] at hcl
      exact ⟨pq, hpq, u, w, hdp_of_ix _ _ hu, hdp_of_ix _ _ hw, hcl⟩
    · cases hf
  have hsc_all : ∀ pq ∈ O.axioms.flatMap subPairs, ∃ (u w : Fin (dprops O).length),
      (dprops O)[u] = pq.1 ∧ (dprops O)[w] = pq.2 ∧ ContextCalculus.SRIQD.Clause.dSub u w ∈ sc := by
    intro pq hpq
    obtain ⟨l, hf, hl⟩ := SRIQKB.collect_some hsc pq hpq
    unfold subClauseOf at hf
    split at hf
    · rename_i u w hu hw
      cases hf
      exact ⟨u, w, hdp_of_ix _ _ hu, hdp_of_ix _ _ hw, hl _ (List.mem_singleton_self _)⟩
    · cases hf
  -- the object part
  have hentry_nobj : ∀ (e : DExpr) (F W : Fin Tobj.conceptCount) (u : Fin (dprops O).length)
      (jj : Fin (table O).length), ∀ cl ∈ entryClauses (m := Tobj.roleCount) e F W u jj,
      ContextCalculus.SRIQD.toObj cl = none := by
    intro e F W u jj cl hcl
    unfold entryClauses at hcl
    split at hcl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl <;>
      rcases hcl with rfl | rfl <;> rfl
  have hobjPart : ContextCalculus.SRIQD.objPart (Tobj.ontology.map ContextCalculus.SRIQD.Clause.obj
      ++ dc ++ sc) = Tobj.ontology := by
    have h1 : dc.filterMap ContextCalculus.SRIQD.toObj = [] := List.filterMap_eq_nil_iff.2
      fun cl hcl => by
        obtain ⟨e, -, F, W, u, jj, -, -, -, -, hcl'⟩ := hdc_mem cl hcl
        exact hentry_nobj e F W u jj cl hcl'
    have h2 : sc.filterMap ContextCalculus.SRIQD.toObj = [] := List.filterMap_eq_nil_iff.2
      fun cl hcl => by
        obtain ⟨-, -, u, w, -, -, rfl⟩ := hsc_mem cl hcl
        rfl
    unfold ContextCalculus.SRIQD.objPart
    rw [List.filterMap_append, List.filterMap_append, List.filterMap_map, h1, h2]
    simp [ContextCalculus.SRIQD.toObj]
  have hobjSHIQ : (objOnt O (SRIQKB.defBase O requested)).isSHIQ = true :=
    translateSRIQ_isSHIQ hTobj
  have hO' : ∀ ax ∈ O.axioms, ax.isSHIQD = true := by
    simpa [Ontology.isSHIQD, List.all_eq_true] using hO
  have hmem_rw : ∀ ax0 ∈ O.axioms, ∀ ax ∈ rwAxiom ax0,
      absAx (fName (SRIQKB.defBase O requested) (table O)) ax ∈
        (objOnt O (SRIQKB.defBase O requested)).axioms := fun ax0 h0 ax hax =>
    List.mem_append_left _ (List.mem_map_of_mem (List.mem_flatMap.2 ⟨ax0, h0, hax⟩))
  have hmem_or : ∀ e ∈ table O, Axiom.subClassOf .thing
      (.or [.cls (fName (SRIQKB.defBase O requested) (table O) e),
        .cls (wName (SRIQKB.defBase O requested) (table O) e)]) ∈
        (objOnt O (SRIQKB.defBase O requested)).axioms := fun e he =>
    List.mem_append_right _ (List.mem_map_of_mem he)
  have hdex_tab : ∀ ax0 ∈ O.axioms, ∀ ax ∈ rwAxiom ax0, ∀ e ∈ axDexprs ax, e ∈ table O :=
    fun ax0 h0 ax hax e he => mem_table.2 ⟨ax, List.mem_flatMap.2 ⟨ax0, h0, hax⟩, he⟩
  have hfresh_ax : ∀ ax ∈ O.axioms, ∀ a ∈ ax.classNames, ∀ n,
      a ≠ SRIQKB.defName (SRIQKB.defBase O requested) n :=
    fun ax hax a ha n => SRIQKB.fresh_ax hax ha n
  have hNsw : ∀ {DM : DatatypeMap} {Dom : Type} (I : Interp DM Dom) {ax : Axiom}, ax.isSHIQD = true →
      ∀ N N' : List IRI, I.sat N ax ↔ I.sat N' ax := by
    intro DM Dom I ax hax N N'
    exact sat_congr_cls rfl rfl rfl hax (fun _ _ => rfl) N N'
  change i < requested.eraseDups.length at hi
  change j < requested.eraseDups.length at hj
  obtain ⟨hi2, hin⟩ := hpre i hi
  obtain ⟨hj2, hjn⟩ := hpre j hj
  show EntailsSubAt (owl2MapP pat) O requested.eraseDups[i] requested.eraseDups[j] ↔
    ContextCalculus.SRIQD.EntailsSub (owlTheory pat (spec (table O)))
      (Tobj.ontology.map ContextCalculus.SRIQD.Clause.obj ++ dc ++ sc) ⟨i, hi'⟩ ⟨j, hj'⟩
  constructor
  · intro hE Dom V _ atom hΘ K hK x hx
    obtain ⟨eqv, dtype, hatom⟩ := hΘ
    have hKm := ContextCalculus.SRIQD.models_iff.1 hK
    rw [hobjPart] at hKm
    obtain ⟨R, hR, hRc⟩ := (translateSRIQ_models hTobj).1 Dom K.toInterp hKm.1
    let I : Interp (owl2MapP pat) Dom :=
      { cls := R.cls, role := R.role, ind := R.ind,
        dprop := fun p y w => ∃ u : Fin (dprops O).length, (dprops O)[u] = p ∧ K.d u y (eqv.symm w),
        dtype := dtype }
    have hobjAx : ∀ ax ∈ (objOnt O (SRIQKB.defBase O requested)).axioms, ax.isSHIQ = true := by
      simpa [Ontology.isSHIQ, List.all_eq_true] using hobjSHIQ
    have hIobj : OWL.Model (objOnt O (SRIQKB.defBase O requested)) I := fun ax hax =>
      (Axiom.sat_congr' (I := R) (J := I) rfl rfl (hobjAx ax hax) _ _).1 (hR ax hax)
    have hIc : ∀ (F : Fin Tobj.conceptCount) (hF : F.val < Tobj.named.length) y,
        I.cls Tobj.named[F.val] y ↔ K.c F y := fun F hF y => hRc F.val hF y
    have hdpK : ∀ (u : Fin (dprops O).length) y v, I.dprop (dprops O)[u] y (eqv v) ↔ K.d u y v := by
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
    have hH : ∀ e ∈ table O, ∀ y, I.cls (fName (SRIQKB.defBase O requested) (table O) e) y ↔ I.ext e.toCE y := by
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
          show (spec (table O) jj).ext (owl2MapP pat) dtype (eqv v) ↔ e.R.ext (owl2MapP pat) dtype (eqv v)
          simp only [spec, hjj]
      have hneg := negK_iff_not e (table_kind2 he) (K.d u y) (atom jj)
      have hFc : I.cls (fName (SRIQKB.defBase O requested) (table O) e) y ↔ K.c F y := by
        rw [← hFn]; exact hIc F hFl y
      have hWc : I.cls (wName (SRIQKB.defBase O requested) (table O) e) y ↔ K.c W y := by
        rw [← hWn]; exact hIc W hWl y
      have hor : I.cls (fName (SRIQKB.defBase O requested) (table O) e) y ∨
          I.cls (wName (SRIQKB.defBase O requested) (table O) e) y := by
        have := hIobj _ (hmem_or e he) y (by rw [Interp.ext]; trivial)
        rw [Interp.ext] at this
        obtain ⟨c, hc, hcy⟩ := this
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · left; rw [Interp.ext] at hcy; exact hcy
        · right; rw [Interp.ext] at hcy; exact hcy
      constructor
      · intro h; exact hpos.1 (hloc.1 (hFc.1 h))
      · intro h
        rcases hor with hf | hw
        · exact hf
        · exact absurd (hpos.2 h) (hneg.1 (hloc.2 (hWc.1 hw)))
    have hIO : OWL.Model O I := by
      intro ax0 h0
      refine (sat_rwAxiom I (hO' ax0 h0) _).2 ⟨fun ax hax => ?_, fun pq hpq y v hv => ?_⟩
      · have hrw := rw_isSHIQD (hO' ax0 h0) hax
        have := (sat_absAx hrw.1 (fun e he y => hH e (hdex_tab ax0 h0 ax hax e he) y) _).1
          (hIobj _ (hmem_rw ax0 h0 ax hax))
        exact (hNsw I hrw.1 _ _).1 this
      · obtain ⟨u, w, hu, hw, hmem⟩ := hsc_all pq (List.mem_flatMap.2 ⟨ax0, h0, hpq⟩)
        have hloc := hKm.2 _ (List.mem_append_right _ hmem) y
        rw [← hu] at hv
        rw [← hw]
        have h1 := (hdpK u y (eqv.symm v)).1 (by simpa using hv)
        have h2 := hloc (eqv.symm v) h1
        simpa using (hdpK w y (eqv.symm v)).2 h2
    have h1 : I.cls requested.eraseDups[i] x := by
      rw [← hin]; exact (hIc ⟨i, hi'⟩ hi2 x).2 hx
    have h2 := hE Dom I hIO x h1
    rw [← hjn] at h2
    exact (hIc ⟨j, hj'⟩ hj2 x).1 h2
  · intro hS Dom _ I hI x hx
    let isF : IRI → Prop := fun a => ∃ e ∈ table O, fName (SRIQKB.defBase O requested) (table O) e = a
    let isW : IRI → Prop := fun a => ∃ e ∈ table O, wName (SRIQKB.defBase O requested) (table O) e = a
    let I' : Interp (owl2MapP pat) Dom :=
      { cls := fun a y => if isF a then ∃ e ∈ table O, fName (SRIQKB.defBase O requested) (table O) e = a ∧ I.ext e.toCE y
          else if isW a then ∃ e ∈ table O, wName (SRIQKB.defBase O requested) (table O) e = a ∧ ¬ I.ext e.toCE y
          else I.cls a y,
        role := I.role, ind := I.ind, dprop := I.dprop, dtype := I.dtype }
    have hI'ext : ∀ e : DExpr, I'.ext e.toCE = I.ext e.toCE := fun e =>
      ext_congr_cls (I := I') (J := I) rfl rfl rfl e.toCE (toCE_isALCIQD e) (by simp [toCE_names])
    have hI'F : ∀ e ∈ table O, ∀ y, I'.cls (fName (SRIQKB.defBase O requested) (table O) e) y ↔ I.ext e.toCE y := by
      intro e he y
      show (if isF _ then _ else _) ↔ _
      rw [if_pos ⟨e, he, rfl⟩]
      constructor
      · rintro ⟨e', he', hn, h⟩
        rw [fName_inj he' he hn] at h
        exact h
      · intro h; exact ⟨e, he, rfl, h⟩
    have hI'W : ∀ e ∈ table O, ∀ y, I'.cls (wName (SRIQKB.defBase O requested) (table O) e) y ↔ ¬ I.ext e.toCE y := by
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
      (sat_congr_cls (I := I) (J := I') rfl rfl rfl (hO' ax hax)
        (fun a ha => (hI'old a (hfresh_ax ax hax a ha)).symm) _ _).1 (hI ax hax)
    have hI'obj : OWL.Model (objOnt O (SRIQKB.defBase O requested)) I' := by
      intro ax hax
      rcases List.mem_append.1 hax with h1 | h1
      · obtain ⟨ax', hax', rfl⟩ := List.mem_map.1 h1
        obtain ⟨ax0, h0, hax'0⟩ := List.mem_flatMap.1 hax'
        have hrw := rw_isSHIQD (hO' ax0 h0) hax'0
        refine (sat_absAx hrw.1 (fun e he y => ?_) _).2 ?_
        · rw [hI'F e (hdex_tab ax0 h0 ax' hax'0 e he) y, hI'ext]
        · exact (hNsw I' hrw.1 _ _).1 (((sat_rwAxiom I' (hO' ax0 h0) _).1 (hI'O ax0 h0)).1 ax' hax'0)
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h1
        intro y _
        rw [Interp.ext]
        by_cases hy : I.ext e.toCE y
        · exact ⟨_, List.mem_cons_self, by rw [Interp.ext]; exact (hI'F e he y).2 hy⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
            rw [Interp.ext]; exact (hI'W e he y).2 hy⟩
    obtain ⟨J, hJ, hJc⟩ := (translateSRIQ_models hTobj).2 _ Dom I' hI'obj
    let K : ContextCalculus.SRIQD.DInterp Dom Val (Fin Tobj.conceptCount) (Fin Tobj.roleCount)
        (Fin (dprops O).length) :=
      { toInterp := J, d := fun u y v => I.dprop (dprops O)[u] y v }
    let atom : Fin (table O).length → Val → Prop := fun p v =>
      (spec (table O) p).ext (owl2MapP pat) I.dtype v
    have hΘ : owlTheory pat (spec (table O)) Val atom := ⟨Equiv.refl _, I.dtype, fun _ _ => Iff.rfl⟩
    have hKc : ∀ (F : Fin Tobj.conceptCount) (hF : F.val < Tobj.named.length) y,
        K.c F y ↔ I'.cls Tobj.named[F.val] y := fun F hF y => hJc F.val hF y
    have hK : ContextCalculus.SRIQD.models atom K
        (Tobj.ontology.map ContextCalculus.SRIQD.Clause.obj ++ dc ++ sc) := by
      refine ContextCalculus.SRIQD.models_iff.2 ⟨by rw [hobjPart]; exact hJ, fun cl hcl y => ?_⟩
      rcases List.mem_append.1 hcl with hcl | hcl
      · rcases List.mem_append.1 hcl with hcl | hcl
        · obtain ⟨c, -, rfl⟩ := List.mem_map.1 hcl
          trivial
        · obtain ⟨e, he, F, W, u, jj, hjj, hF, hW, hu, hcl'⟩ := hdc_mem cl hcl
          obtain ⟨hFl, hFn⟩ := hnamed_of_ix _ F hF
          obtain ⟨hWl, hWn⟩ := hnamed_of_ix _ W hW
          have hpos : posK e (K.d u y) (atom jj) ↔ I.ext e.toCE y := by
            refine posK_iff_ext I e y (Equiv.refl _) _ _ (fun v => ?_) (fun v => ?_)
            · show I.dprop (dprops O)[u] y v ↔ _
              rw [hdp_of_ix _ _ hu]; rfl
            · show (spec (table O) jj).ext (owl2MapP pat) I.dtype v ↔ e.R.ext (owl2MapP pat) I.dtype v
              simp only [spec, hjj]
          have hneg := negK_iff_not e (table_kind2 he) (K.d u y) (atom jj)
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
        have := ((sat_rwAxiom I (hO' ax0 h0) _).1 (hI ax0 h0)).2 pq hpq0 y v
        show I.dprop (dprops O)[w] y v
        rw [hw]
        exact this (by rw [← hu]; exact hv)
    have h1 : K.c ⟨i, hi'⟩ x := by
      rw [hKc ⟨i, hi'⟩ hi2 x]
      show I'.cls Tobj.named[i] x
      rw [hin, hI'old _ (hreqfresh i hi)]
      exact hx
    have h2 := hS Dom Val atom hΘ K hK x h1
    rw [hKc ⟨j, hj'⟩ hj2 x] at h2
    change I'.cls Tobj.named[j] x at h2
    rw [hjn, hI'old _ (hreqfresh j hj)] at h2
    exact h2

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.translateSRIQD_correct
