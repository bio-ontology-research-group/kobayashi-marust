import ContextCalculus.OWLFrontend.SHOIQDNom
import ContextCalculus.OWLFrontend.SHOIQC2aReference
import ContextCalculus.OWLFrontend.SRIQDKBRows
import ContextCalculus.SRIQN.DataParts

/-!
# The OWL route for SHOIQ(D) knowledge bases in C2a (stage C2a with data)

`docs/V1.7.0-C2-NOMINALS-DESIGN.md`, sections 1, 5, 6 and 7. An ontology
of the SHOIQ(D) knowledge-base part (`Ontology.isSHOIQDKB`) is rewritten
with nominal classes (`nomOntD`), translated by the SHIQ(D)
knowledge-base translation (`translateSRIQDKB`, here without assertions),
and read as an `SRIQN` data ontology: the translated clauses plus `nom X`
for the index `X` of each nominal class (`dosn`). The route requires a
SHIQ object part (`isSHIQB`), C2a of the object part with the nominal
clauses after transitivity removal (`IsC2aD`), and supported data atoms;
it decides with the cell parts of the OWL 2 datatype map
(`consistentPartsN`, the bounded oracles of the SHIQ(D) route).

* `owlSHOIQDC2aConsistent O hint`: consistency at `owl2MapP pat`, exact for
  every reading `pat` of `xsd:pattern` and every hint
  (`owlSHOIQDC2aConsistent_sound`), answering exactly on the SHOIQ(D)
  knowledge-base part with the checks passed (`_isSome_iff`).
* Rows, each a consistency test on the ontology with added axioms, exact
  for every hint (`_sound`) and answering when the checks pass on the
  extension (`_complete`): type (`ClassAssertion(C a)`), same
  (`SameIndividual(a b)`), subsumption (`SubClassOf(A B)`), different
  (`DifferentIndividuals(a b)`), role (`ObjectPropertyAssertion(r a b)`)
  and negative role (`NegativeObjectPropertyAssertion(r a b)`).
-/

namespace ContextCalculus.OWL

variable {DM : DatatypeMap} {Dom : Type}

/-- A class expression has the same extension in two interpretations that
differ at most on the individuals it does not mention. -/
theorem ClassExpr.ext_congr_ind {I J : Interp DM Dom} (hc : I.cls = J.cls) (hr : I.role = J.role)
    (hd : I.dprop = J.dprop) (ht : I.dtype = J.dtype) :
    ∀ c : ClassExpr, (∀ i : Individual, (∀ a ∈ i.namedIRI, a ∈ c.namedIndividuals) →
      I.ind i = J.ind i) → I.ext c = J.ext c
  | .cls a, _ => by funext x; rw [Interp.ext, Interp.ext, hc]
  | .thing, _ => by funext x; rw [Interp.ext, Interp.ext]
  | .nothing, _ => by funext x; rw [Interp.ext, Interp.ext]
  | .and cs, h => by
    have ih : ∀ c ∈ cs, I.ext c = J.ext c := fun c hm =>
      ext_congr_ind hc hr hd ht c fun i hi => h i fun a ha => mem_inds_and hm (hi a ha)
    funext x; rw [Interp.ext, Interp.ext]
    apply propext
    exact ⟨fun h' c hm => (ih c hm) ▸ h' c hm, fun h' c hm => (ih c hm).symm ▸ h' c hm⟩
  | .or cs, h => by
    have ih : ∀ c ∈ cs, I.ext c = J.ext c := fun c hm =>
      ext_congr_ind hc hr hd ht c fun i hi => h i fun a ha => mem_inds_or hm (hi a ha)
    funext x; rw [Interp.ext, Interp.ext]
    apply propext
    exact ⟨fun ⟨c, hm, h'⟩ => ⟨c, hm, (ih c hm) ▸ h'⟩,
      fun ⟨c, hm, h'⟩ => ⟨c, hm, (ih c hm).symm ▸ h'⟩⟩
  | .not c, h => by
    have ih := ext_congr_ind hc hr hd ht c fun i hi => h i fun a ha => by
      rw [namedIndividuals]; exact hi a ha
    funext x; rw [Interp.ext, Interp.ext, ih]
  | .some r c, h => by
    have ih := ext_congr_ind hc hr hd ht c fun i hi => h i fun a ha => by
      rw [namedIndividuals]; exact hi a ha
    funext x; rw [Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .all r c, h => by
    have ih := ext_congr_ind hc hr hd ht c fun i hi => h i fun a ha => by
      rw [namedIndividuals]; exact hi a ha
    funext x; rw [Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .min k r c, h => by
    have ih := ext_congr_ind hc hr hd ht c fun i hi => h i fun a ha => by
      rw [namedIndividuals]; exact hi a ha
    funext x; rw [Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .max k r c, h => by
    have ih := ext_congr_ind hc hr hd ht c fun i hi => h i fun a ha => by
      rw [namedIndividuals]; exact hi a ha
    funext x; rw [Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .exact k r c, h => by
    have ih := ext_congr_ind hc hr hd ht c fun i hi => h i fun a ha => by
      rw [namedIndividuals]; exact hi a ha
    funext x; rw [Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .oneOf as, h => by
    have hm : ∀ i ∈ as, I.ind i = J.ind i := fun i hi => h i fun a ha => by
      rw [namedIndividuals]; exact List.mem_flatMap.2 ⟨i, hi, ha⟩
    funext x; rw [Interp.ext, Interp.ext]
    apply propext
    exact ⟨fun ⟨i, hi, he⟩ => ⟨i, hi, he.trans (hm i hi)⟩,
      fun ⟨i, hi, he⟩ => ⟨i, hi, he.trans (hm i hi).symm⟩⟩
  | .hasValue r i, h => by
    have hm : I.ind i = J.ind i := h i fun a ha => by rw [namedIndividuals]; exact ha
    funext x; rw [Interp.ext, Interp.ext, hm, Interp.prop_congr hr]
  | .hasSelf r, _ => by funext x; rw [Interp.ext, Interp.ext, Interp.prop_congr hr]
  | .dataSome p r, _ | .dataAll p r, _ | .dataHasValue p r, _ | .dataMin _ p r, _
  | .dataMax _ p r, _ | .dataExact _ p r, _ => by
    funext x
    rw [Interp.ext, Interp.ext]
    cases p <;> simp [Interp.dp, Interp.drExt, hd, ht]
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

end ContextCalculus.OWL

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ

variable {DM : DatatypeMap} {D : Type}

/-! ## Satisfaction and individuals on the SHOIQ(D) part -/

/-- Satisfaction on the SHOIQ(D) knowledge-base part does not depend on the
named-individual list. -/
theorem sat_N_shoiqd {I : Interp DM D} {ax : Axiom} (h : ax.isSHOIQDKB = true) (N N' : List IRI) :
    I.sat N ax ↔ I.sat N' ax := by
  cases ax <;> first | exact Iff.rfl | simp [Axiom.isSHOIQDKB, Axiom.isSHIQD, Axiom.isSHI,
    Axiom.isSRI] at h

/-- **Satisfaction ignores the individuals an axiom does not mention**, on
the SHOIQ(D) knowledge-base part. -/
theorem sat_updN {I : Interp DM D} {f : IRI} {x : D} {ax : Axiom} (hax : ax.isSHOIQDKB = true)
    (hf : f ∉ ax.namedIndividuals) (N : List IRI) : (updI I f x).sat N ax ↔ I.sat N ax := by
  have hJ : ∀ i : Individual, (∀ a ∈ i.namedIRI, a ∈ ax.namedIndividuals) →
      (updI I f x).ind i = I.ind i := by
    intro i hm
    cases i with
    | anon _ => rfl
    | named a =>
      have ha : a ≠ f := fun h => hf (h ▸ hm a (by simp [Individual.namedIRI]))
      simp only [updI]
      exact Function.update_of_ne (fun h => ha (Individual.named.inj h)) _ _
  have he : ∀ c : ClassExpr, (∀ a ∈ c.namedIndividuals, a ∈ ax.namedIndividuals) →
      (updI I f x).ext c = I.ext c := fun c hc =>
    ClassExpr.ext_congr_ind (I := updI I f x) (J := I) rfl rfl rfl rfl c
      fun i hi => hJ i fun a ha => hc a (hi a ha)
  cases ax
  case subClassOf c d =>
    simp only [Interp.sat]
    rw [he c (fun a ha => by simp [Axiom.namedIndividuals, ha]),
      he d (fun a ha => by simp [Axiom.namedIndividuals, ha])]
  case equivalentClasses cs =>
    have ih : ∀ c ∈ cs, (updI I f x).ext c = I.ext c := fun c hc =>
      he c fun a ha => by simp only [Axiom.namedIndividuals, List.mem_flatMap]; exact ⟨c, hc, ha⟩
    simp only [Interp.sat]
    exact ⟨fun h c hm d hd x' hx => (ih d hd) ▸ h c hm d hd x' ((ih c hm).symm ▸ hx),
      fun h c hm d hd x' hx => (ih d hd).symm ▸ h c hm d hd x' ((ih c hm) ▸ hx)⟩
  case disjointClasses cs =>
    have ih : ∀ c ∈ cs, (updI I f x).ext c = I.ext c := fun c hc =>
      he c fun a ha => by simp only [Axiom.namedIndividuals, List.mem_flatMap]; exact ⟨c, hc, ha⟩
    simp only [Interp.sat]
    constructor
    · exact fun h => h.imp_of_mem fun hc hd h' x' => (ih _ hc) ▸ (ih _ hd) ▸ h' x'
    · exact fun h => h.imp_of_mem fun hc hd h' x' => (ih _ hc).symm ▸ (ih _ hd).symm ▸ h' x'
  case domain r c =>
    simp only [Interp.sat]
    rw [he c (fun a ha => by simp [Axiom.namedIndividuals, ha])]
    rfl
  case range r c =>
    simp only [Interp.sat]
    rw [he c (fun a ha => by simp [Axiom.namedIndividuals, ha])]
    rfl
  case dataDomain p c =>
    simp only [Interp.sat]
    rw [he c (fun a ha => by simp [Axiom.namedIndividuals, ha])]
    rfl
  case classAssertion c a =>
    simp only [Interp.sat]
    rw [he c (fun b hb => by simp [Axiom.namedIndividuals, hb]),
      hJ a (fun b hb => by simp [Axiom.namedIndividuals, hb])]
  case objectPropertyAssertion r a b =>
    simp only [Interp.sat]
    rw [hJ a (fun c hc => by simp [Axiom.namedIndividuals, hc]),
      hJ b (fun c hc => by simp [Axiom.namedIndividuals, hc])]
    rfl
  case negativeObjectPropertyAssertion r a b =>
    simp only [Interp.sat]
    rw [hJ a (fun c hc => by simp [Axiom.namedIndividuals, hc]),
      hJ b (fun c hc => by simp [Axiom.namedIndividuals, hc])]
    rfl
  case sameIndividual as =>
    have hm : ∀ a ∈ as, (updI I f x).ind a = I.ind a := fun a ha =>
      hJ a (fun c hc => by
        simp only [Axiom.namedIndividuals, List.mem_flatMap]; exact ⟨a, ha, hc⟩)
    simp only [Interp.sat]
    constructor
    · intro h a ha b hb; rw [← hm a ha, ← hm b hb]; exact h a ha b hb
    · intro h a ha b hb; rw [hm a ha, hm b hb]; exact h a ha b hb
  case differentIndividuals as =>
    have hm : ∀ a ∈ as, (updI I f x).ind a = I.ind a := fun a ha =>
      hJ a (fun c hc => by
        simp only [Axiom.namedIndividuals, List.mem_flatMap]; exact ⟨a, ha, hc⟩)
    simp only [Interp.sat]
    constructor
    · exact List.Pairwise.imp_of_mem fun ha hb h => by rwa [← hm _ ha, ← hm _ hb]
    · exact List.Pairwise.imp_of_mem fun ha hb h => by rwa [hm _ ha, hm _ hb]
  case dataPropertyAssertion p a l =>
    simp only [Interp.sat]
    rw [hJ a (fun c hc => by simp [Axiom.namedIndividuals, hc])]
    rfl
  case negativeDataPropertyAssertion p a l =>
    simp only [Interp.sat]
    rw [hJ a (fun c hc => by simp [Axiom.namedIndividuals, hc])]
    rfl
  case declareNamedIndividual a => simp only [Interp.sat]
  case hasKey c rs ps => simp [Axiom.isSHOIQDKB, Axiom.isSHIQD, Axiom.isSHI, Axiom.isSRI] at hax
  all_goals
    exact sat_congr_cls (I := updI I f x) (J := I) rfl rfl rfl
      (by simpa [Axiom.isSHOIQDKB] using hax) (fun _ _ => rfl) N N

theorem model_updN {O : Ontology} (hO : O.isSHOIQDKB = true) {I : Interp DM D} {f : IRI}
    (hf : f ∉ O.namedIndividuals) (x : D) : OWL.Model O (updI I f x) ↔ OWL.Model O I := by
  have hO' : ∀ a ∈ O.axioms, a.isSHOIQDKB = true := by
    simpa [Ontology.isSHOIQDKB, List.all_eq_true] using hO
  have hfa : ∀ a ∈ O.axioms, f ∉ a.namedIndividuals := fun a ha hm =>
    hf (List.mem_flatMap.2 ⟨a, ha, hm⟩)
  simp only [OWL.Model]
  exact forall_congr' fun a => imp_congr_right fun ha => sat_updN (hO' a ha) (hfa a ha) _

theorem isSHOIQDKB_addAxs {O : Ontology} {L : List Axiom} :
    (addAxs O L).isSHOIQDKB = (O.isSHOIQDKB && L.all Axiom.isSHOIQDKB) := by
  simp [addAxs, Ontology.isSHOIQDKB, List.all_append]

theorem model_addAxsN {O : Ontology} {L : List Axiom} (hO : O.isSHOIQDKB = true)
    (hL : ∀ ax ∈ L, ax.isSHOIQDKB = true) (I : Interp DM D) :
    OWL.Model (addAxs O L) I ↔ OWL.Model O I ∧ ∀ ax ∈ L, I.sat [] ax := by
  have hO' : ∀ a ∈ O.axioms, a.isSHOIQDKB = true := by
    simpa [Ontology.isSHOIQDKB, List.all_eq_true] using hO
  simp only [OWL.Model, addAxs, List.mem_append]
  constructor
  · intro h
    exact ⟨fun a ha => (sat_N_shoiqd (hO' a ha) _ _).1 (h a (Or.inl ha)),
      fun a ha => (sat_N_shoiqd (hL a ha) _ _).1 (h a (Or.inr ha))⟩
  · rintro ⟨h1, h2⟩ a (ha | ha)
    · exact (sat_N_shoiqd (hO' a ha) _ _).1 (h1 a ha)
    · exact (sat_N_shoiqd (hL a ha) _ _).1 (h2 a ha)

/-! ## The translation -/

/-- The translation of the SHOIQ(D) route. -/
def translateSHOIQD (O : Ontology) (requested : List IRI) : Option SRIQDKBTranslation :=
  if O.isSHOIQDKB then translateSRIQDKB (nomOntD O requested) (requested ++ nomNames O requested)
  else none

/-- The `SRIQN` data ontology of a translation. -/
def dosn (T : SRIQDKBTranslation) (L : List IRI) :
    SRIQN.DOntology (Fin T.obj.conceptCount) (Fin T.obj.roleCount) (Fin T.dps.length)
      (Fin T.tab.length) :=
  T.ontology.map SRIQN.DClause.base ++ (nomIxs T.obj L).map fun a => .nom (id a)

theorem dbase_dosn (T : SRIQDKBTranslation) (L : List IRI) : SRIQN.dbase (dosn T L) = T.ontology :=
  SRIQN.Proc.dbase_map_noms _ _ _

theorem dnoms_dosn (T : SRIQDKBTranslation) (L : List IRI) :
    SRIQN.dnoms (dosn T L) = nomIxs T.obj L := by
  simp [dosn, SRIQN.dnoms, List.filterMap_append, List.filterMap_map]

theorem translateSRIQDKB_obj {O : Ontology} {requested extra : List IRI} {T : SRIQDKBTranslation}
    (h : translateSRIQDKB O requested extra = some T) :
    translateSRIQKB (objOntK O (SRIQKB.defBase O requested))
      (requested ++ freshNames (SRIQKB.defBase O requested) (tableK O)) extra = some T.obj ∧
    T.abox = T.obj.abox.map ContextCalculus.SRIQD.Assertion.obj := by
  unfold translateSRIQDKB at h
  split_ifs at h
  dsimp only at h
  split at h
  · cases h
  rename_i Tobj hTobj
  split at h
  swap
  · cases h
  cases h
  exact ⟨hTobj, rfl⟩

theorem translateSRIQKB_abox_nil {O : Ontology} {requested extra : List IRI} {T : SRIQKBTranslation}
    (h : translateSRIQKB O requested extra = some T)
    (hna : ∀ ax ∈ O.axioms, ax.isAssertion = false) : T.abox = [] := by
  unfold translateSRIQKB at h
  dsimp only at h
  split at h
  · split at h
    · obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.1 h
      refine collect_nil hA fun p hp => ?_
      obtain ⟨ax, j⟩ := p
      exact assertsOf_nonAssert (hna ax (SRIQKB.mem_of_zipIdx hp)) j
    · simp at h
  · simp at h

theorem objOntK_nonAssert {O : Ontology}
    (hna : ∀ ax ∈ O.axioms, ax.isSHIQD = true ∧ ax.isAssertion = false)
    (base : String) : ∀ ax ∈ (objOntK O base).axioms, ax.isAssertion = false := by
  intro ax hax
  obtain ⟨ax', hax', rfl⟩ := List.mem_map.1 hax
  obtain ⟨ax0, h0, h'⟩ := List.mem_flatMap.1 hax'
  obtain ⟨h1, h2⟩ := hna ax0 h0
  cases ax0 <;> first
    | (simp [Axiom.isSHIQD, Axiom.isSHI, Axiom.isSRI] at h1; done)
    | (simp [Axiom.isAssertion] at h2; done)
    | (simp only [rwAxiomK, rwAxiom, List.mem_singleton, List.not_mem_nil] at h'
       subst h'; rfl)
    | (simp [rwAxiomK, rwAxiom] at h'; done)

variable {O : Ontology} {requested : List IRI} {T : SRIQDKBTranslation}

theorem translateSHOIQD_spec (h : translateSHOIQD O requested = some T) :
    O.isSHOIQDKB = true ∧
      translateSRIQDKB (nomOntD O requested) (requested ++ nomNames O requested) = some T := by
  unfold translateSHOIQD at h
  split at h
  · exact ⟨by assumption, h⟩
  · simp at h

theorem translateSHOIQD_isSome (hO : O.isSHOIQDKB = true) (requested : List IRI) :
    (translateSHOIQD O requested).isSome = true := by
  unfold translateSHOIQD
  rw [if_pos hO]
  exact translateSRIQDKB_isSome _ _ (nomOntD_isSHIQDKB hO requested)

theorem translateSHOIQD_abox (h : translateSHOIQD O requested = some T) : T.abox = [] := by
  obtain ⟨hO, hT⟩ := translateSHOIQD_spec h
  obtain ⟨hobj, ha⟩ := translateSRIQDKB_obj hT
  rw [ha, translateSRIQKB_abox_nil hobj (objOntK_nonAssert
    (fun ax hax => nomOntD_isSHIQD hO requested ax hax) _)]
  rfl

theorem named_obj (h : translateSHOIQD O requested = some T) {a : IRI}
    (ha : a ∈ requested ++ nomNames O requested) : a ∈ T.obj.named := by
  obtain ⟨-, hT⟩ := translateSHOIQD_spec h
  obtain ⟨hobj, -⟩ := translateSRIQDKB_obj hT
  rw [(translateSRIQKB_spec hobj).2.1]
  exact List.mem_eraseDups.2 (List.mem_append_left _ ha)

theorem nomD_mem (h : translateSHOIQD O requested = some T) {a : IRI} (ha : a ∈ O.individualNames)
    {x : Fin T.obj.conceptCount} (hx : nameIx T.obj (nmOf O requested a) = some x) :
    x ∈ SRIQN.dnoms (dosn T (nomNames O requested)) := by
  rw [dnoms_dosn]
  exact List.mem_filterMap.2 ⟨_, List.mem_map_of_mem ha, hx⟩

/-- **Up.** -/
theorem shoiqd_up (pat : String → String → Prop) (h : translateSHOIQD O requested = some T)
    {Dom : Type} [Nonempty Dom] (I : Interp (owl2MapP pat) Dom) (hI : OWL.Model O I) :
    ∃ (V : Type) (atom : Fin T.tab.length → V → Prop), owlTheory pat (spec T.tab) V atom ∧
      ∃ K : ContextCalculus.SRIQD.DInterp Dom V (Fin T.obj.conceptCount) (Fin T.obj.roleCount)
          (Fin T.dps.length),
        ContextCalculus.SRIQD.models atom K (SRIQN.dbase (dosn T (nomNames O requested))) ∧
        (∀ a ∈ SRIQN.dnoms (dosn T (nomNames O requested)), SRIQN.NomAt K.toInterp a) ∧
        ∀ s ∈ requested ++ nomNames O requested, ∀ (ix : Fin T.obj.conceptCount),
          nameIx T.obj s = some ix → ∀ y, K.c ix y ↔ (upI O requested I).cls s y := by
  obtain ⟨hO, hT⟩ := translateSHOIQD_spec h
  obtain ⟨V, atom, hΘ, K, -, hK, -, hc⟩ :=
    (translateSRIQDKB_maps pat hT).1 Dom (upI O requested I) (nomOntD_up hO requested hI)
  have hcs : ∀ s ∈ requested ++ nomNames O requested, ∀ (ix : Fin T.obj.conceptCount),
      nameIx T.obj s = some ix → ∀ y, K.c ix y ↔ (upI O requested I).cls s y := by
    intro s hs ix hix y
    obtain ⟨hi, he⟩ := nameIx_spec hix
    have := hc ix.val hi (he ▸ hs) y
    rw [he] at this
    exact this
  refine ⟨V, atom, hΘ, K, by rw [dbase_dosn]; exact hK, fun x hx => ?_, hcs⟩
  rw [dnoms_dosn] at hx
  obtain ⟨s, hs, hsx⟩ := List.mem_filterMap.1 hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
  exact ⟨I.ind (.named a), fun y => (hcs _ (List.mem_append_right _ hs) x hsx y).trans
    (upI_nom I ha y)⟩

/-- **Down.** -/
theorem shoiqd_down (pat : String → String → Prop) (h : translateSHOIQD O requested = some T)
    {Dom V : Type} [Nonempty Dom] {atom : Fin T.tab.length → V → Prop}
    (hΘ : owlTheory pat (spec T.tab) V atom)
    (K : ContextCalculus.SRIQD.DInterp Dom V (Fin T.obj.conceptCount) (Fin T.obj.roleCount)
      (Fin T.dps.length))
    (hK : ContextCalculus.SRIQD.models atom K (SRIQN.dbase (dosn T (nomNames O requested))))
    (hn : ∀ a ∈ SRIQN.dnoms (dosn T (nomNames O requested)), SRIQN.NomAt K.toInterp a) :
    ∃ I : Interp (owl2MapP pat) Dom, OWL.Model O I ∧
      (∀ s ∈ requested ++ nomNames O requested, ∀ (ix : Fin T.obj.conceptCount),
        nameIx T.obj s = some ix → ∀ y, I.cls s y ↔ K.c ix y) ∧
      ∀ a ∈ O.individualNames, ∀ ix, nameIx T.obj (nmOf O requested a) = some ix →
        ∀ x, K.c ix x ↔ x = I.ind (.named a) := by
  obtain ⟨hO, hT⟩ := translateSHOIQD_spec h
  obtain ⟨x0⟩ := (inferInstance : Nonempty Dom)
  rw [dbase_dosn] at hK
  obtain ⟨I0, hI0, hc⟩ := (translateSRIQDKB_maps pat hT).2 Dom V atom hΘ K (fun _ => x0) hK
    (by rw [translateSHOIQD_abox h]; intro _ h'; simp at h')
  have hcs : ∀ s ∈ requested ++ nomNames O requested, ∀ (ix : Fin T.obj.conceptCount),
      nameIx T.obj s = some ix → ∀ y, I0.cls s y ↔ K.c ix y := by
    intro s hs ix hix y
    obtain ⟨hi, he⟩ := nameIx_spec hix
    have := hc ix.val hi (he ▸ hs) y
    rw [he] at this
    exact this
  have hmem : ∀ a ∈ O.individualNames, nmOf O requested a ∈ requested ++ nomNames O requested :=
    fun a ha => List.mem_append_right _ (List.mem_map_of_mem ha)
  have hsing : ∀ a ∈ O.individualNames, ∃ x, ∀ y, I0.cls (nmOf O requested a) y ↔ y = x := by
    intro a ha
    obtain ⟨ix, hix⟩ := nameIx_some (named_obj h (hmem a ha))
    obtain ⟨z, hz⟩ := hn ix (nomD_mem h ha hix)
    exact ⟨z, fun y => (hcs _ (hmem a ha) ix hix y).trans (hz y)⟩
  obtain ⟨hM, hcls⟩ := nomOntD_down hO requested hI0 hsing
  refine ⟨downI O requested I0, hM, fun s hs ix hix y => by rw [hcls]; exact hcs s hs ix hix y,
    fun a ha ix hix x => ?_⟩
  rw [← hcs _ (hmem a ha) ix hix x]
  exact downI_nom (hsing a ha) x

theorem shoiqd_consistent (pat : String → String → Prop) (h : translateSHOIQD O requested = some T) :
    ConsistentAt (owl2MapP pat) O ↔
      SRIQN.ConsistentDN (owlTheory pat (spec T.tab)) (dosn T (nomNames O requested)) := by
  constructor
  · rintro ⟨Dom, hD, I, hI⟩
    obtain ⟨V, atom, hΘ, K, hK, hn, -⟩ := shoiqd_up pat h I hI
    exact ⟨Dom, V, hD, atom, hΘ, K, hK, hn⟩
  · rintro ⟨Dom, V, hD, atom, hΘ, K, hK, hn⟩
    obtain ⟨I, hI, -⟩ := shoiqd_down pat h hΘ K hK hn
    exact ⟨Dom, hD, I, hI⟩

/-! ## The route -/

instance {n m p q : Nat} (O : SRIQN.DOntology (Fin n) (Fin m) (Fin p) (Fin q)) :
    Decidable (SRIQN.IsC2aD O) := by
  unfold SRIQN.IsC2aD; infer_instance

/-- The checks: a SHIQ object part, C2a after transitivity removal, and
supported data atoms. -/
def kbdnOK (T : SRIQDKBTranslation) (L : List IRI) : Bool :=
  isSHIQB (ContextCalculus.SRIQD.objPart T.ontology) &&
    decide (SRIQN.IsC2aD (SRIQN.Proc.encTransDN (dosn T L))) &&
    (List.finRange T.tab.length).all fun p => drSupported (spec T.tab p)

/-- The small-cell threshold. -/
def kbdnBound (T : SRIQDKBTranslation) (L : List IRI) : Nat :=
  ContextCalculus.SRIQD.dbnd (SRIQN.dbase (SRIQN.Proc.encTransDN (dosn T L))) *
    (ContextCalculus.SRIQD.allG (allFrees (spec T.tab)).length).length

/-- Some part of the data theory accepts the `SRIQN` data ontology. -/
def kbdnConsistent (T : SRIQDKBTranslation) (L : List IRI) (hint : Option RawHint) : Bool :=
  let sp := spec T.tab
  let as := allBases sp
  let cs := cellsOf as
  SRIQN.consistentPartsN (dosn T L) cs (cellSize as)
    (ContextCalculus.SRIQD.splitCell cs (cellSize as) (kbdnBound T L) (owlE sp)) (owlE sp)
    (hint.bind fun h => h.toHintN _ _)

theorem kbdnConsistent_iff (pat : String → String → Prop) {T : SRIQDKBTranslation} {L : List IRI}
    (hok : kbdnOK T L = true) (hint : Option RawHint) :
    kbdnConsistent T L hint = true ↔
      SRIQN.ConsistentDN (owlTheory pat (spec T.tab)) (dosn T L) := by
  simp only [kbdnOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨h1, h2⟩, h3⟩ := hok
  have hS : ContextCalculus.SRIQD.Proc.IsSHIQD (SRIQN.dbase (dosn T L)) := by
    unfold ContextCalculus.SRIQD.Proc.IsSHIQD
    rw [dbase_dosn]
    exact isSHIQ_of_isSHIQB h1
  have hsup : ∀ p, drSupported (spec T.tab p) = true := fun p =>
    List.all_eq_true.1 h3 p (List.mem_finRange p)
  have heq : owlTheory pat (spec T.tab) = ContextCalculus.SRIQD.cellTheory
      (cellOf (allBases (spec T.tab))) (owlE (spec T.tab)) := by
    funext V atom
    exact propext (owlTheory_iff pat hsup V atom)
  rw [heq]
  exact SRIQN.consistentPartsN_iff (cellSpec _) (le_refl (kbdnBound T L))
    ContextCalculus.SRIQD.splitCell_ok.1 ContextCalculus.SRIQD.splitCell_ok.2 hS (le_refl _) h2 _

/-- **Consistency of a SHOIQ(D) knowledge base in C2a** at the OWL 2
datatype map. -/
def owlSHOIQDC2aConsistent (O : OWL.Ontology) (hint : Option RawHint) : Option Bool :=
  match translateSHOIQD O [] with
  | none => none
  | some T => if kbdnOK T (nomNames O []) then some (kbdnConsistent T (nomNames O []) hint) else none

/-- **Soundness.** Every answer is consistency at `owl2MapP pat`, for every
reading of `xsd:pattern` and every hint. -/
theorem owlSHOIQDC2aConsistent_sound (pat : String → String → Prop) {O : OWL.Ontology}
    {hint : Option RawHint} {v : Bool} (h : owlSHOIQDC2aConsistent O hint = some v) :
    v = true ↔ ConsistentAt (owl2MapP pat) O := by
  unfold owlSHOIQDC2aConsistent at h
  split at h
  · cases h
  next T hT =>
    split at h
    · next hok =>
      simp only [Option.some.injEq] at h
      subst h
      rw [kbdnConsistent_iff pat hok, ← shoiqd_consistent pat hT]
    · cases h

/-- The checks of the route on the translation. -/
def SHOIQDC2aChecks (O : OWL.Ontology) : Prop :=
  ∀ T, translateSHOIQD O [] = some T → kbdnOK T (nomNames O []) = true

/-- **Completeness.** The route answers exactly on the SHOIQ(D)
knowledge-base part with the checks passed, for every hint. -/
theorem owlSHOIQDC2aConsistent_isSome_iff (O : OWL.Ontology) (hint : Option RawHint) :
    (owlSHOIQDC2aConsistent O hint).isSome = true ↔ O.isSHOIQDKB = true ∧ SHOIQDC2aChecks O := by
  constructor
  · intro h
    unfold owlSHOIQDC2aConsistent at h
    split at h
    · simp at h
    · next T hT =>
      split at h
      · next hok =>
        refine ⟨(translateSHOIQD_spec hT).1, fun T' hT' => ?_⟩
        rw [hT] at hT'
        cases hT'
        exact hok
      · simp at h
  · rintro ⟨hO, hc⟩
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 (translateSHOIQD_isSome hO [])
    unfold owlSHOIQDC2aConsistent
    rw [hT]
    dsimp only
    rw [if_pos (hc T hT)]
    rfl

/-! ## Rows -/

/-- The assertion added for a different row. -/
def diffAxs (a b : IRI) : List Axiom := [.sameIndividual [.named a, .named b]]

/-- The assertion added for a role row. -/
def roleAxs (r : ObjProp) (a b : IRI) : List Axiom :=
  [.negativeObjectPropertyAssertion r (.named a) (.named b)]

/-- The assertion added for a negative role row. -/
def nroleAxs (r : ObjProp) (a b : IRI) : List Axiom :=
  [.objectPropertyAssertion r (.named a) (.named b)]

/-- A row: the negated consistency of the extension. -/
def rowN (O : OWL.Ontology) (L : List Axiom) (hint : Option RawHint) : Option Bool :=
  (owlSHOIQDC2aConsistent (addAxs O L) hint).map (!·)

theorem rowN_of {O : Ontology} {L : List Axiom} {hint : Option RawHint} {v : Bool}
    (pat : String → String → Prop) (h : rowN O L hint = some v) :
    O.isSHOIQDKB = true ∧ (v = true ↔ ¬ ConsistentAt (owl2MapP pat) (addAxs O L)) := by
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h
  have hk : (addAxs O L).isSHOIQDKB = true :=
    ((owlSHOIQDC2aConsistent_isSome_iff (addAxs O L) hint).1 (by rw [hw]; rfl)).1
  rw [isSHOIQDKB_addAxs, Bool.and_eq_true] at hk
  refine ⟨hk.1, ?_⟩
  rw [← owlSHOIQDC2aConsistent_sound pat hw]
  cases w <;> simp

theorem rowN_complete {O : Ontology} {L : List Axiom} (hO : O.isSHOIQDKB = true)
    (hL : ∀ ax ∈ L, ax.isSHOIQDKB = true) (hc : SHOIQDC2aChecks (addAxs O L))
    (hint : Option RawHint) : (rowN O L hint).isSome = true := by
  unfold rowN
  rw [Option.isSome_map]
  exact (owlSHOIQDC2aConsistent_isSome_iff _ hint).2
    ⟨by rw [isSHOIQDKB_addAxs, hO, List.all_eq_true.2 hL]; rfl, hc⟩

theorem typeAxs_okN (C a : IRI) : ∀ ax ∈ typeAxs C a, ax.isSHOIQDKB = true := by
  simp [typeAxs, Axiom.isSHOIQDKB, ClassExpr.isALCOIQD, Individual.isNamed]

theorem sameAxs_okN (a b : IRI) : ∀ ax ∈ sameAxs a b, ax.isSHOIQDKB = true := by
  simp [sameAxs, Axiom.isSHOIQDKB, Individual.isNamed]

theorem subAxs_okN (O : Ontology) (A B : IRI) : ∀ ax ∈ subAxs O A B, ax.isSHOIQDKB = true := by
  simp [subAxs, Axiom.isSHOIQDKB, ClassExpr.isALCOIQD, Individual.isNamed]

theorem diffAxs_ok (a b : IRI) : ∀ ax ∈ diffAxs a b, ax.isSHOIQDKB = true := by
  simp [diffAxs, Axiom.isSHOIQDKB, Individual.isNamed]

theorem roleAxs_ok {r : ObjProp} (hr : r.isBasic = true) (a b : IRI) :
    ∀ ax ∈ roleAxs r a b, ax.isSHOIQDKB = true := by
  simp [roleAxs, Axiom.isSHOIQDKB, Individual.isNamed, hr]

theorem nroleAxs_ok {r : ObjProp} (hr : r.isBasic = true) (a b : IRI) :
    ∀ ax ∈ nroleAxs r a b, ax.isSHOIQDKB = true := by
  simp [nroleAxs, Axiom.isSHOIQDKB, Individual.isNamed, hr]

/-- **Type row**: decides `O ⊨ ClassAssertion(C a)`. -/
def owlSHOIQDTypeRow (O : OWL.Ontology) (C a : IRI) (hint : Option RawHint) : Option Bool :=
  rowN O (typeAxs C a) hint

/-- **Same row**: decides `O ⊨ SameIndividual(a b)`. -/
def owlSHOIQDSameRow (O : OWL.Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  rowN O (sameAxs a b) hint

/-- **Subsumption row**: decides `O ⊨ SubClassOf(A B)`. -/
def owlSHOIQDSubRow (O : OWL.Ontology) (A B : IRI) (hint : Option RawHint) : Option Bool :=
  rowN O (subAxs O A B) hint

/-- **Different row**: decides `O ⊨ DifferentIndividuals(a b)`. -/
def owlSHOIQDDiffRow (O : OWL.Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  rowN O (diffAxs a b) hint

/-- **Role row**: decides `O ⊨ ObjectPropertyAssertion(r a b)` for a basic `r`. -/
def owlSHOIQDRoleRow (O : OWL.Ontology) (r : ObjProp) (a b : IRI) (hint : Option RawHint) :
    Option Bool :=
  if r.isBasic then rowN O (roleAxs r a b) hint else none

/-- **Negative role row**: decides `O ⊨ NegativeObjectPropertyAssertion(r a b)`. -/
def owlSHOIQDNRoleRow (O : OWL.Ontology) (r : ObjProp) (a b : IRI) (hint : Option RawHint) :
    Option Bool :=
  if r.isBasic then rowN O (nroleAxs r a b) hint else none

theorem owlSHOIQDTypeRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {C a : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSHOIQDTypeRow O C a hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.classAssertion (.cls C) (.named a)) := by
  obtain ⟨hO, hv⟩ := rowN_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI
    by_contra hc
    refine hi Dom I ((model_addAxsN hO (typeAxs_okN C a) I).2 ⟨hI, ?_⟩)
    simpa [typeAxs, Interp.sat, Interp.ext] using hc
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsN hO (typeAxs_okN C a) I).1 hI
    have := he Dom I hI
    simp only [typeAxs, List.mem_singleton, forall_eq, Interp.sat, Interp.ext] at hs this
    exact hs this

theorem sat_diff {Dom : Type} (I : Interp DM Dom) (N : List IRI) (a b : IRI) :
    I.sat N (.differentIndividuals [.named a, .named b]) ↔ I.ind (.named a) ≠ I.ind (.named b) := by
  simp [Interp.sat]

theorem owlSHOIQDSameRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {a b : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSHOIQDSameRow O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.sameIndividual [.named a, .named b]) := by
  obtain ⟨hO, hv⟩ := rowN_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI
    rw [sat_same]
    by_contra hc
    refine hi Dom I ((model_addAxsN hO (sameAxs_okN a b) I).2 ⟨hI, ?_⟩)
    simp only [sameAxs, List.mem_singleton, forall_eq]
    exact (sat_diff I _ a b).2 hc
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsN hO (sameAxs_okN a b) I).1 hI
    have := (sat_same I _ a b).1 (he Dom I hI)
    simp only [sameAxs, List.mem_singleton, forall_eq] at hs
    exact (sat_diff I _ a b).1 hs this

theorem owlSHOIQDSubRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {A B : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSHOIQDSubRow O A B hint = some v) :
    v = true ↔ EntailsSubAt (owl2MapP pat) O A B := by
  obtain ⟨hO, hv⟩ := rowN_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI x hA
    by_contra hB
    have hU := (model_updN hO (freshInd_not_mem O) x).2 hI
    refine hi Dom (updI I (freshInd O) x) ((model_addAxsN hO (subAxs_okN O A B) _).2 ⟨hU, ?_⟩)
    simp only [subAxs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Interp.sat, Interp.ext, updI, Function.update_self]
    exact ⟨hA, hB⟩
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsN hO (subAxs_okN O A B) I).1 hI
    simp only [subAxs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Interp.sat, Interp.ext] at hs
    exact hs.2 (he Dom I hI _ hs.1)

theorem owlSHOIQDDiffRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {a b : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSHOIQDDiffRow O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.differentIndividuals [.named a, .named b]) := by
  obtain ⟨hO, hv⟩ := rowN_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  have hd : ∀ {Dom : Type} (I : Interp (owl2MapP pat) Dom) (N : List IRI),
      I.sat N (.differentIndividuals [.named a, .named b]) ↔ ¬ I.ind (.named a) = I.ind (.named b) := by
    intro Dom I N
    simp [Interp.sat]
  constructor
  · intro hi Dom _ I hI
    rw [hd]
    intro hc
    refine hi Dom I ((model_addAxsN hO (diffAxs_ok a b) I).2 ⟨hI, ?_⟩)
    simp only [diffAxs, List.mem_singleton, forall_eq]
    exact (sat_same I _ a b).2 hc
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsN hO (diffAxs_ok a b) I).1 hI
    simp only [diffAxs, List.mem_singleton, forall_eq] at hs
    exact (hd I _).1 (he Dom I hI) ((sat_same I _ a b).1 hs)

theorem owlSHOIQDRoleRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {r : ObjProp}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : owlSHOIQDRoleRow O r a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.objectPropertyAssertion r (.named a) (.named b)) := by
  unfold owlSHOIQDRoleRow at h
  split at h
  swap
  · cases h
  rename_i hr
  obtain ⟨hO, hv⟩ := rowN_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI
    by_contra hc
    refine hi Dom I ((model_addAxsN hO (roleAxs_ok hr a b) I).2 ⟨hI, ?_⟩)
    simpa [roleAxs, Interp.sat] using hc
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsN hO (roleAxs_ok hr a b) I).1 hI
    simp only [roleAxs, List.mem_singleton, forall_eq, Interp.sat] at hs
    exact hs (he Dom I hI)

theorem owlSHOIQDNRoleRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {r : ObjProp}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : owlSHOIQDNRoleRow O r a b hint = some v) :
    v = true ↔
      EntailsAt (owl2MapP pat) O (.negativeObjectPropertyAssertion r (.named a) (.named b)) := by
  unfold owlSHOIQDNRoleRow at h
  split at h
  swap
  · cases h
  rename_i hr
  obtain ⟨hO, hv⟩ := rowN_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI hc
    exact hi Dom I ((model_addAxsN hO (nroleAxs_ok hr a b) I).2 ⟨hI, by simpa [nroleAxs, Interp.sat] using hc⟩)
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsN hO (nroleAxs_ok hr a b) I).1 hI
    simp only [nroleAxs, List.mem_singleton, forall_eq, Interp.sat] at hs
    exact he Dom I hI hs

theorem owlSHOIQDTypeRow_complete {O : OWL.Ontology} (C a : IRI) (hO : O.isSHOIQDKB = true)
    (hc : SHOIQDC2aChecks (addAxs O (typeAxs C a))) (hint : Option RawHint) :
    (owlSHOIQDTypeRow O C a hint).isSome = true :=
  rowN_complete hO (typeAxs_okN C a) hc hint

theorem owlSHOIQDSameRow_complete {O : OWL.Ontology} (a b : IRI) (hO : O.isSHOIQDKB = true)
    (hc : SHOIQDC2aChecks (addAxs O (sameAxs a b))) (hint : Option RawHint) :
    (owlSHOIQDSameRow O a b hint).isSome = true :=
  rowN_complete hO (sameAxs_okN a b) hc hint

theorem owlSHOIQDSubRow_complete {O : OWL.Ontology} (A B : IRI) (hO : O.isSHOIQDKB = true)
    (hc : SHOIQDC2aChecks (addAxs O (subAxs O A B))) (hint : Option RawHint) :
    (owlSHOIQDSubRow O A B hint).isSome = true :=
  rowN_complete hO (subAxs_okN O A B) hc hint

theorem owlSHOIQDDiffRow_complete {O : OWL.Ontology} (a b : IRI) (hO : O.isSHOIQDKB = true)
    (hc : SHOIQDC2aChecks (addAxs O (diffAxs a b))) (hint : Option RawHint) :
    (owlSHOIQDDiffRow O a b hint).isSome = true :=
  rowN_complete hO (diffAxs_ok a b) hc hint

theorem owlSHOIQDRoleRow_complete {O : OWL.Ontology} {r : ObjProp} (hr : r.isBasic = true)
    (a b : IRI) (hO : O.isSHOIQDKB = true) (hc : SHOIQDC2aChecks (addAxs O (roleAxs r a b)))
    (hint : Option RawHint) : (owlSHOIQDRoleRow O r a b hint).isSome = true := by
  unfold owlSHOIQDRoleRow
  rw [if_pos hr]
  exact rowN_complete hO (roleAxs_ok hr a b) hc hint

theorem owlSHOIQDNRoleRow_complete {O : OWL.Ontology} {r : ObjProp} (hr : r.isBasic = true)
    (a b : IRI) (hO : O.isSHOIQDKB = true) (hc : SHOIQDC2aChecks (addAxs O (nroleAxs r a b)))
    (hint : Option RawHint) : (owlSHOIQDNRoleRow O r a b hint).isSome = true := by
  unfold owlSHOIQDNRoleRow
  rw [if_pos hr]
  exact rowN_complete hO (nroleAxs_ok hr a b) hc hint

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.shoiqd_consistent
#print axioms ContextCalculus.OWLFrontend.owlSHOIQDC2aConsistent_sound
#print axioms ContextCalculus.OWLFrontend.owlSHOIQDC2aConsistent_isSome_iff
#print axioms ContextCalculus.OWLFrontend.owlSHOIQDTypeRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSHOIQDSameRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSHOIQDSubRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSHOIQDDiffRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSHOIQDRoleRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSHOIQDNRoleRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSHOIQDTypeRow_complete
#print axioms ContextCalculus.OWLFrontend.owlSHOIQDSameRow_complete
#print axioms ContextCalculus.OWLFrontend.owlSHOIQDSubRow_complete
#print axioms ContextCalculus.OWLFrontend.owlSHOIQDDiffRow_complete
#print axioms ContextCalculus.OWLFrontend.owlSHOIQDRoleRow_complete
#print axioms ContextCalculus.OWLFrontend.owlSHOIQDNRoleRow_complete
