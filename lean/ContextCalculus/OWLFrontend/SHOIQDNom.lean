import ContextCalculus.OWLFrontend.SHOIQNom
import ContextCalculus.OWLFrontend.SRIQDKBCorrect

/-!
# Nominals with data: the SHOIQ(D) knowledge-base part (stage C2a)

`docs/V1.7.0-C2-NOMINALS-DESIGN.md`, sections 1 and 6. The SHOIQ(D)
knowledge-base part (`Ontology.isSHOIQDKB`) is the SHIQ(D)
knowledge-base part with `ObjectOneOf` and `ObjectHasValue` over named
individuals in any class position. `nomOntD` rewrites it as `nomOnt` does
(`rwC` leaves data expressions alone) and turns the data property
assertions into TBox axioms on nominal classes
(`DataPropertyAssertion(p a l)` becomes `SubClassOf(N_a DataHasValue(p l))`).
The result is in the SHIQ(D) part without assertions, so the SHIQ(D)
knowledge-base translation applies; `nomOntD_up` and `nomOntD_down` are
the model maps.
-/

namespace ContextCalculus.OWL

/-- ALCIQD class expressions with nominals over named individuals. -/
def ClassExpr.isALCOIQD : ClassExpr → Bool
  | .cls _ | .thing | .nothing => true
  | .and cs | .or cs => cs.attach.all fun ⟨c, _⟩ => c.isALCOIQD
  | .not c => c.isALCOIQD
  | .some r c | .all r c => r.isBasic && c.isALCOIQD
  | .min _ r c | .max _ r c | .exact _ r c => r.isBasic && c.isALCOIQD
  | .dataSome p _ | .dataAll p _ | .dataHasValue p _ => p.isNamed
  | .dataMin _ p _ | .dataMax _ p _ | .dataExact _ p _ => p.isNamed
  | .oneOf as => as.all Individual.isNamed
  | .hasValue r a => r.isBasic && a.isNamed
  | .hasSelf _ => false
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

/-- An axiom of the SHOIQ(D) knowledge-base part. -/
def Axiom.isSHOIQDKB : Axiom → Bool
  | .subClassOf c d => c.isALCOIQD && d.isALCOIQD
  | .equivalentClasses cs | .disjointClasses cs => cs.all ClassExpr.isALCOIQD
  | .domain r c | .range r c => r.isBasic && c.isALCOIQD
  | .dataDomain p c => p.isNamed && c.isALCOIQD
  | .classAssertion c a => c.isALCOIQD && a.isNamed
  | .objectPropertyAssertion r a b => r.isBasic && a.isNamed && b.isNamed
  | .negativeObjectPropertyAssertion r a b => r.isBasic && a.isNamed && b.isNamed
  | .sameIndividual as | .differentIndividuals as => as.all Individual.isNamed
  | .declareNamedIndividual _ => true
  | .dataPropertyAssertion p a _ | .negativeDataPropertyAssertion p a _ => p.isNamed && a.isNamed
  | ax => ax.isSHIQD

def Ontology.isSHOIQDKB (O : Ontology) : Bool := O.axioms.all Axiom.isSHOIQDKB

end ContextCalculus.OWL

namespace ContextCalculus.OWLFrontend.SHOIQ

open ContextCalculus.OWL SHIQD

/-- The axioms of the rewriting of one axiom, with data. -/
def rwAxD (nm : IRI → IRI) : Axiom → List Axiom
  | .subClassOf c d => [.subClassOf (rwC nm c) (rwC nm d)]
  | .equivalentClasses cs => [.equivalentClasses (cs.map (rwC nm))]
  | .disjointClasses cs => [.disjointClasses (cs.map (rwC nm))]
  | .domain r c => [.domain r (rwC nm c)]
  | .range r c => [.range r (rwC nm c)]
  | .dataDomain p c => [.dataDomain p (rwC nm c)]
  | .classAssertion c a => [.subClassOf (nomI nm a) (rwC nm c)]
  | .objectPropertyAssertion r a b => [.subClassOf (nomI nm a) (.some r (nomI nm b))]
  | .negativeObjectPropertyAssertion r a b =>
      [.subClassOf (nomI nm a) (.all r (.not (nomI nm b)))]
  | .sameIndividual as => [.equivalentClasses (as.map (nomI nm))]
  | .differentIndividuals as => [.disjointClasses (as.map (nomI nm))]
  | .dataPropertyAssertion p a l => [.subClassOf (nomI nm a) (.dataHasValue p l)]
  | .negativeDataPropertyAssertion p a l =>
      [.subClassOf (nomI nm a) (.not (.dataHasValue p l))]
  | .declareNamedIndividual _ => []
  | ax => [ax]

/-- The rewritten ontology, with data. -/
def nomOntD (O : Ontology) (requested : List IRI) : Ontology :=
  ⟨O.axioms.flatMap (rwAxD (nmOf O requested))⟩

variable {DM : DatatypeMap} {Dom : Type}

theorem nomI_isALCIQD (nm : IRI → IRI) (i : Individual) : (nomI nm i).isALCIQD = true := by
  cases i <;> simp [nomI, ClassExpr.isALCIQD]

theorem nomOneOf_isALCIQD (nm : IRI → IRI) (as : List Individual) :
    (nomOneOf nm as).isALCIQD = true := by
  unfold nomOneOf
  split
  · exact nomI_isALCIQD nm _
  · rw [ClassExpr.isALCIQD]
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall, List.mem_map]
    rintro _ ⟨i, -, rfl⟩
    exact nomI_isALCIQD nm i

theorem rwC_isALCIQD (nm : IRI → IRI) : ∀ c : ClassExpr, c.isALCOIQD = true →
    (rwC nm c).isALCIQD = true
  | .cls _, _ => by rw [rwC, ClassExpr.isALCIQD]
  | .thing, _ => by rw [rwC, ClassExpr.isALCIQD]
  | .nothing, _ => by rw [rwC, ClassExpr.isALCIQD]
  | .and cs, h => by
    rw [ClassExpr.isALCOIQD] at h
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at h
    rw [rwC, ClassExpr.isALCIQD]
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall, List.mem_map,
      Subtype.exists]
    rintro _ ⟨c, hc, -, rfl⟩
    exact rwC_isALCIQD nm c (h c hc)
  | .or cs, h => by
    rw [ClassExpr.isALCOIQD] at h
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at h
    rw [rwC, ClassExpr.isALCIQD]
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall, List.mem_map,
      Subtype.exists]
    rintro _ ⟨c, hc, -, rfl⟩
    exact rwC_isALCIQD nm c (h c hc)
  | .not c, h => by
    rw [ClassExpr.isALCOIQD] at h
    rw [rwC, ClassExpr.isALCIQD]
    exact rwC_isALCIQD nm c h
  | .some r c, h => by
    rw [ClassExpr.isALCOIQD, Bool.and_eq_true] at h
    rw [rwC, ClassExpr.isALCIQD, Bool.and_eq_true]
    exact ⟨h.1, rwC_isALCIQD nm c h.2⟩
  | .all r c, h => by
    rw [ClassExpr.isALCOIQD, Bool.and_eq_true] at h
    rw [rwC, ClassExpr.isALCIQD, Bool.and_eq_true]
    exact ⟨h.1, rwC_isALCIQD nm c h.2⟩
  | .min k r c, h => by
    rw [ClassExpr.isALCOIQD, Bool.and_eq_true] at h
    rw [rwC, ClassExpr.isALCIQD, Bool.and_eq_true]
    exact ⟨h.1, rwC_isALCIQD nm c h.2⟩
  | .max k r c, h => by
    rw [ClassExpr.isALCOIQD, Bool.and_eq_true] at h
    rw [rwC, ClassExpr.isALCIQD, Bool.and_eq_true]
    exact ⟨h.1, rwC_isALCIQD nm c h.2⟩
  | .exact k r c, h => by
    rw [ClassExpr.isALCOIQD, Bool.and_eq_true] at h
    rw [rwC, ClassExpr.isALCIQD, Bool.and_eq_true]
    exact ⟨h.1, rwC_isALCIQD nm c h.2⟩
  | .oneOf as, _ => by
    rw [rwC]
    exact nomOneOf_isALCIQD nm as
  | .hasValue r a, h => by
    rw [ClassExpr.isALCOIQD, Bool.and_eq_true] at h
    rw [rwC, ClassExpr.isALCIQD, Bool.and_eq_true]
    exact ⟨h.1, nomI_isALCIQD nm a⟩
  | .hasSelf _, h => by rw [ClassExpr.isALCOIQD] at h; exact absurd h (by simp)
  | .dataSome .., h | .dataAll .., h | .dataHasValue .., h | .dataMin .., h
  | .dataMax .., h | .dataExact .., h => by
    rw [ClassExpr.isALCOIQD] at h
    rw [rwC, ClassExpr.isALCIQD]
    exact h
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)



/-- The rewriting of an axiom is in the SHIQ(D) part and has no
assertions. -/
theorem rwAxD_isSHIQD (nm : IRI → IRI) {ax : Axiom} (hax : ax.isSHOIQDKB = true) :
    ∀ ax' ∈ rwAxD nm ax, ax'.isSHIQD = true ∧ ax'.isAssertion = false := by
  have hcs : ∀ cs : List ClassExpr, cs.all ClassExpr.isALCOIQD = true →
      (cs.map (rwC nm)).all ClassExpr.isALCIQD = true := by
    intro cs h
    simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at h ⊢
    exact fun c hc => rwC_isALCIQD nm c (h c hc)
  have his : ∀ as : List Individual, (as.map (nomI nm)).all ClassExpr.isALCIQD = true := by
    intro as
    simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    exact fun i _ => nomI_isALCIQD nm i
  intro ax' hax'
  cases ax with
  | subClassOf c d =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [rwAxD, List.mem_singleton] at hax'
    subst hax'
    simp [Axiom.isSHIQD, Axiom.isAssertion, rwC_isALCIQD nm _ hax.1, rwC_isALCIQD nm _ hax.2]
  | equivalentClasses cs =>
    simp only [Axiom.isSHOIQDKB] at hax
    simp only [rwAxD, List.mem_singleton] at hax'
    subst hax'
    simp only [Axiom.isSHIQD, Axiom.isAssertion, hcs _ hax, and_self]
  | disjointClasses cs =>
    simp only [Axiom.isSHOIQDKB] at hax
    simp only [rwAxD, List.mem_singleton] at hax'
    subst hax'
    simp only [Axiom.isSHIQD, Axiom.isAssertion, hcs _ hax, and_self]
  | domain r c =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [rwAxD, List.mem_singleton] at hax'
    subst hax'
    simp [Axiom.isSHIQD, Axiom.isAssertion, hax.1, rwC_isALCIQD nm _ hax.2]
  | range r c =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [rwAxD, List.mem_singleton] at hax'
    subst hax'
    simp [Axiom.isSHIQD, Axiom.isAssertion, hax.1, rwC_isALCIQD nm _ hax.2]
  | dataDomain p c =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [rwAxD, List.mem_singleton] at hax'
    subst hax'
    simp [Axiom.isSHIQD, Axiom.isAssertion, hax.1, rwC_isALCIQD nm _ hax.2]
  | classAssertion c i =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [rwAxD, List.mem_singleton] at hax'
    subst hax'
    simp [Axiom.isSHIQD, Axiom.isAssertion, nomI_isALCIQD, rwC_isALCIQD nm _ hax.1]
  | objectPropertyAssertion r i i' =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [rwAxD, List.mem_singleton] at hax'
    subst hax'
    simp [Axiom.isSHIQD, Axiom.isAssertion, ClassExpr.isALCIQD, nomI_isALCIQD, hax.1.1]
  | negativeObjectPropertyAssertion r i i' =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [rwAxD, List.mem_singleton] at hax'
    subst hax'
    simp [Axiom.isSHIQD, Axiom.isAssertion, ClassExpr.isALCIQD, nomI_isALCIQD, hax.1.1]
  | sameIndividual as =>
    simp only [rwAxD, List.mem_singleton] at hax'
    subst hax'
    simp only [Axiom.isSHIQD, Axiom.isAssertion, his, and_self]
  | differentIndividuals as =>
    simp only [rwAxD, List.mem_singleton] at hax'
    subst hax'
    simp only [Axiom.isSHIQD, Axiom.isAssertion, his, and_self]
  | dataPropertyAssertion p i l =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [rwAxD, List.mem_singleton] at hax'
    subst hax'
    simp [Axiom.isSHIQD, Axiom.isAssertion, ClassExpr.isALCIQD, nomI_isALCIQD, hax.1]
  | negativeDataPropertyAssertion p i l =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [rwAxD, List.mem_singleton] at hax'
    subst hax'
    simp [Axiom.isSHIQD, Axiom.isAssertion, ClassExpr.isALCIQD, nomI_isALCIQD, hax.1]
  | declareNamedIndividual _ => simp [rwAxD] at hax'
  | _ =>
    simp only [rwAxD, List.mem_singleton] at hax'
    subst hax'
    simp only [Axiom.isSHOIQDKB] at hax
    exact ⟨hax, by simp_all [Axiom.isAssertion, Axiom.isSHIQD, Axiom.isSHI, Axiom.isSRI]⟩

variable {I J : Interp DM Dom}

theorem rwC_extD {I J : Interp DM Dom} (hr : J.role = I.role) (hd : J.dprop = I.dprop)
    (ht : J.dtype = I.dtype) (nm : IRI → IRI) :
    ∀ c : ClassExpr, c.isALCOIQD = true → (∀ a ∈ c.names, J.cls a = I.cls a) →
      (∀ a ∈ c.namedIndividuals, ∀ x, J.cls (nm a) x ↔ x = I.ind (.named a)) →
      J.ext (rwC nm c) = I.ext c
  | .cls a, _, h, _ => by
    funext x; rw [rwC, Interp.ext, Interp.ext, h a (by simp [ClassExpr.names])]
  | .thing, _, _, _ => by funext x; rw [rwC, Interp.ext, Interp.ext]
  | .nothing, _, _, _ => by funext x; rw [rwC, Interp.ext, Interp.ext]
  | .and cs, hc, h, hn => by
    rw [ClassExpr.isALCOIQD] at hc
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at hc
    have ih : ∀ c ∈ cs, J.ext (rwC nm c) = I.ext c := fun c hm =>
      rwC_extD hr hd ht nm c (hc c hm) (fun a ha => h a (ClassExpr.mem_names_and hm ha))
        (fun a ha => hn a (ClassExpr.mem_inds_and hm ha))
    funext x; rw [rwC, Interp.ext, Interp.ext]
    apply propext
    constructor
    · intro H c hm
      exact (congrFun (ih c hm) x).mp (H _ (List.mem_map.2 ⟨⟨c, hm⟩, List.mem_attach _ _, rfl⟩))
    · intro H c' hc'
      obtain ⟨⟨c, hm⟩, -, rfl⟩ := List.mem_map.1 hc'
      exact (congrFun (ih c hm) x).mpr (H c hm)
  | .or cs, hc, h, hn => by
    rw [ClassExpr.isALCOIQD] at hc
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at hc
    have ih : ∀ c ∈ cs, J.ext (rwC nm c) = I.ext c := fun c hm =>
      rwC_extD hr hd ht nm c (hc c hm) (fun a ha => h a (ClassExpr.mem_names_or hm ha))
        (fun a ha => hn a (ClassExpr.mem_inds_or hm ha))
    funext x; rw [rwC, Interp.ext, Interp.ext]
    apply propext
    constructor
    · rintro ⟨c', hc', H⟩
      obtain ⟨⟨c, hm⟩, -, rfl⟩ := List.mem_map.1 hc'
      exact ⟨c, hm, (congrFun (ih c hm) x).mp H⟩
    · rintro ⟨c, hm, H⟩
      exact ⟨_, List.mem_map.2 ⟨⟨c, hm⟩, List.mem_attach _ _, rfl⟩, (congrFun (ih c hm) x).mpr H⟩
  | .not c, hc, h, hn => by
    rw [ClassExpr.isALCOIQD] at hc
    have ih := rwC_extD hr hd ht nm c hc (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      (fun a ha => hn a (by rw [ClassExpr.namedIndividuals]; exact ha))
    funext x; rw [rwC, Interp.ext, Interp.ext, ih]
  | .some r c, hc, h, hn => by
    rw [ClassExpr.isALCOIQD, Bool.and_eq_true] at hc
    have ih := rwC_extD hr hd ht nm c hc.2 (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      (fun a ha => hn a (by rw [ClassExpr.namedIndividuals]; exact ha))
    funext x; rw [rwC, Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .all r c, hc, h, hn => by
    rw [ClassExpr.isALCOIQD, Bool.and_eq_true] at hc
    have ih := rwC_extD hr hd ht nm c hc.2 (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      (fun a ha => hn a (by rw [ClassExpr.namedIndividuals]; exact ha))
    funext x; rw [rwC, Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .min k r c, hc, h, hn => by
    rw [ClassExpr.isALCOIQD, Bool.and_eq_true] at hc
    have ih := rwC_extD hr hd ht nm c hc.2 (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      (fun a ha => hn a (by rw [ClassExpr.namedIndividuals]; exact ha))
    funext x; rw [rwC, Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .max k r c, hc, h, hn => by
    rw [ClassExpr.isALCOIQD, Bool.and_eq_true] at hc
    have ih := rwC_extD hr hd ht nm c hc.2 (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      (fun a ha => hn a (by rw [ClassExpr.namedIndividuals]; exact ha))
    funext x; rw [rwC, Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .exact k r c, hc, h, hn => by
    rw [ClassExpr.isALCOIQD, Bool.and_eq_true] at hc
    have ih := rwC_extD hr hd ht nm c hc.2 (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      (fun a ha => hn a (by rw [ClassExpr.namedIndividuals]; exact ha))
    funext x; rw [rwC, Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .oneOf as, hc, _, hn => by
    rw [ClassExpr.isALCOIQD, List.all_eq_true] at hc
    have hn' : ∀ i ∈ as, ∀ a ∈ i.namedIRI, ∀ x, J.cls (nm a) x ↔ x = I.ind (.named a) :=
      fun i hi a ha => hn a (by rw [ClassExpr.namedIndividuals]; exact List.mem_flatMap.2 ⟨i, hi, ha⟩)
    funext x; rw [rwC, Interp.ext]
    exact propext (nomOneOf_ext hc hn' x)
  | .hasValue r i, hc, _, hn => by
    rw [ClassExpr.isALCOIQD, Bool.and_eq_true] at hc
    have hn' : ∀ a ∈ i.namedIRI, ∀ x, J.cls (nm a) x ↔ x = I.ind (.named a) :=
      fun a ha => hn a (by rw [ClassExpr.namedIndividuals]; exact ha)
    funext x; rw [rwC, Interp.ext, Interp.ext, Interp.prop_congr hr]
    apply propext
    constructor
    · rintro ⟨y, hy, H⟩
      rw [(nomI_ext hc.2 hn' y).1 H] at hy
      exact hy
    · intro H
      exact ⟨_, H, (nomI_ext hc.2 hn' _).2 rfl⟩
  | .hasSelf _, hc, _, _ => by rw [ClassExpr.isALCOIQD] at hc; exact absurd hc (by simp)
  | .dataSome p r, hc, _, _ | .dataAll p r, hc, _, _ | .dataHasValue p r, hc, _, _
  | .dataMin _ p r, hc, _, _ | .dataMax _ p r, hc, _, _ | .dataExact _ p r, hc, _, _ => by
    rw [ClassExpr.isALCOIQD] at hc
    rw [rwC]
    exact ext_congr_cls hr hd ht _ (by rw [ClassExpr.isALCIQD]; exact hc)
      (by simp [ClassExpr.names])
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)


/-- **Rewriting keeps satisfaction** of an axiom of the SHOIQ(D) part. -/
theorem sat_rwAxD (hr : J.role = I.role) (hd : J.dprop = I.dprop) (ht : J.dtype = I.dtype)
    (nm : IRI → IRI) {ax : Axiom} (hax : ax.isSHOIQDKB = true) (hc : ∀ a ∈ ax.classNames, J.cls a = I.cls a)
    (hn : ∀ a ∈ ax.namedIndividuals, ∀ x, J.cls (nm a) x ↔ x = I.ind (.named a))
    (N N' : List IRI) : (∀ ax' ∈ rwAxD nm ax, J.sat N ax') ↔ I.sat N' ax := by
  have hp := Interp.prop_congr hr
  have hdp : ∀ q : DataProp, J.dp q = I.dp q := fun q => by cases q <;> simp [Interp.dp, hd]
  cases ax with
  | subClassOf c d =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [Axiom.classNames, List.mem_append] at hc
    simp only [Axiom.namedIndividuals, List.mem_append] at hn
    simp only [rwAxD, List.mem_singleton, forall_eq, Interp.sat]
    rw [rwC_extD hr hd ht nm c hax.1 (fun a ha => hc a (Or.inl ha)) (fun a ha => hn a (Or.inl ha)),
      rwC_extD hr hd ht nm d hax.2 (fun a ha => hc a (Or.inr ha)) (fun a ha => hn a (Or.inr ha))]
  | equivalentClasses cs =>
    simp only [Axiom.isSHOIQDKB, List.all_eq_true] at hax
    simp only [Axiom.classNames, List.mem_flatMap] at hc
    simp only [Axiom.namedIndividuals, List.mem_flatMap] at hn
    have ih : ∀ c ∈ cs, J.ext (rwC nm c) = I.ext c := fun c hm =>
      rwC_extD hr hd ht nm c (hax c hm) (fun a ha => hc a ⟨c, hm, ha⟩) (fun a ha => hn a ⟨c, hm, ha⟩)
    simp only [rwAxD, List.mem_singleton, forall_eq, Interp.sat, List.mem_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    constructor
    · intro h c hm d hd x hx
      rw [← ih d hd]
      exact h c hm d hd x (by rw [ih c hm]; exact hx)
    · intro h c hm d hd x hx
      rw [ih d hd]
      exact h c hm d hd x (by rw [← ih c hm]; exact hx)
  | disjointClasses cs =>
    simp only [Axiom.isSHOIQDKB, List.all_eq_true] at hax
    simp only [Axiom.classNames, List.mem_flatMap] at hc
    simp only [Axiom.namedIndividuals, List.mem_flatMap] at hn
    have ih : ∀ c ∈ cs, J.ext (rwC nm c) = I.ext c := fun c hm =>
      rwC_extD hr hd ht nm c (hax c hm) (fun a ha => hc a ⟨c, hm, ha⟩) (fun a ha => hn a ⟨c, hm, ha⟩)
    simp only [rwAxD, List.mem_singleton, forall_eq, Interp.sat, List.pairwise_map]
    constructor
    · intro h
      exact h.imp_of_mem fun hc hd h' x => (ih _ hc) ▸ (ih _ hd) ▸ h' x
    · intro h
      exact h.imp_of_mem fun hc hd h' x => (ih _ hc).symm ▸ (ih _ hd).symm ▸ h' x
  | domain r c =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [Axiom.classNames] at hc
    simp only [Axiom.namedIndividuals] at hn
    simp only [rwAxD, List.mem_singleton, forall_eq, Interp.sat]
    rw [rwC_extD hr hd ht nm c hax.2 hc hn, hp]
  | range r c =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [Axiom.classNames] at hc
    simp only [Axiom.namedIndividuals] at hn
    simp only [rwAxD, List.mem_singleton, forall_eq, Interp.sat]
    rw [rwC_extD hr hd ht nm c hax.2 hc hn, hp]
  | classAssertion c i =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [Axiom.classNames] at hc
    simp only [Axiom.namedIndividuals, List.mem_append] at hn
    simp only [rwAxD, List.mem_singleton, forall_eq, Interp.sat]
    rw [rwC_extD hr hd ht nm c hax.1 hc (fun a ha => hn a (Or.inl ha))]
    have hi := nomI_ext (I := I) (J := J) (nm := nm) hax.2 (fun a ha => hn a (Or.inr ha))
    constructor
    · intro h
      exact h _ ((hi _).2 rfl)
    · intro h x hx
      rw [(hi x).1 hx]
      exact h
  | objectPropertyAssertion r i i' =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [Axiom.namedIndividuals, List.mem_append] at hn
    simp only [rwAxD, List.mem_singleton, forall_eq, Interp.sat, Interp.ext]
    have hi := nomI_ext (I := I) (J := J) (nm := nm) hax.1.2 (fun a ha => hn a (Or.inl ha))
    have hi' := nomI_ext (I := I) (J := J) (nm := nm) hax.2 (fun a ha => hn a (Or.inr ha))
    rw [hp]
    constructor
    · intro h
      obtain ⟨y, hy, hy'⟩ := h _ ((hi _).2 rfl)
      rw [(hi' y).1 hy'] at hy
      exact hy
    · intro h x hx
      rw [(hi x).1 hx]
      exact ⟨_, h, (hi' _).2 rfl⟩
  | negativeObjectPropertyAssertion r i i' =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [Axiom.namedIndividuals, List.mem_append] at hn
    simp only [rwAxD, List.mem_singleton, forall_eq, Interp.sat, Interp.ext]
    have hi := nomI_ext (I := I) (J := J) (nm := nm) hax.1.2 (fun a ha => hn a (Or.inl ha))
    have hi' := nomI_ext (I := I) (J := J) (nm := nm) hax.2 (fun a ha => hn a (Or.inr ha))
    rw [hp]
    constructor
    · intro h hR
      exact h _ ((hi _).2 rfl) _ hR ((hi' _).2 rfl)
    · intro h x hx y hy hy'
      rw [(hi x).1 hx, (hi' y).1 hy'] at hy
      exact h hy
  | sameIndividual as =>
    simp only [Axiom.isSHOIQDKB, List.all_eq_true] at hax
    simp only [Axiom.namedIndividuals, List.mem_flatMap] at hn
    have hi : ∀ i ∈ as, ∀ x, J.ext (nomI nm i) x ↔ x = I.ind i := fun i hi =>
      nomI_ext (hax i hi) (fun a ha => hn a ⟨i, hi, ha⟩)
    simp only [rwAxD, List.mem_singleton, forall_eq, Interp.sat, List.mem_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    constructor
    · intro h i hi' i' hi''
      exact ((hi i' hi'') _).1 (h i hi' i' hi'' (I.ind i) (((hi i hi') _).2 rfl))
    · intro h i hi' i' hi'' x hx
      rw [(hi i hi' x).1 hx, h i hi' i' hi'']
      exact (hi i' hi'' _).2 rfl
  | differentIndividuals as =>
    simp only [Axiom.isSHOIQDKB, List.all_eq_true] at hax
    simp only [Axiom.namedIndividuals, List.mem_flatMap] at hn
    have hi : ∀ i ∈ as, ∀ x, J.ext (nomI nm i) x ↔ x = I.ind i := fun i hi =>
      nomI_ext (hax i hi) (fun a ha => hn a ⟨i, hi, ha⟩)
    simp only [rwAxD, List.mem_singleton, forall_eq, Interp.sat, List.pairwise_map]
    constructor
    · intro h
      refine h.imp_of_mem fun {i i'} hm hm' h' he => h' (I.ind i) ⟨(hi i hm _).2 rfl, ?_⟩
      exact (hi i' hm' _).2 he
    · intro h
      refine h.imp_of_mem fun {i i'} hm hm' h' x ⟨hx, hx'⟩ => h' ?_
      rw [← (hi i hm x).1 hx, ← (hi i' hm' x).1 hx']
  | declareNamedIndividual _ => simp [rwAxD, Interp.sat]
  | dataDomain p c =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [Axiom.classNames] at hc
    simp only [Axiom.namedIndividuals] at hn
    simp only [rwAxD, List.mem_singleton, forall_eq, Interp.sat]
    rw [rwC_extD hr hd ht nm c hax.2 hc hn, hdp]
  | dataPropertyAssertion p i l =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [Axiom.namedIndividuals] at hn
    simp only [rwAxD, List.mem_singleton, forall_eq, Interp.sat, Interp.ext, hdp]
    have hi := nomI_ext (I := I) (J := J) (nm := nm) hax.2 hn
    constructor
    · intro h
      exact h _ ((hi _).2 rfl)
    · intro h x hx
      rw [(hi x).1 hx]
      exact h
  | negativeDataPropertyAssertion p i l =>
    simp only [Axiom.isSHOIQDKB, Bool.and_eq_true] at hax
    simp only [Axiom.namedIndividuals] at hn
    simp only [rwAxD, List.mem_singleton, forall_eq, Interp.sat, Interp.ext, hdp]
    have hi := nomI_ext (I := I) (J := J) (nm := nm) hax.2 hn
    constructor
    · intro h
      exact h _ ((hi _).2 rfl)
    · intro h x hx
      rw [(hi x).1 hx]
      exact h
  | _ =>
    simp only [rwAxD, List.mem_singleton, forall_eq]
    simp only [Axiom.isSHOIQDKB] at hax
    exact sat_congr_cls hr hd ht hax hc N N'


/-- **Up.** A model of `O` gives a model of the rewritten ontology. -/
theorem nomOntD_up {O : Ontology} (hO : O.isSHOIQDKB = true) (requested : List IRI)
    {I : Interp DM Dom} (hI : OWL.Model O I) : OWL.Model (nomOntD O requested) (upI O requested I) := by
  have hO' : ∀ ax ∈ O.axioms, ax.isSHOIQDKB = true := by
    simpa [Ontology.isSHOIQDKB, List.all_eq_true] using hO
  intro ax' hax'
  obtain ⟨ax, hax, hax'⟩ := List.mem_flatMap.1 hax'
  refine (sat_rwAxD (I := I) (J := upI O requested I) rfl rfl rfl (nmOf O requested) (hO' ax hax)
    (fun b hb => upI_old I (List.mem_append_left _ (List.mem_flatMap.2 ⟨ax, hax, hb⟩)))
    (fun a ha x => upI_nom I (mem_individualNames hax ha) x) _ O.namedIndividuals).2
    (hI ax hax) ax' hax'

/-- **Down.** A model of the rewritten ontology whose nominal classes are
singletons gives a model of `O` with the same classes, roles and data. -/
theorem nomOntD_down {O : Ontology} (hO : O.isSHOIQDKB = true) (requested : List IRI)
    {J : Interp DM Dom} (hJ : OWL.Model (nomOntD O requested) J)
    (hs : ∀ a ∈ O.individualNames, ∃ x, ∀ y, J.cls (nmOf O requested a) y ↔ y = x) :
    OWL.Model O (downI O requested J) ∧ (downI O requested J).cls = J.cls := by
  have hO' : ∀ ax ∈ O.axioms, ax.isSHOIQDKB = true := by
    simpa [Ontology.isSHOIQDKB, List.all_eq_true] using hO
  refine ⟨fun ax hax => ?_, rfl⟩
  refine (sat_rwAxD (I := downI O requested J) (J := J) rfl rfl rfl (nmOf O requested)
    (hO' ax hax) (fun b _ => rfl) (fun a ha x => downI_nom (hs a (mem_individualNames hax ha)) x)
    (nomOntD O requested).namedIndividuals _).1 fun ax' hax' => ?_
  exact hJ ax' (List.mem_flatMap.2 ⟨ax, hax, hax'⟩)

/-- The rewritten ontology is in the SHIQ(D) part, without assertions. -/
theorem nomOntD_isSHIQD {O : Ontology} (hO : O.isSHOIQDKB = true) (requested : List IRI) :
    ∀ ax ∈ (nomOntD O requested).axioms, ax.isSHIQD = true ∧ ax.isAssertion = false := by
  have hO' : ∀ ax ∈ O.axioms, ax.isSHOIQDKB = true := by
    simpa [Ontology.isSHOIQDKB, List.all_eq_true] using hO
  intro ax' hax'
  obtain ⟨ax, hax, hax'⟩ := List.mem_flatMap.1 hax'
  exact rwAxD_isSHIQD _ (hO' ax hax) ax' hax'

theorem isSHIQDKB_of_isSHIQD {ax : Axiom} (h : ax.isSHIQD = true) (hn : ax.isAssertion = false) :
    ax.isSHIQDKB = true := by
  cases ax <;> simp_all [Axiom.isSHIQDKB, Axiom.isAssertion, Axiom.isSHIQD, Axiom.isSHI, Axiom.isSRI]

theorem nomOntD_isSHIQDKB {O : Ontology} (hO : O.isSHOIQDKB = true) (requested : List IRI) :
    (nomOntD O requested).isSHIQDKB = true := by
  simp only [Ontology.isSHIQDKB, List.all_eq_true]
  intro ax hax
  obtain ⟨h1, h2⟩ := nomOntD_isSHIQD hO requested ax hax
  exact isSHIQDKB_of_isSHIQD h1 h2

end ContextCalculus.OWLFrontend.SHOIQ

#print axioms ContextCalculus.OWLFrontend.SHOIQ.rwC_extD
#print axioms ContextCalculus.OWLFrontend.SHOIQ.sat_rwAxD
#print axioms ContextCalculus.OWLFrontend.SHOIQ.nomOntD_up
#print axioms ContextCalculus.OWLFrontend.SHOIQ.nomOntD_down
