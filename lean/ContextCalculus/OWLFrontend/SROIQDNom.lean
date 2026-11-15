import ContextCalculus.OWLFrontend.SHOIQDC2aReference
import ContextCalculus.OWLFrontend.SHOIQFast
import ContextCalculus.SROIQ.ChainEncN

/-!
# SROIQ(D) knowledge bases: role chains and reflexivity (stage C3, design section 6)

`docs/V1.7.0-C3-ROLES-DESIGN.md`, section 6. The SROIQ(D) knowledge-base
part (`Ontology.isSROIQDKB`) is the SHOIQ(D) knowledge-base part with two
more object property axioms over basic properties:
`SubObjectPropertyOf` with any nonempty chain and
`ReflexiveObjectProperty`. (Self, irreflexive, asymmetric and disjoint
properties are section 5 of the design and not part of this predicate.)

The translation does not touch the SHIQ(D) translation: `roleOff O`
replaces each such axiom (`Axiom.isRoleC3`) by the inclusions
`SubObjectPropertyOf(p p)` of its properties, which every interpretation
satisfies and which make the translation index the properties; the role
axioms come back as normal-form chains (`roleCls`), built from the role
table of the translation (`T.obj.rnames`). The model maps of the SHIQ(D)
knowledge-base translation state that each entry of the role table stands
for its property (`translateSRIQDKB_mapsR`), which `shoiqd_upR` and
`shoiqd_downR` carry through the nominal rewriting.

* `model_roleOff`: a model of `O` is a model of `roleOff O` that satisfies
  the role axioms.
* `sroiq_consistent`: `O` is consistent at `owl2MapP pat` iff the `SRIQN`
  data ontology `dosnC` (the SHOIQ(D) translation of `roleOff O` with the
  role chains added) is consistent in the OWL 2 data theory.
-/

namespace ContextCalculus.OWL

/-- The property axioms the C3 route moves out of the SHOIQ(D) part: a
`SubObjectPropertyOf` outside the SHI part (a chain of length at least two
that is not transitivity) and reflexivity, over basic properties, and the
vacuous `SubDataPropertyOf(p owl:topDataProperty)`. -/
def Axiom.isRoleC3 : Axiom → Bool
  | .subObjectPropertyOf rs .top => !rs.isEmpty && rs.all ObjProp.isBasic
  | .subObjectPropertyOf rs r =>
      !(rs.length == 1 || rs == [r, r]) && !rs.isEmpty && rs.all ObjProp.isBasic && r.isBasic
  | .reflexive r => r.isBasic
  | .subDataPropertyOf p .top => p.isNamed
  | _ => false

/-- An axiom of the SROIQ(D) knowledge-base part. -/
def Axiom.isSROIQDKB (ax : Axiom) : Bool := ax.isRoleC3 || ax.isSHOIQDKB

def Ontology.isSROIQDKB (O : Ontology) : Bool := O.axioms.all Axiom.isSROIQDKB

theorem Axiom.isSROIQDKB_of_isSHOIQDKB {ax : Axiom} (h : ax.isSHOIQDKB = true) :
    ax.isSROIQDKB = true := by
  simp [isSROIQDKB, h]

theorem Ontology.isSROIQDKB_of_isSHOIQDKB {O : Ontology} (h : O.isSHOIQDKB = true) :
    O.isSROIQDKB = true := by
  simp only [isSROIQDKB, isSHOIQDKB, List.all_eq_true] at h ⊢
  exact fun ax hax => Axiom.isSROIQDKB_of_isSHOIQDKB (h ax hax)

end ContextCalculus.OWL

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ

variable {DM : DatatypeMap} {D : Type}

/-! ## Moving the role axioms out -/

/-- The properties of a role axiom. -/
def offProps : Axiom → List ObjProp
  | .subObjectPropertyOf rs .top => rs
  | .subObjectPropertyOf rs r => rs ++ [r]
  | .reflexive r => [r]
  | _ => []

def offAx (ax : Axiom) : List Axiom :=
  if ax.isRoleC3 then (offProps ax).map fun p => .subObjectPropertyOf [p] p else [ax]

/-- The ontology without its role axioms (their properties kept). -/
def roleOff (O : Ontology) : Ontology := ⟨O.axioms.flatMap offAx⟩

/-- The role axioms. -/
def roleAxsC3 (O : Ontology) : List Axiom := O.axioms.filter Axiom.isRoleC3

theorem offProps_basic {ax : Axiom} (h : ax.isRoleC3 = true) : ∀ p ∈ offProps ax, p.isBasic = true := by
  cases ax with
  | subObjectPropertyOf rs r =>
    cases r with
    | top =>
      simp only [Axiom.isRoleC3, Bool.and_eq_true, List.all_eq_true] at h
      intro p hp
      exact h.2 p hp
    | _ =>
      simp only [Axiom.isRoleC3, Bool.and_eq_true, List.all_eq_true] at h
      intro p hp
      simp only [offProps, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact h.1.2 p hp
      · exact h.2
  | reflexive r =>
    simp only [Axiom.isRoleC3] at h
    intro p hp
    simp only [offProps, List.mem_singleton] at hp
    subst hp; exact h
  | _ => intro p hp; simp [offProps] at hp

theorem roleOff_isSHOIQDKB {O : Ontology} (h : O.isSROIQDKB = true) : (roleOff O).isSHOIQDKB = true := by
  simp only [Ontology.isSROIQDKB, List.all_eq_true] at h
  simp only [Ontology.isSHOIQDKB, roleOff, List.all_eq_true, List.mem_flatMap]
  rintro ax' ⟨ax, hax, hm⟩
  unfold offAx at hm
  split_ifs at hm with hr
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    have := offProps_basic hr p hp
    simp [Axiom.isSHOIQDKB, Axiom.isSHIQD, Axiom.isSHI, this]
  · rw [List.mem_singleton] at hm; subst hm
    have := h ax' hax
    simpa [Axiom.isSROIQDKB, hr] using this

theorem sat_incl (I : Interp DM D) (N : List IRI) (p : ObjProp) :
    I.sat N (.subObjectPropertyOf [p] p) := by
  rintro x y ⟨z, hxz, rfl⟩; exact hxz

/-- The role axioms do not read the named-individual list. -/
theorem sat_N_role {I : Interp DM D} {ax : Axiom} (h : ax.isRoleC3 = true) (N N' : List IRI) :
    I.sat N ax ↔ I.sat N' ax := by
  cases ax <;> first | exact Iff.rfl | simp [Axiom.isRoleC3] at h

theorem sat_N_sroiq {I : Interp DM D} {ax : Axiom} (h : ax.isSROIQDKB = true) (N N' : List IRI) :
    I.sat N ax ↔ I.sat N' ax := by
  by_cases hr : ax.isRoleC3 = true
  · exact sat_N_role hr N N'
  · have : ax.isSHOIQDKB = true := by simpa [Axiom.isSROIQDKB, hr] using h
    exact sat_N_shoiqd this N N'

/-- **The role axioms moved out.** -/
theorem model_roleOff {O : Ontology} (h : O.isSROIQDKB = true) (I : Interp DM D) :
    OWL.Model O I ↔ OWL.Model (roleOff O) I ∧ ∀ ax ∈ roleAxsC3 O, I.sat [] ax := by
  have h' : ∀ ax ∈ O.axioms, ax.isSROIQDKB = true := by
    simpa [Ontology.isSROIQDKB, List.all_eq_true] using h
  constructor
  · intro hI
    refine ⟨fun ax' hax' => ?_, fun ax hax => ?_⟩
    · obtain ⟨ax, hax, hm⟩ := List.mem_flatMap.1 hax'
      unfold offAx at hm
      split_ifs at hm with hr
      · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hm
        exact sat_incl I _ p
      · rw [List.mem_singleton] at hm; subst hm
        exact (sat_N_sroiq (h' ax' hax) _ _).1 (hI ax' hax)
    · obtain ⟨hax, -⟩ := List.mem_filter.1 hax
      exact (sat_N_sroiq (h' ax hax) _ _).1 (hI ax hax)
  · rintro ⟨hI, hR⟩ ax hax
    by_cases hr : ax.isRoleC3 = true
    · exact (sat_N_sroiq (h' ax hax) _ _).1 (hR ax (List.mem_filter.2 ⟨hax, hr⟩))
    · have hm : ax ∈ (roleOff O).axioms :=
        List.mem_flatMap.2 ⟨ax, hax, by simp [offAx, hr]⟩
      exact (sat_N_sroiq (h' ax hax) _ _).1 (hI ax hm)

/-! ## The role table -/

/-- The role term of a basic property in a translation. -/
def roleOfT (T : SRIQDKBTranslation) (p : ObjProp) : Option (SRI.RoleT (Fin T.obj.roleCount)) :=
  (T.obj.rnames.find? fun e => e.1 == EL.propIRI p).bind fun e =>
    SRIT.finRT T.obj.roleCount (SRIT.mkRT p e.2)

theorem roleOfT_spec {T : SRIQDKBTranslation} {p : ObjProp} {R : SRI.RoleT (Fin T.obj.roleCount)}
    (h : roleOfT T p = some R) :
    ∃ k, (EL.propIRI p, k) ∈ T.obj.rnames ∧ SRIT.finRT T.obj.roleCount (SRIT.mkRT p k) = some R := by
  unfold roleOfT at h
  obtain ⟨e, he, hR⟩ := Option.bind_eq_some_iff.1 h
  have hm := List.mem_of_find?_eq_some he
  have hp := List.find?_some he
  rw [beq_iff_eq] at hp
  obtain ⟨a, k⟩ := e
  simp only at hp; subst hp
  exact ⟨k, hm, hR⟩

/-- The role terms of a list of properties. -/
def roleOfL (T : SRIQDKBTranslation) : List ObjProp → Option (List (SRI.RoleT (Fin T.obj.roleCount)))
  | [] => some []
  | p :: ps =>
    match roleOfT T p, roleOfL T ps with
    | some R, some Rs => some (R :: Rs)
    | _, _ => none

/-- The normal-form chain of a role axiom. -/
def roleClause (T : SRIQDKBTranslation) :
    Axiom → Option (List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
  | .subObjectPropertyOf _ .top => some []
  | .subObjectPropertyOf rs r =>
    match roleOfL T rs, roleOfT T r with
    | some body, some S => some [.chain body S]
    | _, _ => none
  | .reflexive r => (roleOfT T r).map fun S => [.chain [] S]
  | _ => some []

/-- The normal-form chains of the role axioms. -/
def roleCls (T : SRIQDKBTranslation) (O : Ontology) :
    Option (List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) :=
  SRIQKB.collect (roleClause T) (roleAxsC3 O)

/-- The `SRIQN` data ontology with the role chains. -/
def dosnC (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) :
    SRIQN.DOntology (Fin T.obj.conceptCount) (Fin T.obj.roleCount) (Fin T.dps.length)
      (Fin T.tab.length) :=
  dosn T L ++ E.map fun cl => .base (.obj cl)

theorem dbase_dosnC (T : SRIQDKBTranslation) (L : List IRI) (E) :
    SRIQN.dbase (dosnC T L E) = T.ontology ++ E.map ContextCalculus.SRIQD.Clause.obj := by
  simp [dosnC, SRIQN.dbase, List.filterMap_append, List.filterMap_map, ← dbase_dosn T L]

theorem dnoms_dosnC (T : SRIQDKBTranslation) (L : List IRI) (E) :
    SRIQN.dnoms (dosnC T L E) = SRIQN.dnoms (dosn T L) := by
  simp [dosnC, SRIQN.dnoms, List.filterMap_append, List.filterMap_map]

/-! ## Role correspondence -/

section Corr

variable {T : SRIQDKBTranslation} {Dom V : Type}

/-- Each role term of the table stands for its property. -/
def RoleCorr (T : SRIQDKBTranslation) (K : SRI.Interp Dom (Fin T.obj.conceptCount) (Fin T.obj.roleCount))
    (I : Interp DM Dom) : Prop :=
  ∀ (r : ObjProp), r.isBasic = true → ∀ k, (EL.propIRI r, k) ∈ T.obj.rnames →
    ∀ R, SRIT.finRT T.obj.roleCount (SRIT.mkRT r k) = some R → ∀ x y, K.rt R x y ↔ I.prop r x y

theorem roleCorr_of {K : SRI.Interp Dom (Fin T.obj.conceptCount) (Fin T.obj.roleCount)}
    {I : Interp DM Dom} (hC : RoleCorr T K I) {r : ObjProp} (hr : r.isBasic = true)
    {R : SRI.RoleT (Fin T.obj.roleCount)} (h : roleOfT T r = some R) (x y : Dom) :
    K.rt R x y ↔ I.prop r x y := by
  obtain ⟨k, hk, hfin⟩ := roleOfT_spec h
  exact hC r hr k hk R hfin x y

theorem roleOfL_path {K : SRI.Interp Dom (Fin T.obj.conceptCount) (Fin T.obj.roleCount)}
    {I : Interp DM Dom} (hC : RoleCorr T K I) :
    ∀ {rs : List ObjProp} {body}, (∀ r ∈ rs, r.isBasic = true) → roleOfL T rs = some body →
      ∀ x y, K.path body x y ↔ I.chain rs x y
  | [], body, _, h, x, y => by
    simp only [roleOfL, Option.some.injEq] at h; subst h; exact Iff.rfl
  | p :: ps, body, hb, h, x, y => by
    simp only [roleOfL] at h
    split at h
    · next R Rs hR hRs =>
      simp only [Option.some.injEq] at h; subst h
      simp only [SRI.Interp.path, Interp.chain]
      refine exists_congr fun z => and_congr (roleCorr_of hC (hb p List.mem_cons_self) hR x z) ?_
      exact roleOfL_path hC (fun r hr => hb r (List.mem_cons_of_mem _ hr)) hRs z y
    · cases h

/-- A role axiom holds iff its chain does. -/
theorem sat_roleClause {K : SRI.Interp Dom (Fin T.obj.conceptCount) (Fin T.obj.roleCount)}
    {I : Interp DM Dom} (hC : RoleCorr T K I) {ax : Axiom} (hax : ax.isRoleC3 = true)
    {l : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))}
    (h : roleClause T ax = some l) : (∀ cl ∈ l, SRIQ.satClause K cl) ↔ I.sat [] ax := by
  cases ax with
  | subObjectPropertyOf rs r =>
    cases r with
    | top =>
      simp only [roleClause, Option.some.injEq] at h; subst h
      simp only [List.not_mem_nil, false_implies, implies_true, true_iff]
      intro x y _; trivial
    | _ =>
    simp only [Axiom.isRoleC3, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.all_eq_true] at hax
    simp only [roleClause] at h
    split at h
    · next body S hb hS =>
      simp only [Option.some.injEq] at h; subst h
      simp only [List.mem_singleton, forall_eq, SRIQ.satClause, Interp.sat]
      refine forall_congr' fun x => forall_congr' fun y => ?_
      rw [roleOfL_path hC hax.1.2 hb x y, roleCorr_of hC hax.2 hS x y]
    · cases h
  | reflexive r =>
    simp only [Axiom.isRoleC3] at hax
    simp only [roleClause] at h
    obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [List.mem_singleton, forall_eq, SRIQ.satClause, Interp.sat, SRI.Interp.path]
    constructor
    · intro h' x; exact (roleCorr_of hC hax hS x x).1 (h' x x rfl)
    · rintro h' x y rfl; exact (roleCorr_of hC hax hS x x).2 (h' x)
  | subDataPropertyOf p q =>
    cases q with
    | top =>
      simp only [roleClause, Option.some.injEq] at h; subst h
      simp only [List.not_mem_nil, false_implies, implies_true, true_iff]
      intro x v _; trivial
    | _ => simp [Axiom.isRoleC3] at hax
  | _ => simp [Axiom.isRoleC3] at hax

/-- The chains of all role axioms hold iff the role axioms do. -/
theorem sat_roleCls {K : SRI.Interp Dom (Fin T.obj.conceptCount) (Fin T.obj.roleCount)}
    {I : Interp DM Dom} (hC : RoleCorr T K I) {O : Ontology} {E}
    (hE : roleCls T O = some E) : (∀ cl ∈ E, SRIQ.satClause K cl) ↔ ∀ ax ∈ roleAxsC3 O, I.sat [] ax := by
  constructor
  · intro h ax hax
    obtain ⟨l, hl, hsub⟩ := SRIQKB.collect_some hE ax hax
    exact (sat_roleClause hC (List.mem_filter.1 hax).2 hl).1 fun cl hcl => h cl (hsub cl hcl)
  · intro h cl hcl
    obtain ⟨ax, hax, l, hl, hcl'⟩ := SRIQKB.collect_mem hE cl hcl
    exact (sat_roleClause hC (List.mem_filter.1 hax).2 hl).2 (h ax hax) cl hcl'

end Corr

/-! ## The model maps with roles -/

variable {O : Ontology} {requested : List IRI} {T : SRIQDKBTranslation}

/-- **Up, with roles.** `shoiqd_up`, and the roles of the table stand for
their properties. -/
theorem shoiqd_upR (pat : String → String → Prop) (h : translateSHOIQD O requested = some T)
    {Dom : Type} [Nonempty Dom] (I : Interp (owl2MapP pat) Dom) (hI : OWL.Model O I) :
    ∃ (V : Type) (atom : Fin T.tab.length → V → Prop), owlTheory pat (spec T.tab) V atom ∧
      ∃ K : ContextCalculus.SRIQD.DInterp Dom V (Fin T.obj.conceptCount) (Fin T.obj.roleCount)
          (Fin T.dps.length),
        ContextCalculus.SRIQD.models atom K (SRIQN.dbase (dosn T (nomNames O requested))) ∧
        (∀ a ∈ SRIQN.dnoms (dosn T (nomNames O requested)), SRIQN.NomAt K.toInterp a) ∧
        RoleCorr T K.toInterp I := by
  obtain ⟨hO, hT⟩ := translateSHOIQD_spec h
  obtain ⟨V, atom, hΘ, K, -, hK, -, hc, hr⟩ :=
    (translateSRIQDKB_mapsR pat hT).1 Dom (upI O requested I) (nomOntD_up hO requested hI)
  have hcs : ∀ s ∈ requested ++ nomNames O requested, ∀ (ix : Fin T.obj.conceptCount),
      nameIx T.obj s = some ix → ∀ y, K.c ix y ↔ (upI O requested I).cls s y := by
    intro s hs ix hix y
    obtain ⟨hi, he⟩ := nameIx_spec hix
    have := hc ix.val hi (he ▸ hs) y
    rw [he] at this
    exact this
  refine ⟨V, atom, hΘ, K, by rw [dbase_dosn]; exact hK, fun x hx => ?_,
    fun r hb k hk R hfin x y => ?_⟩
  · rw [dnoms_dosn] at hx
    obtain ⟨s, hs, hsx⟩ := List.mem_filterMap.1 hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
    exact ⟨I.ind (.named a), fun y => (hcs _ (List.mem_append_right _ hs) x hsx y).trans
      (upI_nom I ha y)⟩
  · have := hr r hb k hk R hfin x y
    cases r <;> exact this

/-- **Down, with roles.** -/
theorem shoiqd_downR (pat : String → String → Prop) (h : translateSHOIQD O requested = some T)
    {Dom V : Type} [Nonempty Dom] {atom : Fin T.tab.length → V → Prop}
    (hΘ : owlTheory pat (spec T.tab) V atom)
    (K : ContextCalculus.SRIQD.DInterp Dom V (Fin T.obj.conceptCount) (Fin T.obj.roleCount)
      (Fin T.dps.length))
    (hK : ContextCalculus.SRIQD.models atom K (SRIQN.dbase (dosn T (nomNames O requested))))
    (hn : ∀ a ∈ SRIQN.dnoms (dosn T (nomNames O requested)), SRIQN.NomAt K.toInterp a) :
    ∃ I : Interp (owl2MapP pat) Dom, OWL.Model O I ∧ RoleCorr T K.toInterp I := by
  obtain ⟨hO, hT⟩ := translateSHOIQD_spec h
  obtain ⟨x0⟩ := (inferInstance : Nonempty Dom)
  rw [dbase_dosn] at hK
  obtain ⟨I0, hI0, hc, hr⟩ := (translateSRIQDKB_mapsR pat hT).2 Dom V atom hΘ K (fun _ => x0) hK
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
  obtain ⟨hM, -⟩ := nomOntD_down hO requested hI0 hsing
  refine ⟨downI O requested I0, hM, fun r hb k hk R hfin x y => ?_⟩
  have := hr r hb k hk R hfin x y
  cases r <;> exact this.symm

/-! ## Consistency -/

theorem models_append_obj {Dom V : Type} {atom : Fin T.tab.length → V → Prop}
    {K : ContextCalculus.SRIQD.DInterp Dom V (Fin T.obj.conceptCount) (Fin T.obj.roleCount)
      (Fin T.dps.length)} {A : ContextCalculus.SRIQD.Ontology (Fin T.obj.conceptCount)
      (Fin T.obj.roleCount) (Fin T.dps.length) (Fin T.tab.length)}
    {E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))} :
    ContextCalculus.SRIQD.models atom K (A ++ E.map ContextCalculus.SRIQD.Clause.obj) ↔
      ContextCalculus.SRIQD.models atom K A ∧ ∀ cl ∈ E, SRIQ.satClause K.toInterp cl := by
  simp only [ContextCalculus.SRIQD.models, List.mem_append, List.mem_map]
  constructor
  · intro h
    exact ⟨fun cl hcl => h cl (Or.inl hcl), fun cl hcl => h _ (Or.inr ⟨cl, hcl, rfl⟩)⟩
  · rintro ⟨h1, h2⟩ cl (hcl | ⟨cl', hcl', rfl⟩)
    · exact h1 cl hcl
    · exact h2 cl' hcl'

/-- **Consistency with role chains.** -/
theorem sroiq_consistent (pat : String → String → Prop) (hO : O.isSROIQDKB = true)
    (hT : translateSHOIQD (roleOff O) [] = some T) {E} (hE : roleCls T O = some E) :
    ConsistentAt (owl2MapP pat) O ↔
      SRIQN.ConsistentDN (owlTheory pat (spec T.tab)) (dosnC T (nomNames (roleOff O) []) E) := by
  constructor
  · rintro ⟨Dom, hD, I, hI⟩
    obtain ⟨hI1, hI2⟩ := (model_roleOff hO I).1 hI
    obtain ⟨V, atom, hΘ, K, hK, hn, hC⟩ := shoiqd_upR pat hT I hI1
    refine ⟨Dom, V, hD, atom, hΘ, K, ?_, by rw [dnoms_dosnC]; exact hn⟩
    rw [dbase_dosnC, models_append_obj]
    exact ⟨by rw [← dbase_dosn T (nomNames (roleOff O) [])]; exact hK, (sat_roleCls hC hE).2 hI2⟩
  · rintro ⟨Dom, V, hD, atom, hΘ, K, hK, hn⟩
    rw [dbase_dosnC, models_append_obj] at hK
    rw [dnoms_dosnC] at hn
    obtain ⟨I, hI, hC⟩ := shoiqd_downR pat hT hΘ K (by rw [dbase_dosn]; exact hK.1) hn
    exact ⟨Dom, hD, I, (model_roleOff hO I).2 ⟨hI, (sat_roleCls hC hE).1 hK.2⟩⟩

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.model_roleOff
#print axioms ContextCalculus.OWLFrontend.shoiqd_upR
#print axioms ContextCalculus.OWLFrontend.shoiqd_downR
#print axioms ContextCalculus.OWLFrontend.sroiq_consistent
