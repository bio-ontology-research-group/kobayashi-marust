import ContextCalculus.OWL.FragmentSHIQ
import ContextCalculus.OWL.Names

/-!
# Entailment at one datatype map (v1.7.0 stage C4, part D)

`OWL.EntailsSub` quantifies over every datatype map. With data, entailment
is taken at one map, the OWL 2 datatype map: `EntailsSubAt DM O A B`
quantifies over the interpretations for `DM` only.

For an ontology of the SHIQ part (`Ontology.isSHIQ`, no data constructs),
the two coincide for every map (`entailsSubAt_iff`): the satisfaction of
its axioms depends only on classes, properties and individuals, and an
interpretation for one map carries over to any other map with the same
object part. So the SHIQ capstones, stated for `EntailsSub`, hold for
`EntailsSubAt` at the OWL 2 map.
-/

namespace ContextCalculus.OWL

variable {DM DM' : DatatypeMap} {Dom : Type}

/-- `O` entails `SubClassOf(A B)` at the datatype map `DM`. -/
def EntailsSubAt (DM : DatatypeMap) (O : Ontology) (A B : IRI) : Prop :=
  ∀ (Domain : Type) [Nonempty Domain] (I : Interp DM Domain),
    Model O I → ∀ x, I.cls A x → I.cls B x

/-- `O` has no model at the datatype map `DM`. -/
def InconsistentAt (DM : DatatypeMap) (O : Ontology) : Prop :=
  ∀ (Domain : Type) [Nonempty Domain] (I : Interp DM Domain), ¬ Model O I

/-- The object part of `I` for another datatype map, without data. -/
def Interp.toMap (I : Interp DM Dom) (DM' : DatatypeMap) : Interp DM' Dom where
  cls := I.cls
  role := I.role
  ind := I.ind
  dprop _ _ _ := False
  dtype _ _ := False

theorem Interp.prop_congr' {I : Interp DM Dom} {J : Interp DM' Dom} (h : I.role = J.role)
    (r : ObjProp) : I.prop r = J.prop r := by
  cases r <;> simp only [Interp.prop, h]

theorem Interp.chain_congr' {I : Interp DM Dom} {J : Interp DM' Dom} (h : I.role = J.role) :
    ∀ rs : List ObjProp, I.chain rs = J.chain rs
  | [] => rfl
  | r :: rs => by
    funext x z
    simp only [Interp.chain, Interp.prop_congr' h r, Interp.chain_congr' h rs]

/-- An ALCIQ class expression has the same extension in two interpretations
(for possibly different maps) with the same classes and roles. -/
theorem ClassExpr.ext_congr' {I : Interp DM Dom} {J : Interp DM' Dom} (hc : I.cls = J.cls)
    (hr : I.role = J.role) : ∀ (c : ClassExpr), c.isALCIQ = true → I.ext c = J.ext c
  | .cls a, _ => by funext x; rw [Interp.ext, Interp.ext, hc]
  | .thing, _ => by funext x; rw [Interp.ext, Interp.ext]
  | .nothing, _ => by funext x; rw [Interp.ext, Interp.ext]
  | .and cs, h => by
    rw [isALCIQ] at h
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at h
    have ih : ∀ c ∈ cs, I.ext c = J.ext c := fun c hm => ext_congr' hc hr c (h c hm)
    funext x; rw [Interp.ext, Interp.ext]
    apply propext
    exact ⟨fun h' c hm => (ih c hm) ▸ h' c hm, fun h' c hm => (ih c hm).symm ▸ h' c hm⟩
  | .or cs, h => by
    rw [isALCIQ] at h
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at h
    have ih : ∀ c ∈ cs, I.ext c = J.ext c := fun c hm => ext_congr' hc hr c (h c hm)
    funext x; rw [Interp.ext, Interp.ext]
    apply propext
    exact ⟨fun ⟨c, hm, h'⟩ => ⟨c, hm, (ih c hm) ▸ h'⟩,
      fun ⟨c, hm, h'⟩ => ⟨c, hm, (ih c hm).symm ▸ h'⟩⟩
  | .not c, h => by
    rw [isALCIQ] at h
    funext x; rw [Interp.ext, Interp.ext, ext_congr' hc hr c h]
  | .some r c, h => by
    rw [isALCIQ, Bool.and_eq_true] at h
    funext x; rw [Interp.ext, Interp.ext, ext_congr' hc hr c h.2, Interp.prop_congr' hr]
  | .all r c, h => by
    rw [isALCIQ, Bool.and_eq_true] at h
    funext x; rw [Interp.ext, Interp.ext, ext_congr' hc hr c h.2, Interp.prop_congr' hr]
  | .min k r c, h => by
    rw [isALCIQ, Bool.and_eq_true] at h
    funext x; rw [Interp.ext, Interp.ext, ext_congr' hc hr c h.2, Interp.prop_congr' hr]
  | .max k r c, h => by
    rw [isALCIQ, Bool.and_eq_true] at h
    funext x; rw [Interp.ext, Interp.ext, ext_congr' hc hr c h.2, Interp.prop_congr' hr]
  | .exact k r c, h => by
    rw [isALCIQ, Bool.and_eq_true] at h
    funext x; rw [Interp.ext, Interp.ext, ext_congr' hc hr c h.2, Interp.prop_congr' hr]
  | .oneOf _, h | .hasValue .., h | .hasSelf _, h | .dataSome .., h
  | .dataAll .., h | .dataHasValue .., h | .dataMin .., h | .dataMax .., h
  | .dataExact .., h => by rw [isALCIQ] at h; exact absurd h (by simp)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)
    | omega

/-- An axiom of the SHIQ part holds in one interpretation iff it holds in
another (for possibly different maps) with the same classes and roles. -/
theorem Axiom.sat_congr' {I : Interp DM Dom} {J : Interp DM' Dom} (hc : I.cls = J.cls)
    (hr : I.role = J.role) {ax : Axiom} (hax : ax.isSHIQ = true) (N N' : List IRI) :
    I.sat N ax ↔ J.sat N' ax := by
  have hp := Interp.prop_congr' hr
  have hch := Interp.chain_congr' hr
  have he := ClassExpr.ext_congr' hc hr
  cases ax with
  | subClassOf c d =>
    simp only [isSHIQ, Bool.and_eq_true] at hax
    rw [Interp.sat, Interp.sat, he c hax.1, he d hax.2]
  | equivalentClasses cs =>
    simp only [isSHIQ, List.all_eq_true] at hax
    have ih : ∀ c ∈ cs, I.ext c = J.ext c := fun c hm => he c (hax c hm)
    simp only [Interp.sat]
    exact ⟨fun h c hm d hd x => (ih c hm) ▸ (ih d hd) ▸ h c hm d hd x,
      fun h c hm d hd x => (ih c hm).symm ▸ (ih d hd).symm ▸ h c hm d hd x⟩
  | disjointClasses cs =>
    simp only [isSHIQ, List.all_eq_true] at hax
    have ih : ∀ c ∈ cs, I.ext c = J.ext c := fun c hm => he c (hax c hm)
    simp only [Interp.sat]
    constructor
    · intro h
      exact h.imp_of_mem fun hc hd h' x => (ih _ hc) ▸ (ih _ hd) ▸ h' x
    · intro h
      exact h.imp_of_mem fun hc hd h' x => (ih _ hc).symm ▸ (ih _ hd).symm ▸ h' x
  | domain r c =>
    simp only [isSHIQ, Bool.and_eq_true] at hax
    rw [Interp.sat, Interp.sat, he c hax.2, hp]
  | range r c =>
    simp only [isSHIQ, Bool.and_eq_true] at hax
    rw [Interp.sat, Interp.sat, he c hax.2, hp]
  | subObjectPropertyOf rs r => simp only [Interp.sat, hp, hch]
  | equivalentObjectProperties rs => simp only [Interp.sat, hp]
  | inverseObjectProperties r s => simp only [Interp.sat, hp]
  | transitive r => simp only [Interp.sat, hp]
  | symmetric r => simp only [Interp.sat, hp]
  | functional r => simp only [Interp.sat, hp]
  | inverseFunctional r => simp only [Interp.sat, hp]
  | declareClass _ | declareObjectProperty _ | declareDataProperty _ | declareNamedIndividual _
  | declareDatatype _ | declareAnnotationProperty _ => simp only [Interp.sat]
  | _ => simp [isSHIQ, isSHI, isSRI] at hax

/-- A model of a SHIQ ontology carries over to any datatype map. -/
theorem model_toMap {O : Ontology} (h : O.isSHIQ = true) {I : Interp DM Dom} (hI : Model O I)
    (DM' : DatatypeMap) : Model O (I.toMap DM') := by
  intro ax hax
  have hs : ax.isSHIQ = true := by
    simp only [Ontology.isSHIQ, List.all_eq_true] at h
    exact h ax hax
  exact (Axiom.sat_congr' (I := I) (J := I.toMap DM') rfl rfl hs _ _).1 (hI ax hax)

/-- **Coincidence.** For a SHIQ ontology, entailment at any datatype map is
entailment over all maps. -/
theorem entailsSubAt_iff {O : Ontology} (h : O.isSHIQ = true) (DM : DatatypeMap) (A B : IRI) :
    EntailsSubAt DM O A B ↔ EntailsSub O A B := by
  constructor
  · intro hE DM' D _ I hI x hx
    exact hE D (I.toMap DM) (model_toMap h hI DM) x hx
  · intro hE D _ I hI x hx
    exact hE DM D I hI x hx

/-- For a SHIQ ontology, inconsistency at any datatype map is inconsistency
over all maps. -/
theorem inconsistentAt_iff {O : Ontology} (h : O.isSHIQ = true) (DM : DatatypeMap) :
    InconsistentAt DM O ↔ Inconsistent O := by
  constructor
  · intro hI DM' D _ I hM
    exact hI D (I.toMap DM) (model_toMap h hM DM)
  · intro hI D _ I hM
    exact hI DM D I hM

end ContextCalculus.OWL

#print axioms ContextCalculus.OWL.entailsSubAt_iff
#print axioms ContextCalculus.OWL.inconsistentAt_iff
