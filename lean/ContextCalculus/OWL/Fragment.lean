import ContextCalculus.OWL.Semantics

/-!
# The EL and ALC parts of the frontend fragment

`docs/V1.6.2-FRONTEND-PLAN.md`, section 7. The phase A theorems are stated
for ontologies in one of two parts of `F`, each matching the normal forms
that a v1.6.0 reference procedure decides exactly:

- **EL** (`ELCompletion`, NF1 to NF7): class expressions built from class
  IRIs, `owl:Thing`, `owl:Nothing`, intersection and existential
  restriction over a named object property; axioms SubClassOf,
  EquivalentClasses, DisjointClasses, ObjectPropertyDomain over a named
  property, SubObjectPropertyOf with a chain of named properties,
  EquivalentObjectProperties and TransitiveObjectProperty over named
  properties, and declarations.
- **ALC** (`Ctx`, finite type elimination): every class constructor of
  `F` over named object properties; axioms SubClassOf, EquivalentClasses,
  DisjointClasses, ObjectPropertyDomain and ObjectPropertyRange over named
  properties, and declarations; no object-property axioms.

Both predicates are Boolean so that the frontend can test them and the
completeness theorems can take them as hypotheses.
-/

namespace ContextCalculus.OWL

/-- An object-property expression is a property IRI, not an inverse. -/
def ObjProp.isNamed : ObjProp → Bool
  | .named _ => true
  | .inv _ | .top | .bot => false

/-- EL class expressions. -/
def ClassExpr.isEL : ClassExpr → Bool
  | .cls _ | .thing | .nothing => true
  | .and cs => cs.attach.all fun ⟨c, _⟩ => c.isEL
  | .some r c => r.isNamed && c.isEL
  | .or _ | .not _ | .all _ _ => false
  | .oneOf _ | .hasValue .. | .hasSelf _ | .min .. | .max .. | .exact ..
  | .dataSome .. | .dataAll .. | .dataHasValue .. | .dataMin .. | .dataMax ..
  | .dataExact .. => false
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)
    | omega

/-- ALC class expressions: every constructor, named properties only. -/
def ClassExpr.isALC : ClassExpr → Bool
  | .cls _ | .thing | .nothing => true
  | .and cs | .or cs => cs.attach.all fun ⟨c, _⟩ => c.isALC
  | .not c => c.isALC
  | .some r c | .all r c => r.isNamed && c.isALC
  | .oneOf _ | .hasValue .. | .hasSelf _ | .min .. | .max .. | .exact ..
  | .dataSome .. | .dataAll .. | .dataHasValue .. | .dataMin .. | .dataMax ..
  | .dataExact .. => false
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)
    | omega

def Axiom.isEL : Axiom → Bool
  | .subClassOf c d => c.isEL && d.isEL
  | .equivalentClasses cs | .disjointClasses cs => cs.all ClassExpr.isEL
  | .domain r c => r.isNamed && c.isEL
  | .range _ _ => false
  | .subObjectPropertyOf rs r => !rs.isEmpty && rs.all ObjProp.isNamed && r.isNamed
  | .equivalentObjectProperties rs => rs.all ObjProp.isNamed
  | .transitive r => r.isNamed
  | .inverseObjectProperties _ _ | .symmetric _ => false
  | .declareClass _ | .declareObjectProperty _ => true
  | .declareDataProperty _ | .declareNamedIndividual _ | .declareDatatype _
  | .declareAnnotationProperty _ => true
  | .disjointUnion .. | .disjointObjectProperties _ | .functional _
  | .inverseFunctional _ | .reflexive _ | .irreflexive _ | .asymmetric _
  | .subDataPropertyOf .. | .equivalentDataProperties _ | .disjointDataProperties _
  | .dataDomain .. | .dataRange .. | .functionalData _ | .datatypeDefinition ..
  | .hasKey .. | .sameIndividual _ | .differentIndividuals _ | .classAssertion ..
  | .objectPropertyAssertion .. | .negativeObjectPropertyAssertion ..
  | .dataPropertyAssertion .. | .negativeDataPropertyAssertion .. => false

def Axiom.isALC : Axiom → Bool
  | .subClassOf c d => c.isALC && d.isALC
  | .equivalentClasses cs | .disjointClasses cs => cs.all ClassExpr.isALC
  | .domain r c | .range r c => r.isNamed && c.isALC
  | .subObjectPropertyOf _ _ | .equivalentObjectProperties _
  | .inverseObjectProperties _ _ | .transitive _ | .symmetric _ => false
  | .declareClass _ | .declareObjectProperty _ => true
  | .declareDataProperty _ | .declareNamedIndividual _ | .declareDatatype _
  | .declareAnnotationProperty _ => true
  | .disjointUnion .. | .disjointObjectProperties _ | .functional _
  | .inverseFunctional _ | .reflexive _ | .irreflexive _ | .asymmetric _
  | .subDataPropertyOf .. | .equivalentDataProperties _ | .disjointDataProperties _
  | .dataDomain .. | .dataRange .. | .functionalData _ | .datatypeDefinition ..
  | .hasKey .. | .sameIndividual _ | .differentIndividuals _ | .classAssertion ..
  | .objectPropertyAssertion .. | .negativeObjectPropertyAssertion ..
  | .dataPropertyAssertion .. | .negativeDataPropertyAssertion .. => false

def Ontology.isEL (O : Ontology) : Bool := O.axioms.all Axiom.isEL
def Ontology.isALC (O : Ontology) : Bool := O.axioms.all Axiom.isALC

/-- The class IRIs one axiom mentions or declares. -/
def Axiom.classIRIs : Axiom → List IRI
  | .subClassOf c d => c.names ++ d.names
  | .equivalentClasses cs | .disjointClasses cs => cs.flatMap ClassExpr.names
  | .domain _ c | .range _ c => c.names
  | .declareClass a => [a]
  | .disjointUnion a cs => a :: cs.flatMap ClassExpr.names
  | .dataDomain _ c | .hasKey c _ _ | .classAssertion c _ => c.names
  | _ => []

/-- `O` mentions the class IRI `A`. -/
def Ontology.mentionsClass (O : Ontology) (A : IRI) : Prop :=
  ∃ ax ∈ O.axioms, A ∈ ax.classIRIs

/-! ## Agreement: interpretations that differ only on unmentioned class IRIs -/

namespace Interp

variable {D : DatatypeMap} {Domain : Type}

/-- `I` with its class extensions replaced by `c`. -/
def withCls (I : Interp D Domain) (c : IRI → Domain → Prop) : Interp D Domain :=
  { I with cls := c }

@[simp] theorem withCls_ind (I : Interp D Domain) (c : IRI → Domain → Prop) :
    (I.withCls c).ind = I.ind := rfl

@[simp] theorem withCls_dp (I : Interp D Domain) (c : IRI → Domain → Prop)
    (p : DataProp) : (I.withCls c).dp p = I.dp p := by
  cases p <;> rfl

@[simp] theorem withCls_dt (I : Interp D Domain) (c : IRI → Domain → Prop) :
    (I.withCls c).dt = I.dt := rfl

@[simp] theorem withCls_drExt (I : Interp D Domain) (c : IRI → Domain → Prop) :
    (I.withCls c).drExt = I.drExt := rfl

@[simp] theorem withCls_isNamed (I : Interp D Domain) (c : IRI → Domain → Prop) :
    (I.withCls c).IsNamed = I.IsNamed := rfl

@[simp] theorem withCls_cls (I : Interp D Domain) (c : IRI → Domain → Prop) :
    (I.withCls c).cls = c := rfl

@[simp] theorem withCls_role (I : Interp D Domain) (c : IRI → Domain → Prop) :
    (I.withCls c).role = I.role := rfl

@[simp] theorem withCls_prop (I : Interp D Domain) (c : IRI → Domain → Prop)
    (r : ObjProp) : (I.withCls c).prop r = I.prop r := by
  cases r <;> rfl

theorem withCls_chain (I : Interp D Domain) (c : IRI → Domain → Prop) :
    ∀ (rs : List ObjProp), (I.withCls c).chain rs = I.chain rs
  | [] => rfl
  | r :: rs => by
      funext x z
      simp only [chain, withCls_prop, withCls_chain I c rs]

theorem ext_and (I : Interp D Domain) (cs : List ClassExpr) (x : Domain) :
    I.ext (.and cs) x ↔ ∀ c ∈ cs, I.ext c x := by
  rw [ext]

theorem ext_or (I : Interp D Domain) (cs : List ClassExpr) (x : Domain) :
    I.ext (.or cs) x ↔ ∃ c ∈ cs, I.ext c x := by
  rw [ext]; simp

mutual

/-- The extension of `E` depends only on the class IRIs `E` mentions. -/
theorem ext_withCls (I : Interp D Domain) (c : IRI → Domain → Prop) :
    ∀ (E : ClassExpr), (∀ a ∈ E.names, c a = I.cls a) →
      ∀ x, (I.withCls c).ext E x ↔ I.ext E x
  | .cls a, h, x => by
      rw [ext, ext]; simp [ClassExpr.names] at h; simp [h]
  | .thing, _, x => by rw [ext, ext]
  | .nothing, _, x => by rw [ext, ext]
  | .and cs, h, x => by
      rw [ext_and, ext_and]
      have := ext_withCls_list I c cs (fun d hd a ha => h a (by
        rw [ClassExpr.names]; simp only [List.mem_flatMap, List.mem_attach, true_and,
          Subtype.exists]; exact ⟨d, hd, ha⟩)) x
      exact this
  | .or cs, h, x => by
      rw [ext_or, ext_or]
      have := ext_withCls_list_or I c cs (fun d hd a ha => h a (by
        rw [ClassExpr.names]; simp only [List.mem_flatMap, List.mem_attach, true_and,
          Subtype.exists]; exact ⟨d, hd, ha⟩)) x
      exact this
  | .not d, h, x => by
      rw [ext, ext]
      exact not_congr (ext_withCls I c d (fun a ha => h a (by rw [ClassExpr.names]; exact ha)) x)
  | .some r d, h, x => by
      rw [ext, ext]
      have := ext_withCls I c d (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      simp only [withCls_prop, this]
  | .all r d, h, x => by
      rw [ext, ext]
      have := ext_withCls I c d (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      simp only [withCls_prop, this]
  | .min n r d, h, x => by
      rw [ext, ext]
      have := ext_withCls I c d (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      simp only [withCls_prop, this]
  | .max n r d, h, x => by
      rw [ext, ext]
      have := ext_withCls I c d (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      simp only [withCls_prop, this]
  | .exact n r d, h, x => by
      rw [ext, ext]
      have := ext_withCls I c d (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      simp only [withCls_prop, this]
  | .oneOf _, _, x => by rw [ext, ext]; rfl
  | .hasValue r a, _, x => by rw [ext, ext]; simp only [withCls_prop, withCls_ind]
  | .hasSelf r, _, x => by rw [ext, ext]; simp only [withCls_prop]
  | .dataSome p r, _, x => by rw [ext, ext]; simp only [withCls_dp, withCls_drExt]
  | .dataAll p r, _, x => by rw [ext, ext]; simp only [withCls_dp, withCls_drExt]
  | .dataHasValue p l, _, x => by rw [ext, ext]; simp only [withCls_dp]
  | .dataMin n p r, _, x => by rw [ext, ext]; simp only [withCls_dp, withCls_drExt]
  | .dataMax n p r, _, x => by rw [ext, ext]; simp only [withCls_dp, withCls_drExt]
  | .dataExact n p r, _, x => by rw [ext, ext]; simp only [withCls_dp, withCls_drExt]

theorem ext_withCls_list (I : Interp D Domain) (c : IRI → Domain → Prop) :
    ∀ (cs : List ClassExpr), (∀ d ∈ cs, ∀ a ∈ d.names, c a = I.cls a) →
      ∀ x, (∀ d ∈ cs, (I.withCls c).ext d x) ↔ (∀ d ∈ cs, I.ext d x)
  | [], _, x => by simp
  | d :: ds, h, x => by
      simp only [List.mem_cons, forall_eq_or_imp]
      rw [ext_withCls I c d (h d (by simp)) x,
        ext_withCls_list I c ds (fun e he => h e (by simp [he])) x]

theorem ext_withCls_list_or (I : Interp D Domain) (c : IRI → Domain → Prop) :
    ∀ (cs : List ClassExpr), (∀ d ∈ cs, ∀ a ∈ d.names, c a = I.cls a) →
      ∀ x, (∃ d ∈ cs, (I.withCls c).ext d x) ↔ (∃ d ∈ cs, I.ext d x)
  | [], _, x => by simp
  | d :: ds, h, x => by
      simp only [List.mem_cons, exists_eq_or_imp]
      rw [ext_withCls I c d (h d (by simp)) x,
        ext_withCls_list_or I c ds (fun e he => h e (by simp [he])) x]

end

/-- Satisfaction of an axiom depends only on the class IRIs it mentions. -/
theorem sat_withCls (I : Interp D Domain) (c : IRI → Domain → Prop) (N : List IRI)
    (ax : Axiom) (h : ∀ a ∈ ax.classIRIs, c a = I.cls a) :
    (I.withCls c).sat N ax ↔ I.sat N ax := by
  have hE : ∀ E : ClassExpr, (∀ a ∈ E.names, a ∈ ax.classIRIs) →
      ∀ x, (I.withCls c).ext E x ↔ I.ext E x :=
    fun E hE => ext_withCls I c E (fun a ha => h a (hE a ha))
  cases ax with
  | subClassOf d e =>
      simp only [sat]
      have h1 := hE d (fun a ha => by simp [Axiom.classIRIs, ha])
      have h2 := hE e (fun a ha => by simp [Axiom.classIRIs, ha])
      simp only [h1, h2]
  | equivalentClasses cs =>
      simp only [sat]
      constructor
      · intro H d hd e he x hx
        have h1 := hE d (fun a ha => by simp only [Axiom.classIRIs, List.mem_flatMap]; exact ⟨d, hd, ha⟩)
        have h2 := hE e (fun a ha => by simp only [Axiom.classIRIs, List.mem_flatMap]; exact ⟨e, he, ha⟩)
        exact (h2 x).1 (H d hd e he x ((h1 x).2 hx))
      · intro H d hd e he x hx
        have h1 := hE d (fun a ha => by simp only [Axiom.classIRIs, List.mem_flatMap]; exact ⟨d, hd, ha⟩)
        have h2 := hE e (fun a ha => by simp only [Axiom.classIRIs, List.mem_flatMap]; exact ⟨e, he, ha⟩)
        exact (h2 x).2 (H d hd e he x ((h1 x).1 hx))
  | disjointClasses cs =>
      simp only [sat]
      have hm : ∀ d ∈ cs, ∀ x, (I.withCls c).ext d x ↔ I.ext d x := fun d hd =>
        hE d (fun a ha => by simp only [Axiom.classIRIs, List.mem_flatMap]; exact ⟨d, hd, ha⟩)
      constructor
      · intro H
        refine List.Pairwise.imp_of_mem ?_ H
        intro d e hd he hde x hx
        exact hde x ⟨(hm d hd x).2 hx.1, (hm e he x).2 hx.2⟩
      · intro H
        refine List.Pairwise.imp_of_mem ?_ H
        intro d e hd he hde x hx
        exact hde x ⟨(hm d hd x).1 hx.1, (hm e he x).1 hx.2⟩
  | domain r d =>
      simp only [sat, withCls_prop]
      have h1 := hE d (fun a ha => by simpa [Axiom.classIRIs] using ha)
      simp only [h1]
  | range r d =>
      simp only [sat, withCls_prop]
      have h1 := hE d (fun a ha => by simpa [Axiom.classIRIs] using ha)
      simp only [h1]
  | subObjectPropertyOf rs r => simp only [sat, withCls_prop, withCls_chain]
  | equivalentObjectProperties rs => simp only [sat, withCls_prop]
  | inverseObjectProperties r s => simp only [sat, withCls_prop]
  | transitive r => simp only [sat, withCls_prop]
  | symmetric r => simp only [sat, withCls_prop]
  | declareClass a => simp only [sat]
  | declareObjectProperty r => simp only [sat]
  | disjointUnion b cs =>
      simp only [sat]
      have hm : ∀ d ∈ cs, ∀ x, (I.withCls c).ext d x ↔ I.ext d x := fun d hd =>
        hE d (fun a ha => by
          simp only [Axiom.classIRIs, List.mem_cons, List.mem_flatMap]; exact Or.inr ⟨d, hd, ha⟩)
      have hb : c b = I.cls b := h b (by simp [Axiom.classIRIs])
      constructor
      · rintro ⟨H1, H2⟩
        refine ⟨fun x => ?_, ?_⟩
        · have := H1 x
          simp only [withCls_cls, hb] at this
          rw [this]
          exact ⟨fun ⟨d, hd, hx⟩ => ⟨d, hd, (hm d hd x).1 hx⟩,
            fun ⟨d, hd, hx⟩ => ⟨d, hd, (hm d hd x).2 hx⟩⟩
        · refine List.Pairwise.imp_of_mem ?_ H2
          intro d e hd he hde x hx
          exact hde x ⟨(hm d hd x).2 hx.1, (hm e he x).2 hx.2⟩
      · rintro ⟨H1, H2⟩
        refine ⟨fun x => ?_, ?_⟩
        · simp only [withCls_cls, hb]
          rw [H1 x]
          exact ⟨fun ⟨d, hd, hx⟩ => ⟨d, hd, (hm d hd x).2 hx⟩,
            fun ⟨d, hd, hx⟩ => ⟨d, hd, (hm d hd x).1 hx⟩⟩
        · refine List.Pairwise.imp_of_mem ?_ H2
          intro d e hd he hde x hx
          exact hde x ⟨(hm d hd x).1 hx.1, (hm e he x).1 hx.2⟩
  | disjointObjectProperties rs => simp only [sat, withCls_prop]
  | functional r => simp only [sat, withCls_prop]
  | inverseFunctional r => simp only [sat, withCls_prop]
  | reflexive r => simp only [sat, withCls_prop]
  | irreflexive r => simp only [sat, withCls_prop]
  | asymmetric r => simp only [sat, withCls_prop]
  | subDataPropertyOf p q => simp only [sat, withCls_dp]
  | equivalentDataProperties ps => simp only [sat, withCls_dp]
  | disjointDataProperties ps => simp only [sat, withCls_dp]
  | dataDomain p d =>
      simp only [sat, withCls_dp]
      have h1 := hE d (fun a ha => by simpa [Axiom.classIRIs] using ha)
      simp only [h1]
  | dataRange p r => simp only [sat, withCls_dp, withCls_drExt]
  | functionalData p => simp only [sat, withCls_dp]
  | datatypeDefinition t r => simp only [sat, withCls_dt, withCls_drExt]
  | hasKey d rs ps =>
      simp only [sat, withCls_dp, withCls_prop, withCls_isNamed]
      have h1 := hE d (fun a ha => by simpa [Axiom.classIRIs] using ha)
      simp only [h1]
  | sameIndividual as => simp only [sat, withCls_ind]
  | differentIndividuals as => simp only [sat, withCls_ind]
  | classAssertion d a =>
      simp only [sat, withCls_ind]
      exact hE d (fun a ha => by simpa [Axiom.classIRIs] using ha) _
  | objectPropertyAssertion r a b => simp only [sat, withCls_prop, withCls_ind]
  | negativeObjectPropertyAssertion r a b => simp only [sat, withCls_prop, withCls_ind]
  | dataPropertyAssertion p a l => simp only [sat, withCls_dp, withCls_ind]
  | negativeDataPropertyAssertion p a l => simp only [sat, withCls_dp, withCls_ind]
  | declareDataProperty _ => simp only [sat]
  | declareNamedIndividual _ => simp only [sat]
  | declareDatatype _ => simp only [sat]
  | declareAnnotationProperty _ => simp only [sat]

end Interp

/-- The agreement lemma: changing the extension of a class IRI that `O` does
not mention keeps a model of `O` a model of `O`. -/
theorem model_update_unmentioned {D : DatatypeMap} {Domain : Type} {O : Ontology} {I : Interp D Domain}
    {Q : IRI} (hQ : ¬ O.mentionsClass Q) (f : Domain → Prop) (hI : Model O I) :
    Model O (I.withCls fun b => if b = Q then f else I.cls b) := by
  intro ax hax
  refine (Interp.sat_withCls I _ _ ax ?_).2 (hI ax hax)
  intro a ha
  have : a ≠ Q := by
    rintro rfl
    exact hQ ⟨ax, hax, ha⟩
  simp [this]

/-! ## The probe reading of unsatisfiability and inconsistency

Statements fixed by the lead; proofs by the translation task. Both rest on
the agreement lemma: changing the extension of a class IRI that `O` does not
mention preserves being a model of `O`. -/

/-- For distinct IRIs `P`, `Q` not mentioned by `O`, `O` is inconsistent
exactly when it entails `SubClassOf(P Q)`. -/
theorem inconsistent_iff_entailsSub_fresh {O : Ontology} {P Q : IRI}
    (hP : ¬ O.mentionsClass P) (hQ : ¬ O.mentionsClass Q) (hPQ : P ≠ Q) :
    Inconsistent O ↔ EntailsSub O P Q := by
  refine ⟨fun h => entailsSub_of_inconsistent h P Q, ?_⟩
  intro hsub D Domain _ I hI
  obtain ⟨x⟩ := ‹Nonempty Domain›
  have hI' := model_update_unmentioned hQ (fun _ => False)
    (model_update_unmentioned hP (fun _ => True) hI)
  have := hsub D Domain _ hI' x
  simp [hPQ] at this

/-- For an IRI `Q` not mentioned by `O` and different from `A`, the class
`A` is unsatisfiable exactly when `O` entails `SubClassOf(A Q)`. -/
theorem unsatisfiable_iff_entailsSub_fresh {O : Ontology} {A Q : IRI}
    (hQ : ¬ O.mentionsClass Q) (hAQ : A ≠ Q) :
    Unsatisfiable O A ↔ EntailsSub O A Q := by
  constructor
  · intro h D Domain _ I hI x hx
    exact absurd hx (h D Domain I hI x)
  · intro hsub D Domain _ I hI x hx
    have hI' := model_update_unmentioned hQ (fun _ => False) hI
    have := hsub D Domain _ hI' x
    simp [hAQ] at this
    exact this hx

#print axioms inconsistent_iff_entailsSub_fresh
#print axioms unsatisfiable_iff_entailsSub_fresh

end ContextCalculus.OWL
