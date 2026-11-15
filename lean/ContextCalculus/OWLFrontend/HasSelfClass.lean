import ContextCalculus.OWLFrontend.ZeroRoute
import ContextCalculus.OWLFrontend.RowsG

/-!
# `ObjectHasSelf` in class expressions (stage C3e, item 1)

`docs/V1.7.0-C3-ROLES-DESIGN.md`, deviation D14. `hsOff O` replaces every
`ObjectHasSelf(r)` of a class expression by a fresh class name `X_r`
(`selfName`, longer than every class IRI of `O`) and adds
`SubObjectPropertyOf(r r)` for each such `r`, so the translation indexes
the property. The pairs `(X_r, r)` (`selfPairs`) are the definitions
`X_r ≡ ∃r.Self`; they go to the Self encoding as the self clauses
`selfR [X_r] r` and `selfL r [X_r]` (`pairCls`).

* `ext_selfToCls`, `sat_selfToCls`: the rewriting read in an interpretation
  whose class `X_r` is `{x | r(x, x)}`.
* `consistentAt_hsOff`: `O` is consistent iff `hsOff O` has a model in which
  every pair holds.
* `shoiqd_upRC`, `shoiqd_downRC`: the model maps of the translation with the
  role table and the class correspondence for the requested names.
* `sroiqH_consistent`: models of the rewritten ontology with the pairs are
  data models of the Self encoding with the pair clauses.
* `owlHSCore` (`_sound`, `_isSome_iff`) and `owlC3HConsistent`: the route of
  `owlC3ZConsistent` first, then this one.
-/

namespace ContextCalculus.OWL

/-! ## The rewriting -/

/-- Replace every `ObjectHasSelf(r)` by the class `f r`. -/
def ClassExpr.selfToCls (f : ObjProp → IRI) : ClassExpr → ClassExpr
  | .cls a => .cls a
  | .thing => .thing
  | .nothing => .nothing
  | .and cs => .and (cs.attach.map fun c => c.1.selfToCls f)
  | .or cs => .or (cs.attach.map fun c => c.1.selfToCls f)
  | .not c => .not (c.selfToCls f)
  | .some r c => .some r (c.selfToCls f)
  | .all r c => .all r (c.selfToCls f)
  | .oneOf as => .oneOf as
  | .hasValue r a => .hasValue r a
  | .hasSelf r => .cls (f r)
  | .min n r c => .min n r (c.selfToCls f)
  | .max n r c => .max n r (c.selfToCls f)
  | .exact n r c => .exact n r (c.selfToCls f)
  | .dataSome p r => .dataSome p r
  | .dataAll p r => .dataAll p r
  | .dataHasValue p l => .dataHasValue p l
  | .dataMin n p r => .dataMin n p r
  | .dataMax n p r => .dataMax n p r
  | .dataExact n p r => .dataExact n p r
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem c.2; omega)

/-- The properties of the `ObjectHasSelf` expressions of a class expression. -/
def ClassExpr.selfRoles : ClassExpr → List ObjProp
  | .and cs | .or cs => cs.attach.flatMap fun ⟨c, _⟩ => c.selfRoles
  | .not c | .some _ c | .all _ c => c.selfRoles
  | .min _ _ c | .max _ _ c | .exact _ _ c => c.selfRoles
  | .hasSelf r => [r]
  | _ => []
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

def Axiom.selfToCls (f : ObjProp → IRI) : Axiom → Axiom
  | .subClassOf c d => .subClassOf (c.selfToCls f) (d.selfToCls f)
  | .equivalentClasses cs => .equivalentClasses (cs.map (·.selfToCls f))
  | .disjointClasses cs => .disjointClasses (cs.map (·.selfToCls f))
  | .domain r c => .domain r (c.selfToCls f)
  | .range r c => .range r (c.selfToCls f)
  | .disjointUnion a cs => .disjointUnion a (cs.map (·.selfToCls f))
  | .dataDomain p c => .dataDomain p (c.selfToCls f)
  | .hasKey c rs ps => .hasKey (c.selfToCls f) rs ps
  | .classAssertion c a => .classAssertion (c.selfToCls f) a
  | ax => ax

def Axiom.selfRoles : Axiom → List ObjProp
  | .subClassOf c d => c.selfRoles ++ d.selfRoles
  | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs =>
      cs.flatMap ClassExpr.selfRoles
  | .domain _ c | .range _ c | .dataDomain _ c | .hasKey c _ _ | .classAssertion c _ =>
      c.selfRoles
  | _ => []

/-! ## Semantics of the rewriting -/

variable {DM : DatatypeMap} {D : Type}

theorem withCls_prop (I : Interp DM D) (c : IRI → D → Prop) (r : ObjProp) :
    (I.withCls c).prop r = I.prop r := by
  cases r <;> rfl

theorem withCls_chain (I : Interp DM D) (c : IRI → D → Prop) :
    ∀ rs : List ObjProp, (I.withCls c).chain rs = I.chain rs
  | [] => rfl
  | r :: rs => by
    funext x z
    simp only [Interp.chain, withCls_prop, withCls_chain I c rs]

theorem mem_names_list {cs : List ClassExpr} {c : ClassExpr} (hc : c ∈ cs) {b : IRI}
    (hb : b ∈ c.names) :
    b ∈ (ClassExpr.and cs).names ∧ b ∈ (ClassExpr.or cs).names := by
  rw [ClassExpr.names, ClassExpr.names]
  exact ⟨List.mem_flatMap.2 ⟨⟨c, hc⟩, List.mem_attach _ _, hb⟩,
    List.mem_flatMap.2 ⟨⟨c, hc⟩, List.mem_attach _ _, hb⟩⟩

theorem mem_selfRoles_list {cs : List ClassExpr} {c : ClassExpr} (hc : c ∈ cs) {r : ObjProp}
    (hr : r ∈ c.selfRoles) :
    r ∈ (ClassExpr.and cs).selfRoles ∧ r ∈ (ClassExpr.or cs).selfRoles := by
  rw [ClassExpr.selfRoles, ClassExpr.selfRoles]
  exact ⟨List.mem_flatMap.2 ⟨⟨c, hc⟩, List.mem_attach _ _, hr⟩,
    List.mem_flatMap.2 ⟨⟨c, hc⟩, List.mem_attach _ _, hr⟩⟩

/-- **The rewritten class expression** in an interpretation whose classes
agree with `I` on the class names of `C` and whose class `f r` is the self
loops of `r`, for every `ObjectHasSelf(r)` of `C`. -/
theorem ext_selfToCls (I : Interp DM D) (c : IRI → D → Prop) (f : ObjProp → IRI) :
    ∀ C : ClassExpr, (∀ b ∈ C.names, c b = I.cls b) →
      (∀ r ∈ C.selfRoles, ∀ x, c (f r) x ↔ I.prop r x x) →
      (I.withCls c).ext (C.selfToCls f) = I.ext C
  | .cls a, h1, _ => by
    rw [ClassExpr.selfToCls]; funext x; rw [Interp.ext, Interp.ext]
    exact congrFun (h1 a (by simp [ClassExpr.names])) x
  | .thing, _, _ => by rw [ClassExpr.selfToCls]; funext x; rw [Interp.ext, Interp.ext]
  | .nothing, _, _ => by rw [ClassExpr.selfToCls]; funext x; rw [Interp.ext, Interp.ext]
  | .and cs, h1, h2 => by
    have ih : ∀ d ∈ cs, (I.withCls c).ext (d.selfToCls f) = I.ext d := fun d hd =>
      ext_selfToCls I c f d (fun b hb => h1 b (mem_names_list hd hb).1)
        (fun r hr => h2 r (mem_selfRoles_list hd hr).1)
    rw [ClassExpr.selfToCls]
    funext x
    simp only [Interp.ext]
    apply propext
    constructor
    · intro h' d hd
      have := h' (d.selfToCls f) (List.mem_map.2 ⟨⟨d, hd⟩, List.mem_attach _ _, rfl⟩)
      rwa [ih d hd] at this
    · intro h' d' hd'
      obtain ⟨⟨d, hd⟩, -, rfl⟩ := List.mem_map.1 hd'
      rw [ih d hd]
      exact h' d hd
  | .or cs, h1, h2 => by
    have ih : ∀ d ∈ cs, (I.withCls c).ext (d.selfToCls f) = I.ext d := fun d hd =>
      ext_selfToCls I c f d (fun b hb => h1 b (mem_names_list hd hb).2)
        (fun r hr => h2 r (mem_selfRoles_list hd hr).2)
    rw [ClassExpr.selfToCls]
    funext x
    simp only [Interp.ext]
    apply propext
    constructor
    · rintro ⟨d', hd', h'⟩
      obtain ⟨⟨d, hd⟩, -, rfl⟩ := List.mem_map.1 hd'
      rw [ih d hd] at h'
      exact ⟨d, hd, h'⟩
    · rintro ⟨d, hd, h'⟩
      refine ⟨d.selfToCls f, List.mem_map.2 ⟨⟨d, hd⟩, List.mem_attach _ _, rfl⟩, ?_⟩
      rw [ih d hd]; exact h'
  | .not d, h1, h2 => by
    have ih := ext_selfToCls I c f d (fun b hb => h1 b (by rw [ClassExpr.names]; exact hb))
      (fun r hr => h2 r (by rw [ClassExpr.selfRoles]; exact hr))
    rw [ClassExpr.selfToCls]; funext x; simp only [Interp.ext, ih]
  | .some s d, h1, h2 => by
    have ih := ext_selfToCls I c f d (fun b hb => h1 b (by rw [ClassExpr.names]; exact hb))
      (fun r hr => h2 r (by rw [ClassExpr.selfRoles]; exact hr))
    rw [ClassExpr.selfToCls]; funext x; simp only [Interp.ext, ih, withCls_prop]
  | .all s d, h1, h2 => by
    have ih := ext_selfToCls I c f d (fun b hb => h1 b (by rw [ClassExpr.names]; exact hb))
      (fun r hr => h2 r (by rw [ClassExpr.selfRoles]; exact hr))
    rw [ClassExpr.selfToCls]; funext x; simp only [Interp.ext, ih, withCls_prop]
  | .oneOf as, _, _ => by rw [ClassExpr.selfToCls]; funext x; rw [Interp.ext, Interp.ext]; rfl
  | .hasValue s a, _, _ => by
    rw [ClassExpr.selfToCls]; funext x; simp only [Interp.ext, withCls_prop]; rfl
  | .hasSelf s, _, h2 => by
    rw [ClassExpr.selfToCls]; funext x; rw [Interp.ext, Interp.ext]
    exact propext (h2 s (by simp [ClassExpr.selfRoles]) x)
  | .min n s d, h1, h2 => by
    have ih := ext_selfToCls I c f d (fun b hb => h1 b (by rw [ClassExpr.names]; exact hb))
      (fun r hr => h2 r (by rw [ClassExpr.selfRoles]; exact hr))
    rw [ClassExpr.selfToCls]; funext x; simp only [Interp.ext, ih, withCls_prop]
  | .max n s d, h1, h2 => by
    have ih := ext_selfToCls I c f d (fun b hb => h1 b (by rw [ClassExpr.names]; exact hb))
      (fun r hr => h2 r (by rw [ClassExpr.selfRoles]; exact hr))
    rw [ClassExpr.selfToCls]; funext x; simp only [Interp.ext, ih, withCls_prop]
  | .exact n s d, h1, h2 => by
    have ih := ext_selfToCls I c f d (fun b hb => h1 b (by rw [ClassExpr.names]; exact hb))
      (fun r hr => h2 r (by rw [ClassExpr.selfRoles]; exact hr))
    rw [ClassExpr.selfToCls]; funext x; simp only [Interp.ext, ih, withCls_prop]
  | .dataSome p r, _, _ => by rw [ClassExpr.selfToCls]; funext x; rw [Interp.ext, Interp.ext]; rfl
  | .dataAll p r, _, _ => by rw [ClassExpr.selfToCls]; funext x; rw [Interp.ext, Interp.ext]; rfl
  | .dataHasValue p l, _, _ => by
    rw [ClassExpr.selfToCls]; funext x; rw [Interp.ext, Interp.ext]; rfl
  | .dataMin n p r, _, _ => by rw [ClassExpr.selfToCls]; funext x; rw [Interp.ext, Interp.ext]; rfl
  | .dataMax n p r, _, _ => by rw [ClassExpr.selfToCls]; funext x; rw [Interp.ext, Interp.ext]; rfl
  | .dataExact n p r, _, _ => by
    rw [ClassExpr.selfToCls]; funext x; rw [Interp.ext, Interp.ext]; rfl
termination_by C => sizeOf C
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

/-- **The rewritten axiom.** -/
theorem sat_selfToCls (I : Interp DM D) (c : IRI → D → Prop) (f : ObjProp → IRI) {ax : Axiom}
    (h1 : ∀ b ∈ ax.classNames, c b = I.cls b)
    (h2 : ∀ r ∈ ax.selfRoles, ∀ x, c (f r) x ↔ I.prop r x x) (N : List IRI) :
    (I.withCls c).sat N (ax.selfToCls f) ↔ I.sat N ax := by
  have hp := withCls_prop I c
  have hl : ∀ {cs : List ClassExpr}, (∀ b ∈ cs.flatMap ClassExpr.names, c b = I.cls b) →
      (∀ r ∈ cs.flatMap ClassExpr.selfRoles, ∀ x, c (f r) x ↔ I.prop r x x) →
      ∀ d ∈ cs, (I.withCls c).ext (d.selfToCls f) = I.ext d := fun h1 h2 d hd =>
    ext_selfToCls I c f d (fun b hb => h1 b (List.mem_flatMap.2 ⟨d, hd, hb⟩))
      (fun r hr => h2 r (List.mem_flatMap.2 ⟨d, hd, hr⟩))
  cases ax with
  | subClassOf d e =>
    simp only [Axiom.classNames, Axiom.selfRoles, List.mem_append] at h1 h2
    simp only [Axiom.selfToCls, Interp.sat,
      ext_selfToCls I c f d (fun b hb => h1 b (Or.inl hb)) (fun r hr => h2 r (Or.inl hr)),
      ext_selfToCls I c f e (fun b hb => h1 b (Or.inr hb)) (fun r hr => h2 r (Or.inr hr))]
  | equivalentClasses cs =>
    have ih := hl h1 h2
    simp only [Axiom.selfToCls, Interp.sat, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    constructor
    · intro h d hd e he x hx
      have := h d hd e he x
      rw [ih d hd, ih e he] at this
      exact this hx
    · intro h d hd e he x hx
      rw [ih d hd] at hx
      rw [ih e he]
      exact h d hd e he x hx
  | disjointClasses cs =>
    have ih := hl h1 h2
    simp only [Axiom.selfToCls, Interp.sat, List.pairwise_map]
    constructor
    · exact fun h => h.imp_of_mem fun hd he h' x => by
        have := h' x; rwa [ih _ hd, ih _ he] at this
    · exact fun h => h.imp_of_mem fun hd he h' x => by
        rw [ih _ hd, ih _ he]; exact h' x
  | domain s d =>
    simp only [Axiom.selfToCls, Interp.sat, hp,
      ext_selfToCls I c f d h1 h2]
  | range s d =>
    simp only [Axiom.selfToCls, Interp.sat, hp,
      ext_selfToCls I c f d h1 h2]
  | disjointUnion a cs =>
    simp only [Axiom.classNames, List.mem_cons, Axiom.selfRoles] at h1 h2
    have ih := hl (fun b hb => h1 b (Or.inr hb)) h2
    have ha := h1 a (Or.inl rfl)
    simp only [Axiom.selfToCls, Interp.sat, List.pairwise_map, List.mem_map]
    have e1 : ∀ x, (∃ d, (∃ d', d' ∈ cs ∧ d'.selfToCls f = d) ∧ (I.withCls c).ext d x) ↔
        ∃ d ∈ cs, I.ext d x := fun x =>
      ⟨fun ⟨_, ⟨d, hd, he⟩, hx⟩ => ⟨d, hd, by rw [← he, ih d hd] at hx; exact hx⟩,
        fun ⟨d, hd, hx⟩ => ⟨_, ⟨d, hd, rfl⟩, by rw [ih d hd]; exact hx⟩⟩
    have e0 : ∀ x, (I.withCls c).cls a x ↔ I.cls a x := fun x => by
      show c a x ↔ I.cls a x; rw [ha]
    simp only [e1, e0]
    refine and_congr Iff.rfl ⟨fun h => h.imp_of_mem fun hd he h' x => ?_,
      fun h => h.imp_of_mem fun hd he h' x => ?_⟩
    · have := h' x; rwa [ih _ hd, ih _ he] at this
    · rw [ih _ hd, ih _ he]; exact h' x
  | dataDomain p d =>
    simp only [Axiom.selfToCls, Interp.sat, ext_selfToCls I c f d h1 h2]; rfl
  | hasKey d rs ps =>
    simp only [Axiom.selfToCls, Interp.sat, ext_selfToCls I c f d h1 h2, hp]; rfl
  | classAssertion d a =>
    simp only [Axiom.selfToCls, Interp.sat, ext_selfToCls I c f d h1 h2]; rfl
  | subObjectPropertyOf rs r =>
    simp only [Axiom.selfToCls, Interp.sat, withCls_chain, hp]
  | _ => exact Iff.rfl

theorem noKey_selfToCls (f : ObjProp → IRI) (ax : Axiom) : (ax.selfToCls f).noKey = ax.noKey := by
  cases ax <;> rfl

end ContextCalculus.OWL

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ

variable {DM : DatatypeMap} {D : Type}

/-! ## Fresh class names -/

/-- The prefix of the fresh names: longer than every class IRI of `O`. -/
def selfBase (O : Ontology) : String :=
  "urn:km:owl-self:".pushn '#' (SRIQKB.maxLen (O.axioms.flatMap Axiom.classNames))

/-- An injective tag of a property expression. -/
def selfTag : ObjProp → String
  | .named p => "+" ++ p
  | .inv p => "-" ++ p
  | .top => "T"
  | .bot => "B"

/-- The fresh class name of `ObjectHasSelf(r)`. -/
def selfName (base : String) (r : ObjProp) : IRI := base ++ selfTag r

theorem selfTag_inj {r s : ObjProp} (h : selfTag r = selfTag s) : r = s := by
  cases r <;> cases s <;> simp only [selfTag, ObjProp.named.injEq, ObjProp.inv.injEq] at h ⊢ <;>
    first
    | exact (String.append_right_inj _).1 h
    | (have h' := congrArg (fun s => s.toList.head?) h; simp [String.toList_append] at h')

theorem selfName_inj {base : String} {r s : ObjProp} (h : selfName base r = selfName base s) :
    r = s :=
  selfTag_inj ((String.append_right_inj base).1 h)

theorem ne_selfName {O : Ontology} {b : IRI} (hb : b ∈ O.axioms.flatMap Axiom.classNames)
    (r : ObjProp) : b ≠ selfName (selfBase O) r := by
  intro he
  have h1 := SRIQKB.length_le_maxLen hb
  have h2 : (selfName (selfBase O) r).length =
      (selfBase O).length + (selfTag r).length := String.length_append _ _
  rw [← he] at h2
  simp only [selfBase, String.length_pushn] at h2
  have : "urn:km:owl-self:".length = 16 := by decide
  omega

/-! ## The rewritten ontology -/

/-- The properties of the `ObjectHasSelf` expressions of `O`. -/
def selfRolesO (O : Ontology) : List ObjProp := (O.axioms.flatMap Axiom.selfRoles).eraseDups

/-- The definitions `X_r ≡ ∃r.Self`, as pairs. -/
def selfPairs (O : Ontology) : List (IRI × ObjProp) :=
  (selfRolesO O).map fun r => (selfName (selfBase O) r, r)

/-- The ontology with its `ObjectHasSelf` expressions replaced by fresh
class names, and `SubObjectPropertyOf(r r)` for their properties. -/
def hsOff (O : Ontology) : Ontology :=
  ⟨O.axioms.map (Axiom.selfToCls (selfName (selfBase O))) ++
    (selfRolesO O).map fun r => .subObjectPropertyOf [r] r⟩

/-- The pairs hold: `X_r` is the set of `r`-loops. -/
def PairsHold (P : List (IRI × ObjProp)) (I : Interp DM D) : Prop :=
  ∀ p ∈ P, ∀ x, I.cls p.1 x ↔ I.prop p.2 x x

/-- `I` with the fresh classes read as loops. -/
def selfI (O : Ontology) (I : Interp DM D) : Interp DM D :=
  I.withCls fun b x => (∃ r, b = selfName (selfBase O) r ∧ I.prop r x x) ∨
    ((∀ r, b ≠ selfName (selfBase O) r) ∧ I.cls b x)

theorem selfI_old {O : Ontology} (I : Interp DM D) {b : IRI}
    (hb : b ∈ O.axioms.flatMap Axiom.classNames) : (selfI O I).cls b = I.cls b := by
  funext x
  apply propext
  show ((∃ r, b = selfName (selfBase O) r ∧ I.prop r x x) ∨
    ((∀ r, b ≠ selfName (selfBase O) r) ∧ I.cls b x)) ↔ I.cls b x
  constructor
  · rintro (⟨r, rfl, -⟩ | ⟨-, h⟩)
    · exact absurd rfl (ne_selfName hb r)
    · exact h
  · exact fun h => Or.inr ⟨ne_selfName hb, h⟩

theorem selfI_new {O : Ontology} (I : Interp DM D) (r : ObjProp) (x : D) :
    (selfI O I).cls (selfName (selfBase O) r) x ↔ I.prop r x x := by
  show ((∃ r', selfName (selfBase O) r = selfName (selfBase O) r' ∧ I.prop r' x x) ∨
    ((∀ r', selfName (selfBase O) r ≠ selfName (selfBase O) r') ∧ _)) ↔ _
  constructor
  · rintro (⟨r', he, h⟩ | ⟨h, -⟩)
    · rwa [selfName_inj he]
    · exact absurd rfl (h r)
  · exact fun h => Or.inl ⟨r, rfl, h⟩

theorem noKey_hsOff {O : Ontology} (h : (hsOff O).noKey = true) : O.noKey = true := by
  simp only [Ontology.noKey, hsOff, List.all_append, List.all_map, Bool.and_eq_true,
    List.all_eq_true, Function.comp_apply, noKey_selfToCls] at h
  simpa only [Ontology.noKey, List.all_eq_true] using h.1

theorem mem_selfRolesO {O : Ontology} {ax : Axiom} (hax : ax ∈ O.axioms) {r : ObjProp}
    (hr : r ∈ ax.selfRoles) : r ∈ selfRolesO O :=
  List.mem_eraseDups.2 (List.mem_flatMap.2 ⟨ax, hax, hr⟩)

/-- **Up.** A model of `O` with the fresh classes read as loops is a model
of `hsOff O` in which the pairs hold. -/
theorem model_hsOff_up {O : Ontology} (hk : O.noKey = true) {I : Interp DM D}
    (hI : OWL.Model O I) : OWL.Model (hsOff O) (selfI O I) ∧ PairsHold (selfPairs O) (selfI O I) := by
  have hk' : ∀ ax ∈ O.axioms, ax.noKey = true := by
    simpa [Ontology.noKey, List.all_eq_true] using hk
  refine ⟨fun ax' hax' => ?_, fun p hp x => ?_⟩
  · rcases List.mem_append.1 hax' with hm | hm
    · obtain ⟨ax, hax, rfl⟩ := List.mem_map.1 hm
      rw [sat_N_noKey _ (by rw [noKey_selfToCls]; exact hk' ax hax) _ O.namedIndividuals]
      refine (sat_selfToCls I _ _ (fun b hb => selfI_old I
        (List.mem_flatMap.2 ⟨ax, hax, hb⟩)) (fun r _ x => selfI_new I r x) _).2 (hI ax hax)
    · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hm
      exact sat_incl _ _ r
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hp
    have hp : (selfI O I).prop r = I.prop r := withCls_prop I _ r
    show (selfI O I).cls (selfName (selfBase O) r) x ↔ (selfI O I).prop r x x
    rw [selfI_new, hp]

/-- **Down.** A model of `hsOff O` in which the pairs hold is a model of `O`. -/
theorem model_hsOff_down {O : Ontology} (hk : O.noKey = true) {J : Interp DM D}
    (hJ : OWL.Model (hsOff O) J) (hP : PairsHold (selfPairs O) J) : OWL.Model O J := by
  have hk' : ∀ ax ∈ O.axioms, ax.noKey = true := by
    simpa [Ontology.noKey, List.all_eq_true] using hk
  intro ax hax
  have hs := hJ _ (List.mem_append_left _ (List.mem_map_of_mem hax))
  rw [sat_N_noKey _ (by rw [noKey_selfToCls]; exact hk' ax hax) _ O.namedIndividuals] at hs
  exact (sat_selfToCls J J.cls _ (fun _ _ => rfl) (fun r hr x =>
    hP _ (List.mem_map.2 ⟨r, mem_selfRolesO hax hr, rfl⟩) x) _).1 hs

/-- **Consistency.** -/
theorem consistentAt_hsOff {O : Ontology} (hk : O.noKey = true) :
    ConsistentAt DM O ↔ ∃ (Dom : Type) (_ : Nonempty Dom) (I : Interp DM Dom),
      OWL.Model (hsOff O) I ∧ PairsHold (selfPairs O) I := by
  constructor
  · rintro ⟨Dom, hD, I, hI⟩
    exact ⟨Dom, hD, selfI O I, model_hsOff_up hk hI⟩
  · rintro ⟨Dom, hD, I, hI, hP⟩
    exact ⟨Dom, hD, I, model_hsOff_down hk hI hP⟩

/-! ## The translation with the class correspondence for requested names -/

/-- The concept of each requested name stands for its class. -/
def ClassCorr (T : SRIQDKBTranslation) (requested : List IRI) {Dom : Type}
    (K : SRI.Interp Dom (Fin T.obj.conceptCount) (Fin T.obj.roleCount)) (I : Interp DM Dom) : Prop :=
  ∀ s ∈ requested, ∀ ix, nameIx T.obj s = some ix → ∀ y, K.c ix y ↔ I.cls s y

/-- **Up, with roles and requested classes** (`shoiqd_upR` with the class
correspondence of `shoiqd_up`). -/
theorem shoiqd_upRC (pat : String → String → Prop) {O : Ontology} {requested : List IRI}
    {T : SRIQDKBTranslation} (h : translateSHOIQD O requested = some T)
    {Dom : Type} [Nonempty Dom] (I : Interp (owl2MapP pat) Dom) (hI : OWL.Model O I) :
    ∃ (V : Type) (atom : Fin T.tab.length → V → Prop), owlTheory pat (spec T.tab) V atom ∧
      ∃ K : ContextCalculus.SRIQD.DInterp Dom V (Fin T.obj.conceptCount) (Fin T.obj.roleCount)
          (Fin T.dps.length),
        ContextCalculus.SRIQD.models atom K (SRIQN.dbase (dosn T (nomNames O requested))) ∧
        (∀ a ∈ SRIQN.dnoms (dosn T (nomNames O requested)), SRIQN.NomAt K.toInterp a) ∧
        RoleCorr T K.toInterp I ∧ ClassCorr T requested K.toInterp I := by
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
    fun r hb k hk R hfin x y => ?_, fun s hs ix hix y => ?_⟩
  · rw [dnoms_dosn] at hx
    obtain ⟨s, hs, hsx⟩ := List.mem_filterMap.1 hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
    exact ⟨I.ind (.named a), fun y => (hcs _ (List.mem_append_right _ hs) x hsx y).trans
      (upI_nom I ha y)⟩
  · have := hr r hb k hk R hfin x y
    cases r <;> exact this
  · have := hcs s (List.mem_append_left _ hs) ix hix y
    rwa [upI_old I (List.mem_append_right _ hs)] at this

/-- **Down, with roles and requested classes.** -/
theorem shoiqd_downRC (pat : String → String → Prop) {O : Ontology} {requested : List IRI}
    {T : SRIQDKBTranslation} (h : translateSHOIQD O requested = some T)
    {Dom V : Type} [Nonempty Dom] {atom : Fin T.tab.length → V → Prop}
    (hΘ : owlTheory pat (spec T.tab) V atom)
    (K : ContextCalculus.SRIQD.DInterp Dom V (Fin T.obj.conceptCount) (Fin T.obj.roleCount)
      (Fin T.dps.length))
    (hK : ContextCalculus.SRIQD.models atom K (SRIQN.dbase (dosn T (nomNames O requested))))
    (hn : ∀ a ∈ SRIQN.dnoms (dosn T (nomNames O requested)), SRIQN.NomAt K.toInterp a) :
    ∃ I : Interp (owl2MapP pat) Dom, OWL.Model O I ∧ RoleCorr T K.toInterp I ∧
      ClassCorr T requested K.toInterp I := by
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
  obtain ⟨hM, hcls⟩ := nomOntD_down hO requested hI0 hsing
  refine ⟨downI O requested I0, hM, fun r hb k hk R hfin x y => ?_, fun s hs ix hix y => ?_⟩
  · have := hr r hb k hk R hfin x y
    cases r <;> exact this.symm
  · rw [hcls]
    exact (hcs s (List.mem_append_left _ hs) ix hix y).symm

/-! ## The pair clauses -/

/-- The self clauses `selfR [X] R` and `selfL R [X]` of a pair. -/
def pairClause (T : SRIQDKBTranslation) (p : IRI × ObjProp) :
    Option (List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) :=
  if p.2.isBasic then
    match nameIx T.obj p.1, roleOfT T p.2 with
    | some a, some R => some [.selfR [a] R, .selfL R [a]]
    | _, _ => none
  else none

def pairCls (T : SRIQDKBTranslation) (P : List (IRI × ObjProp)) :
    Option (List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) :=
  SRIQKB.collect (pairClause T) P

section Corr

variable {T : SRIQDKBTranslation} {Dom : Type}

theorem sat_pairClause {K : SRI.Interp Dom (Fin T.obj.conceptCount) (Fin T.obj.roleCount)}
    {I : Interp DM Dom} {P : List (IRI × ObjProp)} (hR : RoleCorr T K I)
    (hC : ClassCorr T (P.map Prod.fst) K I) {p : IRI × ObjProp} (hp : p ∈ P)
    {l : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))}
    (h : pairClause T p = some l) :
    (∀ sc ∈ l, SRIQN.satS K sc) ↔ ∀ x, I.cls p.1 x ↔ I.prop p.2 x x := by
  unfold pairClause at h
  split_ifs at h with hb
  split at h
  · next a R ha hR' =>
    simp only [Option.some.injEq] at h
    subst h
    have hc : ∀ x, K.c a x ↔ I.cls p.1 x := hC p.1 (List.mem_map_of_mem hp) a ha
    have hr : ∀ x, K.rt R x x ↔ I.prop p.2 x x := fun x => roleCorr_of hR hb hR' x x
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, SRIQN.satS, exists_eq_left]
    constructor
    · rintro ⟨h1, h2⟩ x
      exact ⟨fun hx => (hr x).1 (h1 x ((hc x).2 hx)), fun hx => (hc x).1 (h2 x ((hr x).2 hx))⟩
    · intro h
      exact ⟨fun x hx => (hr x).2 ((h x).1 ((hc x).1 hx)),
        fun x hx => (hc x).2 ((h x).2 ((hr x).1 hx))⟩
  · cases h

theorem sat_pairCls {K : SRI.Interp Dom (Fin T.obj.conceptCount) (Fin T.obj.roleCount)}
    {I : Interp DM Dom} {P : List (IRI × ObjProp)} (hR : RoleCorr T K I)
    (hC : ClassCorr T (P.map Prod.fst) K I) {PC} (hP : pairCls T P = some PC) :
    (∀ sc ∈ PC, SRIQN.satS K sc) ↔ PairsHold P I := by
  constructor
  · intro h p hp
    obtain ⟨l, hl, hsub⟩ := SRIQKB.collect_some hP p hp
    exact (sat_pairClause hR hC hp hl).1 fun sc hsc => h sc (hsub sc hsc)
  · intro h sc hsc
    obtain ⟨p, hp, l, hl, hsc'⟩ := SRIQKB.collect_mem hP sc hsc
    exact (sat_pairClause hR hC hp hl).2 (h p hp) sc hsc'

end Corr

/-- **Consistency with the pairs.** Models of the rewritten ontology in
which the pairs hold are the data models of the encoding with the self
clauses and the pair clauses. -/
theorem sroiqH_consistent (pat : String → String → Prop) {O : Ontology}
    (hO : O.isSROIQDSKB = true) {P : List (IRI × ObjProp)} {T : SRIQDKBTranslation}
    (hT : translateSHOIQD (roleOff (selfOff O)) (P.map Prod.fst) = some T) {E}
    (hE : roleCls T (selfOff O) = some E) {SC} (hS : selfCls T O = some SC) {PC}
    (hP : pairCls T P = some PC) :
    (∃ (Dom : Type) (_ : Nonempty Dom) (I : Interp (owl2MapP pat) Dom),
        OWL.Model O I ∧ PairsHold P I) ↔
      SRIQN.ConsistentDS (owlTheory pat (spec T.tab))
        (dosnC T (nomNames (roleOff (selfOff O)) (P.map Prod.fst)) E) (SC ++ PC) := by
  have hO' := selfOff_isSROIQDKB hO
  constructor
  · rintro ⟨Dom, hD, I, hI, hPI⟩
    obtain ⟨hI0, hIS⟩ := (model_selfOff hO I).1 hI
    obtain ⟨hI1, hI2⟩ := (model_roleOff hO' I).1 hI0
    obtain ⟨V, atom, hΘ, K, hK, hn, hC, hCC⟩ := shoiqd_upRC pat hT I hI1
    refine ⟨Dom, V, hD, atom, hΘ, K, ?_, by rw [dnoms_dosnC]; exact hn, ?_⟩
    · rw [dbase_dosnC, models_append_obj]
      exact ⟨by rw [← dbase_dosn T (nomNames (roleOff (selfOff O)) (P.map Prod.fst))]; exact hK,
        (sat_roleCls hC hE).2 hI2⟩
    · intro sc hsc
      rcases List.mem_append.1 hsc with h | h
      · exact (sat_selfCls hC hS).2 hIS sc h
      · exact (sat_pairCls hC hCC hP).2 hPI sc h
  · rintro ⟨Dom, V, hD, atom, hΘ, K, hK, hn, hSK⟩
    rw [dbase_dosnC, models_append_obj] at hK
    rw [dnoms_dosnC] at hn
    obtain ⟨I, hI, hC, hCC⟩ := shoiqd_downRC pat hT hΘ K (by rw [dbase_dosn]; exact hK.1) hn
    refine ⟨Dom, hD, I, (model_selfOff hO I).2
      ⟨(model_roleOff hO' I).2 ⟨hI, (sat_roleCls hC hE).1 hK.2⟩,
        (sat_selfCls hC hS).1 fun sc h => hSK sc (List.mem_append_left _ h)⟩,
      (sat_pairCls hC hCC hP).1 fun sc h => hSK sc (List.mem_append_right _ h)⟩

/-! ## The route -/

/-- The requested names of the pairs. -/
abbrev pairNames (P : List (IRI × ObjProp)) : List IRI := P.map Prod.fst

/-- The route on a rewritten ontology `O` with pairs `P`. -/
def owlHSCoreOn (O : Ontology) (P : List (IRI × ObjProp)) (hint : Option RawHint) : Option Bool :=
  if O.isSROIQDSKB && !P.isEmpty then
    match translateSHOIQD (roleOff (selfOff O)) (pairNames P) with
    | none => none
    | some T =>
      match roleCls T (selfOff O) with
      | none => none
      | some E =>
        match selfCls T O with
        | none => none
        | some SC =>
          match pairCls T P with
          | none => none
          | some PC =>
            if sroiqSOK T (nomNames (roleOff (selfOff O)) (pairNames P)) E (SC ++ PC) then
              some (sroiqSParts T (nomNames (roleOff (selfOff O)) (pairNames P)) E (SC ++ PC) hint)
            else none
  else none

theorem owlHSCoreOn_sound (pat : String → String → Prop) {O : Ontology} {P : List (IRI × ObjProp)}
    {hint : Option RawHint} {v : Bool} (h : owlHSCoreOn O P hint = some v) :
    v = true ↔ ∃ (Dom : Type) (_ : Nonempty Dom) (I : Interp (owl2MapP pat) Dom),
      OWL.Model O I ∧ PairsHold P I := by
  unfold owlHSCoreOn at h
  split_ifs at h with hO'
  have hO : O.isSROIQDSKB = true := (Bool.and_eq_true _ _ ▸ hO').1
  split at h
  · cases h
  next T hT =>
    split at h
    · cases h
    next E hE =>
      split at h
      · cases h
      next SC hS =>
        split at h
        · cases h
        next PC hP =>
          split_ifs at h with hok
          simp only [Option.some.injEq] at h
          subst h
          rw [sroiqSParts_iff pat hok, ← sroiqH_consistent pat hO hT hE hS hP]

/-- The checks of the route on the translation. -/
def HSChecks (O : Ontology) (P : List (IRI × ObjProp)) : Prop :=
  ∀ T, translateSHOIQD (roleOff (selfOff O)) (pairNames P) = some T →
    ∃ E, roleCls T (selfOff O) = some E ∧ ∃ SC, selfCls T O = some SC ∧
      ∃ PC, pairCls T P = some PC ∧
        sroiqSOK T (nomNames (roleOff (selfOff O)) (pairNames P)) E (SC ++ PC) = true

theorem owlHSCoreOn_isSome_iff (O : Ontology) (P : List (IRI × ObjProp)) (hint : Option RawHint) :
    (owlHSCoreOn O P hint).isSome = true ↔
      (O.isSROIQDSKB && !P.isEmpty) = true ∧ HSChecks O P := by
  constructor
  · intro h
    unfold owlHSCoreOn at h
    split_ifs at h with hO
    · refine ⟨hO, fun T' hT' => ?_⟩
      split at h
      · simp at h
      next T hT =>
        rw [hT] at hT'; cases hT'
        split at h
        · simp at h
        next E hE =>
          split at h
          · simp at h
          next SC hS =>
            split at h
            · simp at h
            next PC hP =>
              split_ifs at h with hok
              · exact ⟨E, hE, SC, hS, PC, hP, hok⟩
              · simp at h
    · simp at h
  · rintro ⟨hO, hc⟩
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1
      (translateSHOIQD_isSome (roleOff_isSHOIQDKB (selfOff_isSROIQDKB
        (Bool.and_eq_true _ _ ▸ hO).1)) (pairNames P))
    obtain ⟨E, hE, SC, hS, PC, hP, hok⟩ := hc T hT
    unfold owlHSCoreOn
    rw [if_pos hO, hT]
    dsimp only
    rw [hE]
    dsimp only
    rw [hS]
    dsimp only
    rw [hP]
    dsimp only
    rw [if_pos hok]
    rfl

theorem noKey_of_isSROIQDSKB_O {O : Ontology} (h : O.isSROIQDSKB = true) : O.noKey = true := by
  simp only [Ontology.isSROIQDSKB, List.all_eq_true] at h
  simp only [Ontology.noKey, List.all_eq_true]
  exact fun ax hax => noKey_of_isSROIQDSKB (h ax hax)

/-- **The route with `ObjectHasSelf` in class expressions**, on an ontology
without anonymous individuals. -/
def owlHSCore (O : Ontology) (hint : Option RawHint) : Option Bool :=
  owlHSCoreOn (hsOff O) (selfPairs O) hint

theorem owlHSCore_noKey {O : Ontology} {hint : Option RawHint}
    (h : (owlHSCore O hint).isSome = true) : O.noKey = true :=
  noKey_hsOff (noKey_of_isSROIQDSKB_O (Bool.and_eq_true _ _ ▸
    ((owlHSCoreOn_isSome_iff _ _ hint).1 h).1).1)

theorem owlHSCore_sound (pat : String → String → Prop) {O : Ontology} {hint : Option RawHint}
    {v : Bool} (h : owlHSCore O hint = some v) : v = true ↔ ConsistentAt (owl2MapP pat) O := by
  rw [consistentAt_hsOff (owlHSCore_noKey (by rw [h]; rfl))]
  exact owlHSCoreOn_sound pat h

theorem owlHSCore_isSome_iff (O : Ontology) (hint : Option RawHint) :
    (owlHSCore O hint).isSome = true ↔
      ((hsOff O).isSROIQDSKB && !(selfPairs O).isEmpty) = true ∧ HSChecks (hsOff O) (selfPairs O) :=
  owlHSCoreOn_isSome_iff _ _ hint

theorem noKey_of_anonOffK {W : List IRI} {O : Ontology} (h : (anonOff W O).noKey = true) :
    O.noKey = true := by
  simp only [Ontology.noKey, anonOff, List.all_map, List.all_eq_true, Function.comp_apply,
    noKey_mapI] at h
  simpa only [Ontology.noKey, List.all_eq_true] using h

/-- **Consistency** (stage C3e): `owlC3ZConsistent`, and when it declines,
the route with `ObjectHasSelf` in class expressions rewritten. -/
def owlC3HConsistent (O : Ontology) (hint : Option RawHint) : Option Bool :=
  match owlC3ZConsistent O hint with
  | some v => some v
  | none => owlHSCore (anonOff [] (duOff O)) hint

theorem owlC3HConsistent_sound (pat : String → String → Prop) {O : Ontology}
    {hint : Option RawHint} {v : Bool} (h : owlC3HConsistent O hint = some v) :
    v = true ↔ ConsistentAt (owl2MapP pat) O := by
  unfold owlC3HConsistent at h
  split at h
  next v' hv =>
    simp only [Option.some.injEq] at h
    subst h
    exact owlC3ZConsistent_sound pat hv
  next =>
    have hk : (duOff O).noKey = true := noKey_of_anonOffK (owlHSCore_noKey (by rw [h]; rfl))
    rw [owlHSCore_sound pat h, consistentAt_anonOff hk, consistentAt_duOff]

theorem owlC3HConsistent_isSome_iff (O : Ontology) (hint : Option RawHint) :
    (owlC3HConsistent O hint).isSome = true ↔
      (owlC3ZConsistent O hint).isSome = true ∨
        (((hsOff (anonOff [] (duOff O))).isSROIQDSKB &&
            !(selfPairs (anonOff [] (duOff O))).isEmpty) = true ∧
          HSChecks (hsOff (anonOff [] (duOff O))) (selfPairs (anonOff [] (duOff O)))) := by
  rw [← owlHSCore_isSome_iff _ hint]
  unfold owlC3HConsistent
  cases owlC3ZConsistent O hint <;> simp

/-! ## Rows -/

/-- The route of this file as a consistency procedure on any ontology. -/
def hsP (O : Ontology) (hint : Option RawHint) : Option Bool :=
  owlHSCore (anonOff [] (duOff O)) hint

theorem hsP_sound : ConsSound hsP := by
  intro pat O hint v h
  have hk : (duOff O).noKey = true := noKey_of_anonOffK (owlHSCore_noKey (by unfold hsP at h; rw [h]; rfl))
  rw [owlHSCore_sound pat h, consistentAt_anonOff hk, consistentAt_duOff]

/-- **Type row** (stage C3e): `owlC3ZTypeRow`, then this route. -/
def owlC3HTypeRow (O : Ontology) (C a : IRI) (hint : Option RawHint) : Option Bool :=
  match owlC3ZTypeRow O C a hint with
  | some v => some v
  | none => rowGType hsP O C a hint

def owlC3HSameRow (O : Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  match owlC3ZSameRow O a b hint with
  | some v => some v
  | none => rowGSame hsP O a b hint

def owlC3HSubRow (O : Ontology) (A B : IRI) (hint : Option RawHint) : Option Bool :=
  match owlC3ZSubRow O A B hint with
  | some v => some v
  | none => rowGSub hsP O A B hint

def owlC3HDiffRow (O : Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  match owlC3ZDiffRow O a b hint with
  | some v => some v
  | none => rowGDiff hsP O a b hint

def owlC3HRoleRow (O : Ontology) (r : ObjProp) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  match owlC3ZRoleRow O r a b hint with
  | some v => some v
  | none => rowGRole hsP O r a b hint

def owlC3HNRoleRow (O : Ontology) (r : ObjProp) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  match owlC3ZNRoleRow O r a b hint with
  | some v => some v
  | none => rowGNRole hsP O r a b hint

theorem owlC3HTypeRow_sound (pat : String → String → Prop) {O : Ontology} {C a : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlC3HTypeRow O C a hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.classAssertion (.cls C) (.named a)) := by
  unfold owlC3HTypeRow at h
  split at h
  next v' hv => simp only [Option.some.injEq] at h; subst h; exact owlC3ZTypeRow_sound pat hv
  next => exact rowGType_sound hsP_sound pat h

theorem owlC3HSameRow_sound (pat : String → String → Prop) {O : Ontology} {a b : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlC3HSameRow O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.sameIndividual [.named a, .named b]) := by
  unfold owlC3HSameRow at h
  split at h
  next v' hv => simp only [Option.some.injEq] at h; subst h; exact owlC3ZSameRow_sound pat hv
  next => exact rowGSame_sound hsP_sound pat h

theorem owlC3HSubRow_sound (pat : String → String → Prop) {O : Ontology} {A B : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlC3HSubRow O A B hint = some v) :
    v = true ↔ EntailsSubAt (owl2MapP pat) O A B := by
  unfold owlC3HSubRow at h
  split at h
  next v' hv => simp only [Option.some.injEq] at h; subst h; exact owlC3ZSubRow_sound pat hv
  next => exact rowGSub_sound hsP_sound pat h

theorem owlC3HDiffRow_sound (pat : String → String → Prop) {O : Ontology} {a b : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlC3HDiffRow O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.differentIndividuals [.named a, .named b]) := by
  unfold owlC3HDiffRow at h
  split at h
  next v' hv => simp only [Option.some.injEq] at h; subst h; exact owlC3ZDiffRow_sound pat hv
  next => exact rowGDiff_sound hsP_sound pat h

theorem owlC3HRoleRow_sound (pat : String → String → Prop) {O : Ontology} {r : ObjProp}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : owlC3HRoleRow O r a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.objectPropertyAssertion r (.named a) (.named b)) := by
  unfold owlC3HRoleRow at h
  split at h
  next v' hv => simp only [Option.some.injEq] at h; subst h; exact owlC3ZRoleRow_sound pat hv
  next => exact rowGRole_sound hsP_sound pat h

theorem owlC3HNRoleRow_sound (pat : String → String → Prop) {O : Ontology} {r : ObjProp}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : owlC3HNRoleRow O r a b hint = some v) :
    v = true ↔
      EntailsAt (owl2MapP pat) O (.negativeObjectPropertyAssertion r (.named a) (.named b)) := by
  unfold owlC3HNRoleRow at h
  split at h
  next v' hv => simp only [Option.some.injEq] at h; subst h; exact owlC3ZNRoleRow_sound pat hv
  next => exact rowGNRole_sound hsP_sound pat h

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWL.ext_selfToCls
#print axioms ContextCalculus.OWL.sat_selfToCls
#print axioms ContextCalculus.OWLFrontend.model_hsOff_up
#print axioms ContextCalculus.OWLFrontend.model_hsOff_down
#print axioms ContextCalculus.OWLFrontend.consistentAt_hsOff
#print axioms ContextCalculus.OWLFrontend.shoiqd_upRC
#print axioms ContextCalculus.OWLFrontend.shoiqd_downRC
#print axioms ContextCalculus.OWLFrontend.sroiqH_consistent
#print axioms ContextCalculus.OWLFrontend.owlHSCore_sound
#print axioms ContextCalculus.OWLFrontend.owlHSCore_isSome_iff
#print axioms ContextCalculus.OWLFrontend.owlC3HConsistent_sound
#print axioms ContextCalculus.OWLFrontend.owlC3HConsistent_isSome_iff
#print axioms ContextCalculus.OWLFrontend.hsP_sound
#print axioms ContextCalculus.OWLFrontend.owlC3HTypeRow_sound
#print axioms ContextCalculus.OWLFrontend.owlC3HSameRow_sound
#print axioms ContextCalculus.OWLFrontend.owlC3HSubRow_sound
#print axioms ContextCalculus.OWLFrontend.owlC3HDiffRow_sound
#print axioms ContextCalculus.OWLFrontend.owlC3HRoleRow_sound
#print axioms ContextCalculus.OWLFrontend.owlC3HNRoleRow_sound

section Tests
open ContextCalculus.OWL ContextCalculus.OWLFrontend

private def tSelf : Ontology :=
  ⟨[.subClassOf (.cls "A") (.hasSelf (.named "r")),
    .subClassOf (.and [.cls "B", .not (.hasSelf (.inv "r"))]) (.hasSelf (.named "r"))]⟩

#guard selfRolesO tSelf == [.named "r", .inv "r"]
#guard (selfPairs tSelf).map Prod.snd == [.named "r", .inv "r"]
#guard (hsOff tSelf).axioms.length == 4
#guard (hsOff tSelf).isSROIQDSKB
#guard !tSelf.isSROIQDSKB
#guard (selfPairs tSelf).all fun p => !(tSelf.axioms.flatMap Axiom.classNames).contains p.1

end Tests
