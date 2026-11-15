import ContextCalculus.OWLFrontend.HasSelfClass

/-!
# `DatatypeDefinition` by unfolding (stage C3e, item 3)

`DatatypeDefinition(t R)` holds iff the datatype `t` has the extension of
`R` (structural specification 9.6, direct semantics table 4). When `t` is
not a datatype of the map (so an interpretation chooses its extension
freely), is the head of no other definition, and does not occur in `R`,
the definition can be unfolded: `dtOff1 O t R` drops it and replaces every
occurrence of `t` in a data range by `R` (`DataRange.substDT`).

* `drExt_substDT`: the substituted range read in one interpretation is the
  range read in another whose `t` is `R` (the two otherwise agree).
* `ext_mapDR`, `sat_mapDR`: the same for class expressions and axioms.
* `consistentAt_dtOff1`: the unfolding keeps consistency (no `HasKey`).
* `dtLoop`: all definitions, one at a time; `consistentAt_dtLoop`.
* `owlC3DConsistent`: `owlC3HConsistent` first, then on the unfolded
  ontology; `_sound`, and the six rows (`owlC3DTypeRow_sound` and others).
-/

namespace ContextCalculus.OWL

/-! ## The substitution -/

/-- Replace the datatype `t` by `R` (also `DatatypeRestriction(t)` without
facets, which has the extension of `t`). -/
def DataRange.substDT (t : IRI) (R : DataRange) : DataRange → DataRange
  | .datatype u => if u = t then R else .datatype u
  | .and rs => .and (rs.attach.map fun ⟨x, _⟩ => (DataRange.substDT t R x))
  | .or rs => .or (rs.attach.map fun ⟨x, _⟩ => (DataRange.substDT t R x))
  | .not r => .not ((DataRange.substDT t R r))
  | .oneOf ls => .oneOf ls
  | .restriction u fs => if u = t ∧ fs = [] then R else .restriction u fs
termination_by r => sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ rs›; omega)

/-- The datatypes a data range mentions. -/
def DataRange.dts : DataRange → List IRI
  | .datatype u => [u]
  | .and rs | .or rs => rs.attach.flatMap fun ⟨r, _⟩ => r.dts
  | .not r => r.dts
  | .oneOf _ => []
  | .restriction u _ => [u]
termination_by r => sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ rs›; omega)

variable {DM : DatatypeMap}

theorem mem_dts_list {rs : List DataRange} {r : DataRange} (hr : r ∈ rs) {u : IRI} (hu : u ∈ r.dts) :
    u ∈ (DataRange.and rs).dts ∧ u ∈ (DataRange.or rs).dts := by
  rw [DataRange.dts, DataRange.dts]
  exact ⟨List.mem_flatMap.2 ⟨⟨r, hr⟩, List.mem_attach _ _, hu⟩,
    List.mem_flatMap.2 ⟨⟨r, hr⟩, List.mem_attach _ _, hu⟩⟩

/-- A range without `t` is unchanged. -/
theorem substDT_of_not_mem (t : IRI) (R : DataRange) :
    ∀ r : DataRange, t ∉ r.dts → (DataRange.substDT t R r) = r
  | .datatype u, h => by
    rw [DataRange.substDT, if_neg]
    intro he; subst he; exact h (by simp [DataRange.dts])
  | .and rs, h => by
    rw [DataRange.substDT]
    congr 1
    conv_rhs => rw [← List.attach_map_subtype_val rs]
    exact List.map_congr_left fun r _ =>
      substDT_of_not_mem t R r.1 fun hm => h (mem_dts_list r.2 hm).1
  | .or rs, h => by
    rw [DataRange.substDT]
    congr 1
    conv_rhs => rw [← List.attach_map_subtype_val rs]
    exact List.map_congr_left fun r _ =>
      substDT_of_not_mem t R r.1 fun hm => h (mem_dts_list r.2 hm).2
  | .not r, h => by
    rw [DataRange.substDT, substDT_of_not_mem t R r (fun hm => h (by rw [DataRange.dts]; exact hm))]
  | .oneOf ls, _ => by rw [DataRange.substDT]
  | .restriction u fs, h => by
    rw [DataRange.substDT, if_neg]
    rintro ⟨rfl, -⟩; exact h (by simp [DataRange.dts])
termination_by r => sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem r.2; omega)
    | omega

/-- **The substituted range.** `dK` and `dI` agree on every datatype but
`t`; `t` in `dI` is `R` in `dK`; `t` has no facets. -/
theorem ext_substDT {t : IRI} {R : DataRange} {dK dI : IRI → DM.Val → Prop}
    (h1 : ∀ u, u ≠ t → DM.dtExt dK u = DM.dtExt dI u)
    (h2 : DM.dtExt dI t = DataRange.ext DM dK R) (h3 : ∀ f l, DM.facet t f l = none) :
    ∀ r : DataRange, DataRange.ext DM dK ((DataRange.substDT t R r)) = DataRange.ext DM dI r
  | .datatype u => by
    rw [DataRange.substDT]
    split_ifs with hu
    · subst hu; rw [DataRange.ext, h2]
    · rw [DataRange.ext, DataRange.ext, h1 u hu]
  | .and rs => by
    rw [DataRange.substDT]
    funext v
    rw [DataRange.ext, DataRange.ext]
    apply propext
    constructor
    · intro h r hr
      have := h _ (List.mem_map.2 ⟨⟨r, hr⟩, List.mem_attach _ _, rfl⟩)
      rwa [ext_substDT h1 h2 h3 r] at this
    · intro h r' hr'
      obtain ⟨⟨r, hr⟩, -, rfl⟩ := List.mem_map.1 hr'
      rw [ext_substDT h1 h2 h3 r]
      exact h r hr
  | .or rs => by
    rw [DataRange.substDT]
    funext v
    rw [DataRange.ext, DataRange.ext]
    apply propext
    constructor
    · rintro ⟨r', hr', h⟩
      obtain ⟨⟨r, hr⟩, -, rfl⟩ := List.mem_map.1 hr'
      rw [ext_substDT h1 h2 h3 r] at h
      exact ⟨r, hr, h⟩
    · rintro ⟨r, hr, h⟩
      refine ⟨_, List.mem_map.2 ⟨⟨r, hr⟩, List.mem_attach _ _, rfl⟩, ?_⟩
      rw [ext_substDT h1 h2 h3 r]; exact h
  | .not r => by
    rw [DataRange.substDT]
    funext v
    rw [DataRange.ext, DataRange.ext, ext_substDT h1 h2 h3 r]
  | .oneOf ls => by
    rw [DataRange.substDT]
    funext v
    rw [DataRange.ext, DataRange.ext]
  | .restriction u fs => by
    rw [DataRange.substDT]
    split_ifs with hu
    · obtain ⟨rfl, rfl⟩ := hu
      funext v
      rw [DataRange.ext, ← h2]
      simp
    · funext v
      rw [DataRange.ext, DataRange.ext]
      by_cases hut : u = t
      · subst hut
        have hfs : fs ≠ [] := fun h => hu ⟨rfl, h⟩
        obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil fs hfs
        apply propext
        constructor
        · rintro ⟨-, h⟩
          obtain ⟨p, hp, -⟩ := h f hf
          rw [h3] at hp; cases hp
        · rintro ⟨-, h⟩
          obtain ⟨p, hp, -⟩ := h f hf
          rw [h3] at hp; cases hp
      · rw [h1 u hut]
termination_by r => sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ rs›; omega)
    | omega

/-! ## Class expressions and axioms -/

/-- Apply `f` to every data range of a class expression. -/
def ClassExpr.mapDR (f : DataRange → DataRange) : ClassExpr → ClassExpr
  | .cls a => .cls a
  | .thing => .thing
  | .nothing => .nothing
  | .and cs => .and (cs.attach.map fun c => c.1.mapDR f)
  | .or cs => .or (cs.attach.map fun c => c.1.mapDR f)
  | .not c => .not (c.mapDR f)
  | .some r c => .some r (c.mapDR f)
  | .all r c => .all r (c.mapDR f)
  | .oneOf as => .oneOf as
  | .hasValue r a => .hasValue r a
  | .hasSelf r => .hasSelf r
  | .min n r c => .min n r (c.mapDR f)
  | .max n r c => .max n r (c.mapDR f)
  | .exact n r c => .exact n r (c.mapDR f)
  | .dataSome p r => .dataSome p (f r)
  | .dataAll p r => .dataAll p (f r)
  | .dataHasValue p l => .dataHasValue p l
  | .dataMin n p r => .dataMin n p (f r)
  | .dataMax n p r => .dataMax n p (f r)
  | .dataExact n p r => .dataExact n p (f r)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem c.2; omega)

def Axiom.mapDR (f : DataRange → DataRange) : Axiom → Axiom
  | .subClassOf c d => .subClassOf (c.mapDR f) (d.mapDR f)
  | .equivalentClasses cs => .equivalentClasses (cs.map (·.mapDR f))
  | .disjointClasses cs => .disjointClasses (cs.map (·.mapDR f))
  | .domain r c => .domain r (c.mapDR f)
  | .range r c => .range r (c.mapDR f)
  | .disjointUnion a cs => .disjointUnion a (cs.map (·.mapDR f))
  | .dataDomain p c => .dataDomain p (c.mapDR f)
  | .dataRange p r => .dataRange p (f r)
  | .datatypeDefinition u r => .datatypeDefinition u (f r)
  | .hasKey c rs ps => .hasKey (c.mapDR f) rs ps
  | .classAssertion c a => .classAssertion (c.mapDR f) a
  | ax => ax

variable {D : Type}

/-- The interpretation with the datatype extensions `d`. -/
def Interp.withDT (I : Interp DM D) (d : IRI → DM.Val → Prop) : Interp DM D := { I with dtype := d }

theorem withDT_prop (I : Interp DM D) (d : IRI → DM.Val → Prop) (r : ObjProp) :
    (I.withDT d).prop r = I.prop r := by
  cases r <;> rfl

theorem withDT_dp (I : Interp DM D) (d : IRI → DM.Val → Prop) (p : DataProp) :
    (I.withDT d).dp p = I.dp p := by
  cases p <;> rfl

theorem withDT_chain (I : Interp DM D) (d : IRI → DM.Val → Prop) :
    ∀ rs : List ObjProp, (I.withDT d).chain rs = I.chain rs
  | [] => rfl
  | r :: rs => by
    funext x z
    simp only [Interp.chain, withDT_prop, withDT_chain I d rs]

/-- **Class expressions with mapped data ranges.** -/
theorem ext_mapDR (I : Interp DM D) (d : IRI → DM.Val → Prop) {f : DataRange → DataRange}
    (hf : ∀ r, (I.withDT d).drExt (f r) = I.drExt r) :
    ∀ C : ClassExpr, (I.withDT d).ext (C.mapDR f) = I.ext C
  | .cls a => by rw [ClassExpr.mapDR]; funext x; rw [Interp.ext, Interp.ext]; rfl
  | .thing => by rw [ClassExpr.mapDR]; funext x; rw [Interp.ext, Interp.ext]
  | .nothing => by rw [ClassExpr.mapDR]; funext x; rw [Interp.ext, Interp.ext]
  | .and cs => by
    rw [ClassExpr.mapDR]
    funext x
    simp only [Interp.ext]
    apply propext
    constructor
    · intro h' c hc
      have := h' (c.mapDR f) (List.mem_map.2 ⟨⟨c, hc⟩, List.mem_attach _ _, rfl⟩)
      rwa [ext_mapDR I d hf c] at this
    · intro h' c' hc'
      obtain ⟨⟨c, hc⟩, -, rfl⟩ := List.mem_map.1 hc'
      rw [ext_mapDR I d hf c]
      exact h' c hc
  | .or cs => by
    rw [ClassExpr.mapDR]
    funext x
    simp only [Interp.ext]
    apply propext
    constructor
    · rintro ⟨c', hc', h'⟩
      obtain ⟨⟨c, hc⟩, -, rfl⟩ := List.mem_map.1 hc'
      rw [ext_mapDR I d hf c] at h'
      exact ⟨c, hc, h'⟩
    · rintro ⟨c, hc, h'⟩
      refine ⟨c.mapDR f, List.mem_map.2 ⟨⟨c, hc⟩, List.mem_attach _ _, rfl⟩, ?_⟩
      rw [ext_mapDR I d hf c]; exact h'
  | .not c => by
    rw [ClassExpr.mapDR]; funext x; simp only [Interp.ext, ext_mapDR I d hf c]
  | .some r c => by
    rw [ClassExpr.mapDR]; funext x; simp only [Interp.ext, ext_mapDR I d hf c, withDT_prop]
  | .all r c => by
    rw [ClassExpr.mapDR]; funext x; simp only [Interp.ext, ext_mapDR I d hf c, withDT_prop]
  | .oneOf as => by rw [ClassExpr.mapDR]; funext x; rw [Interp.ext, Interp.ext]; rfl
  | .hasValue r a => by
    rw [ClassExpr.mapDR]; funext x; simp only [Interp.ext, withDT_prop]; rfl
  | .hasSelf r => by rw [ClassExpr.mapDR]; funext x; simp only [Interp.ext, withDT_prop]
  | .min n r c => by
    rw [ClassExpr.mapDR]; funext x; simp only [Interp.ext, ext_mapDR I d hf c, withDT_prop]
  | .max n r c => by
    rw [ClassExpr.mapDR]; funext x; simp only [Interp.ext, ext_mapDR I d hf c, withDT_prop]
  | .exact n r c => by
    rw [ClassExpr.mapDR]; funext x; simp only [Interp.ext, ext_mapDR I d hf c, withDT_prop]
  | .dataSome p r => by
    rw [ClassExpr.mapDR]; funext x; simp only [Interp.ext, withDT_dp, hf]
  | .dataAll p r => by
    rw [ClassExpr.mapDR]; funext x; simp only [Interp.ext, withDT_dp, hf]
  | .dataHasValue p l => by
    rw [ClassExpr.mapDR]; funext x; simp only [Interp.ext, withDT_dp]
  | .dataMin n p r => by
    rw [ClassExpr.mapDR]; funext x; simp only [Interp.ext, withDT_dp, hf]
  | .dataMax n p r => by
    rw [ClassExpr.mapDR]; funext x; simp only [Interp.ext, withDT_dp, hf]
  | .dataExact n p r => by
    rw [ClassExpr.mapDR]; funext x; simp only [Interp.ext, withDT_dp, hf]
termination_by C => sizeOf C
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

/-- **Axioms with mapped data ranges**, for an axiom that is not a
definition of a datatype whose extension changes. -/
theorem sat_mapDR (I : Interp DM D) (d : IRI → DM.Val → Prop) {f : DataRange → DataRange}
    (hf : ∀ r, (I.withDT d).drExt (f r) = I.drExt r) {ax : Axiom}
    (hd : ∀ u r, ax = .datatypeDefinition u r → (I.withDT d).dt u = I.dt u) (N : List IRI) :
    (I.withDT d).sat N (ax.mapDR f) ↔ I.sat N ax := by
  have he := ext_mapDR I d hf
  have hp := withDT_prop I d
  have hq := withDT_dp I d
  cases ax with
  | subClassOf c e => simp only [Axiom.mapDR, Interp.sat, he]
  | equivalentClasses cs =>
    simp only [Axiom.mapDR, Interp.sat, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, he]
  | disjointClasses cs => simp only [Axiom.mapDR, Interp.sat, List.pairwise_map, he]
  | domain r c => simp only [Axiom.mapDR, Interp.sat, he, hp]
  | range r c => simp only [Axiom.mapDR, Interp.sat, he, hp]
  | disjointUnion a cs =>
    simp only [Axiom.mapDR, Interp.sat, List.pairwise_map, he, List.mem_map]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun x => (h1 x).trans ⟨fun ⟨_, ⟨c, hc, rfl⟩, hx⟩ => ⟨c, hc, by rwa [he] at hx⟩,
        fun ⟨c, hc, hx⟩ => ⟨_, ⟨c, hc, rfl⟩, by rwa [he]⟩⟩, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun x => (h1 x).trans ⟨fun ⟨c, hc, hx⟩ => ⟨_, ⟨c, hc, rfl⟩, by rwa [he]⟩,
        fun ⟨_, ⟨c, hc, rfl⟩, hx⟩ => ⟨c, hc, by rwa [he] at hx⟩⟩, h2⟩
  | dataDomain p c => simp only [Axiom.mapDR, Interp.sat, he, hq]
  | dataRange p r => simp only [Axiom.mapDR, Interp.sat, hq, hf]
  | datatypeDefinition u r =>
    simp only [Axiom.mapDR, Interp.sat, hf, hd u r rfl]
  | hasKey c rs ps =>
    simp only [Axiom.mapDR, Interp.sat, he, hp, hq]; rfl
  | classAssertion c a => simp only [Axiom.mapDR, Interp.sat, he]; rfl
  | subObjectPropertyOf rs r => simp only [Axiom.mapDR, Interp.sat, withDT_chain, hp]
  | equivalentObjectProperties rs => simp only [Axiom.mapDR, Interp.sat, hp]
  | inverseObjectProperties r s => simp only [Axiom.mapDR, Interp.sat, hp]
  | transitive r => simp only [Axiom.mapDR, Interp.sat, hp]
  | symmetric r => simp only [Axiom.mapDR, Interp.sat, hp]
  | disjointObjectProperties rs => simp only [Axiom.mapDR, Interp.sat, hp]
  | functional r => simp only [Axiom.mapDR, Interp.sat, hp]
  | inverseFunctional r => simp only [Axiom.mapDR, Interp.sat, hp]
  | reflexive r => simp only [Axiom.mapDR, Interp.sat, hp]
  | irreflexive r => simp only [Axiom.mapDR, Interp.sat, hp]
  | asymmetric r => simp only [Axiom.mapDR, Interp.sat, hp]
  | subDataPropertyOf p q => simp only [Axiom.mapDR, Interp.sat, hq]
  | equivalentDataProperties ps => simp only [Axiom.mapDR, Interp.sat, hq]
  | disjointDataProperties ps => simp only [Axiom.mapDR, Interp.sat, hq]
  | functionalData p => simp only [Axiom.mapDR, Interp.sat, hq]
  | dataPropertyAssertion p a l => simp only [Axiom.mapDR, Interp.sat, hq]; rfl
  | negativeDataPropertyAssertion p a l => simp only [Axiom.mapDR, Interp.sat, hq]; rfl
  | objectPropertyAssertion r a b => simp only [Axiom.mapDR, Interp.sat, hp]; rfl
  | negativeObjectPropertyAssertion r a b => simp only [Axiom.mapDR, Interp.sat, hp]; rfl
  | _ => exact Iff.rfl

theorem noKey_mapDR (f : DataRange → DataRange) (ax : Axiom) : (ax.mapDR f).noKey = ax.noKey := by
  cases ax <;> rfl

end ContextCalculus.OWL

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes

/-! ## Unfolding one definition -/

/-- The first datatype definition, and the other axioms. -/
def splitDef : List Axiom → Option (IRI × DataRange × List Axiom)
  | [] => none
  | .datatypeDefinition t R :: rest => some (t, R, rest)
  | ax :: rest => (splitDef rest).map fun p => (p.1, p.2.1, ax :: p.2.2)

theorem mem_splitDef : ∀ {L : List Axiom} {t : IRI} {R : DataRange} {l : List Axiom},
    splitDef L = some (t, R, l) → ∀ ax, ax ∈ L ↔ ax = .datatypeDefinition t R ∨ ax ∈ l
  | [], _, _, _, h, _ => by simp [splitDef] at h
  | a :: rest, t, R, l, h, ax => by
    cases a with
    | datatypeDefinition u r =>
      simp only [splitDef, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp
    | _ =>
      simp only [splitDef] at h
      obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨t', R', l'⟩ := p
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have := mem_splitDef hp ax
      simp only [List.mem_cons] at this ⊢
      constructor
      · rintro (h | h)
        · exact Or.inr (Or.inl h)
        · rcases this.1 h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inr h')
      · rintro (h | h | h)
        · exact Or.inr (this.2 (Or.inl h))
        · exact Or.inl h
        · exact Or.inr (this.2 (Or.inr h))

/-- An axiom that does not define `t`. -/
def notDefOf (t : IRI) : Axiom → Bool
  | .datatypeDefinition u _ => u != t
  | _ => true

/-- Unfold the first definition, if the checks hold: no `HasKey`, `t` not a
datatype of the map, `t` not in its own definition, no other definition
of `t`. -/
def dtStep (O : Ontology) : Option Ontology :=
  match splitDef O.axioms with
  | none => none
  | some (t, R, l) =>
    if O.noKey && (kindOf t).isNone && !R.dts.contains t && l.all (notDefOf t) then
      some ⟨l.map (Axiom.mapDR (DataRange.substDT t R))⟩
    else none

variable {pat : String → String → Prop}

theorem dtExt_upd {t u : IRI} (hu : u ≠ t) (d : IRI → Val → Prop) (P : Val → Prop) :
    (owl2MapP pat).dtExt (Function.update d t P) u = (owl2MapP pat).dtExt d u := by
  cases hk : kindOf u with
  | some k => rw [dtExt_some pat hk, dtExt_some pat hk]
  | none => rw [dtExt_none pat hk, dtExt_none pat hk, Function.update_of_ne hu]

theorem facet_none {t : IRI} (h : kindOf t = none) (f : IRI) (l : Literal) :
    (owl2MapP pat).facet t f l = none := by
  show (match kindOf t with
    | some k => facetSem pat k f (litVal l)
    | none => none) = none
  rw [h]

/-- **Unfolding keeps consistency.** -/
theorem consistentAt_dtStep {O O' : Ontology} (h : dtStep O = some O') :
    ConsistentAt (owl2MapP pat) O ↔ ConsistentAt (owl2MapP pat) O' := by
  unfold dtStep at h
  split at h
  · cases h
  next t R l hs =>
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.contains_eq_mem, decide_eq_false_iff_not, List.all_eq_true] at hc
  obtain ⟨⟨⟨hk, hkind⟩, hR⟩, hl⟩ := hc
  have hmem := mem_splitDef hs
  have hkO : ∀ ax ∈ O.axioms, ax.noKey = true := by
    simpa [Ontology.noKey, List.all_eq_true] using hk
  have hf3 := facet_none (pat := pat) hkind
  constructor
  · rintro ⟨Dom, hD, I, hI⟩
    have hdef := hI _ ((hmem _).2 (Or.inl rfl))
    simp only [Interp.sat] at hdef
    have hf : ∀ r, (I.withDT I.dtype).drExt (DataRange.substDT t R r) = I.drExt r :=
      ext_substDT (fun _ _ => rfl) (by funext v; exact propext (hdef v)) hf3
    refine ⟨Dom, hD, I, fun ax' hax' => ?_⟩
    obtain ⟨ax, hax, rfl⟩ := List.mem_map.1 hax'
    have hax0 := (hmem ax).2 (Or.inr hax)
    rw [sat_N_noKey _ (by rw [noKey_mapDR]; exact hkO ax hax0) _ O.namedIndividuals]
    exact (sat_mapDR I I.dtype hf (fun _ _ _ => rfl) _).2 (hI ax hax0)
  · rintro ⟨Dom, hD, J, hJ⟩
    let J' := J.withDT (Function.update J.dtype t (J.drExt R))
    have hJJ : J'.withDT J.dtype = J := rfl
    have hf : ∀ r, (J'.withDT J.dtype).drExt (DataRange.substDT t R r) = J'.drExt r :=
      ext_substDT (fun u hu => (dtExt_upd hu _ _).symm)
        (by
          rw [dtExt_none pat hkind]
          show Function.update J.dtype t (J.drExt R) t = DataRange.ext (owl2MapP pat) J.dtype R
          rw [Function.update_self]; rfl) hf3
    refine ⟨Dom, hD, J', fun ax hax => ?_⟩
    rw [sat_N_noKey _ (hkO ax hax) _ []]
    rcases (hmem ax).1 hax with rfl | hax'
    · intro v
      have h1 : J'.dt t v ↔ J.drExt R v := by
        show (owl2MapP pat).dtExt (Function.update J.dtype t (J.drExt R)) t v ↔ _
        rw [dtExt_none pat hkind, Function.update_self]
      have h2 : J'.drExt R = J.drExt R := by
        rw [← hf R, substDT_of_not_mem t R R hR]; rfl
      rw [h1, h2]
    · have hs := hJ _ (List.mem_map_of_mem hax')
      rw [sat_N_noKey _ (by rw [noKey_mapDR]; exact hkO ax hax) _ []] at hs
      refine (sat_mapDR J' J.dtype hf ?_ _).1 hs
      rintro u r rfl
      have hu : u ≠ t := by simpa [notDefOf] using hl _ hax'
      funext v
      exact congrFun (dtExt_upd hu _ _).symm v

/-! ## All definitions -/

/-- Unfold the definitions one at a time (at most `k` rounds). -/
def dtLoop : Nat → Ontology → Option Ontology
  | 0, O => if (splitDef O.axioms).isNone then some O else none
  | k + 1, O => if (splitDef O.axioms).isNone then some O else (dtStep O).bind (dtLoop k)

theorem consistentAt_dtLoop : ∀ {k : Nat} {O O' : Ontology}, dtLoop k O = some O' →
    (ConsistentAt (owl2MapP pat) O ↔ ConsistentAt (owl2MapP pat) O')
  | 0, O, O', h => by
    simp only [dtLoop] at h
    split_ifs at h
    cases h; exact Iff.rfl
  | k + 1, O, O', h => by
    simp only [dtLoop] at h
    split_ifs at h
    · cases h; exact Iff.rfl
    · obtain ⟨O1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
      exact (consistentAt_dtStep h1).trans (consistentAt_dtLoop h2)

/-! ## The route and the rows -/

/-- The route of `owlC3HConsistent` on the unfolded ontology. -/
def dtP (O : Ontology) (hint : Option RawHint) : Option Bool :=
  if (splitDef O.axioms).isSome then
    match dtLoop O.axioms.length O with
    | some O' => owlC3HConsistent O' hint
    | none => none
  else none

theorem dtP_sound : ConsSound dtP := by
  intro pat O hint v h
  unfold dtP at h
  split_ifs at h
  split at h
  next O' hO' => rw [owlC3HConsistent_sound pat h, consistentAt_dtLoop hO']
  next => cases h

/-- **Consistency** (stage C3e): `owlC3HConsistent`, and when it declines,
the same on the ontology with its datatype definitions unfolded. -/
def owlC3DConsistent (O : Ontology) (hint : Option RawHint) : Option Bool :=
  match owlC3HConsistent O hint with
  | some v => some v
  | none => dtP O hint

theorem owlC3DConsistent_sound (pat : String → String → Prop) {O : Ontology}
    {hint : Option RawHint} {v : Bool} (h : owlC3DConsistent O hint = some v) :
    v = true ↔ ConsistentAt (owl2MapP pat) O := by
  unfold owlC3DConsistent at h
  split at h
  next v' hv => simp only [Option.some.injEq] at h; subst h; exact owlC3HConsistent_sound pat hv
  next => exact dtP_sound pat O hint v h

theorem owlC3DConsistent_isSome_iff (O : Ontology) (hint : Option RawHint) :
    (owlC3DConsistent O hint).isSome = true ↔
      (owlC3HConsistent O hint).isSome = true ∨ (dtP O hint).isSome = true := by
  unfold owlC3DConsistent
  cases owlC3HConsistent O hint <;> simp

def owlC3DTypeRow (O : Ontology) (C a : IRI) (hint : Option RawHint) : Option Bool :=
  match owlC3HTypeRow O C a hint with
  | some v => some v
  | none => rowGType dtP O C a hint

def owlC3DSameRow (O : Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  match owlC3HSameRow O a b hint with
  | some v => some v
  | none => rowGSame dtP O a b hint

def owlC3DSubRow (O : Ontology) (A B : IRI) (hint : Option RawHint) : Option Bool :=
  match owlC3HSubRow O A B hint with
  | some v => some v
  | none => rowGSub dtP O A B hint

def owlC3DDiffRow (O : Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  match owlC3HDiffRow O a b hint with
  | some v => some v
  | none => rowGDiff dtP O a b hint

def owlC3DRoleRow (O : Ontology) (r : ObjProp) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  match owlC3HRoleRow O r a b hint with
  | some v => some v
  | none => rowGRole dtP O r a b hint

def owlC3DNRoleRow (O : Ontology) (r : ObjProp) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  match owlC3HNRoleRow O r a b hint with
  | some v => some v
  | none => rowGNRole dtP O r a b hint

theorem owlC3DTypeRow_sound (pat : String → String → Prop) {O : Ontology} {C a : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlC3DTypeRow O C a hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.classAssertion (.cls C) (.named a)) := by
  unfold owlC3DTypeRow at h
  split at h
  next v' hv => simp only [Option.some.injEq] at h; subst h; exact owlC3HTypeRow_sound pat hv
  next => exact rowGType_sound dtP_sound pat h

theorem owlC3DSameRow_sound (pat : String → String → Prop) {O : Ontology} {a b : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlC3DSameRow O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.sameIndividual [.named a, .named b]) := by
  unfold owlC3DSameRow at h
  split at h
  next v' hv => simp only [Option.some.injEq] at h; subst h; exact owlC3HSameRow_sound pat hv
  next => exact rowGSame_sound dtP_sound pat h

theorem owlC3DSubRow_sound (pat : String → String → Prop) {O : Ontology} {A B : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlC3DSubRow O A B hint = some v) :
    v = true ↔ EntailsSubAt (owl2MapP pat) O A B := by
  unfold owlC3DSubRow at h
  split at h
  next v' hv => simp only [Option.some.injEq] at h; subst h; exact owlC3HSubRow_sound pat hv
  next => exact rowGSub_sound dtP_sound pat h

theorem owlC3DDiffRow_sound (pat : String → String → Prop) {O : Ontology} {a b : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlC3DDiffRow O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.differentIndividuals [.named a, .named b]) := by
  unfold owlC3DDiffRow at h
  split at h
  next v' hv => simp only [Option.some.injEq] at h; subst h; exact owlC3HDiffRow_sound pat hv
  next => exact rowGDiff_sound dtP_sound pat h

theorem owlC3DRoleRow_sound (pat : String → String → Prop) {O : Ontology} {r : ObjProp}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : owlC3DRoleRow O r a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.objectPropertyAssertion r (.named a) (.named b)) := by
  unfold owlC3DRoleRow at h
  split at h
  next v' hv => simp only [Option.some.injEq] at h; subst h; exact owlC3HRoleRow_sound pat hv
  next => exact rowGRole_sound dtP_sound pat h

theorem owlC3DNRoleRow_sound (pat : String → String → Prop) {O : Ontology} {r : ObjProp}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : owlC3DNRoleRow O r a b hint = some v) :
    v = true ↔
      EntailsAt (owl2MapP pat) O (.negativeObjectPropertyAssertion r (.named a) (.named b)) := by
  unfold owlC3DNRoleRow at h
  split at h
  next v' hv => simp only [Option.some.injEq] at h; subst h; exact owlC3HNRoleRow_sound pat hv
  next => exact rowGNRole_sound dtP_sound pat h

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWL.ext_substDT
#print axioms ContextCalculus.OWL.ext_mapDR
#print axioms ContextCalculus.OWL.sat_mapDR
#print axioms ContextCalculus.OWLFrontend.consistentAt_dtStep
#print axioms ContextCalculus.OWLFrontend.consistentAt_dtLoop
#print axioms ContextCalculus.OWLFrontend.owlC3DConsistent_sound
#print axioms ContextCalculus.OWLFrontend.owlC3DTypeRow_sound
#print axioms ContextCalculus.OWLFrontend.owlC3DSameRow_sound
#print axioms ContextCalculus.OWLFrontend.owlC3DSubRow_sound
#print axioms ContextCalculus.OWLFrontend.owlC3DDiffRow_sound
#print axioms ContextCalculus.OWLFrontend.owlC3DRoleRow_sound
#print axioms ContextCalculus.OWLFrontend.owlC3DNRoleRow_sound

section Tests
open ContextCalculus.OWL ContextCalculus.OWLFrontend

private def tDT : Ontology :=
  ⟨[.datatypeDefinition "urn:t" (.datatype "http://www.w3.org/2001/XMLSchema#integer"),
    .subClassOf (.cls "A") (.dataSome (.named "p") (.datatype "urn:t"))]⟩

#guard (dtStep tDT).isSome
#guard ((dtLoop 2 tDT).map (·.axioms.length)) == some 1
#guard (dtStep ⟨[.datatypeDefinition "urn:t" (.datatype "urn:t")]⟩).isNone
#guard (dtStep ⟨[.datatypeDefinition "http://www.w3.org/2001/XMLSchema#integer"
    (.datatype "http://www.w3.org/2001/XMLSchema#decimal")]⟩).isNone

end Tests
