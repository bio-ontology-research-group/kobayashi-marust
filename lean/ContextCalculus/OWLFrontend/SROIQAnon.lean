import ContextCalculus.OWLFrontend.SROIQDC2aReference

/-!
# Anonymous individuals (stage C3, follow-up 1)

In the OWL model (`OWL/Semantics.lean`) an interpretation gives every
individual, named or anonymous, a value (`Interp.ind`), and every notion of
entailment quantifies over all interpretations; so an anonymous individual
is an existential variable of a consistency test and a universal one of an
entailment, exactly as the direct semantics asks (no forest condition is
needed for exactness; OWL 2 DL's forest restriction only matters for the
decidability of the full language).

`anonOff W O` renames every anonymous individual `x` of `O` into the named
individual `base ++ x`. The renaming is an involution `anonF` on individuals
(it also maps the fresh names back), so renaming the individuals of an interpretation
along it turns models of `O` into models of `anonOff W O` and back
(`model_anonOff`). The fresh names are longer than every IRI of `W` and of
the named individuals of `O`, so the individuals a query mentions stay fixed.

* `consistentAt_anonOff`: consistency is unchanged (no `HasKey` in `O`).
* `entailsAt_anonOff`: an axiom whose individuals the renaming fixes is
  entailed by `O` iff by `anonOff W O`.
* `owlSROIQDAConsistent` and the six rows: the SROIQ(D) route on the
  renamed ontology, with `_sound` and `_isSome_iff`.
-/

namespace ContextCalculus.OWL

/-! ## Renaming individuals -/

def ClassExpr.mapI (f : Individual → Individual) : ClassExpr → ClassExpr
  | .cls a => .cls a
  | .thing => .thing
  | .nothing => .nothing
  | .and cs => .and (cs.attach.map fun c => c.1.mapI f)
  | .or cs => .or (cs.attach.map fun c => c.1.mapI f)
  | .not c => .not (c.mapI f)
  | .some r c => .some r (c.mapI f)
  | .all r c => .all r (c.mapI f)
  | .oneOf as => .oneOf (as.map f)
  | .hasValue r a => .hasValue r (f a)
  | .hasSelf r => .hasSelf r
  | .min n r c => .min n r (c.mapI f)
  | .max n r c => .max n r (c.mapI f)
  | .exact n r c => .exact n r (c.mapI f)
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

def Axiom.mapI (f : Individual → Individual) : Axiom → Axiom
  | .subClassOf c d => .subClassOf (c.mapI f) (d.mapI f)
  | .equivalentClasses cs => .equivalentClasses (cs.map (·.mapI f))
  | .disjointClasses cs => .disjointClasses (cs.map (·.mapI f))
  | .domain r c => .domain r (c.mapI f)
  | .range r c => .range r (c.mapI f)
  | .disjointUnion a cs => .disjointUnion a (cs.map (·.mapI f))
  | .dataDomain p c => .dataDomain p (c.mapI f)
  | .hasKey c rs ps => .hasKey (c.mapI f) rs ps
  | .sameIndividual as => .sameIndividual (as.map f)
  | .differentIndividuals as => .differentIndividuals (as.map f)
  | .classAssertion c a => .classAssertion (c.mapI f) (f a)
  | .objectPropertyAssertion r a b => .objectPropertyAssertion r (f a) (f b)
  | .negativeObjectPropertyAssertion r a b => .negativeObjectPropertyAssertion r (f a) (f b)
  | .dataPropertyAssertion p a l => .dataPropertyAssertion p (f a) l
  | .negativeDataPropertyAssertion p a l => .negativeDataPropertyAssertion p (f a) l
  | ax => ax

/-- An axiom other than `HasKey`. -/
def Axiom.noKey : Axiom → Bool
  | .hasKey .. => false
  | _ => true

variable {DM : DatatypeMap} {D : Type}

/-- The interpretation with its individuals read through `g`. -/
def Interp.indMap (I : Interp DM D) (g : Individual → Individual) : Interp DM D :=
  { I with ind := fun i => I.ind (g i) }

theorem indMap_prop (I : Interp DM D) (g : Individual → Individual) (r : ObjProp) :
    (I.indMap g).prop r = I.prop r := by
  cases r <;> rfl

theorem ext_mapI (I : Interp DM D) {f g : Individual → Individual} (h : ∀ i, g (f i) = i) :
    ∀ c : ClassExpr, (I.indMap g).ext (c.mapI f) = I.ext c
  | .cls a => by rw [ClassExpr.mapI]; funext x; rw [Interp.ext, Interp.ext]; rfl
  | .thing => by rw [ClassExpr.mapI]; funext x; rw [Interp.ext, Interp.ext]
  | .nothing => by rw [ClassExpr.mapI]; funext x; rw [Interp.ext, Interp.ext]
  | .and cs => by
    rw [ClassExpr.mapI]
    funext x
    simp only [Interp.ext]
    apply propext
    constructor
    · intro h' c hc
      have := h' (c.mapI f) (List.mem_map.2 ⟨⟨c, hc⟩, List.mem_attach _ _, rfl⟩)
      rwa [ext_mapI I h c] at this
    · intro h' c' hc'
      obtain ⟨⟨c, hc⟩, -, rfl⟩ := List.mem_map.1 hc'
      rw [ext_mapI I h c]
      exact h' c hc
  | .or cs => by
    rw [ClassExpr.mapI]
    funext x
    simp only [Interp.ext]
    apply propext
    constructor
    · rintro ⟨c', hc', h'⟩
      obtain ⟨⟨c, hc⟩, -, rfl⟩ := List.mem_map.1 hc'
      rw [ext_mapI I h c] at h'
      exact ⟨c, hc, h'⟩
    · rintro ⟨c, hc, h'⟩
      refine ⟨c.mapI f, List.mem_map.2 ⟨⟨c, hc⟩, List.mem_attach _ _, rfl⟩, ?_⟩
      rw [ext_mapI I h c]; exact h'
  | .not c => by
    rw [ClassExpr.mapI]; funext x; simp only [Interp.ext, ext_mapI I h c]
  | .some r c => by
    rw [ClassExpr.mapI]; funext x; simp only [Interp.ext, ext_mapI I h c, indMap_prop]
  | .all r c => by
    rw [ClassExpr.mapI]; funext x; simp only [Interp.ext, ext_mapI I h c, indMap_prop]
  | .oneOf as => by
    rw [ClassExpr.mapI]; funext x
    simp only [Interp.ext, List.mem_map]
    apply propext
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, he⟩
      refine ⟨a, ha, ?_⟩
      have : (I.indMap g).ind (f a) = I.ind a := by simp [Interp.indMap, h]
      rw [he, this]
    · rintro ⟨a, ha, he⟩
      refine ⟨f a, ⟨a, ha, rfl⟩, ?_⟩
      have : (I.indMap g).ind (f a) = I.ind a := by simp [Interp.indMap, h]
      rw [this, he]
  | .hasValue r a => by
    rw [ClassExpr.mapI]; funext x
    have : (I.indMap g).ind (f a) = I.ind a := by simp [Interp.indMap, h]
    simp only [Interp.ext, indMap_prop, this]
  | .hasSelf r => by rw [ClassExpr.mapI]; funext x; simp only [Interp.ext, indMap_prop]
  | .min n r c => by
    rw [ClassExpr.mapI]; funext x; simp only [Interp.ext, ext_mapI I h c, indMap_prop]
  | .max n r c => by
    rw [ClassExpr.mapI]; funext x; simp only [Interp.ext, ext_mapI I h c, indMap_prop]
  | .exact n r c => by
    rw [ClassExpr.mapI]; funext x; simp only [Interp.ext, ext_mapI I h c, indMap_prop]
  | .dataSome p r => by rw [ClassExpr.mapI]; funext x; rw [Interp.ext, Interp.ext]; rfl
  | .dataAll p r => by rw [ClassExpr.mapI]; funext x; rw [Interp.ext, Interp.ext]; rfl
  | .dataHasValue p l => by rw [ClassExpr.mapI]; funext x; rw [Interp.ext, Interp.ext]; rfl
  | .dataMin n p r => by rw [ClassExpr.mapI]; funext x; rw [Interp.ext, Interp.ext]; rfl
  | .dataMax n p r => by rw [ClassExpr.mapI]; funext x; rw [Interp.ext, Interp.ext]; rfl
  | .dataExact n p r => by rw [ClassExpr.mapI]; funext x; rw [Interp.ext, Interp.ext]; rfl
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

theorem chain_indMap (I : Interp DM D) (g : Individual → Individual) :
    ∀ rs : List ObjProp, (I.indMap g).chain rs = I.chain rs
  | [] => rfl
  | r :: rs => by
    funext x z
    simp only [Interp.chain, indMap_prop, chain_indMap I g rs]

/-- **Satisfaction under renaming.** -/
theorem sat_mapI (I : Interp DM D) {f g : Individual → Individual} (h : ∀ i, g (f i) = i)
    {ax : Axiom} (hk : ax.noKey = true) (N N' : List IRI) :
    (I.indMap g).sat N (ax.mapI f) ↔ I.sat N' ax := by
  have hi : ∀ a, (I.indMap g).ind (f a) = I.ind a := fun a => by simp [Interp.indMap, h]
  have he := ext_mapI I h
  cases ax with
  | subClassOf c d => simp only [Axiom.mapI, Interp.sat, he]
  | equivalentClasses cs =>
    simp only [Axiom.mapI, Interp.sat, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, he]
  | disjointClasses cs =>
    simp only [Axiom.mapI, Interp.sat, List.pairwise_map, he]
  | domain r c => simp only [Axiom.mapI, Interp.sat, he, indMap_prop]
  | range r c => simp only [Axiom.mapI, Interp.sat, he, indMap_prop]
  | disjointUnion a cs =>
    simp only [Axiom.mapI, Interp.sat, List.pairwise_map, he, List.mem_map]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun x => (h1 x).trans ⟨fun ⟨_, ⟨c, hc, rfl⟩, hx⟩ => ⟨c, hc, by rwa [he] at hx⟩,
        fun ⟨c, hc, hx⟩ => ⟨_, ⟨c, hc, rfl⟩, by rwa [he]⟩⟩, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun x => (h1 x).trans ⟨fun ⟨c, hc, hx⟩ => ⟨_, ⟨c, hc, rfl⟩, by rwa [he]⟩,
        fun ⟨_, ⟨c, hc, rfl⟩, hx⟩ => ⟨c, hc, by rwa [he] at hx⟩⟩, h2⟩
  | dataDomain p c => simp only [Axiom.mapI, Interp.sat, he]; rfl
  | hasKey c rs ps => simp [Axiom.noKey] at hk
  | sameIndividual as =>
    simp only [Axiom.mapI, Interp.sat, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, hi]
  | differentIndividuals as => simp only [Axiom.mapI, Interp.sat, List.pairwise_map, hi]
  | classAssertion c a => simp only [Axiom.mapI, Interp.sat, he, hi]
  | objectPropertyAssertion r a b => simp only [Axiom.mapI, Interp.sat, hi, indMap_prop]
  | negativeObjectPropertyAssertion r a b => simp only [Axiom.mapI, Interp.sat, hi, indMap_prop]
  | dataPropertyAssertion p a l => simp only [Axiom.mapI, Interp.sat, hi]; rfl
  | negativeDataPropertyAssertion p a l => simp only [Axiom.mapI, Interp.sat, hi]; rfl
  | subObjectPropertyOf rs r => simp only [Axiom.mapI, Interp.sat, chain_indMap, indMap_prop]
  | equivalentObjectProperties rs => simp only [Axiom.mapI, Interp.sat, indMap_prop]
  | inverseObjectProperties r s => simp only [Axiom.mapI, Interp.sat, indMap_prop]
  | transitive r => simp only [Axiom.mapI, Interp.sat, indMap_prop]
  | symmetric r => simp only [Axiom.mapI, Interp.sat, indMap_prop]
  | disjointObjectProperties rs => simp only [Axiom.mapI, Interp.sat, indMap_prop]
  | functional r => simp only [Axiom.mapI, Interp.sat, indMap_prop]
  | inverseFunctional r => simp only [Axiom.mapI, Interp.sat, indMap_prop]
  | reflexive r => simp only [Axiom.mapI, Interp.sat, indMap_prop]
  | irreflexive r => simp only [Axiom.mapI, Interp.sat, indMap_prop]
  | asymmetric r => simp only [Axiom.mapI, Interp.sat, indMap_prop]
  | _ => rfl

/-! ## The renaming -/

/-- No axiom is a `HasKey`. -/
def Ontology.noKey (O : Ontology) : Bool := O.axioms.all Axiom.noKey

end ContextCalculus.OWL

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL SRIQKB

/-- The fresh name of the anonymous individual `x`: the base followed by `x`. -/
def anonEnc (base x : String) : IRI := String.ofList (base.toList ++ x.toList)

/-- The anonymous individual a fresh name stands for. -/
def anonDec (base a : String) : Option String :=
  if base.toList.isPrefixOf a.toList then some (String.ofList (a.toList.drop base.length))
  else none

theorem anonDec_enc (base x : String) : anonDec base (anonEnc base x) = some x := by
  unfold anonDec anonEnc
  rw [String.toList_ofList, if_pos (List.isPrefixOf_iff_prefix.2 (List.prefix_append _ _))]
  congr 1
  apply String.toList_injective
  rw [String.toList_ofList, ← String.length_toList, List.drop_left]

theorem anonDec_some {base a x : String} (h : anonDec base a = some x) : a = anonEnc base x := by
  unfold anonDec at h
  split_ifs at h with hp
  simp only [Option.some.injEq] at h
  subst h
  apply String.toList_injective
  unfold anonEnc
  rw [String.toList_ofList, String.toList_ofList, ← String.length_toList]
  exact (List.prefix_iff_eq_append.1 (List.isPrefixOf_iff_prefix.1 hp)).symm

theorem anonDec_short {base a : String} (h : a.length < base.length) : anonDec base a = none := by
  unfold anonDec
  rw [if_neg]
  intro hp
  have := (List.isPrefixOf_iff_prefix.1 hp).length_le
  rw [String.length_toList, String.length_toList] at this
  omega

/-- The renaming: an anonymous individual `x` and the fresh name of `x`
change places; every other individual stays. -/
def anonF (base : String) : Individual → Individual
  | .anon x => .named (anonEnc base x)
  | .named a =>
    match anonDec base a with
    | some x => .anon x
    | none => .named a

/-- **The renaming is an involution.** -/
theorem anonF_anonF (base : String) (i : Individual) : anonF base (anonF base i) = i := by
  cases i with
  | anon x => simp only [anonF, anonDec_enc]
  | named a =>
    cases h : anonDec base a with
    | none => simp only [anonF, h]
    | some x => simp only [anonF, h, ← anonDec_some h]

/-- A name shorter than the base is fixed. -/
theorem anonF_short {base : String} {a : IRI} (ha : a.length < base.length) :
    anonF base (.named a) = .named a := by
  simp only [anonF, anonDec_short ha]

/-- The base of the fresh names: longer than every IRI of `W` and every
named individual of `O`. -/
def anonBase (W : List IRI) (O : Ontology) : String :=
  "urn:km:owl-anon:".pushn '#' (maxLen (W ++ O.namedIndividuals) + 1)

theorem anonBase_long {W : List IRI} {O : Ontology} {a : IRI} (h : a ∈ W ++ O.namedIndividuals) :
    a.length < (anonBase W O).length := by
  have h1 := length_le_maxLen h
  have : (anonBase W O).length = "urn:km:owl-anon:".length + (maxLen (W ++ O.namedIndividuals) + 1) :=
    by unfold anonBase; rw [String.length_pushn]
  omega

/-- The renaming of an ontology. -/
abbrev anonG (W : List IRI) (O : Ontology) : Individual → Individual :=
  anonF (anonBase W O)

/-- **Anonymous individuals as fresh named individuals.** -/
def anonOff (W : List IRI) (O : Ontology) : Ontology := ⟨O.axioms.map (Axiom.mapI (anonG W O))⟩

theorem anonG_inv (W : List IRI) (O : Ontology) (i : Individual) : anonG W O (anonG W O i) = i :=
  anonF_anonF _ i

variable {DM : DatatypeMap} {D : Type}

theorem indMap_indMap (I : Interp DM D) {g : Individual → Individual} (h : ∀ i, g (g i) = i) :
    (I.indMap g).indMap g = I := by
  cases I
  simp only [Interp.indMap, h]

/-- **Models under the renaming.** -/
theorem model_anonOff {W : List IRI} {O : Ontology} (hk : O.noKey = true) (I : Interp DM D) :
    OWL.Model (anonOff W O) (I.indMap (anonG W O)) ↔ OWL.Model O I := by
  have hk' : ∀ ax ∈ O.axioms, ax.noKey = true := by
    simpa [Ontology.noKey, List.all_eq_true] using hk
  simp only [OWL.Model, anonOff, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  exact forall_congr' fun ax => imp_congr_right fun hax =>
    sat_mapI I (anonG_inv W O) (hk' ax hax) _ _

theorem consistentAt_anonOff {W : List IRI} {O : Ontology} (hk : O.noKey = true) :
    ConsistentAt DM (anonOff W O) ↔ ConsistentAt DM O := by
  constructor
  · rintro ⟨Dom, hD, J, hJ⟩
    refine ⟨Dom, hD, J.indMap (anonG W O), (model_anonOff (W := W) hk _).1 ?_⟩
    rwa [indMap_indMap J (anonG_inv W O)]
  · rintro ⟨Dom, hD, I, hI⟩
    exact ⟨Dom, hD, _, (model_anonOff hk I).2 hI⟩

/-- **Entailment under the renaming**, for an axiom the renaming fixes. -/
theorem entailsAt_anonOff {W : List IRI} {O : Ontology} (hk : O.noKey = true) {α : Axiom}
    (hα : α.mapI (anonG W O) = α) (hαk : α.noKey = true) :
    EntailsAt DM (anonOff W O) α ↔ EntailsAt DM O α := by
  constructor
  · intro h Dom _ I hI
    have := h Dom _ ((model_anonOff hk I).2 hI)
    exact (sat_mapI I (anonG_inv W O) hαk α.namedIndividuals α.namedIndividuals).1
      (by rw [hα]; exact this)
  · intro h Dom _ J hJ
    have hI : OWL.Model O (J.indMap (anonG W O)) := by
      apply (model_anonOff (W := W) hk _).1
      rwa [indMap_indMap J (anonG_inv W O)]
    have := h Dom _ hI
    have h2 := (sat_mapI (J.indMap (anonG W O)) (anonG_inv W O) hαk α.namedIndividuals
      α.namedIndividuals).2 this
    rwa [indMap_indMap J (anonG_inv W O), hα] at h2

theorem entailsSubAt_anonOff {W : List IRI} {O : Ontology} (hk : O.noKey = true) (A B : IRI) :
    EntailsSubAt DM (anonOff W O) A B ↔ EntailsSubAt DM O A B := by
  constructor
  · intro h Dom _ I hI x hx
    exact h Dom _ ((model_anonOff hk I).2 hI) x hx
  · intro h Dom _ J hJ x hx
    have hI : OWL.Model O (J.indMap (anonG W O)) := by
      apply (model_anonOff (W := W) hk _).1
      rwa [indMap_indMap J (anonG_inv W O)]
    exact h Dom _ hI x hx

/-! ## The route -/

open ContextCalculus.OWL.Datatypes

theorem noKey_mapI (f : Individual → Individual) (ax : Axiom) : (ax.mapI f).noKey = ax.noKey := by
  cases ax <;> rfl

theorem noKey_of_isSROIQDKB {ax : Axiom} (h : ax.isSROIQDKB = true) : ax.noKey = true := by
  cases ax <;> simp_all [Axiom.isSROIQDKB, Axiom.isRoleC3, Axiom.isSHOIQDKB, Axiom.isSHIQD,
    Axiom.isSHI, Axiom.isSRI, Axiom.noKey]

theorem noKey_of_anonOff {W : List IRI} {O : Ontology} (h : (anonOff W O).isSROIQDKB = true) :
    O.noKey = true := by
  simp only [Ontology.isSROIQDKB, anonOff, List.all_map, List.all_eq_true, Function.comp_apply] at h
  simp only [Ontology.noKey, List.all_eq_true]
  intro ax hax
  rw [← noKey_mapI (anonG W O)]
  exact noKey_of_isSROIQDKB (h ax hax)

/-- **Consistency of a SROIQ(D) knowledge base with anonymous individuals**:
the SROIQ(D) route on the renamed ontology. -/
def owlSROIQDAConsistent (O : Ontology) (hint : Option RawHint) : Option Bool :=
  owlSROIQDC2aConsistent (anonOff [] O) hint

theorem owlSROIQDAConsistent_sound (pat : String → String → Prop) {O : Ontology}
    {hint : Option RawHint} {v : Bool} (h : owlSROIQDAConsistent O hint = some v) :
    v = true ↔ ConsistentAt (owl2MapP pat) O := by
  have hk : O.noKey = true := noKey_of_anonOff
    ((owlSROIQDC2aConsistent_isSome_iff _ hint).1 (by unfold owlSROIQDAConsistent at h; rw [h]; rfl)).1
  rw [owlSROIQDC2aConsistent_sound pat h, consistentAt_anonOff hk]

theorem owlSROIQDAConsistent_isSome_iff (O : Ontology) (hint : Option RawHint) :
    (owlSROIQDAConsistent O hint).isSome = true ↔
      (anonOff [] O).isSROIQDKB = true ∧ SROIQDC2aChecks (anonOff [] O) :=
  owlSROIQDC2aConsistent_isSome_iff _ hint

/-- The renaming fixes a named individual of `W`. -/
theorem anonG_fix {W : List IRI} {O : Ontology} {a : IRI} (h : a ∈ W) :
    anonG W O (.named a) = .named a :=
  anonF_short (anonBase_long (List.mem_append_left _ h))

/-- **Type row** with anonymous individuals. -/
def owlSROIQDATypeRow (O : Ontology) (C a : IRI) (hint : Option RawHint) : Option Bool :=
  owlSROIQDTypeRow (anonOff [a] O) C a hint

/-- **Same row** with anonymous individuals. -/
def owlSROIQDASameRow (O : Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  owlSROIQDSameRow (anonOff [a, b] O) a b hint

/-- **Subsumption row** with anonymous individuals. -/
def owlSROIQDASubRow (O : Ontology) (A B : IRI) (hint : Option RawHint) : Option Bool :=
  owlSROIQDSubRow (anonOff [] O) A B hint

/-- **Different row** with anonymous individuals. -/
def owlSROIQDADiffRow (O : Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  owlSROIQDDiffRow (anonOff [a, b] O) a b hint

/-- **Role row** with anonymous individuals. -/
def owlSROIQDARoleRow (O : Ontology) (r : ObjProp) (a b : IRI) (hint : Option RawHint) :
    Option Bool :=
  owlSROIQDRoleRow (anonOff [a, b] O) r a b hint

/-- **Negative role row** with anonymous individuals. -/
def owlSROIQDANRoleRow (O : Ontology) (r : ObjProp) (a b : IRI) (hint : Option RawHint) :
    Option Bool :=
  owlSROIQDNRoleRow (anonOff [a, b] O) r a b hint

theorem rowS_isSome {O : Ontology} {L : List Axiom} {hint : Option RawHint} {v : Bool}
    (h : rowS O L hint = some v) : O.isSROIQDKB = true := by
  obtain ⟨w, hw, -⟩ := Option.map_eq_some_iff.1 h
  have hk := ((owlSROIQDC2aConsistent_isSome_iff (addAxs O L) hint).1 (by rw [hw]; rfl)).1
  rw [isSROIQDKB_addAxs, Bool.and_eq_true] at hk
  exact hk.1

theorem owlSROIQDATypeRow_sound (pat : String → String → Prop) {O : Ontology} {C a : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSROIQDATypeRow O C a hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.classAssertion (.cls C) (.named a)) := by
  have hk := noKey_of_anonOff (rowS_isSome h)
  rw [owlSROIQDTypeRow_sound pat h, entailsAt_anonOff hk (by
    simp only [Axiom.mapI, ClassExpr.mapI, anonG_fix (List.mem_singleton_self a)]) rfl]

theorem owlSROIQDASameRow_sound (pat : String → String → Prop) {O : Ontology} {a b : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSROIQDASameRow O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.sameIndividual [.named a, .named b]) := by
  have hk := noKey_of_anonOff (rowS_isSome h)
  rw [owlSROIQDSameRow_sound pat h, entailsAt_anonOff hk (by
    simp [Axiom.mapI, anonG_fix (W := [a, b]) (O := O) (a := a) (by simp),
      anonG_fix (W := [a, b]) (O := O) (a := b) (by simp)]) rfl]

theorem owlSROIQDASubRow_sound (pat : String → String → Prop) {O : Ontology} {A B : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSROIQDASubRow O A B hint = some v) :
    v = true ↔ EntailsSubAt (owl2MapP pat) O A B := by
  have hk := noKey_of_anonOff (rowS_isSome h)
  rw [owlSROIQDSubRow_sound pat h, entailsSubAt_anonOff hk]

theorem owlSROIQDADiffRow_sound (pat : String → String → Prop) {O : Ontology} {a b : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSROIQDADiffRow O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.differentIndividuals [.named a, .named b]) := by
  have hk := noKey_of_anonOff (rowS_isSome h)
  rw [owlSROIQDDiffRow_sound pat h, entailsAt_anonOff hk (by
    simp [Axiom.mapI, anonG_fix (W := [a, b]) (O := O) (a := a) (by simp),
      anonG_fix (W := [a, b]) (O := O) (a := b) (by simp)]) rfl]

theorem owlSROIQDARoleRow_sound (pat : String → String → Prop) {O : Ontology} {r : ObjProp}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : owlSROIQDARoleRow O r a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.objectPropertyAssertion r (.named a) (.named b)) := by
  have h' := h
  unfold owlSROIQDARoleRow owlSROIQDRoleRow at h'
  split at h'
  swap
  · cases h'
  have hk := noKey_of_anonOff (rowS_isSome h')
  rw [owlSROIQDRoleRow_sound pat h, entailsAt_anonOff hk (by
    simp [Axiom.mapI, anonG_fix (W := [a, b]) (O := O) (a := a) (by simp),
      anonG_fix (W := [a, b]) (O := O) (a := b) (by simp)]) rfl]

theorem owlSROIQDANRoleRow_sound (pat : String → String → Prop) {O : Ontology} {r : ObjProp}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : owlSROIQDANRoleRow O r a b hint = some v) :
    v = true ↔
      EntailsAt (owl2MapP pat) O (.negativeObjectPropertyAssertion r (.named a) (.named b)) := by
  have h' := h
  unfold owlSROIQDANRoleRow owlSROIQDNRoleRow at h'
  split at h'
  swap
  · cases h'
  have hk := noKey_of_anonOff (rowS_isSome h')
  rw [owlSROIQDNRoleRow_sound pat h, entailsAt_anonOff hk (by
    simp [Axiom.mapI, anonG_fix (W := [a, b]) (O := O) (a := a) (by simp),
      anonG_fix (W := [a, b]) (O := O) (a := b) (by simp)]) rfl]

theorem owlSROIQDATypeRow_complete {O : Ontology} (C a : IRI)
    (hO : (anonOff [a] O).isSROIQDKB = true)
    (hc : SROIQDC2aChecks (addAxs (anonOff [a] O) (typeAxs C a))) (hint : Option RawHint) :
    (owlSROIQDATypeRow O C a hint).isSome = true :=
  owlSROIQDTypeRow_complete C a hO hc hint

theorem owlSROIQDASameRow_complete {O : Ontology} (a b : IRI)
    (hO : (anonOff [a, b] O).isSROIQDKB = true)
    (hc : SROIQDC2aChecks (addAxs (anonOff [a, b] O) (sameAxs a b))) (hint : Option RawHint) :
    (owlSROIQDASameRow O a b hint).isSome = true :=
  owlSROIQDSameRow_complete a b hO hc hint

theorem owlSROIQDASubRow_complete {O : Ontology} (A B : IRI)
    (hO : (anonOff [] O).isSROIQDKB = true)
    (hc : SROIQDC2aChecks (addAxs (anonOff [] O) (subAxs (anonOff [] O) A B)))
    (hint : Option RawHint) : (owlSROIQDASubRow O A B hint).isSome = true :=
  owlSROIQDSubRow_complete A B hO hc hint

theorem owlSROIQDADiffRow_complete {O : Ontology} (a b : IRI)
    (hO : (anonOff [a, b] O).isSROIQDKB = true)
    (hc : SROIQDC2aChecks (addAxs (anonOff [a, b] O) (diffAxs a b))) (hint : Option RawHint) :
    (owlSROIQDADiffRow O a b hint).isSome = true :=
  owlSROIQDDiffRow_complete a b hO hc hint

theorem owlSROIQDARoleRow_complete {O : Ontology} {r : ObjProp} (hr : r.isBasic = true) (a b : IRI)
    (hO : (anonOff [a, b] O).isSROIQDKB = true)
    (hc : SROIQDC2aChecks (addAxs (anonOff [a, b] O) (roleAxs r a b))) (hint : Option RawHint) :
    (owlSROIQDARoleRow O r a b hint).isSome = true :=
  owlSROIQDRoleRow_complete hr a b hO hc hint

theorem owlSROIQDANRoleRow_complete {O : Ontology} {r : ObjProp} (hr : r.isBasic = true) (a b : IRI)
    (hO : (anonOff [a, b] O).isSROIQDKB = true)
    (hc : SROIQDC2aChecks (addAxs (anonOff [a, b] O) (nroleAxs r a b))) (hint : Option RawHint) :
    (owlSROIQDANRoleRow O r a b hint).isSome = true :=
  owlSROIQDNRoleRow_complete hr a b hO hc hint

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.owlSROIQDATypeRow_complete
#print axioms ContextCalculus.OWLFrontend.consistentAt_anonOff
#print axioms ContextCalculus.OWLFrontend.entailsAt_anonOff
#print axioms ContextCalculus.OWLFrontend.owlSROIQDAConsistent_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDAConsistent_isSome_iff
#print axioms ContextCalculus.OWLFrontend.owlSROIQDATypeRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDASameRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDASubRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDADiffRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDARoleRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDANRoleRow_sound
