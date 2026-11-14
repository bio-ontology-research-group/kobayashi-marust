import ContextCalculus.OWLFrontend.SRIQKBTranslateCorrect

/-!
# Nominals in OWL class expressions as nominal classes (stage C2)

`docs/V1.7.0-C2-NOMINALS-DESIGN.md`, section 1. The SHOIQ knowledge-base
part (`Ontology.isSHOIQKB`) is the SHIQ knowledge-base part with
`ObjectOneOf` and `ObjectHasValue` (over named individuals) in any class
position.

`nomOnt O requested` replaces each named individual `a` of `O` by a fresh
class IRI `nm a` (its nominal class): `ObjectOneOf(a1 ... an)` becomes
`ObjectUnionOf(nm a1 ... nm an)`, `ObjectHasValue(r a)` becomes
`ObjectSomeValuesFrom(r nm a)`, and every assertion becomes a TBox axiom on
nominal classes (`ClassAssertion(C a)` becomes `SubClassOf(nm a C)`, and so
on). The result is in the SHIQ part and has no assertions.

* `nomOnt_up`: a model of `O` gives a model of `nomOnt O requested` that
  interprets `nm a` as `{a}` and keeps every other class IRI.
* `nomOnt_down`: a model of `nomOnt O requested` in which every nominal
  class is a singleton gives a model of `O` with the same classes and
  roles, each individual at the element of its nominal class.

The nominal classes are fresh by length: `nm a` is the definition name
`defName (nomBase O requested) (inds.idxOf a)`, longer than every class IRI
of `O` and every requested IRI.
-/

namespace ContextCalculus.OWL

/-- ALCIQ class expressions with nominals over named individuals. -/
def ClassExpr.isALCOIQ : ClassExpr → Bool
  | .cls _ | .thing | .nothing => true
  | .and cs | .or cs => cs.attach.all fun ⟨c, _⟩ => c.isALCOIQ
  | .not c => c.isALCOIQ
  | .some r c | .all r c => r.isBasic && c.isALCOIQ
  | .min _ r c | .max _ r c | .exact _ r c => r.isBasic && c.isALCOIQ
  | .oneOf as => as.all Individual.isNamed
  | .hasValue r a => r.isBasic && a.isNamed
  | .hasSelf _
  | .dataSome .. | .dataAll .. | .dataHasValue .. | .dataMin .. | .dataMax ..
  | .dataExact .. => false
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

/-- An axiom of the SHOIQ knowledge-base part. -/
def Axiom.isSHOIQKB : Axiom → Bool
  | .subClassOf c d => c.isALCOIQ && d.isALCOIQ
  | .equivalentClasses cs | .disjointClasses cs => cs.all ClassExpr.isALCOIQ
  | .domain r c | .range r c => r.isBasic && c.isALCOIQ
  | .classAssertion c a => c.isALCOIQ && a.isNamed
  | .objectPropertyAssertion r a b => r.isBasic && a.isNamed && b.isNamed
  | .negativeObjectPropertyAssertion r a b => r.isBasic && a.isNamed && b.isNamed
  | .sameIndividual as | .differentIndividuals as => as.all Individual.isNamed
  | .declareNamedIndividual _ => true
  | ax => ax.isSHIQ

def Ontology.isSHOIQKB (O : Ontology) : Bool := O.axioms.all Axiom.isSHOIQKB

theorem ClassExpr.mem_inds_and {cs : List ClassExpr} {c : ClassExpr} (hc : c ∈ cs) {a : IRI}
    (ha : a ∈ c.namedIndividuals) : a ∈ (ClassExpr.and cs).namedIndividuals := by
  rw [ClassExpr.namedIndividuals]
  simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists]
  exact ⟨c, hc, ha⟩

theorem ClassExpr.mem_inds_or {cs : List ClassExpr} {c : ClassExpr} (hc : c ∈ cs) {a : IRI}
    (ha : a ∈ c.namedIndividuals) : a ∈ (ClassExpr.or cs).namedIndividuals := by
  rw [ClassExpr.namedIndividuals]
  simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists]
  exact ⟨c, hc, ha⟩

end ContextCalculus.OWL

namespace ContextCalculus.OWLFrontend.SHOIQ

open ContextCalculus.OWL

/-- The nominal class of an individual. -/
def nomI (nm : IRI → IRI) : Individual → ClassExpr
  | .named a => .cls (nm a)
  | .anon _ => .nothing

/-- `ObjectOneOf` as nominal classes: one member is its nominal class,
several members their union. -/
def nomOneOf (nm : IRI → IRI) : List Individual → ClassExpr
  | [i] => nomI nm i
  | as => .or (as.map (nomI nm))

/-- Nominals as nominal classes. -/
def rwC (nm : IRI → IRI) : ClassExpr → ClassExpr
  | .cls a => .cls a
  | .thing => .thing
  | .nothing => .nothing
  | .and cs => .and (cs.attach.map fun ⟨c, _⟩ => rwC nm c)
  | .or cs => .or (cs.attach.map fun ⟨c, _⟩ => rwC nm c)
  | .not c => .not (rwC nm c)
  | .some r c => .some r (rwC nm c)
  | .all r c => .all r (rwC nm c)
  | .oneOf as => nomOneOf nm as
  | .hasValue r a => .some r (nomI nm a)
  | .hasSelf r => .hasSelf r
  | .min k r c => .min k r (rwC nm c)
  | .max k r c => .max k r (rwC nm c)
  | .exact k r c => .exact k r (rwC nm c)
  | .dataSome p r => .dataSome p r
  | .dataAll p r => .dataAll p r
  | .dataHasValue p l => .dataHasValue p l
  | .dataMin k p r => .dataMin k p r
  | .dataMax k p r => .dataMax k p r
  | .dataExact k p r => .dataExact k p r
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

/-- The axioms of the rewriting of one axiom. -/
def rwAx (nm : IRI → IRI) : Axiom → List Axiom
  | .subClassOf c d => [.subClassOf (rwC nm c) (rwC nm d)]
  | .equivalentClasses cs => [.equivalentClasses (cs.map (rwC nm))]
  | .disjointClasses cs => [.disjointClasses (cs.map (rwC nm))]
  | .domain r c => [.domain r (rwC nm c)]
  | .range r c => [.range r (rwC nm c)]
  | .classAssertion c a => [.subClassOf (nomI nm a) (rwC nm c)]
  | .objectPropertyAssertion r a b => [.subClassOf (nomI nm a) (.some r (nomI nm b))]
  | .negativeObjectPropertyAssertion r a b =>
      [.subClassOf (nomI nm a) (.all r (.not (nomI nm b)))]
  | .sameIndividual as => [.equivalentClasses (as.map (nomI nm))]
  | .differentIndividuals as => [.disjointClasses (as.map (nomI nm))]
  | .declareNamedIndividual _ => []
  | ax => [ax]

/-! ## Fresh nominal classes -/

/-- The prefix of the nominal classes. -/
def nomBase (O : Ontology) (requested : List IRI) : String :=
  "urn:km:owl-nom:".pushn '#' (SRIQKB.maxLen (O.axioms.flatMap Axiom.classNames ++ requested))

/-- The nominal class of the named individual `a`. -/
def nmOf (O : Ontology) (requested : List IRI) (a : IRI) : IRI :=
  SRIQKB.defName (nomBase O requested) (O.individualNames.idxOf a)

/-- The rewritten ontology. -/
def nomOnt (O : Ontology) (requested : List IRI) : Ontology :=
  ⟨O.axioms.flatMap (rwAx (nmOf O requested))⟩

/-- The nominal classes, one per named individual of `O`. -/
def nomNames (O : Ontology) (requested : List IRI) : List IRI :=
  O.individualNames.map (nmOf O requested)

theorem ne_nmOf {O : Ontology} {requested : List IRI} {b : IRI}
    (h : b ∈ O.axioms.flatMap Axiom.classNames ++ requested) (a : IRI) :
    b ≠ nmOf O requested a := by
  intro he
  have h1 := SRIQKB.length_le_maxLen h
  have h2 := congrArg String.length he
  rw [nmOf, SRIQKB.defName_length] at h2
  simp only [nomBase, String.length_pushn] at h2
  have : "urn:km:owl-nom:".length = 15 := by decide
  omega

theorem nmOf_inj {O : Ontology} {requested : List IRI} {a b : IRI}
    (ha : a ∈ O.individualNames) (h : nmOf O requested a = nmOf O requested b) : a = b := by
  have := SRIQKB.defName_inj h
  exact (List.idxOf_inj ha).1 this

theorem mem_individualNames {O : Ontology} {ax : Axiom} (hax : ax ∈ O.axioms) {a : IRI}
    (ha : a ∈ ax.namedIndividuals) : a ∈ O.individualNames :=
  (O.mem_namesBy _ a).2 ⟨ax, hax, ha⟩

/-! ## The rewriting of class expressions -/

variable {DM : DatatypeMap} {Dom : Type}

theorem nomI_isALCIQ (nm : IRI → IRI) (i : Individual) : (nomI nm i).isALCIQ = true := by
  cases i <;> simp [nomI, ClassExpr.isALCIQ]

theorem nomOneOf_isALCIQ (nm : IRI → IRI) (as : List Individual) :
    (nomOneOf nm as).isALCIQ = true := by
  unfold nomOneOf
  split
  · exact nomI_isALCIQ nm _
  · rw [ClassExpr.isALCIQ]
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall, List.mem_map]
    rintro _ ⟨i, -, rfl⟩
    exact nomI_isALCIQ nm i

theorem rwC_isALCIQ (nm : IRI → IRI) : ∀ c : ClassExpr, c.isALCOIQ = true →
    (rwC nm c).isALCIQ = true
  | .cls _, _ => by rw [rwC, ClassExpr.isALCIQ]
  | .thing, _ => by rw [rwC, ClassExpr.isALCIQ]
  | .nothing, _ => by rw [rwC, ClassExpr.isALCIQ]
  | .and cs, h => by
    rw [ClassExpr.isALCOIQ] at h
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at h
    rw [rwC, ClassExpr.isALCIQ]
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall, List.mem_map,
      Subtype.exists]
    rintro _ ⟨c, hc, -, rfl⟩
    exact rwC_isALCIQ nm c (h c hc)
  | .or cs, h => by
    rw [ClassExpr.isALCOIQ] at h
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at h
    rw [rwC, ClassExpr.isALCIQ]
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall, List.mem_map,
      Subtype.exists]
    rintro _ ⟨c, hc, -, rfl⟩
    exact rwC_isALCIQ nm c (h c hc)
  | .not c, h => by
    rw [ClassExpr.isALCOIQ] at h
    rw [rwC, ClassExpr.isALCIQ]
    exact rwC_isALCIQ nm c h
  | .some r c, h => by
    rw [ClassExpr.isALCOIQ, Bool.and_eq_true] at h
    rw [rwC, ClassExpr.isALCIQ, Bool.and_eq_true]
    exact ⟨h.1, rwC_isALCIQ nm c h.2⟩
  | .all r c, h => by
    rw [ClassExpr.isALCOIQ, Bool.and_eq_true] at h
    rw [rwC, ClassExpr.isALCIQ, Bool.and_eq_true]
    exact ⟨h.1, rwC_isALCIQ nm c h.2⟩
  | .min k r c, h => by
    rw [ClassExpr.isALCOIQ, Bool.and_eq_true] at h
    rw [rwC, ClassExpr.isALCIQ, Bool.and_eq_true]
    exact ⟨h.1, rwC_isALCIQ nm c h.2⟩
  | .max k r c, h => by
    rw [ClassExpr.isALCOIQ, Bool.and_eq_true] at h
    rw [rwC, ClassExpr.isALCIQ, Bool.and_eq_true]
    exact ⟨h.1, rwC_isALCIQ nm c h.2⟩
  | .exact k r c, h => by
    rw [ClassExpr.isALCOIQ, Bool.and_eq_true] at h
    rw [rwC, ClassExpr.isALCIQ, Bool.and_eq_true]
    exact ⟨h.1, rwC_isALCIQ nm c h.2⟩
  | .oneOf as, _ => by
    rw [rwC]
    exact nomOneOf_isALCIQ nm as
  | .hasValue r a, h => by
    rw [ClassExpr.isALCOIQ, Bool.and_eq_true] at h
    rw [rwC, ClassExpr.isALCIQ, Bool.and_eq_true]
    exact ⟨h.1, nomI_isALCIQ nm a⟩
  | .hasSelf _, h | .dataSome .., h | .dataAll .., h | .dataHasValue .., h | .dataMin .., h
  | .dataMax .., h | .dataExact .., h => by rw [ClassExpr.isALCOIQ] at h; exact absurd h (by simp)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

theorem nomI_names {nm : IRI → IRI} {i : Individual} {a : IRI} (h : a ∈ (nomI nm i).names) :
    ∃ b ∈ i.namedIRI, a = nm b := by
  cases i with
  | named b =>
    simp only [nomI, ClassExpr.names, List.mem_singleton] at h
    exact ⟨b, by simp [Individual.namedIRI], h⟩
  | anon _ => simp [nomI, ClassExpr.names] at h

theorem nomOneOf_names {nm : IRI → IRI} {as : List Individual} {a : IRI}
    (h : a ∈ (nomOneOf nm as).names) : ∃ i ∈ as, ∃ b ∈ i.namedIRI, a = nm b := by
  unfold nomOneOf at h
  split at h
  · exact ⟨_, List.mem_singleton_self _, nomI_names h⟩
  · rw [ClassExpr.names] at h
    simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists, List.mem_map] at h
    obtain ⟨_, ⟨i, hi, rfl⟩, ha⟩ := h
    exact ⟨i, hi, nomI_names ha⟩

theorem rwC_names (nm : IRI → IRI) : ∀ (c : ClassExpr) {a : IRI}, a ∈ (rwC nm c).names →
    a ∈ c.names ∨ ∃ b ∈ c.namedIndividuals, a = nm b
  | .cls _, a, h => by rw [rwC] at h; exact Or.inl h
  | .thing, a, h => by rw [rwC] at h; exact Or.inl h
  | .nothing, a, h => by rw [rwC] at h; exact Or.inl h
  | .and cs, a, h => by
    rw [rwC, ClassExpr.names] at h
    simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists, List.mem_map] at h
    obtain ⟨_, ⟨c, hc, -, rfl⟩, ha⟩ := h
    rcases rwC_names nm c ha with h' | ⟨b, hb, rfl⟩
    · exact Or.inl (ClassExpr.mem_names_and hc h')
    · exact Or.inr ⟨b, ClassExpr.mem_inds_and hc hb, rfl⟩
  | .or cs, a, h => by
    rw [rwC, ClassExpr.names] at h
    simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists, List.mem_map] at h
    obtain ⟨_, ⟨c, hc, -, rfl⟩, ha⟩ := h
    rcases rwC_names nm c ha with h' | ⟨b, hb, rfl⟩
    · exact Or.inl (ClassExpr.mem_names_or hc h')
    · exact Or.inr ⟨b, ClassExpr.mem_inds_or hc hb, rfl⟩
  | .not c, a, h => by
    rw [rwC, ClassExpr.names] at h
    rw [ClassExpr.names, ClassExpr.namedIndividuals]
    exact rwC_names nm c h
  | .some r c, a, h => by
    rw [rwC, ClassExpr.names] at h
    rw [ClassExpr.names, ClassExpr.namedIndividuals]
    exact rwC_names nm c h
  | .all r c, a, h => by
    rw [rwC, ClassExpr.names] at h
    rw [ClassExpr.names, ClassExpr.namedIndividuals]
    exact rwC_names nm c h
  | .min k r c, a, h => by
    rw [rwC, ClassExpr.names] at h
    rw [ClassExpr.names, ClassExpr.namedIndividuals]
    exact rwC_names nm c h
  | .max k r c, a, h => by
    rw [rwC, ClassExpr.names] at h
    rw [ClassExpr.names, ClassExpr.namedIndividuals]
    exact rwC_names nm c h
  | .exact k r c, a, h => by
    rw [rwC, ClassExpr.names] at h
    rw [ClassExpr.names, ClassExpr.namedIndividuals]
    exact rwC_names nm c h
  | .oneOf as, a, h => by
    rw [rwC] at h
    obtain ⟨i, hi, b, hb, rfl⟩ := nomOneOf_names h
    refine Or.inr ⟨b, ?_, rfl⟩
    rw [ClassExpr.namedIndividuals]
    exact List.mem_flatMap.2 ⟨i, hi, hb⟩
  | .hasValue r i, a, h => by
    rw [rwC, ClassExpr.names] at h
    obtain ⟨b, hb, rfl⟩ := nomI_names h
    refine Or.inr ⟨b, ?_, rfl⟩
    rw [ClassExpr.namedIndividuals]
    exact hb
  | .hasSelf _, a, h | .dataSome .., a, h | .dataAll .., a, h | .dataHasValue .., a, h
  | .dataMin .., a, h | .dataMax .., a, h | .dataExact .., a, h => by
    rw [rwC] at h; exact Or.inl h
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

theorem nomI_ext {I J : Interp DM Dom} {nm : IRI → IRI} {i : Individual} (hi : i.isNamed = true)
    (hn : ∀ a ∈ i.namedIRI, ∀ x, J.cls (nm a) x ↔ x = I.ind (.named a)) (x : Dom) :
    J.ext (nomI nm i) x ↔ x = I.ind i := by
  cases i with
  | named a =>
    rw [nomI, Interp.ext]
    exact hn a (by simp [Individual.namedIRI]) x
  | anon _ => simp [Individual.isNamed] at hi

theorem nomOneOf_ext {I J : Interp DM Dom} {nm : IRI → IRI} {as : List Individual}
    (hc : ∀ i ∈ as, i.isNamed = true)
    (hn : ∀ i ∈ as, ∀ a ∈ i.namedIRI, ∀ x, J.cls (nm a) x ↔ x = I.ind (.named a)) (x : Dom) :
    J.ext (nomOneOf nm as) x ↔ ∃ i ∈ as, x = I.ind i := by
  unfold nomOneOf
  split
  · rename_i i
    rw [nomI_ext (hc i (by simp)) (hn i (by simp)) x]
    simp
  · rw [Interp.ext]
    constructor
    · rintro ⟨c', hc', H⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc'
      exact ⟨i, hi, (nomI_ext (hc i hi) (hn i hi) x).1 H⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, (nomI_ext (hc i hi) (hn i hi) _).2 rfl⟩

/-- **Rewriting keeps extensions** when the nominal classes stand for
their individuals and the other class IRIs are unchanged. -/
theorem rwC_ext {I J : Interp DM Dom} (hr : J.role = I.role) (nm : IRI → IRI) :
    ∀ c : ClassExpr, c.isALCOIQ = true → (∀ a ∈ c.names, J.cls a = I.cls a) →
      (∀ a ∈ c.namedIndividuals, ∀ x, J.cls (nm a) x ↔ x = I.ind (.named a)) →
      J.ext (rwC nm c) = I.ext c
  | .cls a, _, h, _ => by
    funext x; rw [rwC, Interp.ext, Interp.ext, h a (by simp [ClassExpr.names])]
  | .thing, _, _, _ => by funext x; rw [rwC, Interp.ext, Interp.ext]
  | .nothing, _, _, _ => by funext x; rw [rwC, Interp.ext, Interp.ext]
  | .and cs, hc, h, hn => by
    rw [ClassExpr.isALCOIQ] at hc
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at hc
    have ih : ∀ c ∈ cs, J.ext (rwC nm c) = I.ext c := fun c hm =>
      rwC_ext hr nm c (hc c hm) (fun a ha => h a (ClassExpr.mem_names_and hm ha))
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
    rw [ClassExpr.isALCOIQ] at hc
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at hc
    have ih : ∀ c ∈ cs, J.ext (rwC nm c) = I.ext c := fun c hm =>
      rwC_ext hr nm c (hc c hm) (fun a ha => h a (ClassExpr.mem_names_or hm ha))
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
    rw [ClassExpr.isALCOIQ] at hc
    have ih := rwC_ext hr nm c hc (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      (fun a ha => hn a (by rw [ClassExpr.namedIndividuals]; exact ha))
    funext x; rw [rwC, Interp.ext, Interp.ext, ih]
  | .some r c, hc, h, hn => by
    rw [ClassExpr.isALCOIQ, Bool.and_eq_true] at hc
    have ih := rwC_ext hr nm c hc.2 (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      (fun a ha => hn a (by rw [ClassExpr.namedIndividuals]; exact ha))
    funext x; rw [rwC, Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .all r c, hc, h, hn => by
    rw [ClassExpr.isALCOIQ, Bool.and_eq_true] at hc
    have ih := rwC_ext hr nm c hc.2 (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      (fun a ha => hn a (by rw [ClassExpr.namedIndividuals]; exact ha))
    funext x; rw [rwC, Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .min k r c, hc, h, hn => by
    rw [ClassExpr.isALCOIQ, Bool.and_eq_true] at hc
    have ih := rwC_ext hr nm c hc.2 (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      (fun a ha => hn a (by rw [ClassExpr.namedIndividuals]; exact ha))
    funext x; rw [rwC, Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .max k r c, hc, h, hn => by
    rw [ClassExpr.isALCOIQ, Bool.and_eq_true] at hc
    have ih := rwC_ext hr nm c hc.2 (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      (fun a ha => hn a (by rw [ClassExpr.namedIndividuals]; exact ha))
    funext x; rw [rwC, Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .exact k r c, hc, h, hn => by
    rw [ClassExpr.isALCOIQ, Bool.and_eq_true] at hc
    have ih := rwC_ext hr nm c hc.2 (fun a ha => h a (by rw [ClassExpr.names]; exact ha))
      (fun a ha => hn a (by rw [ClassExpr.namedIndividuals]; exact ha))
    funext x; rw [rwC, Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .oneOf as, hc, _, hn => by
    rw [ClassExpr.isALCOIQ, List.all_eq_true] at hc
    have hn' : ∀ i ∈ as, ∀ a ∈ i.namedIRI, ∀ x, J.cls (nm a) x ↔ x = I.ind (.named a) :=
      fun i hi a ha => hn a (by rw [ClassExpr.namedIndividuals]; exact List.mem_flatMap.2 ⟨i, hi, ha⟩)
    funext x; rw [rwC, Interp.ext]
    exact propext (nomOneOf_ext hc hn' x)
  | .hasValue r i, hc, _, hn => by
    rw [ClassExpr.isALCOIQ, Bool.and_eq_true] at hc
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
  | .hasSelf _, hc, _, _ | .dataSome .., hc, _, _ | .dataAll .., hc, _, _
  | .dataHasValue .., hc, _, _ | .dataMin .., hc, _, _ | .dataMax .., hc, _, _
  | .dataExact .., hc, _, _ => by rw [ClassExpr.isALCOIQ] at hc; exact absurd hc (by simp)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

/-! ## Axioms -/

/-- The rewriting of an axiom is in the SHIQ part and has no assertions. -/
theorem rwAx_isSHIQ (nm : IRI → IRI) {ax : Axiom} (hax : ax.isSHOIQKB = true) :
    ∀ ax' ∈ rwAx nm ax, ax'.isSHIQ = true ∧ ax'.isAssertion = false := by
  have hcs : ∀ cs : List ClassExpr, cs.all ClassExpr.isALCOIQ = true →
      (cs.map (rwC nm)).all ClassExpr.isALCIQ = true := by
    intro cs h
    simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at h ⊢
    exact fun c hc => rwC_isALCIQ nm c (h c hc)
  have his : ∀ as : List Individual, (as.map (nomI nm)).all ClassExpr.isALCIQ = true := by
    intro as
    simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    exact fun i _ => nomI_isALCIQ nm i
  intro ax' hax'
  cases ax with
  | subClassOf c d =>
    simp only [Axiom.isSHOIQKB, Bool.and_eq_true] at hax
    simp only [rwAx, List.mem_singleton] at hax'
    subst hax'
    simp [Axiom.isSHIQ, Axiom.isAssertion, rwC_isALCIQ nm _ hax.1, rwC_isALCIQ nm _ hax.2]
  | equivalentClasses cs =>
    simp only [Axiom.isSHOIQKB] at hax
    simp only [rwAx, List.mem_singleton] at hax'
    subst hax'
    simp only [Axiom.isSHIQ, Axiom.isAssertion, hcs _ hax, and_self]
  | disjointClasses cs =>
    simp only [Axiom.isSHOIQKB] at hax
    simp only [rwAx, List.mem_singleton] at hax'
    subst hax'
    simp only [Axiom.isSHIQ, Axiom.isAssertion, hcs _ hax, and_self]
  | domain r c =>
    simp only [Axiom.isSHOIQKB, Bool.and_eq_true] at hax
    simp only [rwAx, List.mem_singleton] at hax'
    subst hax'
    simp [Axiom.isSHIQ, Axiom.isAssertion, hax.1, rwC_isALCIQ nm _ hax.2]
  | range r c =>
    simp only [Axiom.isSHOIQKB, Bool.and_eq_true] at hax
    simp only [rwAx, List.mem_singleton] at hax'
    subst hax'
    simp [Axiom.isSHIQ, Axiom.isAssertion, hax.1, rwC_isALCIQ nm _ hax.2]
  | classAssertion c i =>
    simp only [Axiom.isSHOIQKB, Bool.and_eq_true] at hax
    simp only [rwAx, List.mem_singleton] at hax'
    subst hax'
    simp [Axiom.isSHIQ, Axiom.isAssertion, nomI_isALCIQ, rwC_isALCIQ nm _ hax.1]
  | objectPropertyAssertion r i i' =>
    simp only [Axiom.isSHOIQKB, Bool.and_eq_true] at hax
    simp only [rwAx, List.mem_singleton] at hax'
    subst hax'
    simp [Axiom.isSHIQ, Axiom.isAssertion, ClassExpr.isALCIQ, nomI_isALCIQ, hax.1.1]
  | negativeObjectPropertyAssertion r i i' =>
    simp only [Axiom.isSHOIQKB, Bool.and_eq_true] at hax
    simp only [rwAx, List.mem_singleton] at hax'
    subst hax'
    simp [Axiom.isSHIQ, Axiom.isAssertion, ClassExpr.isALCIQ, nomI_isALCIQ, hax.1.1]
  | sameIndividual as =>
    simp only [rwAx, List.mem_singleton] at hax'
    subst hax'
    simp only [Axiom.isSHIQ, Axiom.isAssertion, his, and_self]
  | differentIndividuals as =>
    simp only [rwAx, List.mem_singleton] at hax'
    subst hax'
    simp only [Axiom.isSHIQ, Axiom.isAssertion, his, and_self]
  | declareNamedIndividual _ => simp [rwAx] at hax'
  | _ =>
    simp only [rwAx, List.mem_singleton] at hax'
    subst hax'
    simp only [Axiom.isSHOIQKB] at hax
    exact ⟨hax, by simp_all [Axiom.isAssertion, Axiom.isSHIQ, Axiom.isSHI, Axiom.isSRI]⟩

variable {I J : Interp DM Dom}

/-- **Rewriting keeps satisfaction** of an axiom of the SHOIQ part. -/
theorem sat_rwAx (hr : J.role = I.role) (nm : IRI → IRI) {ax : Axiom}
    (hax : ax.isSHOIQKB = true) (hc : ∀ a ∈ ax.classNames, J.cls a = I.cls a)
    (hn : ∀ a ∈ ax.namedIndividuals, ∀ x, J.cls (nm a) x ↔ x = I.ind (.named a))
    (N N' : List IRI) : (∀ ax' ∈ rwAx nm ax, J.sat N ax') ↔ I.sat N' ax := by
  have hp := Interp.prop_congr hr
  cases ax with
  | subClassOf c d =>
    simp only [Axiom.isSHOIQKB, Bool.and_eq_true] at hax
    simp only [Axiom.classNames, List.mem_append] at hc
    simp only [Axiom.namedIndividuals, List.mem_append] at hn
    simp only [rwAx, List.mem_singleton, forall_eq, Interp.sat]
    rw [rwC_ext hr nm c hax.1 (fun a ha => hc a (Or.inl ha)) (fun a ha => hn a (Or.inl ha)),
      rwC_ext hr nm d hax.2 (fun a ha => hc a (Or.inr ha)) (fun a ha => hn a (Or.inr ha))]
  | equivalentClasses cs =>
    simp only [Axiom.isSHOIQKB, List.all_eq_true] at hax
    simp only [Axiom.classNames, List.mem_flatMap] at hc
    simp only [Axiom.namedIndividuals, List.mem_flatMap] at hn
    have ih : ∀ c ∈ cs, J.ext (rwC nm c) = I.ext c := fun c hm =>
      rwC_ext hr nm c (hax c hm) (fun a ha => hc a ⟨c, hm, ha⟩) (fun a ha => hn a ⟨c, hm, ha⟩)
    simp only [rwAx, List.mem_singleton, forall_eq, Interp.sat, List.mem_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    constructor
    · intro h c hm d hd x hx
      rw [← ih d hd]
      exact h c hm d hd x (by rw [ih c hm]; exact hx)
    · intro h c hm d hd x hx
      rw [ih d hd]
      exact h c hm d hd x (by rw [← ih c hm]; exact hx)
  | disjointClasses cs =>
    simp only [Axiom.isSHOIQKB, List.all_eq_true] at hax
    simp only [Axiom.classNames, List.mem_flatMap] at hc
    simp only [Axiom.namedIndividuals, List.mem_flatMap] at hn
    have ih : ∀ c ∈ cs, J.ext (rwC nm c) = I.ext c := fun c hm =>
      rwC_ext hr nm c (hax c hm) (fun a ha => hc a ⟨c, hm, ha⟩) (fun a ha => hn a ⟨c, hm, ha⟩)
    simp only [rwAx, List.mem_singleton, forall_eq, Interp.sat, List.pairwise_map]
    constructor
    · intro h
      exact h.imp_of_mem fun hc hd h' x => (ih _ hc) ▸ (ih _ hd) ▸ h' x
    · intro h
      exact h.imp_of_mem fun hc hd h' x => (ih _ hc).symm ▸ (ih _ hd).symm ▸ h' x
  | domain r c =>
    simp only [Axiom.isSHOIQKB, Bool.and_eq_true] at hax
    simp only [Axiom.classNames] at hc
    simp only [Axiom.namedIndividuals] at hn
    simp only [rwAx, List.mem_singleton, forall_eq, Interp.sat]
    rw [rwC_ext hr nm c hax.2 hc hn, hp]
  | range r c =>
    simp only [Axiom.isSHOIQKB, Bool.and_eq_true] at hax
    simp only [Axiom.classNames] at hc
    simp only [Axiom.namedIndividuals] at hn
    simp only [rwAx, List.mem_singleton, forall_eq, Interp.sat]
    rw [rwC_ext hr nm c hax.2 hc hn, hp]
  | classAssertion c i =>
    simp only [Axiom.isSHOIQKB, Bool.and_eq_true] at hax
    simp only [Axiom.classNames] at hc
    simp only [Axiom.namedIndividuals, List.mem_append] at hn
    simp only [rwAx, List.mem_singleton, forall_eq, Interp.sat]
    rw [rwC_ext hr nm c hax.1 hc (fun a ha => hn a (Or.inl ha))]
    have hi := nomI_ext (I := I) (J := J) (nm := nm) hax.2 (fun a ha => hn a (Or.inr ha))
    constructor
    · intro h
      exact h _ ((hi _).2 rfl)
    · intro h x hx
      rw [(hi x).1 hx]
      exact h
  | objectPropertyAssertion r i i' =>
    simp only [Axiom.isSHOIQKB, Bool.and_eq_true] at hax
    simp only [Axiom.namedIndividuals, List.mem_append] at hn
    simp only [rwAx, List.mem_singleton, forall_eq, Interp.sat, Interp.ext]
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
    simp only [Axiom.isSHOIQKB, Bool.and_eq_true] at hax
    simp only [Axiom.namedIndividuals, List.mem_append] at hn
    simp only [rwAx, List.mem_singleton, forall_eq, Interp.sat, Interp.ext]
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
    simp only [Axiom.isSHOIQKB, List.all_eq_true] at hax
    simp only [Axiom.namedIndividuals, List.mem_flatMap] at hn
    have hi : ∀ i ∈ as, ∀ x, J.ext (nomI nm i) x ↔ x = I.ind i := fun i hi =>
      nomI_ext (hax i hi) (fun a ha => hn a ⟨i, hi, ha⟩)
    simp only [rwAx, List.mem_singleton, forall_eq, Interp.sat, List.mem_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    constructor
    · intro h i hi' i' hi''
      exact ((hi i' hi'') _).1 (h i hi' i' hi'' (I.ind i) (((hi i hi') _).2 rfl))
    · intro h i hi' i' hi'' x hx
      rw [(hi i hi' x).1 hx, h i hi' i' hi'']
      exact (hi i' hi'' _).2 rfl
  | differentIndividuals as =>
    simp only [Axiom.isSHOIQKB, List.all_eq_true] at hax
    simp only [Axiom.namedIndividuals, List.mem_flatMap] at hn
    have hi : ∀ i ∈ as, ∀ x, J.ext (nomI nm i) x ↔ x = I.ind i := fun i hi =>
      nomI_ext (hax i hi) (fun a ha => hn a ⟨i, hi, ha⟩)
    simp only [rwAx, List.mem_singleton, forall_eq, Interp.sat, List.pairwise_map]
    constructor
    · intro h
      refine h.imp_of_mem fun {i i'} hm hm' h' he => h' (I.ind i) ⟨(hi i hm _).2 rfl, ?_⟩
      exact (hi i' hm' _).2 he
    · intro h
      refine h.imp_of_mem fun {i i'} hm hm' h' x ⟨hx, hx'⟩ => h' ?_
      rw [← (hi i hm x).1 hx, ← (hi i' hm' x).1 hx']
  | declareNamedIndividual _ => simp [rwAx, Interp.sat]
  | _ =>
    simp only [rwAx, List.mem_singleton, forall_eq]
    simp only [Axiom.isSHOIQKB] at hax
    exact Axiom.sat_congr hr hax hc N N'

/-! ## The model maps -/

/-- A model of `O` read on the rewritten ontology: `nm a` is `{a}`. -/
def upI (O : Ontology) (requested : List IRI) (I : Interp DM Dom) : Interp DM Dom :=
  { I with cls := fun b x =>
      (∃ a ∈ O.individualNames, b = nmOf O requested a ∧ x = I.ind (.named a)) ∨
        ((∀ a ∈ O.individualNames, b ≠ nmOf O requested a) ∧ I.cls b x) }

theorem upI_old {O : Ontology} {requested : List IRI} (I : Interp DM Dom) {b : IRI}
    (hb : b ∈ O.axioms.flatMap Axiom.classNames ++ requested) :
    (upI O requested I).cls b = I.cls b := by
  funext x
  apply propext
  simp only [upI]
  constructor
  · rintro (⟨a, -, rfl, -⟩ | ⟨-, h⟩)
    · exact absurd rfl (ne_nmOf hb a)
    · exact h
  · intro h
    exact Or.inr ⟨fun a _ => ne_nmOf hb a, h⟩

theorem upI_nom {O : Ontology} {requested : List IRI} (I : Interp DM Dom) {a : IRI}
    (ha : a ∈ O.individualNames) (x : Dom) :
    (upI O requested I).cls (nmOf O requested a) x ↔ x = I.ind (.named a) := by
  simp only [upI]
  constructor
  · rintro (⟨a', ha', he, rfl⟩ | ⟨h, -⟩)
    · rw [nmOf_inj ha he]
    · exact absurd rfl (h a ha)
  · intro h
    exact Or.inl ⟨a, ha, rfl, h⟩

/-- **Up.** A model of `O` gives a model of the rewritten ontology. -/
theorem nomOnt_up {O : Ontology} (hO : O.isSHOIQKB = true) (requested : List IRI)
    {I : Interp DM Dom} (hI : OWL.Model O I) : OWL.Model (nomOnt O requested) (upI O requested I) := by
  have hO' : ∀ ax ∈ O.axioms, ax.isSHOIQKB = true := by
    simpa [Ontology.isSHOIQKB, List.all_eq_true] using hO
  intro ax' hax'
  obtain ⟨ax, hax, hax'⟩ := List.mem_flatMap.1 hax'
  refine (sat_rwAx (I := I) (J := upI O requested I) rfl (nmOf O requested) (hO' ax hax)
    (fun b hb => upI_old I (List.mem_append_left _ (List.mem_flatMap.2 ⟨ax, hax, hb⟩)))
    (fun a ha x => upI_nom I (mem_individualNames hax ha) x) _ O.namedIndividuals).2
    (hI ax hax) ax' hax'

/-- A model of the rewritten ontology with its individuals at the elements
of their nominal classes. -/
noncomputable def downI (O : Ontology) (requested : List IRI) (J : Interp DM Dom) :
    Interp DM Dom := by
  classical
  exact { J with ind := fun i => match i with
    | .named a => if h : ∃ x, J.cls (nmOf O requested a) x then h.choose else J.ind i
    | .anon _ => J.ind i }

theorem downI_nom {O : Ontology} {requested : List IRI} {J : Interp DM Dom} {a : IRI}
    (h : ∃ x, ∀ y, J.cls (nmOf O requested a) y ↔ y = x) (y : Dom) :
    J.cls (nmOf O requested a) y ↔ y = (downI O requested J).ind (.named a) := by
  obtain ⟨x, hx⟩ := h
  have hex : ∃ x, J.cls (nmOf O requested a) x := ⟨x, (hx x).2 rfl⟩
  have hv : (downI O requested J).ind (.named a) = x := by
    simp only [downI, dif_pos hex]
    exact (hx _).1 hex.choose_spec
  rw [hv]
  exact hx y

/-- **Down.** A model of the rewritten ontology whose nominal classes are
singletons gives a model of `O` with the same classes and roles. -/
theorem nomOnt_down {O : Ontology} (hO : O.isSHOIQKB = true) (requested : List IRI)
    {J : Interp DM Dom} (hJ : OWL.Model (nomOnt O requested) J)
    (hs : ∀ a ∈ O.individualNames, ∃ x, ∀ y, J.cls (nmOf O requested a) y ↔ y = x) :
    OWL.Model O (downI O requested J) ∧ (downI O requested J).cls = J.cls := by
  have hO' : ∀ ax ∈ O.axioms, ax.isSHOIQKB = true := by
    simpa [Ontology.isSHOIQKB, List.all_eq_true] using hO
  refine ⟨fun ax hax => ?_, rfl⟩
  refine (sat_rwAx (I := downI O requested J) (J := J) rfl (nmOf O requested) (hO' ax hax)
    (fun b _ => rfl) (fun a ha x => downI_nom (hs a (mem_individualNames hax ha)) x)
    (nomOnt O requested).namedIndividuals _).1 fun ax' hax' => ?_
  exact hJ ax' (List.mem_flatMap.2 ⟨ax, hax, hax'⟩)

/-- The rewritten ontology is in the SHIQ part. -/
theorem nomOnt_isSHIQ {O : Ontology} (hO : O.isSHOIQKB = true) (requested : List IRI) :
    (nomOnt O requested).isSHIQ = true ∧ ∀ ax ∈ (nomOnt O requested).axioms,
      ax.isAssertion = false := by
  have hO' : ∀ ax ∈ O.axioms, ax.isSHOIQKB = true := by
    simpa [Ontology.isSHOIQKB, List.all_eq_true] using hO
  refine ⟨?_, fun ax' hax' => ?_⟩
  · simp only [Ontology.isSHIQ, List.all_eq_true]
    intro ax' hax'
    obtain ⟨ax, hax, hax'⟩ := List.mem_flatMap.1 hax'
    exact (rwAx_isSHIQ _ (hO' ax hax) ax' hax').1
  · obtain ⟨ax, hax, hax'⟩ := List.mem_flatMap.1 hax'
    exact (rwAx_isSHIQ _ (hO' ax hax) ax' hax').2

end ContextCalculus.OWLFrontend.SHOIQ

#print axioms ContextCalculus.OWLFrontend.SHOIQ.rwC_ext
#print axioms ContextCalculus.OWLFrontend.SHOIQ.sat_rwAx
#print axioms ContextCalculus.OWLFrontend.SHOIQ.nomOnt_up
#print axioms ContextCalculus.OWLFrontend.SHOIQ.nomOnt_down
