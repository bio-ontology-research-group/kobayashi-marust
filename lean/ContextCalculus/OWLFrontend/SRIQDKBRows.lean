import ContextCalculus.OWLFrontend.SRIQDKBReference

/-!
# Rows of the SHIQ(D) knowledge-base route (v1.7.0 stage C4)

Each row is a consistency test (`owlSHIQDKBConsistent`) on the ontology
with added assertions:

* type row `O ⊨ ClassAssertion(C a)`: add `ClassAssertion(ObjectComplementOf(C) a)`;
* same row `O ⊨ SameIndividual(a b)`: add `DifferentIndividuals(a b)`;
* class row `O ⊨ SubClassOf(A B)`: add `ClassAssertion(A f)` and
  `ClassAssertion(ObjectComplementOf(B) f)` for an individual `f` that is
  longer than every named individual of `O` (`freshInd`).

The added assertions are in the SHIQ(D) knowledge-base part, and the
satisfaction of its axioms does not depend on the named-individual list of
`HasKey` (`sat_N`) nor on the individuals an axiom does not mention
(`sat_upd`). So a model of the extended ontology is a model of `O` that
satisfies the added assertions (`model_addAxs`), and each row is exact at
`owl2MapP pat`, for every reading `pat` of `xsd:pattern` and every hint.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD

variable {DM : DatatypeMap} {D : Type}

/-- `O` entails `ax` at the datatype map `DM`. -/
def EntailsAt (DM : DatatypeMap) (O : Ontology) (ax : Axiom) : Prop :=
  ∀ (Dom : Type) [Nonempty Dom] (I : Interp DM Dom), OWL.Model O I → I.sat ax.namedIndividuals ax

/-- `O` with the axioms `L` appended. -/
def addAxs (O : Ontology) (L : List Axiom) : Ontology := ⟨O.axioms ++ L⟩

theorem isSHIQDKB_addAxs {O : Ontology} {L : List Axiom} :
    (addAxs O L).isSHIQDKB = (O.isSHIQDKB && L.all Axiom.isSHIQDKB) := by
  simp [addAxs, Ontology.isSHIQDKB, List.all_append]

/-- Satisfaction on the SHIQ(D) knowledge-base part does not depend on the
named-individual list. -/
theorem sat_N {I : Interp DM D} {ax : Axiom} (h : ax.isSHIQDKB = true) (N N' : List IRI) :
    I.sat N ax ↔ I.sat N' ax :=
  sat_congr_clsK rfl rfl rfl rfl h (fun _ _ => rfl) N N'

theorem model_addAxs {O : Ontology} {L : List Axiom} (hO : O.isSHIQDKB = true)
    (hL : ∀ ax ∈ L, ax.isSHIQDKB = true) (I : Interp DM D) :
    OWL.Model (addAxs O L) I ↔ OWL.Model O I ∧ ∀ ax ∈ L, I.sat [] ax := by
  have hO' : ∀ a ∈ O.axioms, a.isSHIQDKB = true := by
    simpa [Ontology.isSHIQDKB, List.all_eq_true] using hO
  simp only [OWL.Model, addAxs, List.mem_append]
  constructor
  · intro h
    exact ⟨fun a ha => (sat_N (hO' a ha) _ _).1 (h a (Or.inl ha)),
      fun a ha => (sat_N (hL a ha) _ _).1 (h a (Or.inr ha))⟩
  · rintro ⟨h1, h2⟩ a (ha | ha)
    · exact (sat_N (hO' a ha) _ _).1 (h1 a ha)
    · exact (sat_N (hL a ha) _ _).1 (h2 a ha)

/-! ## Updating an unmentioned individual -/

/-- `I` with the named individual `f` sent to `x`. -/
def updI (I : Interp DM D) (f : IRI) (x : D) : Interp DM D :=
  { I with ind := Function.update I.ind (.named f) x }

theorem upd_ind_of {I : Interp DM D} {f : IRI} {x : D} {i : Individual} {L : List IRI}
    (hn : i.isNamed = true) (hm : ∀ a ∈ i.namedIRI, a ∈ L) (hf : f ∉ L) :
    (updI I f x).ind i = I.ind i := by
  cases i with
  | anon _ => simp [Individual.isNamed] at hn
  | named a =>
    have ha : a ≠ f := fun h => hf (h ▸ hm a (by simp [Individual.namedIRI]))
    simp only [updI]
    exact Function.update_of_ne (fun h => ha (Individual.named.inj h)) _ _

/-- **Satisfaction ignores the individuals an axiom does not mention**, on
the SHIQ(D) knowledge-base part. -/
theorem sat_upd {I : Interp DM D} {f : IRI} {x : D} {ax : Axiom} (hax : ax.isSHIQDKB = true)
    (hf : f ∉ ax.namedIndividuals) (N : List IRI) : (updI I f x).sat N ax ↔ I.sat N ax := by
  have hJ : ∀ i : Individual, i.isNamed = true → (∀ a ∈ i.namedIRI, a ∈ ax.namedIndividuals) →
      (updI I f x).ind i = I.ind i := fun i hn hm => upd_ind_of hn hm hf
  cases ax
  case classAssertion c a =>
    simp only [Axiom.isSHIQDKB, Bool.and_eq_true] at hax
    simp only [Interp.sat]
    rw [ext_congr_cls (I := updI I f x) (J := I) rfl rfl rfl c hax.1 (fun _ _ => rfl),
      hJ a hax.2 (fun b hb => by simp [Axiom.namedIndividuals, hb])]
  case objectPropertyAssertion r a b =>
    simp only [Axiom.isSHIQDKB, Bool.and_eq_true] at hax
    simp only [Interp.sat]
    rw [hJ a hax.1.2 (fun c hc => by simp [Axiom.namedIndividuals, hc]),
      hJ b hax.2 (fun c hc => by simp [Axiom.namedIndividuals, hc])]
    rfl
  case negativeObjectPropertyAssertion r a b =>
    simp only [Axiom.isSHIQDKB, Bool.and_eq_true] at hax
    simp only [Interp.sat]
    rw [hJ a hax.1.2 (fun c hc => by simp [Axiom.namedIndividuals, hc]),
      hJ b hax.2 (fun c hc => by simp [Axiom.namedIndividuals, hc])]
    rfl
  case sameIndividual as =>
    simp only [Axiom.isSHIQDKB, List.all_eq_true] at hax
    have hm : ∀ a ∈ as, (updI I f x).ind a = I.ind a := fun a ha =>
      hJ a (hax a ha) (fun c hc => by
        simp only [Axiom.namedIndividuals, List.mem_flatMap]; exact ⟨a, ha, hc⟩)
    simp only [Interp.sat]
    constructor
    · intro h a ha b hb; rw [← hm a ha, ← hm b hb]; exact h a ha b hb
    · intro h a ha b hb; rw [hm a ha, hm b hb]; exact h a ha b hb
  case differentIndividuals as =>
    simp only [Axiom.isSHIQDKB, List.all_eq_true] at hax
    have hm : ∀ a ∈ as, (updI I f x).ind a = I.ind a := fun a ha =>
      hJ a (hax a ha) (fun c hc => by
        simp only [Axiom.namedIndividuals, List.mem_flatMap]; exact ⟨a, ha, hc⟩)
    simp only [Interp.sat]
    constructor
    · exact List.Pairwise.imp_of_mem fun ha hb h => by rwa [← hm _ ha, ← hm _ hb]
    · exact List.Pairwise.imp_of_mem fun ha hb h => by rwa [hm _ ha, hm _ hb]
  case declareNamedIndividual a => simp only [Interp.sat]
  case dataPropertyAssertion p a l =>
    simp only [Axiom.isSHIQDKB, Bool.and_eq_true] at hax
    simp only [Interp.sat]
    rw [hJ a hax.2 (fun c hc => by simp [Axiom.namedIndividuals, hc])]
    rfl
  case negativeDataPropertyAssertion p a l =>
    simp only [Axiom.isSHIQDKB, Bool.and_eq_true] at hax
    simp only [Interp.sat]
    rw [hJ a hax.2 (fun c hc => by simp [Axiom.namedIndividuals, hc])]
    rfl
  all_goals exact sat_congr_cls (I := updI I f x) (J := I) rfl rfl rfl
                            (by simpa [Axiom.isSHIQDKB] using hax) (fun _ _ => rfl) N N

/-- An individual longer than every named individual of `O`. -/
def freshInd (O : Ontology) : IRI := "".pushn '#' (SRIQKB.maxLen O.namedIndividuals + 1)

theorem freshInd_not_mem (O : Ontology) : freshInd O ∉ O.namedIndividuals := by
  intro h
  have h1 := SRIQKB.length_le_maxLen h
  simp only [freshInd, String.length_pushn] at h1
  have : "".length = 0 := rfl
  omega

theorem model_upd {O : Ontology} (hO : O.isSHIQDKB = true) {I : Interp DM D} {f : IRI}
    (hf : f ∉ O.namedIndividuals) (x : D) : OWL.Model O (updI I f x) ↔ OWL.Model O I := by
  have hO' : ∀ a ∈ O.axioms, a.isSHIQDKB = true := by
    simpa [Ontology.isSHIQDKB, List.all_eq_true] using hO
  have hfa : ∀ a ∈ O.axioms, f ∉ a.namedIndividuals := fun a ha hm =>
    hf (List.mem_flatMap.2 ⟨a, ha, hm⟩)
  simp only [OWL.Model]
  exact forall_congr' fun a => imp_congr_right fun ha => sat_upd (hO' a ha) (hfa a ha) _

/-! ## The rows -/

/-- The assertion added for a type row. -/
def typeAxs (C a : IRI) : List Axiom := [.classAssertion (.not (.cls C)) (.named a)]

/-- The assertion added for a same row. -/
def sameAxs (a b : IRI) : List Axiom := [.differentIndividuals [.named a, .named b]]

/-- The assertions added for a class row. -/
def subAxs (O : Ontology) (A B : IRI) : List Axiom :=
  [.classAssertion (.cls A) (.named (freshInd O)), .classAssertion (.not (.cls B)) (.named (freshInd O))]

/-- **Type of an individual**: decides `O ⊨ ClassAssertion(C a)`. -/
def owlTypeRowD (O : OWL.Ontology) (C a : OWL.IRI) (hint : Option RawHint) : Option Bool :=
  (owlSHIQDKBConsistent (addAxs O (typeAxs C a)) hint).map (!·)

/-- **Equality of individuals**: decides `O ⊨ SameIndividual(a b)`. -/
def owlSameRowD (O : OWL.Ontology) (a b : OWL.IRI) (hint : Option RawHint) : Option Bool :=
  (owlSHIQDKBConsistent (addAxs O (sameAxs a b)) hint).map (!·)

/-- **Subsumption**: decides `O ⊨ SubClassOf(A B)` for class IRIs. -/
def owlSubRowD (O : OWL.Ontology) (A B : OWL.IRI) (hint : Option RawHint) : Option Bool :=
  (owlSHIQDKBConsistent (addAxs O (subAxs O A B)) hint).map (!·)

theorem typeAxs_ok (C a : IRI) : ∀ ax ∈ typeAxs C a, ax.isSHIQDKB = true := by
  simp [typeAxs, Axiom.isSHIQDKB, ClassExpr.isALCIQD, Individual.isNamed]

theorem sameAxs_ok (a b : IRI) : ∀ ax ∈ sameAxs a b, ax.isSHIQDKB = true := by
  simp [sameAxs, Axiom.isSHIQDKB, Individual.isNamed]

theorem subAxs_ok (O : Ontology) (A B : IRI) : ∀ ax ∈ subAxs O A B, ax.isSHIQDKB = true := by
  simp [subAxs, Axiom.isSHIQDKB, ClassExpr.isALCIQD, Individual.isNamed]

/-- A row answer: `v` is the negated consistency of the extension. -/
theorem row_of {O : Ontology} {L : List Axiom} {hint : Option RawHint} {v : Bool}
    (pat : String → String → Prop)
    (h : (owlSHIQDKBConsistent (addAxs O L) hint).map (!·) = some v) :
    O.isSHIQDKB = true ∧ (v = true ↔ ¬ ConsistentAt (owl2MapP pat) (addAxs O L)) := by
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h
  have hk : (addAxs O L).isSHIQDKB = true := by
    have := (owlSHIQDKBConsistent_isSome_iff (addAxs O L) hint).1 (by rw [hw]; rfl)
    exact this.1
  rw [isSHIQDKB_addAxs, Bool.and_eq_true] at hk
  refine ⟨hk.1, ?_⟩
  rw [← owlSHIQDKBConsistent_sound pat hw]
  cases w <;> simp

/-- **Exactness of the type row**, at the OWL 2 datatype map, for every
reading of `xsd:pattern` and every hint. -/
theorem owlTypeRowD_sound (pat : String → String → Prop) {O : OWL.Ontology} {C a : OWL.IRI}
    {hint : Option RawHint} {v : Bool} (h : owlTypeRowD O C a hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.classAssertion (.cls C) (.named a)) := by
  obtain ⟨hO, hv⟩ := row_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI
    by_contra hc
    refine hi Dom I ((model_addAxs hO (typeAxs_ok C a) I).2 ⟨hI, ?_⟩)
    simpa [typeAxs, Interp.sat, Interp.ext] using hc
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxs hO (typeAxs_ok C a) I).1 hI
    have := he Dom I hI
    simp only [typeAxs, List.mem_singleton, forall_eq, Interp.sat, Interp.ext] at hs this
    exact hs this

/-- **Exactness of the same row.** -/
theorem owlSameRowD_sound (pat : String → String → Prop) {O : OWL.Ontology} {a b : OWL.IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSameRowD O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.sameIndividual [.named a, .named b]) := by
  obtain ⟨hO, hv⟩ := row_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI
    by_contra hc
    refine hi Dom I ((model_addAxs hO (sameAxs_ok a b) I).2 ⟨hI, ?_⟩)
    simp only [Interp.sat, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, not_and] at hc
    simp only [sameAxs, forall_eq, Interp.sat, List.pairwise_cons,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil, and_true]
    exact ⟨fun he => hc ⟨trivial, he⟩ he.symm trivial, fun _ h => h.elim⟩
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxs hO (sameAxs_ok a b) I).1 hI
    have := he Dom I hI
    simp only [sameAxs, forall_eq, Interp.sat, List.pairwise_cons,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil, and_true] at hs
    exact hs.1 (this _ (by simp) _ (by simp))

/-- **Exactness of the class row.** -/
theorem owlSubRowD_sound (pat : String → String → Prop) {O : OWL.Ontology} {A B : OWL.IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSubRowD O A B hint = some v) :
    v = true ↔ EntailsSubAt (owl2MapP pat) O A B := by
  obtain ⟨hO, hv⟩ := row_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI x hA
    by_contra hB
    have hU := (model_upd hO (freshInd_not_mem O) x).2 hI
    refine hi Dom (updI I (freshInd O) x) ((model_addAxs hO (subAxs_ok O A B) _).2 ⟨hU, ?_⟩)
    simp only [subAxs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Interp.sat, Interp.ext, updI, Function.update_self]
    exact ⟨hA, hB⟩
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxs hO (subAxs_ok O A B) I).1 hI
    simp only [subAxs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Interp.sat, Interp.ext] at hs
    exact hs.2 (he Dom I hI _ hs.1)

/-- On the SHIQ(D) knowledge-base part, the type row answers when the
checks pass on the extension, for every hint. -/
theorem owlTypeRowD_complete {O : OWL.Ontology} (C a : OWL.IRI) (h : O.isSHIQDKB = true)
    (hs : SHIQDKBChecks (addAxs O (typeAxs C a))) (hint : Option RawHint) :
    (owlTypeRowD O C a hint).isSome = true := by
  unfold owlTypeRowD
  rw [Option.isSome_map]
  exact (owlSHIQDKBConsistent_isSome_iff _ hint).2
    ⟨by rw [isSHIQDKB_addAxs, h, List.all_eq_true.2 (typeAxs_ok C a)]; rfl, hs⟩

theorem owlSameRowD_complete {O : OWL.Ontology} (a b : OWL.IRI) (h : O.isSHIQDKB = true)
    (hs : SHIQDKBChecks (addAxs O (sameAxs a b))) (hint : Option RawHint) :
    (owlSameRowD O a b hint).isSome = true := by
  unfold owlSameRowD
  rw [Option.isSome_map]
  exact (owlSHIQDKBConsistent_isSome_iff _ hint).2
    ⟨by rw [isSHIQDKB_addAxs, h, List.all_eq_true.2 (sameAxs_ok a b)]; rfl, hs⟩

theorem owlSubRowD_complete {O : OWL.Ontology} (A B : OWL.IRI) (h : O.isSHIQDKB = true)
    (hs : SHIQDKBChecks (addAxs O (subAxs O A B))) (hint : Option RawHint) :
    (owlSubRowD O A B hint).isSome = true := by
  unfold owlSubRowD
  rw [Option.isSome_map]
  exact (owlSHIQDKBConsistent_isSome_iff _ hint).2
    ⟨by rw [isSHIQDKB_addAxs, h, List.all_eq_true.2 (subAxs_ok O A B)]; rfl, hs⟩

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.sat_upd
#print axioms ContextCalculus.OWLFrontend.model_addAxs
#print axioms ContextCalculus.OWLFrontend.owlTypeRowD_sound
#print axioms ContextCalculus.OWLFrontend.owlSameRowD_sound
#print axioms ContextCalculus.OWLFrontend.owlSubRowD_sound
#print axioms ContextCalculus.OWLFrontend.owlTypeRowD_complete
#print axioms ContextCalculus.OWLFrontend.owlSameRowD_complete
#print axioms ContextCalculus.OWLFrontend.owlSubRowD_complete
