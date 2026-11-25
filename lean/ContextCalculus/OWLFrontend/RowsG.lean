import ContextCalculus.OWLFrontend.SROIQAnon

/-!
# Rows from any sound consistency procedure (stage C3e)

The six rows of `SROIQDC2aReference.lean` (type, same, subsumption,
different, role, negative role) are the negated consistency of the ontology
with added axioms. `rowG P O L` asks a consistency procedure `P` about
`O` with the axioms `L`; for every `P` whose answers are consistency
(`ConsSound P`), each row answers its entailment. No fragment condition is
needed besides the absence of `HasKey` (checked by `rowG`), since the
lemmas below hold for every axiom:

* `sat_updI_noKey`: satisfaction ignores an individual the axiom does not
  mention;
* `model_addAxs_noKey`: a model of `O` with `L` is a model of `O` that
  satisfies `L`.
-/

namespace ContextCalculus.OWL

variable {DM : DatatypeMap} {D : Type}

/-- Satisfaction of an axiom other than `HasKey` does not read the list of
named individuals. -/
theorem sat_N_noKey (I : Interp DM D) {ax : Axiom} (h : ax.noKey = true) (N N' : List IRI) :
    I.sat N ax ↔ I.sat N' ax := by
  cases ax <;> first | exact Iff.rfl | simp [Axiom.noKey] at h

end ContextCalculus.OWL

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ

variable {DM : DatatypeMap} {D : Type}

/-- **Satisfaction ignores the individuals an axiom does not mention**, for
every axiom other than `HasKey`. -/
theorem sat_updI_noKey {I : Interp DM D} {f : IRI} {x : D} {ax : Axiom} (hk : ax.noKey = true)
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
  case disjointUnion b cs =>
    have ih : ∀ c ∈ cs, (updI I f x).ext c = I.ext c := fun c hc =>
      he c fun a ha => by simp only [Axiom.namedIndividuals, List.mem_flatMap]; exact ⟨c, hc, ha⟩
    simp only [Interp.sat]
    refine and_congr (forall_congr' fun y => ?_) ⟨fun h => h.imp_of_mem fun hc hd h' x' =>
      (ih _ hc) ▸ (ih _ hd) ▸ h' x', fun h => h.imp_of_mem fun hc hd h' x' =>
      (ih _ hc).symm ▸ (ih _ hd).symm ▸ h' x'⟩
    refine iff_congr Iff.rfl ⟨fun ⟨c, hc, hy⟩ => ⟨c, hc, ih c hc ▸ hy⟩,
      fun ⟨c, hc, hy⟩ => ⟨c, hc, (ih c hc).symm ▸ hy⟩⟩
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
  case hasKey c rs ps => simp [Axiom.noKey] at hk
  case subObjectPropertyOf rs r =>
    have hrole : (updI I f x).role = I.role := rfl
    simp only [Interp.sat, Interp.chain_congr hrole, Interp.prop_congr hrole]
  all_goals exact Iff.rfl

theorem model_upd_noKey {O : Ontology} (hO : O.noKey = true) {I : Interp DM D} {f : IRI}
    (hf : f ∉ O.namedIndividuals) (x : D) : OWL.Model O (updI I f x) ↔ OWL.Model O I := by
  have hO' : ∀ a ∈ O.axioms, a.noKey = true := by
    simpa [Ontology.noKey, List.all_eq_true] using hO
  have hfa : ∀ a ∈ O.axioms, f ∉ a.namedIndividuals := fun a ha hm =>
    hf (List.mem_flatMap.2 ⟨a, ha, hm⟩)
  simp only [OWL.Model]
  exact forall_congr' fun a => imp_congr_right fun ha => sat_updI_noKey (hO' a ha) (hfa a ha) _

theorem noKey_addAxs {O : Ontology} {L : List Axiom} :
    (addAxs O L).noKey = (O.noKey && L.all Axiom.noKey) := by
  simp [addAxs, Ontology.noKey, List.all_append]

theorem model_addAxs_noKey {O : Ontology} {L : List Axiom} (hO : O.noKey = true)
    (hL : ∀ ax ∈ L, ax.noKey = true) (I : Interp DM D) :
    OWL.Model (addAxs O L) I ↔ OWL.Model O I ∧ ∀ ax ∈ L, I.sat [] ax := by
  have hO' : ∀ a ∈ O.axioms, a.noKey = true := by
    simpa [Ontology.noKey, List.all_eq_true] using hO
  simp only [OWL.Model, addAxs, List.mem_append]
  constructor
  · intro h
    exact ⟨fun a ha => (sat_N_noKey I (hO' a ha) _ _).1 (h a (Or.inl ha)),
      fun a ha => (sat_N_noKey I (hL a ha) _ _).1 (h a (Or.inr ha))⟩
  · rintro ⟨h1, h2⟩ a (ha | ha)
    · exact (sat_N_noKey I (hO' a ha) _ _).1 (h1 a ha)
    · exact (sat_N_noKey I (hL a ha) _ _).1 (h2 a ha)

/-! ## Rows -/

/-- A consistency procedure whose every answer is consistency. -/
def ConsSound (P : Ontology → Option RawHint → Option Bool) : Prop :=
  ∀ (pat : String → String → Prop) (O : Ontology) (hint : Option RawHint) (v : Bool),
    P O hint = some v → (v = true ↔ ConsistentAt (owl2MapP pat) O)

/-- A row: the negated answer of `P` on the extension. -/
def rowG (P : Ontology → Option RawHint → Option Bool) (O : Ontology) (L : List Axiom)
    (hint : Option RawHint) : Option Bool :=
  if (addAxs O L).noKey then (P (addAxs O L) hint).map (!·) else none

variable {P : Ontology → Option RawHint → Option Bool}

theorem rowG_of (hP : ConsSound P) {O : Ontology} {L : List Axiom} {hint : Option RawHint}
    {v : Bool} (pat : String → String → Prop) (h : rowG P O L hint = some v) :
    O.noKey = true ∧ (∀ ax ∈ L, ax.noKey = true) ∧
      (v = true ↔ ¬ ConsistentAt (owl2MapP pat) (addAxs O L)) := by
  unfold rowG at h
  split_ifs at h with hk
  rw [noKey_addAxs, Bool.and_eq_true, List.all_eq_true] at hk
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h
  refine ⟨hk.1, hk.2, ?_⟩
  rw [← hP pat _ _ _ hw]
  cases w <;> simp

/-- **Type row**: decides `O ⊨ ClassAssertion(C a)`. -/
def rowGType (P : Ontology → Option RawHint → Option Bool) (O : Ontology) (C a : IRI)
    (hint : Option RawHint) : Option Bool :=
  rowG P O (typeAxs C a) hint

def rowGSame (P : Ontology → Option RawHint → Option Bool) (O : Ontology) (a b : IRI)
    (hint : Option RawHint) : Option Bool :=
  rowG P O (sameAxs a b) hint

def rowGSub (P : Ontology → Option RawHint → Option Bool) (O : Ontology) (A B : IRI)
    (hint : Option RawHint) : Option Bool :=
  rowG P O (subAxs O A B) hint

def rowGDiff (P : Ontology → Option RawHint → Option Bool) (O : Ontology) (a b : IRI)
    (hint : Option RawHint) : Option Bool :=
  rowG P O (diffAxs a b) hint

def rowGRole (P : Ontology → Option RawHint → Option Bool) (O : Ontology) (r : ObjProp)
    (a b : IRI) (hint : Option RawHint) : Option Bool :=
  rowG P O (roleAxs r a b) hint

def rowGNRole (P : Ontology → Option RawHint → Option Bool) (O : Ontology) (r : ObjProp)
    (a b : IRI) (hint : Option RawHint) : Option Bool :=
  rowG P O (nroleAxs r a b) hint

theorem rowGType_sound (hP : ConsSound P) (pat : String → String → Prop) {O : Ontology}
    {C a : IRI} {hint : Option RawHint} {v : Bool} (h : rowGType P O C a hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.classAssertion (.cls C) (.named a)) := by
  obtain ⟨hO, hL, hv⟩ := rowG_of hP pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI
    by_contra hc
    refine hi Dom I ((model_addAxs_noKey hO hL I).2 ⟨hI, ?_⟩)
    simpa [typeAxs, Interp.sat, Interp.ext] using hc
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxs_noKey hO hL I).1 hI
    have := he Dom I hI
    simp only [typeAxs, List.mem_singleton, forall_eq, Interp.sat, Interp.ext] at hs this
    exact hs this

theorem rowGSame_sound (hP : ConsSound P) (pat : String → String → Prop) {O : Ontology}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : rowGSame P O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.sameIndividual [.named a, .named b]) := by
  obtain ⟨hO, hL, hv⟩ := rowG_of hP pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI
    rw [sat_same]
    by_contra hc
    refine hi Dom I ((model_addAxs_noKey hO hL I).2 ⟨hI, ?_⟩)
    simp only [sameAxs, List.mem_singleton, forall_eq]
    exact (sat_diff I _ a b).2 hc
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxs_noKey hO hL I).1 hI
    have := (sat_same I _ a b).1 (he Dom I hI)
    simp only [sameAxs, List.mem_singleton, forall_eq] at hs
    exact (sat_diff I _ a b).1 hs this

theorem rowGSub_sound (hP : ConsSound P) (pat : String → String → Prop) {O : Ontology}
    {A B : IRI} {hint : Option RawHint} {v : Bool} (h : rowGSub P O A B hint = some v) :
    v = true ↔ EntailsSubAt (owl2MapP pat) O A B := by
  obtain ⟨hO, hL, hv⟩ := rowG_of hP pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI x hA
    by_contra hB
    have hU := (model_upd_noKey hO (freshInd_not_mem O) x).2 hI
    refine hi Dom (updI I (freshInd O) x) ((model_addAxs_noKey hO hL _).2 ⟨hU, ?_⟩)
    simp only [subAxs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Interp.sat, Interp.ext, updI, Function.update_self]
    exact ⟨hA, hB⟩
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxs_noKey hO hL I).1 hI
    simp only [subAxs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Interp.sat, Interp.ext] at hs
    exact hs.2 (he Dom I hI _ hs.1)

theorem rowGDiff_sound (hP : ConsSound P) (pat : String → String → Prop) {O : Ontology}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : rowGDiff P O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.differentIndividuals [.named a, .named b]) := by
  obtain ⟨hO, hL, hv⟩ := rowG_of hP pat h
  rw [hv, consistentAt_iff_not, not_not]
  have hd : ∀ {Dom : Type} (I : Interp (owl2MapP pat) Dom) (N : List IRI),
      I.sat N (.differentIndividuals [.named a, .named b]) ↔ ¬ I.ind (.named a) = I.ind (.named b) := by
    intro Dom I N
    simp [Interp.sat]
  constructor
  · intro hi Dom _ I hI
    rw [hd]
    intro hc
    refine hi Dom I ((model_addAxs_noKey hO hL I).2 ⟨hI, ?_⟩)
    simp only [diffAxs, List.mem_singleton, forall_eq]
    exact (sat_same I _ a b).2 hc
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxs_noKey hO hL I).1 hI
    simp only [diffAxs, List.mem_singleton, forall_eq] at hs
    exact (hd I _).1 (he Dom I hI) ((sat_same I _ a b).1 hs)

theorem rowGRole_sound (hP : ConsSound P) (pat : String → String → Prop) {O : Ontology}
    {r : ObjProp} {a b : IRI} {hint : Option RawHint} {v : Bool}
    (h : rowGRole P O r a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.objectPropertyAssertion r (.named a) (.named b)) := by
  obtain ⟨hO, hL, hv⟩ := rowG_of hP pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI
    by_contra hc
    refine hi Dom I ((model_addAxs_noKey hO hL I).2 ⟨hI, ?_⟩)
    simpa [roleAxs, Interp.sat] using hc
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxs_noKey hO hL I).1 hI
    simp only [roleAxs, List.mem_singleton, forall_eq, Interp.sat] at hs
    exact hs (he Dom I hI)

theorem rowGNRole_sound (hP : ConsSound P) (pat : String → String → Prop) {O : Ontology}
    {r : ObjProp} {a b : IRI} {hint : Option RawHint} {v : Bool}
    (h : rowGNRole P O r a b hint = some v) :
    v = true ↔
      EntailsAt (owl2MapP pat) O (.negativeObjectPropertyAssertion r (.named a) (.named b)) := by
  obtain ⟨hO, hL, hv⟩ := rowG_of hP pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI hc
    exact hi Dom I ((model_addAxs_noKey hO hL I).2 ⟨hI, by simpa [nroleAxs, Interp.sat] using hc⟩)
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxs_noKey hO hL I).1 hI
    simp only [nroleAxs, List.mem_singleton, forall_eq, Interp.sat] at hs
    exact he Dom I hI hs

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.sat_updI_noKey
#print axioms ContextCalculus.OWLFrontend.model_addAxs_noKey
#print axioms ContextCalculus.OWLFrontend.rowGType_sound
#print axioms ContextCalculus.OWLFrontend.rowGSame_sound
#print axioms ContextCalculus.OWLFrontend.rowGSub_sound
#print axioms ContextCalculus.OWLFrontend.rowGDiff_sound
#print axioms ContextCalculus.OWLFrontend.rowGRole_sound
#print axioms ContextCalculus.OWLFrontend.rowGNRole_sound
