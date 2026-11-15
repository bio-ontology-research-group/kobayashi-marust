import ContextCalculus.OWLFrontend.SROIQDSelfRows

/-!
# `DisjointUnion` as syntactic sugar (stage C3c, item 2)

`DisjointUnion(A C₁ … Cₙ)` holds iff `EquivalentClasses(A ObjectUnionOf(C₁ … Cₙ))`
and `DisjointClasses(C₁ … Cₙ)` hold (structural specification 9.1.4).
`duOff` makes this rewriting; it keeps the models (`model_duOff`), so it
keeps consistency and every entailment. `owlC3Consistent` and
`owlC3TypeRow` run the route of `SROIQDSelfRows.lean` on the rewritten
ontology.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes

variable {DM : DatatypeMap} {D : Type}

/-- The rewriting of one axiom. -/
def duAx : Axiom → List Axiom
  | .disjointUnion a cs => [.equivalentClasses [.cls a, .or cs], .disjointClasses cs]
  | ax => [ax]

/-- The ontology with its disjoint unions rewritten. -/
def duOff (O : Ontology) : Ontology := ⟨O.axioms.flatMap duAx⟩

theorem namedIndividuals_or (cs : List ClassExpr) :
    (ClassExpr.or cs).namedIndividuals = cs.flatMap ClassExpr.namedIndividuals := by
  rw [ClassExpr.namedIndividuals]
  conv_rhs => rw [← List.attach_map_subtype_val cs]
  rw [List.flatMap_map]

/-- The rewriting keeps the named individuals, as a set. -/
theorem mem_namedIndividuals_duOff (O : Ontology) (a : IRI) :
    a ∈ (duOff O).namedIndividuals ↔ a ∈ O.namedIndividuals := by
  simp only [Ontology.namedIndividuals, duOff, List.mem_flatMap]
  constructor
  · rintro ⟨ax', ⟨ax, hax, hm⟩, ha⟩
    refine ⟨ax, hax, ?_⟩
    cases ax with
    | disjointUnion b cs =>
      simp only [duAx, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · simp only [Axiom.namedIndividuals, List.flatMap_cons, List.flatMap_nil,
          ClassExpr.namedIndividuals, namedIndividuals_or, List.nil_append, List.append_nil] at ha
        simpa [Axiom.namedIndividuals] using ha
      · simpa [Axiom.namedIndividuals] using ha
    | _ =>
      simp only [duAx, List.mem_singleton] at hm
      subst hm; exact ha
  · rintro ⟨ax, hax, ha⟩
    cases ax with
    | disjointUnion b cs =>
      refine ⟨.disjointClasses cs, ⟨_, hax, by simp [duAx]⟩, ?_⟩
      simpa [Axiom.namedIndividuals] using ha
    | _ => exact ⟨_, ⟨_, hax, by simp [duAx]⟩, ha⟩

/-- Satisfaction depends on the named individuals as a set. -/
theorem sat_congrN (I : Interp DM D) {N N' : List IRI} (h : ∀ a, a ∈ N ↔ a ∈ N') (ax : Axiom) :
    I.sat N ax ↔ I.sat N' ax := by
  have hn : ∀ x, I.IsNamed N x ↔ I.IsNamed N' x := fun x => by
    simp only [Interp.IsNamed, h]
  cases ax with
  | hasKey c rs ps => simp only [Interp.sat, hn]
  | _ => exact Iff.rfl

/-- **`DisjointUnion` is sugar.** -/
theorem sat_disjointUnion (I : Interp DM D) (N : List IRI) (a : IRI) (cs : List ClassExpr) :
    I.sat N (.disjointUnion a cs) ↔
      I.sat N (.equivalentClasses [.cls a, .or cs]) ∧ I.sat N (.disjointClasses cs) := by
  have hc : ∀ x, I.ext (.cls a) x ↔ I.cls a x := fun x => by rw [Interp.ext]
  simp only [Interp.sat, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro h c hc' d hd x hx
    rcases hc' with rfl | rfl <;> rcases hd with rfl | rfl
    · exact hx
    · rw [Interp.ext_or]; exact (h x).1 ((hc x).1 hx)
    · rw [Interp.ext_or] at hx; exact (hc x).2 ((h x).2 hx)
    · exact hx
  · intro h x
    constructor
    · intro hx
      have := h _ (Or.inl rfl) _ (Or.inr rfl) x ((hc x).2 hx)
      rwa [Interp.ext_or] at this
    · intro hx
      exact (hc x).1 (h _ (Or.inr rfl) _ (Or.inl rfl) x (by rw [Interp.ext_or]; exact hx))

/-- **The rewriting keeps the models.** -/
theorem model_duOff (O : Ontology) (I : Interp DM D) : OWL.Model (duOff O) I ↔ OWL.Model O I := by
  have hN := mem_namedIndividuals_duOff O
  constructor
  · intro h ax hax
    cases ax with
    | disjointUnion b cs =>
      rw [sat_disjointUnion]
      refine ⟨(sat_congrN I hN _).1 (h _ ?_), (sat_congrN I hN _).1 (h _ ?_)⟩ <;>
        exact List.mem_flatMap.2 ⟨_, hax, by simp [duAx]⟩
    | _ => exact (sat_congrN I hN _).1 (h _ (List.mem_flatMap.2 ⟨_, hax, by simp [duAx]⟩))
  · intro h ax' hax'
    obtain ⟨ax, hax, hm⟩ := List.mem_flatMap.1 hax'
    have hs := (sat_congrN I hN ax).2 (h ax hax)
    cases ax with
    | disjointUnion b cs =>
      rw [sat_disjointUnion] at hs
      simp only [duAx, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact hs.1
      · exact hs.2
    | _ =>
      simp only [duAx, List.mem_singleton] at hm
      subst hm; exact hs

theorem consistentAt_duOff (O : Ontology) : ConsistentAt DM (duOff O) ↔ ConsistentAt DM O := by
  unfold ConsistentAt
  simp only [model_duOff]

theorem entailsAt_duOff (O : Ontology) (α : Axiom) : EntailsAt DM (duOff O) α ↔ EntailsAt DM O α := by
  unfold EntailsAt
  simp only [model_duOff]

theorem entailsSubAt_duOff (O : Ontology) (A B : IRI) :
    EntailsSubAt DM (duOff O) A B ↔ EntailsSubAt DM O A B := by
  unfold EntailsSubAt
  simp only [model_duOff]

/-! ## The route of stage C3 -/

/-- **Consistency** (stage C3c): the route of `owlSROIQDSConsistent` on the
ontology with its disjoint unions rewritten. -/
def owlC3Consistent (O : Ontology) (hint : Option RawHint) : Option Bool :=
  owlSROIQDSConsistent (duOff O) hint

theorem owlC3Consistent_sound (pat : String → String → Prop) {O : Ontology}
    {hint : Option RawHint} {v : Bool} (h : owlC3Consistent O hint = some v) :
    v = true ↔ ConsistentAt (owl2MapP pat) O := by
  rw [owlSROIQDSConsistent_sound pat h, consistentAt_duOff]

theorem owlC3Consistent_isSome_iff (O : Ontology) (hint : Option RawHint) :
    (owlC3Consistent O hint).isSome = true ↔
      ((anonOff [] (duOff O)).isSROIQDKB = true ∧ SROIQDC2aChecks (anonOff [] (duOff O))) ∨
        (((anonOff [] (duOff O)).isSROIQDSKB && !(selfAxs (anonOff [] (duOff O))).isEmpty) = true ∧
          SelfChecks (anonOff [] (duOff O))) :=
  owlSROIQDSConsistent_isSome_iff _ hint

/-- **Type row** (stage C3c). -/
def owlC3TypeRow (O : Ontology) (C a : IRI) (hint : Option RawHint) : Option Bool :=
  owlSROIQDSTypeRow (duOff O) C a hint

theorem owlC3TypeRow_sound (pat : String → String → Prop) {O : Ontology} {C a : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlC3TypeRow O C a hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.classAssertion (.cls C) (.named a)) := by
  rw [owlSROIQDSTypeRow_sound pat h, entailsAt_duOff]

/-- **Same, subsumption, different, role and negative role rows**. -/
def owlC3SameRow (O : Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  owlSROIQDSSameRow (duOff O) a b hint

def owlC3SubRow (O : Ontology) (A B : IRI) (hint : Option RawHint) : Option Bool :=
  owlSROIQDSSubRow (duOff O) A B hint

def owlC3DiffRow (O : Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  owlSROIQDSDiffRow (duOff O) a b hint

def owlC3RoleRow (O : Ontology) (r : ObjProp) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  owlSROIQDSRoleRow (duOff O) r a b hint

def owlC3NRoleRow (O : Ontology) (r : ObjProp) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  owlSROIQDSNRoleRow (duOff O) r a b hint

theorem owlC3SameRow_sound (pat : String → String → Prop) {O : Ontology} {a b : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlC3SameRow O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.sameIndividual [.named a, .named b]) := by
  rw [owlSROIQDSSameRow_sound pat h, entailsAt_duOff]

theorem owlC3SubRow_sound (pat : String → String → Prop) {O : Ontology} {A B : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlC3SubRow O A B hint = some v) :
    v = true ↔ EntailsSubAt (owl2MapP pat) O A B := by
  rw [owlSROIQDSSubRow_sound pat h, entailsSubAt_duOff]

theorem owlC3DiffRow_sound (pat : String → String → Prop) {O : Ontology} {a b : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlC3DiffRow O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.differentIndividuals [.named a, .named b]) := by
  rw [owlSROIQDSDiffRow_sound pat h, entailsAt_duOff]

theorem owlC3RoleRow_sound (pat : String → String → Prop) {O : Ontology} {r : ObjProp}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : owlC3RoleRow O r a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.objectPropertyAssertion r (.named a) (.named b)) := by
  rw [owlSROIQDSRoleRow_sound pat h, entailsAt_duOff]

theorem owlC3NRoleRow_sound (pat : String → String → Prop) {O : Ontology} {r : ObjProp}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : owlC3NRoleRow O r a b hint = some v) :
    v = true ↔
      EntailsAt (owl2MapP pat) O (.negativeObjectPropertyAssertion r (.named a) (.named b)) := by
  rw [owlSROIQDSNRoleRow_sound pat h, entailsAt_duOff]

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.model_duOff
#print axioms ContextCalculus.OWLFrontend.owlC3Consistent_sound
#print axioms ContextCalculus.OWLFrontend.owlC3Consistent_isSome_iff
#print axioms ContextCalculus.OWLFrontend.owlC3TypeRow_sound
#print axioms ContextCalculus.OWLFrontend.owlC3SameRow_sound
#print axioms ContextCalculus.OWLFrontend.owlC3SubRow_sound
#print axioms ContextCalculus.OWLFrontend.owlC3DiffRow_sound
#print axioms ContextCalculus.OWLFrontend.owlC3RoleRow_sound
#print axioms ContextCalculus.OWLFrontend.owlC3NRoleRow_sound
