/-! Role disjointness in the native completion bridge.

The bridge represents `AsymmetricObjectProperty(R)` as Konclude does
(`CConcreteOntologyUpdateBuilder`, BETASYMMETRICPROPERTY): the role is made
disjoint from its own inverse, `Dis(R, R⁻)`, and the completion graph keeps
negation (disjoint-role) edges next to its positive role links.
`IrreflexiveObjectProperty(R)` is the global GCI `⊤ ⊑ ¬∃R.Self`
(BETIRREFLEXIVEPROPERTY). This file proves the semantic facts the Rust port
relies on:

* the two encodings have exactly the models of the source axioms
  (`asymmetric_iff_disjoint_inverse`, `irreflexive_iff_global_not_self`),
  and asymmetry implies irreflexivity (`asymmetric_irreflexive`);
* an irreflexivity axiom may be dropped only for a role that is empty in
  some model, and an unconditional reflexive fact forces the role nonempty
  (`irreflexive_of_empty`, `reflexive_role_nonempty`);
* with negation edges stored in both orientations, a positive fact stored
  at either endpoint is found by a lookup at one endpoint
  (`mirrored_negation_detects_either_orientation`);
* the merge test: identifying `i₁` with `i₂` creates a clash in a
  clash-free graph only through a negation edge incident to `i₁` or `i₂`,
  and every reported conflict is a clash of the merged graph
  (`merge_conflict_incident`, `reported_conflict_is_merged_clash`).

The completion engine's data structures (hashes, dependency tracking) are
not modelled; these lemmas fix the conditions its checks must test. -/
namespace ContextCalculus.RoleDisjointnessNormalization

universe u v

/-- Asymmetry is disjointness of `R` and its inverse. -/
theorem asymmetric_iff_disjoint_inverse {D : Type u} (R : D → D → Prop) :
    (∀ x y, R x y → ¬ R y x) ↔ (∀ x y, R x y → (fun a b => R b a) x y → False) :=
  Iff.rfl

/-- Asymmetry excludes self loops. -/
theorem asymmetric_irreflexive {D : Type u} (R : D → D → Prop)
    (asym : ∀ x y, R x y → ¬ R y x) : ∀ x, ¬ R x x :=
  fun x h => asym x x h h

/-- Irreflexivity is the global restriction `⊤ ⊑ ¬∃R.Self`. -/
theorem irreflexive_iff_global_not_self {D : Type u} (R : D → D → Prop) :
    (∀ x, ¬ R x x) ↔ (∀ x, True → ¬ R x x) :=
  ⟨fun h x _ => h x, fun h x => h x True.intro⟩

/-- An empty role satisfies irreflexivity. -/
theorem irreflexive_of_empty {D : Type u} (R : D → D → Prop)
    (empty : ∀ x y, ¬ R x y) : ∀ x, ¬ R x x :=
  fun x => empty x x

/-- A reflexivity fact makes the role nonempty in every (nonempty) model. -/
theorem reflexive_role_nonempty {D : Type u} (R : D → D → Prop)
    (refl : ∀ x, R x x) (d : D) : ∃ x y, R x y :=
  ⟨d, d, refl d⟩

section Graph

variable {V : Type u} {Rl : Type v}

/-- A positive fact `role(a,b)`, stored at `a` or at `b` under the inverse. -/
def Holds (pos : V → V → Rl → Prop) (inv : Rl → Rl) (a b : V) (role : Rl) : Prop :=
  pos a b role ∨ pos b a (inv role)

/-- Negation edges are stored in both orientations. -/
def Mirrored (neg : V → V → Rl → Prop) (inv : Rl → Rl) : Prop :=
  ∀ a b role, neg a b role → neg b a (inv role)

theorem mirrored_negation_detects_either_orientation
    (pos neg : V → V → Rl → Prop) (inv : Rl → Rl) (mirror : Mirrored neg inv)
    (a b : V) (role : Rl) (hn : neg a b role) (hp : Holds pos inv a b role) :
    (neg a b role ∧ pos a b role) ∨ (neg b a (inv role) ∧ pos b a (inv role)) := by
  rcases hp with h | h
  · exact Or.inl ⟨hn, h⟩
  · exact Or.inr ⟨mirror a b role hn, h⟩

/-- Identification of `i₁` with `i₂`. -/
def mergeMap [DecidableEq V] (i₁ i₂ : V) (x : V) : V :=
  if x = i₁ then i₂ else x

/-- A clash of the merged graph: a negation edge and a positive fact whose
endpoints have the same images. -/
def MergedClash [DecidableEq V] (pos neg : V → V → Rl → Prop) (inv : Rl → Rl)
    (i₁ i₂ : V) : Prop :=
  ∃ a b a' b' role, neg a b role ∧ Holds pos inv a' b' role ∧
    mergeMap i₁ i₂ a = mergeMap i₁ i₂ a' ∧ mergeMap i₁ i₂ b = mergeMap i₁ i₂ b'

/-- The graph before the merge has no clash. -/
def ClashFree (pos neg : V → V → Rl → Prop) (inv : Rl → Rl) : Prop :=
  ∀ a b role, neg a b role → ¬ Holds pos inv a b role

theorem mergeMap_fixed [DecidableEq V] (i₁ i₂ x : V) (hx : x ≠ i₁) :
    mergeMap i₁ i₂ x = x := by
  unfold mergeMap
  exact if_neg hx

theorem mergeMap_merged [DecidableEq V] (i₁ i₂ x : V) (hx : x = i₁) :
    mergeMap i₁ i₂ x = i₂ := by
  unfold mergeMap
  exact if_pos hx

/-- In a clash-free graph, a clash created by identifying `i₁` with `i₂`
uses a negation edge incident to `i₁` or `i₂`, and a positive fact between
preimages of its mapped endpoints. Scanning the negation edges stored at
`i₁` and `i₂` (all of them, by mirroring) therefore finds every clash. -/
theorem merge_conflict_incident [DecidableEq V]
    (pos neg : V → V → Rl → Prop) (inv : Rl → Rl) (i₁ i₂ : V)
    (free : ClashFree pos neg inv) (clash : MergedClash pos neg inv i₁ i₂) :
    ∃ a b a' b' role, neg a b role ∧ Holds pos inv a' b' role ∧
      (a = i₁ ∨ a = i₂ ∨ b = i₁ ∨ b = i₂) ∧
      mergeMap i₁ i₂ a = mergeMap i₁ i₂ a' ∧ mergeMap i₁ i₂ b = mergeMap i₁ i₂ b' := by
  obtain ⟨a, b, a', b', role, hn, hp, ha, hb⟩ := clash
  refine ⟨a, b, a', b', role, hn, hp, ?_, ha, hb⟩
  by_cases h₁ : a = i₁
  · exact Or.inl h₁
  by_cases h₂ : a = i₂
  · exact Or.inr (Or.inl h₂)
  by_cases h₃ : b = i₁
  · exact Or.inr (Or.inr (Or.inl h₃))
  by_cases h₄ : b = i₂
  · exact Or.inr (Or.inr (Or.inr h₄))
  exfalso
  have fa : mergeMap i₁ i₂ a = a := mergeMap_fixed i₁ i₂ a h₁
  have fb : mergeMap i₁ i₂ b = b := mergeMap_fixed i₁ i₂ b h₃
  -- `a'` is not `i₁`: its image would be `i₂ = a`.
  have ha' : a' ≠ i₁ := by
    intro e
    have := mergeMap_merged i₁ i₂ a' e
    exact h₂ (fa ▸ ha.trans this)
  have hb' : b' ≠ i₁ := by
    intro e
    have := mergeMap_merged i₁ i₂ b' e
    exact h₄ (fb ▸ hb.trans this)
  have ea : a = a' := by
    have := ha; rw [fa, mergeMap_fixed i₁ i₂ a' ha'] at this; exact this
  have eb : b = b' := by
    have := hb; rw [fb, mergeMap_fixed i₁ i₂ b' hb'] at this; exact this
  subst ea; subst eb
  exact free a b role hn hp

/-- Soundness of a reported conflict: a negation edge and a positive fact
between preimages of the same mapped endpoints is a clash of the merged
graph, so declaring the pair unmergeable never discards a model. -/
theorem reported_conflict_is_merged_clash [DecidableEq V]
    (pos neg : V → V → Rl → Prop) (inv : Rl → Rl) (i₁ i₂ : V)
    (a b a' b' : V) (role : Rl) (hn : neg a b role) (hp : Holds pos inv a' b' role)
    (ha : mergeMap i₁ i₂ a = mergeMap i₁ i₂ a') (hb : mergeMap i₁ i₂ b = mergeMap i₁ i₂ b') :
    MergedClash pos neg inv i₁ i₂ :=
  ⟨a, b, a', b', role, hn, hp, ha, hb⟩

end Graph

/-! Thing-typed ABox elision (`frontend::profile::top_identity_abox_tbox_separable`).

An ABox made only of `ClassAssertion(owl:Thing a)` and `SameIndividual`
axioms, over a TBox in which no individual name occurs, constrains only the
interpretation of its own names. Every model of the TBox expands to a model
of the whole ontology by sending every name to one domain element, so the
two have the same class-level consequences. -/
section TopIdentityABox

variable {Ind : Type u}

/-- Every list of identity axioms is satisfied by a constant naming map. -/
theorem constant_names_satisfy_identities {D : Type v} (d : D)
    (same : List (Ind × Ind)) :
    ∀ p ∈ same, (fun _ : Ind => d) p.1 = (fun _ : Ind => d) p.2 :=
  fun _ _ => rfl

/-- The whole ontology entails a statement about the TBox signature exactly
when the TBox does. `Model I` is a model of the TBox over the structure `I`,
`Domain I` its (nonempty) domain, and `φ` any property of `I` alone. -/
theorem top_identity_abox_entailment_iff {S : Type (max u v)}
    (Domain : S → Type v) (Model : S → Prop) (element : ∀ I, Domain I)
    (same : List (Ind × Ind)) (φ : S → Prop) :
    (∀ I, Model I → ∀ names : Ind → Domain I,
        (∀ p ∈ same, names p.1 = names p.2) → φ I) ↔
      (∀ I, Model I → φ I) := by
  constructor
  · intro h I hI
    exact h I hI (fun _ => element I) (fun _ _ => rfl)
  · intro h I hI _ _
    exact h I hI

/-- Consistency is preserved in both directions. -/
theorem top_identity_abox_consistent_iff {S : Type (max u v)}
    (Domain : S → Type v) (Model : S → Prop) (element : ∀ I, Domain I)
    (same : List (Ind × Ind)) :
    (∃ I, Model I ∧ ∃ names : Ind → Domain I, ∀ p ∈ same, names p.1 = names p.2) ↔
      (∃ I, Model I) := by
  constructor
  · rintro ⟨I, hI, _⟩
    exact ⟨I, hI⟩
  · rintro ⟨I, hI⟩
    exact ⟨I, hI, fun _ => element I, fun _ _ => rfl⟩

end TopIdentityABox

end ContextCalculus.RoleDisjointnessNormalization

#print axioms ContextCalculus.RoleDisjointnessNormalization.asymmetric_iff_disjoint_inverse
#print axioms ContextCalculus.RoleDisjointnessNormalization.asymmetric_irreflexive
#print axioms ContextCalculus.RoleDisjointnessNormalization.irreflexive_iff_global_not_self
#print axioms ContextCalculus.RoleDisjointnessNormalization.irreflexive_of_empty
#print axioms ContextCalculus.RoleDisjointnessNormalization.reflexive_role_nonempty
#print axioms ContextCalculus.RoleDisjointnessNormalization.mirrored_negation_detects_either_orientation
#print axioms ContextCalculus.RoleDisjointnessNormalization.merge_conflict_incident
#print axioms ContextCalculus.RoleDisjointnessNormalization.reported_conflict_is_merged_clash
#print axioms ContextCalculus.RoleDisjointnessNormalization.top_identity_abox_entailment_iff
#print axioms ContextCalculus.RoleDisjointnessNormalization.top_identity_abox_consistent_iff
