import ContextCalculus.ELCompletionRefinement
import Mathlib.Data.Fintype.Pi

/-!
# Canonical-model certificates for an ELC ontology with residual axioms

The plain Rust `CertMode::Check` route first computes the exact ELC closure and
then checks every non-EL residual clause in that closure's canonical model.
This file proves the semantic composition principle behind that route. The
residual theory is deliberately abstract here; the executable wire layer must
separately prove that its finite residual-clause check establishes `holds`.
-/

namespace ContextCalculus.ELCompletion

variable {Concept Role : Type} {top bottom : Concept}

/-- A theory over the same concept and role interpretation as the ELC core. -/
structure ResidualTheory (Concept Role : Type) (top bottom : Concept) where
  holds : {Domain : Type} → Interp Domain Concept Role top bottom → Prop

/-- The exact atom language produced by Rust's `compile_residual`. -/
inductive CompiledResidualAtom (Concept Role Var : Type) where
  | concept (concept : Concept) (varId : Var)
  | role (role : Role) (source target : Var)
  | eq (left right : Var)
deriving DecidableEq

/--
A compiled residual clause. Pins interpret Skolem-function occurrences as
fixed canonical witness nodes. Ordinary variables remain universally
quantified; an assignment is relevant only when it respects every pin.
-/
structure CompiledResidualClause (Domain Concept Role Var : Type) where
  body : List (CompiledResidualAtom Concept Role Var)
  head : List (CompiledResidualAtom Concept Role Var)
  pins : List (Var × Domain)
deriving DecidableEq

def satCompiledResidualAtom {Domain Var : Type}
    (I : Interp Domain Concept Role top bottom) (assignment : Var → Domain) :
    CompiledResidualAtom Concept Role Var → Prop
  | .concept concept varId => I.concept concept (assignment varId)
  | .role role source target => I.role role (assignment source) (assignment target)
  | .eq left right => assignment left = assignment right

def satCompiledResidualClause {Domain Var : Type}
    (I : Interp Domain Concept Role top bottom)
    (clause : CompiledResidualClause Domain Concept Role Var) : Prop :=
  ∀ assignment : Var → Domain,
    (∀ pin ∈ clause.pins, assignment pin.1 = pin.2) →
    (∀ atom ∈ clause.body, satCompiledResidualAtom I assignment atom) →
    ∃ atom ∈ clause.head, satCompiledResidualAtom I assignment atom

def modelsCompiledResidual {Domain Var : Type}
    (I : Interp Domain Concept Role top bottom)
    (residual : List (CompiledResidualClause Domain Concept Role Var)) : Prop :=
  ∀ clause ∈ residual, satCompiledResidualClause I clause

/-! ## Independent finite checker used by the certificate wire -/

structure FiniteResidualModel (Domain Concept Role : Type) where
  concept : Concept → Domain → Bool
  role : Role → Domain → Domain → Bool

def FiniteResidualModel.toInterp
    (model : FiniteResidualModel Domain Concept Role) (top bottom : Concept)
    (top_true : ∀ x, model.concept top x = true)
    (bottom_false : ∀ x, model.concept bottom x = false) :
    Interp Domain Concept Role top bottom where
  concept := fun concept x => model.concept concept x = true
  role := fun role x y => model.role role x y = true
  top_true := top_true
  bottom_false := by
    intro x hbottom
    rw [bottom_false x] at hbottom
    contradiction

def evalCompiledResidualAtom [DecidableEq Domain]
    (model : FiniteResidualModel Domain Concept Role) (assignment : Var → Domain) :
    CompiledResidualAtom Concept Role Var → Bool
  | .concept concept varId => model.concept concept (assignment varId)
  | .role role source target => model.role role (assignment source) (assignment target)
  | .eq left right => decide (assignment left = assignment right)

theorem evalCompiledResidualAtom_eq_true
    [DecidableEq Domain]
    (model : FiniteResidualModel Domain Concept Role)
    (top bottom : Concept)
    (htop : ∀ x, model.concept top x = true)
    (hbottom : ∀ x, model.concept bottom x = false)
    (assignment : Var → Domain) (atom : CompiledResidualAtom Concept Role Var) :
    evalCompiledResidualAtom model assignment atom = true ↔
      satCompiledResidualAtom (model.toInterp top bottom htop hbottom) assignment atom := by
  cases atom <;> simp [evalCompiledResidualAtom, satCompiledResidualAtom,
    FiniteResidualModel.toInterp]

def checkCompiledResidualClause [Fintype Domain] [DecidableEq Domain]
    [Fintype Var] [DecidableEq Var]
    (model : FiniteResidualModel Domain Concept Role)
    (top bottom : Concept)
    (htop : ∀ x, model.concept top x = true)
    (hbottom : ∀ x, model.concept bottom x = false)
    (clause : CompiledResidualClause Domain Concept Role Var) : Bool :=
  let I := model.toInterp top bottom htop hbottom
  letI (assignment : Var → Domain) (atom : CompiledResidualAtom Concept Role Var) :
      Decidable (satCompiledResidualAtom I assignment atom) := by
    cases atom with
    | concept concept varId =>
        change Decidable (model.concept concept (assignment varId) = true)
        exact inferInstance
    | role role source target =>
        change Decidable (model.role role (assignment source) (assignment target) = true)
        exact inferInstance
    | eq left right =>
        change Decidable (assignment left = assignment right)
        exact inferInstance
  letI : Decidable (satCompiledResidualClause I clause) := by
    unfold satCompiledResidualClause
    infer_instance
  decide (satCompiledResidualClause I clause)

theorem checkCompiledResidualClause_eq_true
    [Fintype Domain] [DecidableEq Domain] [Fintype Var] [DecidableEq Var]
    (model : FiniteResidualModel Domain Concept Role)
    (top bottom : Concept)
    (htop : ∀ x, model.concept top x = true)
    (hbottom : ∀ x, model.concept bottom x = false)
    (clause : CompiledResidualClause Domain Concept Role Var) :
    checkCompiledResidualClause model top bottom htop hbottom clause = true ↔
      satCompiledResidualClause (model.toInterp top bottom htop hbottom) clause := by
  simp [checkCompiledResidualClause]

namespace ResidualExamples

def model : FiniteResidualModel (Fin 2) (Fin 2) (Fin 1) where
  concept := fun concept _ => concept = 0
  role := fun _ _ _ => false

theorem model_top (x : Fin 2) : model.concept 0 x = true := by simp [model]
theorem model_bottom (x : Fin 2) : model.concept 1 x = false := by simp [model]

def tautology : CompiledResidualClause (Fin 2) (Fin 2) (Fin 1) (Fin 1) where
  body := [.concept 0 0]
  head := [.concept 0 0]
  pins := []

example : checkCompiledResidualClause model 0 1 model_top model_bottom tautology = true := by
  native_decide

end ResidualExamples

/-! ## Canonical model restricted to Rust's concept signature -/

def Clause.mentionsConcept (concept : Concept) : Clause Concept Role → Prop
  | .nf1 sub sup => concept = sub ∨ concept = sup
  | .nf2 left right sup => concept = left ∨ concept = right ∨ concept = sup
  | .nf3 sub _ filler => concept = sub ∨ concept = filler
  | .nf4 _ filler sup => concept = filler ∨ concept = sup
  | .nf5 sub => concept = sub
  | .nf6 _ _ | .nf7 _ _ _ | .reflexive _ => False

structure SignatureClosed (active : Concept → Prop) (top : Concept)
    (O : Ontology Concept Role) : Prop where
  top_active : active top
  clause_active : ∀ clause ∈ O, ∀ concept,
    clause.mentionsConcept concept → active concept

abbrev ActiveAlive (active : Concept → Prop) (top bottom : Concept)
    (O : Ontology Concept Role) :=
  {a : Concept // active a ∧ ¬Sub top bottom O a bottom}

def canonOn (active : Concept → Prop) {top bottom : Concept}
    {O : Ontology Concept Role} :
    Interp (ActiveAlive active top bottom O) Concept Role top bottom where
  concept := fun concept x => Sub top bottom O x.1 concept
  role := fun role x y => Edge top bottom O x.1 role y.1
  top_true := fun x => Sub.top x.1
  bottom_false := fun x => x.2.2

theorem canonOn_models {active : Concept → Prop} {top bottom : Concept}
    {O : Ontology Concept Role} (hsig : SignatureClosed active top O) :
    models (canonOn active (top := top) (bottom := bottom) (O := O)) O := by
  intro clause hcl
  cases clause with
  | nf1 sub sup =>
      intro x hx
      exact Sub.nf1 hx hcl
  | nf2 left right sup =>
      intro x hl hr
      exact Sub.nf2 hl hr hcl
  | nf3 sub role filler =>
      intro x hx
      have hedge : Edge top bottom O x.1 role filler := Edge.nf3 hx hcl
      have alive : ¬Sub top bottom O filler bottom := by
        intro hbottom
        exact x.2.2 (Sub.bottomEdge hedge hbottom)
      have activeFiller : active filler :=
        hsig.clause_active (.nf3 sub role filler) hcl filler (Or.inr rfl)
      exact ⟨⟨filler, activeFiller, alive⟩, hedge, Sub.refl filler⟩
  | nf4 role filler sup =>
      intro x hex
      rcases hex with ⟨target, hedge, hfiller⟩
      exact Sub.nf4 hedge hfiller hcl
  | nf5 sub =>
      intro x hx
      exact x.2.2 (Sub.nf5 hx hcl)
  | nf6 sub sup =>
      intro x y hedge
      exact Edge.nf6 hedge hcl
  | nf7 first second sup =>
      intro x y z hxy hyz
      exact Edge.nf7 hxy hyz hcl
  | reflexive role =>
      intro x
      exact Edge.reflexive x.1 hcl

theorem activeAlive_nonempty {active : Concept → Prop} {top bottom : Concept}
    {O : Ontology Concept Role} (hsig : SignatureClosed active top O)
    (h : ¬Sub top bottom O top bottom) :
    Nonempty (ActiveAlive active top bottom O) :=
  ⟨⟨top, hsig.top_active, h⟩⟩

/-! ## Finite canonical model of an executable materialization -/

abbrev MaterializedActiveAlive (active : Concept → Prop)
    (m : Materialization Concept Role) (bottom : Concept) :=
  {a : Concept // active a ∧ ¬m.sub a bottom}

def materializedCanon (active : Concept → Prop)
    (m : Materialization Concept Role) (top bottom : Concept)
    (closed : ClosedState m top bottom O) :
    Interp (MaterializedActiveAlive active m bottom) Concept Role top bottom where
  concept := fun concept x => m.sub x.1 concept
  role := fun role x y => m.edge x.1 role y.1
  top_true := fun x => closed.initTop x.1
  bottom_false := fun x => x.2.2

/-- Closure alone makes the finite, active-and-alive materialization domain a
model of every NF1–NF7 and reflexive axiom. This is the exact finite domain the
native residual checker enumerates. -/
theorem materializedCanon_models
    (active : Concept → Prop) (m : Materialization Concept Role)
    (closed : ClosedState m top bottom O)
    (hsig : SignatureClosed active top O) :
    models (materializedCanon active m top bottom closed) O := by
  intro clause hclause
  cases clause with
  | nf1 sub sup =>
      intro x hsub
      exact closed.closeNf1 hsub hclause
  | nf2 left right sup =>
      intro x hleft hright
      exact closed.closeNf2 hleft hright hclause
  | nf3 sub role filler =>
      intro x hsub
      have hedge : m.edge x.1 role filler := closed.closeNf3 hsub hclause
      have halive : ¬m.sub filler bottom := by
        intro hbottom
        exact x.2.2 (closed.closeBottomEdge hedge hbottom)
      have hactive : active filler :=
        hsig.clause_active (.nf3 sub role filler) hclause filler (Or.inr rfl)
      exact ⟨⟨filler, hactive, halive⟩, hedge, closed.initRefl filler⟩
  | nf4 role filler sup =>
      intro x hexists
      obtain ⟨target, hedge, hfiller⟩ := hexists
      exact closed.closeNf4 hedge hfiller hclause
  | nf5 sub =>
      intro x hsub
      exact x.2.2 (closed.closeNf5 hsub hclause)
  | nf6 sub sup =>
      intro x y hedge
      exact closed.closeNf6 hedge hclause
  | nf7 first second sup =>
      intro x y z hfirst hsecond
      exact closed.closeNf7 hfirst hsecond hclause
  | reflexive role =>
      intro x
      exact closed.closeReflexive x.1 hclause

theorem materializedActiveAlive_nonempty
    (active : Concept → Prop) (m : Materialization Concept Role)
    (hsig : SignatureClosed active top O)
    (halive : ¬m.sub top bottom) :
    Nonempty (MaterializedActiveAlive active m bottom) :=
  ⟨⟨top, hsig.top_active, halive⟩⟩

def modelsWithResidual {Domain : Type} (O : Ontology Concept Role)
    (R : ResidualTheory Concept Role top bottom)
    (I : Interp Domain Concept Role top bottom) : Prop :=
  models I O ∧ R.holds I

def EntailsSubWithResidual (O : Ontology Concept Role)
    (R : ResidualTheory Concept Role top bottom) (sub sup : Concept) : Prop :=
  ∀ {Domain : Type} (I : Interp Domain Concept Role top bottom),
    modelsWithResidual O R I → ∀ x, I.concept sub x → I.concept sup x

def UnsatisfiableWithResidual (O : Ontology Concept Role)
    (R : ResidualTheory Concept Role top bottom) : Prop :=
  ∀ {Domain : Type} [Nonempty Domain] (I : Interp Domain Concept Role top bottom),
    modelsWithResidual O R I → False

/-- Every ELC derivation remains sound after adding arbitrary residual axioms. -/
theorem sub_sound_withResidual {O : Ontology Concept Role}
    {R : ResidualTheory Concept Role top bottom} {a b : Concept}
    (h : Sub top bottom O a b) :
    EntailsSubWithResidual O R a b := by
  intro Domain I hmodels x hax
  exact sub_sound hmodels.1 h x hax

/-- An ELC-bottom label remains a sound unsatisfiable-class answer. -/
theorem bottom_sound_withResidual {O : Ontology Concept Role}
    {R : ResidualTheory Concept Role top bottom} {a b : Concept}
    (h : Sub top bottom O a bottom) :
    EntailsSubWithResidual O R a b := by
  intro Domain I hmodels x hax
  exact False.elim (I.bottom_false x (sub_sound hmodels.1 h x hax))

/-- ELC inconsistency remains sound for every extension by residual axioms. -/
theorem top_bottom_sound_withResidual {O : Ontology Concept Role}
    {R : ResidualTheory Concept Role top bottom}
    (h : Sub top bottom O top bottom) :
    UnsatisfiableWithResidual O R := by
  intro Domain inhabited I hmodels
  exact inhabited.elim fun x =>
    I.bottom_false x (sub_sound hmodels.1 h x (I.top_true x))

/--
If the ELC canonical model satisfies the residual theory, every full-theory
taxonomy entailment is either an ELC-bottom label or an explicit ELC label.
The alive context for `a` is the required full-theory countermodel witness.
-/
theorem subsumption_complete_withResidual {O : Ontology Concept Role}
    (R : ResidualTheory Concept Role top bottom)
    (hresidual : R.holds (canon (top := top) (bottom := bottom) (O := O)))
    (a b : Concept)
    (hentails : EntailsSubWithResidual O R a b) :
    Sub top bottom O a bottom ∨ Sub top bottom O a b := by
  by_cases ha : Sub top bottom O a bottom
  · exact Or.inl ha
  · right
    let x : Alive top bottom O := ⟨a, ha⟩
    exact hentails canon ⟨canon_models, hresidual⟩ x (Sub.refl a)

/-- A passing canonical residual check makes the ELC taxonomy exact. -/
theorem entailsSubWithResidual_iff {O : Ontology Concept Role}
    (R : ResidualTheory Concept Role top bottom)
    (hresidual : R.holds (canon (top := top) (bottom := bottom) (O := O)))
    (a b : Concept) :
    EntailsSubWithResidual O R a b ↔
      Sub top bottom O a bottom ∨ Sub top bottom O a b := by
  constructor
  · exact subsumption_complete_withResidual R hresidual a b
  · rintro (hbottom | hsub)
    · exact bottom_sound_withResidual hbottom
    · exact sub_sound_withResidual hsub

/-- A passing canonical residual check also makes consistency exact. -/
theorem unsatisfiableWithResidual_iff {O : Ontology Concept Role}
    (R : ResidualTheory Concept Role top bottom)
    (hresidual : R.holds (canon (top := top) (bottom := bottom) (O := O))) :
    UnsatisfiableWithResidual O R ↔ Sub top bottom O top bottom := by
  constructor
  · intro hunsat
    apply Classical.byContradiction
    intro hnot
    letI : Nonempty (Alive top bottom O) := alive_nonempty hnot
    exact hunsat canon ⟨canon_models, hresidual⟩
  · exact top_bottom_sound_withResidual

/-- Exact taxonomy theorem over the concept-only domain enumerated by Rust. -/
theorem entailsSubWithResidual_iff_on {O : Ontology Concept Role}
    (active : Concept → Prop) (hsig : SignatureClosed active top O)
    (R : ResidualTheory Concept Role top bottom)
    (hresidual : R.holds (canonOn active (top := top) (bottom := bottom) (O := O)))
    (a b : Concept) (ha : active a) :
    EntailsSubWithResidual O R a b ↔
      Sub top bottom O a bottom ∨ Sub top bottom O a b := by
  constructor
  · intro hentails
    by_cases hbottom : Sub top bottom O a bottom
    · exact Or.inl hbottom
    · right
      let x : ActiveAlive active top bottom O := ⟨a, ha, hbottom⟩
      exact hentails (canonOn active) ⟨canonOn_models hsig, hresidual⟩ x (Sub.refl a)
  · rintro (hbottom | hsub)
    · exact bottom_sound_withResidual hbottom
    · exact sub_sound_withResidual hsub

/-- Exact inconsistency theorem over Rust's concept-only canonical domain. -/
theorem unsatisfiableWithResidual_iff_on {O : Ontology Concept Role}
    (active : Concept → Prop) (hsig : SignatureClosed active top O)
    (R : ResidualTheory Concept Role top bottom)
    (hresidual : R.holds (canonOn active (top := top) (bottom := bottom) (O := O))) :
    UnsatisfiableWithResidual O R ↔ Sub top bottom O top bottom := by
  constructor
  · intro hunsat
    apply Classical.byContradiction
    intro hnot
    letI : Nonempty (ActiveAlive active top bottom O) := activeAlive_nonempty hsig hnot
    exact hunsat (canonOn active) ⟨canonOn_models hsig, hresidual⟩
  · exact top_bottom_sound_withResidual

/-- Executable exact-state corollary for Rust's materialized stores. -/
theorem entailsSubWithResidual_iff_materialized {O : Ontology Concept Role}
    {m : Materialization Concept Role}
    (closed : ClosedState m top bottom O) (sound : SoundState m top bottom O)
    (R : ResidualTheory Concept Role top bottom)
    (hresidual : R.holds (canon (top := top) (bottom := bottom) (O := O)))
    (a b : Concept) :
    EntailsSubWithResidual O R a b ↔ m.sub a bottom ∨ m.sub a b := by
  rw [entailsSubWithResidual_iff R hresidual]
  constructor
  · rintro (hbottom | hsub)
    · exact Or.inl (closed.sub_complete hbottom)
    · exact Or.inr (closed.sub_complete hsub)
  · rintro (hbottom | hsub)
    · exact Or.inl (sound.subSound hbottom)
    · exact Or.inr (sound.subSound hsub)

/-- Executable exact-state inconsistency corollary. -/
theorem unsatisfiableWithResidual_iff_materialized {O : Ontology Concept Role}
    {m : Materialization Concept Role}
    (closed : ClosedState m top bottom O) (sound : SoundState m top bottom O)
    (R : ResidualTheory Concept Role top bottom)
    (hresidual : R.holds (canon (top := top) (bottom := bottom) (O := O))) :
    UnsatisfiableWithResidual O R ↔ m.sub top bottom := by
  rw [unsatisfiableWithResidual_iff R hresidual]
  exact (sub_iff_of_exact closed sound).symm

/-- Materialized form of the concept-signature-restricted taxonomy theorem. -/
theorem entailsSubWithResidual_iff_materialized_on {O : Ontology Concept Role}
    {m : Materialization Concept Role}
    (closed : ClosedState m top bottom O) (sound : SoundState m top bottom O)
    (active : Concept → Prop) (hsig : SignatureClosed active top O)
    (R : ResidualTheory Concept Role top bottom)
    (hresidual : R.holds (canonOn active (top := top) (bottom := bottom) (O := O)))
    (a b : Concept) (ha : active a) :
    EntailsSubWithResidual O R a b ↔ m.sub a bottom ∨ m.sub a b := by
  rw [entailsSubWithResidual_iff_on active hsig R hresidual a b ha]
  constructor
  · rintro (hbottom | hsub)
    · exact Or.inl (closed.sub_complete hbottom)
    · exact Or.inr (closed.sub_complete hsub)
  · rintro (hbottom | hsub)
    · exact Or.inl (sound.subSound hbottom)
    · exact Or.inr (sound.subSound hsub)

/-- Materialized form of the restricted inconsistency theorem. -/
theorem unsatisfiableWithResidual_iff_materialized_on {O : Ontology Concept Role}
    {m : Materialization Concept Role}
    (closed : ClosedState m top bottom O) (sound : SoundState m top bottom O)
    (active : Concept → Prop) (hsig : SignatureClosed active top O)
    (R : ResidualTheory Concept Role top bottom)
    (hresidual : R.holds (canonOn active (top := top) (bottom := bottom) (O := O))) :
    UnsatisfiableWithResidual O R ↔ m.sub top bottom := by
  rw [unsatisfiableWithResidual_iff_on active hsig R hresidual]
  exact (sub_iff_of_exact closed sound).symm

/-- Exact taxonomy theorem whose countermodel is the finite materialized domain
enumerated by the native residual checker. Unlike the earlier executable
corollaries, its residual premise is checked on that same finite domain. -/
theorem entailsSubWithResidual_iff_finiteMaterialized {O : Ontology Concept Role}
    {m : Materialization Concept Role}
    (closed : ClosedState m top bottom O) (sound : SoundState m top bottom O)
    (active : Concept → Prop) (hsig : SignatureClosed active top O)
    (R : ResidualTheory Concept Role top bottom)
    (hresidual : R.holds (materializedCanon active m top bottom closed))
    (a b : Concept) (ha : active a) :
    EntailsSubWithResidual O R a b ↔ m.sub a bottom ∨ m.sub a b := by
  constructor
  · intro hentails
    by_cases hbottom : m.sub a bottom
    · exact Or.inl hbottom
    · right
      let x : MaterializedActiveAlive active m bottom := ⟨a, ha, hbottom⟩
      exact hentails (materializedCanon active m top bottom closed)
        ⟨materializedCanon_models active m closed hsig, hresidual⟩ x
        (closed.initRefl a)
  · rintro (hbottom | hsub)
    · exact bottom_sound_withResidual (sound.subSound hbottom)
    · exact sub_sound_withResidual (sound.subSound hsub)

/-- Exact inconsistency theorem over the finite materialized domain enumerated
by the native residual checker. -/
theorem unsatisfiableWithResidual_iff_finiteMaterialized
    {O : Ontology Concept Role} {m : Materialization Concept Role}
    (closed : ClosedState m top bottom O) (sound : SoundState m top bottom O)
    (active : Concept → Prop) (hsig : SignatureClosed active top O)
    (R : ResidualTheory Concept Role top bottom)
    (hresidual : R.holds (materializedCanon active m top bottom closed)) :
    UnsatisfiableWithResidual O R ↔ m.sub top bottom := by
  constructor
  · intro hunsat
    apply Classical.byContradiction
    intro hnot
    letI : Nonempty (MaterializedActiveAlive active m bottom) :=
      materializedActiveAlive_nonempty active m hsig hnot
    exact hunsat (materializedCanon active m top bottom closed)
      ⟨materializedCanon_models active m closed hsig, hresidual⟩
  · exact fun hbottom => top_bottom_sound_withResidual (sound.subSound hbottom)

end ContextCalculus.ELCompletion

#print axioms ContextCalculus.ELCompletion.entailsSubWithResidual_iff_materialized
#print axioms ContextCalculus.ELCompletion.unsatisfiableWithResidual_iff_materialized
#print axioms ContextCalculus.ELCompletion.entailsSubWithResidual_iff_materialized_on
#print axioms ContextCalculus.ELCompletion.unsatisfiableWithResidual_iff_materialized_on
#print axioms ContextCalculus.ELCompletion.entailsSubWithResidual_iff_finiteMaterialized
#print axioms ContextCalculus.ELCompletion.unsatisfiableWithResidual_iff_finiteMaterialized
