import ContextCalculus.ELCompletionRefinement

/-!
# Relative refinement contract for an ELC materialisation

`ELCompletionRefinement.ClosedState` quantifies over every concept name.  An
executable materialisation computed over a finite universe cannot satisfy it:
for a concept outside the universe it stores nothing.  This module restricts
the closure obligations to contexts in a predicate `U` and shows that this is
enough for every context in `U`, because the closure never leaves `U`: every
edge target is an nf3 filler, the context itself (reflexive roles), or the
target of an earlier edge.

The reference saturation of v1.6.0 (`ELReferenceSaturation`) discharges
`ClosedStateOn` for the universe of the requested named concepts and the
ontology's concept names, and `SoundState` globally.
-/

namespace ContextCalculus.ELCompletion

variable {Concept Role : Type} {top bottom : Concept}
  {O : Ontology Concept Role}

/-- Closure obligations restricted to contexts in `U`.  `fillerIn` is the
only condition on `U` itself: it must contain every nf3 filler, so that edge
targets stay inside it. -/
structure ClosedStateOn (U : Concept → Prop) (m : Materialization Concept Role)
    (top bottom : Concept) (O : Ontology Concept Role) : Prop where
  fillerIn : ∀ {sub filler : Concept} {role : Role},
    .nf3 sub role filler ∈ O → U filler
  initRefl : ∀ a, U a → m.sub a a
  initTop : ∀ a, U a → m.sub a top
  closeNf1 : ∀ {a sub sup}, U a → m.sub a sub → .nf1 sub sup ∈ O → m.sub a sup
  closeNf2 : ∀ {a left right sup}, U a →
    m.sub a left → m.sub a right → .nf2 left right sup ∈ O → m.sub a sup
  closeNf5 : ∀ {a sub}, U a → m.sub a sub → .nf5 sub ∈ O → m.sub a bottom
  closeNf4 : ∀ {a target filler sup role}, U a → U target →
    m.edge a role target → m.sub target filler → .nf4 role filler sup ∈ O →
    m.sub a sup
  closeBottomEdge : ∀ {a target role}, U a → U target →
    m.edge a role target → m.sub target bottom → m.sub a bottom
  closeNf3 : ∀ {a sub filler role}, U a →
    m.sub a sub → .nf3 sub role filler ∈ O → m.edge a role filler
  closeNf6 : ∀ {a target sub sup}, U a →
    m.edge a sub target → .nf6 sub sup ∈ O → m.edge a sup target
  closeNf7 : ∀ {a middle target first second sup}, U a → U middle →
    m.edge a first middle → m.edge middle second target →
    .nf7 first second sup ∈ O → m.edge a sup target
  closeReflexive : ∀ a {role}, U a → .reflexive role ∈ O → m.edge a role a

/-- A globally closed materialisation is closed on every predicate that
contains the nf3 fillers. -/
theorem ClosedState.toOn {m : Materialization Concept Role}
    (hm : ClosedState m top bottom O) (U : Concept → Prop)
    (hfiller : ∀ {sub filler : Concept} {role : Role},
      .nf3 sub role filler ∈ O → U filler) :
    ClosedStateOn U m top bottom O where
  fillerIn := hfiller
  initRefl a _ := hm.initRefl a
  initTop a _ := hm.initTop a
  closeNf1 _ hsub hcl := hm.closeNf1 hsub hcl
  closeNf2 _ hl hr hcl := hm.closeNf2 hl hr hcl
  closeNf5 _ hsub hcl := hm.closeNf5 hsub hcl
  closeNf4 _ _ hedge hsub hcl := hm.closeNf4 hedge hsub hcl
  closeBottomEdge _ _ hedge hbottom := hm.closeBottomEdge hedge hbottom
  closeNf3 _ hsub hcl := hm.closeNf3 hsub hcl
  closeNf6 _ hedge hcl := hm.closeNf6 hedge hcl
  closeNf7 _ _ h₁ h₂ hcl := hm.closeNf7 h₁ h₂ hcl
  closeReflexive a _ _ hcl := hm.closeReflexive a hcl

/-- A materialisation closed on `U` contains every derivable label fact of a
context in `U`. -/
theorem ClosedStateOn.sub_complete {U : Concept → Prop}
    {m : Materialization Concept Role}
    (hm : ClosedStateOn U m top bottom O) {a b : Concept}
    (h : Sub top bottom O a b) (ha : U a) : m.sub a b :=
  Sub.rec
    (motive_1 := fun a b _ => U a → m.sub a b)
    (motive_2 := fun a role b _ => U a → m.edge a role b ∧ U b)
    (fun a ha => hm.initRefl a ha)
    (fun a ha => hm.initTop a ha)
    (fun _ hcl ih ha => hm.closeNf1 ha (ih ha) hcl)
    (fun _ _ hcl ihl ihr ha => hm.closeNf2 ha (ihl ha) (ihr ha) hcl)
    (fun _ hcl ih ha => hm.closeNf5 ha (ih ha) hcl)
    (fun _ _ hcl ihe ihs ha =>
      let ⟨hedge, htarget⟩ := ihe ha
      hm.closeNf4 ha htarget hedge (ihs htarget) hcl)
    (fun _ _ ihe ihb ha =>
      let ⟨hedge, htarget⟩ := ihe ha
      hm.closeBottomEdge ha htarget hedge (ihb htarget))
    (fun _ hcl ihs ha => ⟨hm.closeNf3 ha (ihs ha) hcl, hm.fillerIn hcl⟩)
    (fun _ hcl ihe ha =>
      let ⟨hedge, htarget⟩ := ihe ha
      ⟨hm.closeNf6 ha hedge hcl, htarget⟩)
    (fun _ _ hcl ihe₁ ihe₂ ha =>
      let ⟨hfirst, hmiddle⟩ := ihe₁ ha
      let ⟨hsecond, htarget⟩ := ihe₂ hmiddle
      ⟨hm.closeNf7 ha hmiddle hfirst hsecond hcl, htarget⟩)
    (fun a _ hcl ha => ⟨hm.closeReflexive a ha hcl, ha⟩)
    h ha

/-- Edge counterpart: the stored edge exists and its target stays in `U`. -/
theorem ClosedStateOn.edge_complete {U : Concept → Prop}
    {m : Materialization Concept Role}
    (hm : ClosedStateOn U m top bottom O) {a target : Concept} {role : Role}
    (h : Edge top bottom O a role target) (ha : U a) :
    m.edge a role target ∧ U target :=
  Edge.rec
    (motive_1 := fun a b _ => U a → m.sub a b)
    (motive_2 := fun a role b _ => U a → m.edge a role b ∧ U b)
    (fun a ha => hm.initRefl a ha)
    (fun a ha => hm.initTop a ha)
    (fun _ hcl ih ha => hm.closeNf1 ha (ih ha) hcl)
    (fun _ _ hcl ihl ihr ha => hm.closeNf2 ha (ihl ha) (ihr ha) hcl)
    (fun _ hcl ih ha => hm.closeNf5 ha (ih ha) hcl)
    (fun _ _ hcl ihe ihs ha =>
      let ⟨hedge, htarget⟩ := ihe ha
      hm.closeNf4 ha htarget hedge (ihs htarget) hcl)
    (fun _ _ ihe ihb ha =>
      let ⟨hedge, htarget⟩ := ihe ha
      hm.closeBottomEdge ha htarget hedge (ihb htarget))
    (fun _ hcl ihs ha => ⟨hm.closeNf3 ha (ihs ha) hcl, hm.fillerIn hcl⟩)
    (fun _ hcl ihe ha =>
      let ⟨hedge, htarget⟩ := ihe ha
      ⟨hm.closeNf6 ha hedge hcl, htarget⟩)
    (fun _ _ hcl ihe₁ ihe₂ ha =>
      let ⟨hfirst, hmiddle⟩ := ihe₁ ha
      let ⟨hsecond, htarget⟩ := ihe₂ hmiddle
      ⟨hm.closeNf7 ha hmiddle hfirst hsecond hcl, htarget⟩)
    (fun a _ hcl ha => ⟨hm.closeReflexive a ha hcl, ha⟩)
    h ha

/-- Exact label facts for contexts in `U`. -/
theorem sub_iff_of_exact_on {U : Concept → Prop}
    {m : Materialization Concept Role}
    (closed : ClosedStateOn U m top bottom O) (sound : SoundState m top bottom O)
    {a b : Concept} (ha : U a) :
    m.sub a b ↔ Sub top bottom O a b :=
  ⟨sound.subSound, fun h => closed.sub_complete h ha⟩

/-- Exact named-class taxonomy for subjects in `U`. -/
theorem entails_iff_materialized_on {U : Concept → Prop}
    {m : Materialization Concept Role}
    (closed : ClosedStateOn U m top bottom O) (sound : SoundState m top bottom O)
    {a b : Concept} (ha : U a) :
    EntailsSub (top := top) (bottom := bottom) O a b ↔
      m.sub a bottom ∨ m.sub a b := by
  constructor
  · intro hentails
    rcases subsumption_complete a b hentails with hbottom | hsub
    · exact Or.inl (closed.sub_complete hbottom ha)
    · exact Or.inr (closed.sub_complete hsub ha)
  · intro hmat Domain I hI x hax
    rcases hmat with hbottom | hsub
    · have hderived := sound.subSound hbottom
      exact False.elim (I.bottom_false x (sub_sound hI hderived x hax))
    · exact sub_sound hI (sound.subSound hsub) x hax

/-- Exact inconsistency readout when `top` is a context of the universe. -/
theorem unsat_iff_materialized_on {U : Concept → Prop}
    {m : Materialization Concept Role}
    (closed : ClosedStateOn U m top bottom O) (sound : SoundState m top bottom O)
    (htop : U top) :
    Unsatisfiable (top := top) (bottom := bottom) O ↔ m.sub top bottom := by
  constructor
  · intro hunsat
    apply Classical.byContradiction
    intro hnot
    have hnotDerived : ¬ Sub top bottom O top bottom := by
      intro hderived
      exact hnot (closed.sub_complete hderived htop)
    rcases top_bottom_complete hnotDerived with ⟨nonempty, hmodel⟩
    letI := nonempty
    exact hunsat canon hmodel
  · intro hmat
    exact top_bottom_sound (sound.subSound hmat)

#print axioms ClosedStateOn.sub_complete
#print axioms ClosedStateOn.edge_complete
#print axioms entails_iff_materialized_on
#print axioms unsat_iff_materialized_on

end ContextCalculus.ELCompletion
