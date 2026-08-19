import ContextCalculus.ELCompletion

/-!
# Refinement contract for an ELC materialisation

`ELCompletion` defines the semantic closure.  This module states the exact
obligations of a concrete worklist result.  A materialised state must contain
the initial facts and be closed under every NF1–NF7 rule.  If every stored fact
also has an inductive derivation, the representation is extensionally equal to
the semantic closure and its taxonomy and inconsistency readouts are exact.

The next executable-refinement layer must prove that the final Rust `State`
satisfies `ClosedState` and `SoundState`; this module removes all further
reasoning-algorithm obligations once those facts are established.
-/

namespace ContextCalculus.ELCompletion

variable {Concept Role : Type} {top bottom : Concept}
  {O : Ontology Concept Role}

/-- Abstract view of Rust's completed `sub_super` and `edges` stores. -/
structure Materialization (Concept Role : Type) where
  sub : Concept → Concept → Prop
  edge : Concept → Role → Concept → Prop

/-- Initialisation and closure obligations corresponding to Rust's `run`. -/
structure ClosedState (m : Materialization Concept Role)
    (top bottom : Concept) (O : Ontology Concept Role) : Prop where
  initRefl : ∀ a, m.sub a a
  initTop : ∀ a, m.sub a top
  closeNf1 : ∀ {a sub sup}, m.sub a sub → .nf1 sub sup ∈ O → m.sub a sup
  closeNf2 : ∀ {a left right sup},
    m.sub a left → m.sub a right → .nf2 left right sup ∈ O → m.sub a sup
  closeNf5 : ∀ {a sub}, m.sub a sub → .nf5 sub ∈ O → m.sub a bottom
  closeNf4 : ∀ {a target filler sup role},
    m.edge a role target → m.sub target filler → .nf4 role filler sup ∈ O →
    m.sub a sup
  closeBottomEdge : ∀ {a target role},
    m.edge a role target → m.sub target bottom → m.sub a bottom
  closeNf3 : ∀ {a sub filler role},
    m.sub a sub → .nf3 sub role filler ∈ O → m.edge a role filler
  closeNf6 : ∀ {a target sub sup},
    m.edge a sub target → .nf6 sub sup ∈ O → m.edge a sup target
  closeNf7 : ∀ {a middle target first second sup},
    m.edge a first middle → m.edge middle second target →
    .nf7 first second sup ∈ O → m.edge a sup target
  closeReflexive : ∀ a {role}, .reflexive role ∈ O → m.edge a role a

/-- No stored fact is outside the inductive ELC closure. -/
structure SoundState (m : Materialization Concept Role)
    (top bottom : Concept) (O : Ontology Concept Role) : Prop where
  subSound : ∀ {a b}, m.sub a b → Sub top bottom O a b
  edgeSound : ∀ {a role b}, m.edge a role b → Edge top bottom O a role b

/-- A closed materialisation contains every inductively derivable fact. -/
theorem ClosedState.sub_complete
    {m : Materialization Concept Role} (hm : ClosedState m top bottom O)
    {a b : Concept} (h : Sub top bottom O a b) : m.sub a b :=
  Sub.rec
    (motive_1 := fun a b _ => m.sub a b)
    (motive_2 := fun a role b _ => m.edge a role b)
    hm.initRefl
    hm.initTop
    (fun _ hcl ih => hm.closeNf1 ih hcl)
    (fun _ _ hcl ihl ihr => hm.closeNf2 ihl ihr hcl)
    (fun _ hcl ih => hm.closeNf5 ih hcl)
    (fun _ _ hcl ihe ihs => hm.closeNf4 ihe ihs hcl)
    (fun _ _ ihe ihb => hm.closeBottomEdge ihe ihb)
    (fun _ hcl ih => hm.closeNf3 ih hcl)
    (fun _ hcl ihe => hm.closeNf6 ihe hcl)
    (fun _ _ hcl ihe₁ ihe₂ => hm.closeNf7 ihe₁ ihe₂ hcl)
    (fun _ _ hcl => hm.closeReflexive _ hcl)
    h

/-- Edge counterpart of `ClosedState.sub_complete`. -/
theorem ClosedState.edge_complete
    {m : Materialization Concept Role} (hm : ClosedState m top bottom O)
    {a target : Concept} {role : Role} (h : Edge top bottom O a role target) :
    m.edge a role target :=
  Edge.rec
    (motive_1 := fun a b _ => m.sub a b)
    (motive_2 := fun a role b _ => m.edge a role b)
    hm.initRefl
    hm.initTop
    (fun _ hcl ih => hm.closeNf1 ih hcl)
    (fun _ _ hcl ihl ihr => hm.closeNf2 ihl ihr hcl)
    (fun _ hcl ih => hm.closeNf5 ih hcl)
    (fun _ _ hcl ihe ihs => hm.closeNf4 ihe ihs hcl)
    (fun _ _ ihe ihb => hm.closeBottomEdge ihe ihb)
    (fun _ hcl ih => hm.closeNf3 ih hcl)
    (fun _ hcl ihe => hm.closeNf6 ihe hcl)
    (fun _ _ hcl ihe₁ ihe₂ => hm.closeNf7 ihe₁ ihe₂ hcl)
    (fun _ _ hcl => hm.closeReflexive _ hcl)
    h

theorem sub_iff_of_exact {m : Materialization Concept Role}
    (closed : ClosedState m top bottom O) (sound : SoundState m top bottom O)
    {a b : Concept} :
    m.sub a b ↔ Sub top bottom O a b :=
  ⟨sound.subSound, closed.sub_complete⟩

theorem edge_iff_of_exact {m : Materialization Concept Role}
    (closed : ClosedState m top bottom O) (sound : SoundState m top bottom O)
    {a target : Concept} {role : Role} :
    m.edge a role target ↔ Edge top bottom O a role target :=
  ⟨sound.edgeSound, closed.edge_complete⟩

/-- Exact materialisation yields the exact named-class taxonomy. -/
theorem entails_iff_materialized {m : Materialization Concept Role}
    (closed : ClosedState m top bottom O) (sound : SoundState m top bottom O)
    (a b : Concept) :
    EntailsSub (top := top) (bottom := bottom) O a b ↔
      m.sub a bottom ∨ m.sub a b := by
  constructor
  · intro hentails
    rcases subsumption_complete a b hentails with hbottom | hsub
    · exact Or.inl (closed.sub_complete hbottom)
    · exact Or.inr (closed.sub_complete hsub)
  · intro hmat Domain I hI x hax
    rcases hmat with hbottom | hsub
    · have hderived := sound.subSound hbottom
      exact False.elim (I.bottom_false x (sub_sound hI hderived x hax))
    · exact sub_sound hI (sound.subSound hsub) x hax

/-- Exact materialisation yields the exact ontology inconsistency readout. -/
theorem unsat_iff_materialized {m : Materialization Concept Role}
    (closed : ClosedState m top bottom O) (sound : SoundState m top bottom O) :
    Unsatisfiable (top := top) (bottom := bottom) O ↔ m.sub top bottom := by
  constructor
  · intro hunsat
    apply Classical.byContradiction
    intro hnot
    have hnotDerived : ¬ Sub top bottom O top bottom := by
      intro hderived
      exact hnot (closed.sub_complete hderived)
    rcases top_bottom_complete hnotDerived with ⟨nonempty, hmodel⟩
    letI := nonempty
    exact hunsat canon hmodel
  · intro hmat
    exact top_bottom_sound (sound.subSound hmat)

end ContextCalculus.ELCompletion
