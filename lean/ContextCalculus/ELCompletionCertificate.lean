import ContextCalculus.ELCompletionRefinement

/-!
# Checkable proof traces for ELC materializations

This module turns the abstract `SoundState` obligation into a finite,
executable certificate check.  A trace is stored in reverse dependency order:
every premise of a step must occur later in the list.  Successful checking
proves that every materialized fact belongs to the semantic ELC closure.
-/

namespace ContextCalculus.ELCompletion

variable {Concept Role : Type} [DecidableEq Concept] [DecidableEq Role]

inductive Fact (Concept Role : Type) where
  | sub (a b : Concept)
  | edge (a : Concept) (role : Role) (target : Concept)
deriving DecidableEq

inductive Step (Concept Role : Type) where
  | refl (a : Concept)
  | top (a : Concept)
  | nf1 (a sub sup : Concept)
  | nf2 (a left right sup : Concept)
  | nf5 (a sub : Concept)
  | nf4 (a target filler sup : Concept) (role : Role)
  | bottomEdge (a target : Concept) (role : Role)
  | nf3 (a sub filler : Concept) (role : Role)
  | nf6 (a target : Concept) (sub sup : Role)
  | nf7 (a middle target : Concept) (first second sup : Role)
  | reflexive (a : Concept) (role : Role)

def Step.conclusion (top bottom : Concept) : Step Concept Role → Fact Concept Role
  | .refl a => .sub a a
  | .top a => .sub a top
  | .nf1 a _ sup => .sub a sup
  | .nf2 a _ _ sup => .sub a sup
  | .nf5 a _ => .sub a bottom
  | .nf4 a _ _ sup _ => .sub a sup
  | .bottomEdge a _ _ => .sub a bottom
  | .nf3 a _ filler role => .edge a role filler
  | .nf6 a target _ sup => .edge a sup target
  | .nf7 a _ target _ _ sup => .edge a sup target
  | .reflexive a role => .edge a role a

def ValidStep (top bottom : Concept) (O : Ontology Concept Role)
    (available : List (Fact Concept Role)) : Step Concept Role → Prop
  | .refl _ | .top _ => True
  | .nf1 a sub sup =>
      .sub a sub ∈ available ∧ .nf1 sub sup ∈ O
  | .nf2 a left right sup =>
      .sub a left ∈ available ∧ .sub a right ∈ available ∧
        .nf2 left right sup ∈ O
  | .nf5 a sub => .sub a sub ∈ available ∧ .nf5 sub ∈ O
  | .nf4 a target filler sup role =>
      .edge a role target ∈ available ∧ .sub target filler ∈ available ∧
        .nf4 role filler sup ∈ O
  | .bottomEdge a target role =>
      .edge a role target ∈ available ∧ .sub target bottom ∈ available
  | .nf3 a sub filler role =>
      .sub a sub ∈ available ∧ .nf3 sub role filler ∈ O
  | .nf6 a target sub sup =>
      .edge a sub target ∈ available ∧ .nf6 sub sup ∈ O
  | .nf7 a middle target first second sup =>
      .edge a first middle ∈ available ∧
        .edge middle second target ∈ available ∧ .nf7 first second sup ∈ O
  | .reflexive _ role => .reflexive role ∈ O

instance instDecidableValidStep (top bottom : Concept) (O : Ontology Concept Role)
    (available : List (Fact Concept Role)) (step : Step Concept Role) :
    Decidable (ValidStep top bottom O available step) := by
  cases step <;> simp only [ValidStep] <;> infer_instance

def checkTrace (top bottom : Concept) (O : Ontology Concept Role) :
    List (Step Concept Role) → Bool
  | [] => true
  | step :: tail =>
      decide (ValidStep top bottom O (tail.map (Step.conclusion top bottom)) step) &&
        checkTrace top bottom O tail

def Derivable (top bottom : Concept) (O : Ontology Concept Role) :
    Fact Concept Role → Prop
  | .sub a b => Sub top bottom O a b
  | .edge a role target => Edge top bottom O a role target

theorem validStep_derivable {top bottom : Concept} {O : Ontology Concept Role}
    {available : List (Fact Concept Role)}
    (havail : ∀ fact ∈ available, Derivable top bottom O fact)
    {step : Step Concept Role} (hstep : ValidStep top bottom O available step) :
    Derivable top bottom O (step.conclusion top bottom) := by
  cases step with
  | refl a => exact Sub.refl a
  | top a => exact Sub.top a
  | nf1 a sub sup => exact Sub.nf1 (havail _ hstep.1) hstep.2
  | nf2 a left right sup =>
      exact Sub.nf2 (havail _ hstep.1) (havail _ hstep.2.1) hstep.2.2
  | nf5 a sub => exact Sub.nf5 (havail _ hstep.1) hstep.2
  | nf4 a target filler sup role =>
      exact Sub.nf4 (havail _ hstep.1) (havail _ hstep.2.1) hstep.2.2
  | bottomEdge a target role =>
      exact Sub.bottomEdge (havail _ hstep.1) (havail _ hstep.2)
  | nf3 a sub filler role => exact Edge.nf3 (havail _ hstep.1) hstep.2
  | nf6 a target sub sup => exact Edge.nf6 (havail _ hstep.1) hstep.2
  | nf7 a middle target first second sup =>
      exact Edge.nf7 (havail _ hstep.1) (havail _ hstep.2.1) hstep.2.2
  | reflexive a role => exact Edge.reflexive a hstep

theorem checkTrace_sound {top bottom : Concept} {O : Ontology Concept Role}
    {trace : List (Step Concept Role)} (hcheck : checkTrace top bottom O trace = true) :
    ∀ fact ∈ trace.map (Step.conclusion top bottom),
      Derivable top bottom O fact := by
  induction trace with
  | nil => simp
  | cons step tail ih =>
      simp only [checkTrace, Bool.and_eq_true] at hcheck
      have htail := ih hcheck.2
      intro fact hfact
      simp only [List.map_cons, List.mem_cons] at hfact
      rcases hfact with rfl | hfact
      · exact validStep_derivable htail (of_decide_eq_true hcheck.1)
      · exact htail fact hfact

def traceMaterialization (top bottom : Concept)
    (trace : List (Step Concept Role)) : Materialization Concept Role where
  sub a b := Fact.sub a b ∈ trace.map (Step.conclusion top bottom)
  edge a role target :=
    Fact.edge a role target ∈ trace.map (Step.conclusion top bottom)

theorem checkedTrace_soundState {top bottom : Concept} {O : Ontology Concept Role}
    {trace : List (Step Concept Role)} (hcheck : checkTrace top bottom O trace = true) :
    SoundState (traceMaterialization top bottom trace) top bottom O where
  subSound h := checkTrace_sound hcheck (Fact.sub _ _) h
  edgeSound h := checkTrace_sound hcheck (Fact.edge _ _ _) h

end ContextCalculus.ELCompletion
