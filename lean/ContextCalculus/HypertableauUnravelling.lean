import ContextCalculus.HypertableauCardinality

/-!
# Regular path unravelling for blocked hypertableau endpoints

A blocked completion graph is not itself the semantic model in expressive
description logics.  Its model is obtained by unravelling successor steps into
paths.  Reusing a finite graph node at a later path position creates a new
domain value, and a natural-number slot keeps distinct cardinality witnesses
separate even when they reuse the same finite node.

This module defines the path domain independently of a particular blocking
policy.  `redirect` chooses the finite node whose outgoing witness edges are
used at a path endpoint; a concrete pairwise blocker will later instantiate and
justify that map.  The first endpoint theorem proves that witness completion at
redirected nodes gives a genuine, distinct path witness.
-/

namespace ContextCalculus.Hypertableau

universe u v w

variable {Node : Type u} {Concept : Type v} {Role : Type w}

inductive UnravellingPath
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node) :
    Node → Type (max u w) where
  | root : UnravellingPath state redirect slotAllowed root root
  | step {source target : Node}
      (parent : UnravellingPath state redirect slotAllowed root source)
      (slot : Nat) (role : Role)
      (edge : state.edge role (redirect source) target)
      (allowed : slotAllowed source role target slot) :
      UnravellingPath state redirect slotAllowed root target

namespace UnravellingPath

def depth {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root endpoint : Node} :
    UnravellingPath state redirect slotAllowed root endpoint → Nat
  | .root => 0
  | .step parent _ _ _ _ => parent.depth + 1

def lastSlot {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root endpoint : Node} :
    UnravellingPath state redirect slotAllowed root endpoint → Option Nat
  | .root => none
  | .step _ slot _ _ _ => some slot

@[simp] theorem depth_root
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node) :
    (UnravellingPath.root :
      UnravellingPath state redirect slotAllowed root root).depth = 0 := rfl

@[simp] theorem depth_step
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root source target : Node}
    (parent : UnravellingPath state redirect slotAllowed root source)
    (slot : Nat) (role : Role) (edge : state.edge role (redirect source) target)
    (allowed : slotAllowed source role target slot) :
    (UnravellingPath.step parent slot role edge allowed).depth = parent.depth + 1 := rfl

end UnravellingPath

abbrev UnravellingDomain
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node) :=
  Σ endpoint, UnravellingPath state redirect slotAllowed root endpoint

def UnravellingDomain.depth
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root : Node}
    (value : UnravellingDomain state redirect slotAllowed root) : Nat :=
  value.2.depth

def UnravellingDomain.lastSlot
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root : Node}
    (value : UnravellingDomain state redirect slotAllowed root) : Option Nat :=
  value.2.lastSlot

inductive UnravellingDirectRole
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node) (role : Role) :
    UnravellingDomain state redirect slotAllowed root →
      UnravellingDomain state redirect slotAllowed root → Prop where
  | step {source target : Node}
      (parent : UnravellingPath state redirect slotAllowed root source)
      (slot : Nat) (edge : state.edge role (redirect source) target)
      (allowed : slotAllowed source role target slot) :
      UnravellingDirectRole state redirect slotAllowed root role
        ⟨source, parent⟩
        ⟨target, UnravellingPath.step parent slot role edge allowed⟩

def State.unravelling
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node) :
    Interp (UnravellingDomain state redirect slotAllowed root) Concept Role where
  concept concept value := state.label value.1 (.pos concept)
  role := UnravellingDirectRole state redirect slotAllowed root

/-- Normalized role rules used by the regular path interpretation. Unary
inclusions, inverse bridges, binary chains (including transitivity), and
reflexivity cover the role-clause shapes emitted to HT. -/
structure UnravellingRoleRules (Role : Type w) where
  subRole : Role → Role → Prop
  inverseRole : Role → Role → Prop
  chain : Role → Role → Role → Prop
  reflexive : Role → Prop

inductive UnravellingRole
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role) :
    Role → UnravellingDomain state redirect slotAllowed root →
      UnravellingDomain state redirect slotAllowed root → Prop where
  | direct {role source target}
      (edge : UnravellingDirectRole state redirect slotAllowed root
        role source target) :
      UnravellingRole state redirect slotAllowed root rules role source target
  | sub {premise conclusion source target}
      (rule : rules.subRole premise conclusion)
      (edge : UnravellingRole state redirect slotAllowed root rules
        premise source target) :
      UnravellingRole state redirect slotAllowed root rules
        conclusion source target
  | inverse {premise conclusion source target}
      (rule : rules.inverseRole premise conclusion)
      (edge : UnravellingRole state redirect slotAllowed root rules
        premise source target) :
      UnravellingRole state redirect slotAllowed root rules
        conclusion target source
  | chain {first second conclusion source middle target}
      (rule : rules.chain first second conclusion)
      (left : UnravellingRole state redirect slotAllowed root rules
        first source middle)
      (right : UnravellingRole state redirect slotAllowed root rules
        second middle target) :
      UnravellingRole state redirect slotAllowed root rules
        conclusion source target
  | refl {role source} (rule : rules.reflexive role) :
      UnravellingRole state redirect slotAllowed root rules role source source

def State.regularUnravelling
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role) :
    Interp (UnravellingDomain state redirect slotAllowed root) Concept Role where
  concept concept value := state.label value.1 (.pos concept)
  role := UnravellingRole state redirect slotAllowed root rules

theorem State.regularUnravelling_direct
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role)
    {role : Role} {source target : UnravellingDomain state redirect slotAllowed root}
    (edge : (state.unravelling redirect slotAllowed root).role role source target) :
    (state.regularUnravelling redirect slotAllowed root rules).role
      role source target :=
  UnravellingRole.direct edge

theorem State.regularUnravelling_subRole
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role)
    {premise conclusion : Role} (rule : rules.subRole premise conclusion) :
    ∀ source target,
      (state.regularUnravelling redirect slotAllowed root rules).role
        premise source target →
      (state.regularUnravelling redirect slotAllowed root rules).role
        conclusion source target :=
  fun _ _ edge => UnravellingRole.sub rule edge

theorem State.regularUnravelling_inverseRole
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role)
    {premise conclusion : Role} (rule : rules.inverseRole premise conclusion) :
    ∀ source target,
      (state.regularUnravelling redirect slotAllowed root rules).role
        premise source target →
      (state.regularUnravelling redirect slotAllowed root rules).role
        conclusion target source :=
  fun _ _ edge => UnravellingRole.inverse rule edge

theorem State.regularUnravelling_chain
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role)
    {first second conclusion : Role} (rule : rules.chain first second conclusion) :
    ∀ source middle target,
      (state.regularUnravelling redirect slotAllowed root rules).role
        first source middle →
      (state.regularUnravelling redirect slotAllowed root rules).role
        second middle target →
      (state.regularUnravelling redirect slotAllowed root rules).role
        conclusion source target :=
  fun _ _ _ left right => UnravellingRole.chain rule left right

theorem State.regularUnravelling_reflexive
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role)
    {role : Role} (rule : rules.reflexive role) :
    ∀ source, (state.regularUnravelling redirect slotAllowed root rules).role
      role source source :=
  fun _ => UnravellingRole.refl rule

def UnravellingRoleRules.SimpleExact
    (rules : UnravellingRoleRules Role)
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (role : Role) : Prop :=
  ∀ source target,
    UnravellingRole state redirect slotAllowed root rules role source target →
      UnravellingDirectRole state redirect slotAllowed root role source target

/-- Cardinality satisfaction transfers from the direct path interpretation to
the regular role closure. Minimum witnesses remain edges by `direct`; maximum
bounds require the SROIQ simple-role premise that closure is exact on the
number-restricted role. -/
theorem State.regularUnravelling_modelsCardinalityDef_of_direct
    {Node : Type u} {Concept Role : Type}
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role)
    (definition : CardinalityDef Concept Role)
    (hdirect : (state.unravelling redirect slotAllowed root).modelsCardinalityDef
      definition)
    (hsimple : definition.kind = .maximum →
      rules.SimpleExact state redirect slotAllowed root definition.role) :
    (state.regularUnravelling redirect slotAllowed root rules).modelsCardinalityDef
      definition := by
  intro source hmarker
  cases hkind : definition.kind with
  | minimum =>
      have hminimum : HasAtLeast definition.bound
          ((state.unravelling redirect slotAllowed root).cardinalitySuccessor
            definition source) := by
        simpa [Interp.modelsCardinalityDef, hkind] using hdirect source hmarker
      rcases hminimum with ⟨witness, hinjective, hsuccessor⟩
      refine ⟨witness, hinjective, ?_⟩
      intro index
      rcases hsuccessor index with ⟨hrole, hfiller⟩
      exact ⟨state.regularUnravelling_direct redirect slotAllowed root rules hrole,
        hfiller⟩
  | maximum =>
      have hmaximum : HasAtMost definition.bound
          ((state.unravelling redirect slotAllowed root).cardinalitySuccessor
            definition source) := by
        simpa [Interp.modelsCardinalityDef, hkind] using hdirect source hmarker
      intro hatLeast
      apply hmaximum
      rcases hatLeast with ⟨witness, hinjective, hsuccessor⟩
      refine ⟨witness, hinjective, ?_⟩
      intro index
      rcases hsuccessor index with ⟨hrole, hfiller⟩
      exact ⟨hsimple hkind source (witness index) hrole, hfiller⟩

theorem State.regularUnravelling_modelsCardinalityDefs_of_direct
    {Node : Type u} {Concept Role : Type}
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role)
    (definitions : List (CardinalityDef Concept Role))
    (hdirect : (state.unravelling redirect slotAllowed root).modelsCardinalityDefs
      definitions)
    (hsimple : ∀ definition ∈ definitions,
      definition.kind = .maximum →
      rules.SimpleExact state redirect slotAllowed root definition.role) :
    (state.regularUnravelling redirect slotAllowed root rules).modelsCardinalityDefs
      definitions := by
  intro definition hdefinition
  exact state.regularUnravelling_modelsCardinalityDef_of_direct
    redirect slotAllowed root rules definition (hdirect definition hdefinition)
    (hsimple definition hdefinition)

theorem UnravellingDirectRole.target_depth
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root : Node}
    {role : Role}
    {source target : UnravellingDomain state redirect slotAllowed root}
    (hedge : UnravellingDirectRole state redirect slotAllowed root role source target) :
    target.depth = source.depth + 1 := by
  cases hedge
  rfl

theorem UnravellingDirectRole.ne
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root : Node}
    {role : Role}
    {source target : UnravellingDomain state redirect slotAllowed root}
    (hedge : UnravellingDirectRole state redirect slotAllowed root role source target) :
    target ≠ source := by
  intro hequal
  have hdepth := hedge.target_depth
  rw [hequal] at hdepth
  omega

theorem State.unravelling_sat_label
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (hclash : state.ClashFree)
    (value : UnravellingDomain state redirect slotAllowed root) (lit : Lit Concept)
    (hlabel : state.label value.1 lit) :
    (state.unravelling redirect slotAllowed root).satLit lit value := by
  rcases lit with ⟨concept, neg⟩
  cases neg with
  | false => exact hlabel
  | true =>
      intro hpositive
      exact hclash value.1 concept ⟨hpositive, hlabel⟩

/-- A redirected completion-graph witness becomes a genuinely new path-domain
value.  The finite target node may repeat; path depth still distinguishes the
semantic witness from its predecessor. -/
theorem State.unravelling_obligation_witness
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (hclash : state.ClashFree)
    (hwitness : state.WitnessComplete)
    (hobligationRedirect : ∀ node role filler,
      state.obligation role filler node →
        state.obligation role filler (redirect node))
    (source : UnravellingDomain state redirect slotAllowed root)
    (role : Role) (filler : Lit Concept)
    (hslot : ∀ target, state.edge role (redirect source.1) target →
      slotAllowed source.1 role target 0)
    (hobligation : state.obligation role filler source.1) :
    ∃ target,
      (state.unravelling redirect slotAllowed root).role role source target ∧
      (state.unravelling redirect slotAllowed root).satLit filler target ∧
      target ≠ source := by
  obtain ⟨targetNode, hedge, hlabel⟩ :=
    hwitness (redirect source.1) role filler
      (hobligationRedirect source.1 role filler hobligation)
  let target : UnravellingDomain state redirect slotAllowed root :=
    ⟨targetNode, UnravellingPath.step source.2 0 role hedge (hslot targetNode hedge)⟩
  have hrole : (state.unravelling redirect slotAllowed root).role
      role source target := by
    exact UnravellingDirectRole.step source.2 0 hedge (hslot targetNode hedge)
  exact ⟨target, hrole,
    state.unravelling_sat_label redirect slotAllowed root hclash target filler hlabel,
    hrole.ne⟩

theorem State.regularUnravelling_sat_label
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role)
    (hclash : state.ClashFree)
    (value : UnravellingDomain state redirect slotAllowed root)
    (lit : Lit Concept) (hlabel : state.label value.1 lit) :
    (state.regularUnravelling redirect slotAllowed root rules).satLit lit value := by
  exact state.unravelling_sat_label redirect slotAllowed root hclash
    value lit hlabel

theorem State.regularUnravelling_obligation_witness
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role)
    (hclash : state.ClashFree)
    (hwitness : state.WitnessComplete)
    (hobligationRedirect : ∀ node role filler,
      state.obligation role filler node →
        state.obligation role filler (redirect node))
    (source : UnravellingDomain state redirect slotAllowed root)
    (role : Role) (filler : Lit Concept)
    (hslot : ∀ target, state.edge role (redirect source.1) target →
      slotAllowed source.1 role target 0)
    (hobligation : state.obligation role filler source.1) :
    ∃ target,
      (state.regularUnravelling redirect slotAllowed root rules).role
        role source target ∧
      (state.regularUnravelling redirect slotAllowed root rules).satLit
        filler target ∧
      target ≠ source := by
  obtain ⟨target, hrole, hfiller, hne⟩ :=
    state.unravelling_obligation_witness redirect slotAllowed root hclash
      hwitness hobligationRedirect source role filler hslot hobligation
  exact ⟨target,
    state.regularUnravelling_direct redirect slotAllowed root rules hrole,
    hfiller, hne⟩

/-- Syntactic truth on regular paths. Unlike finite-graph `holdsAtom`, role
atoms use the full role closure generated by inclusions, inverses, chains, and
reflexivity. Existential atoms remain finite completion-graph obligations at
the path endpoint. -/
def State.RegularHoldsAtom
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role)
    (assignment : Variable → UnravellingDomain state redirect slotAllowed root) :
    Atom Variable Concept Role → Prop
  | .concept lit node => state.label (assignment node).1 lit
  | .role role source target =>
      UnravellingRole state redirect slotAllowed root rules role
        (assignment source) (assignment target)
  | .exists_ role filler node =>
      state.obligation role filler (assignment node).1
  | .eq left right => assignment left = assignment right

def State.RegularDischarges
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role)
    (clause : Clause Variable Concept Role) : Prop :=
  ∀ assignment,
    (∀ atom ∈ clause.body,
      state.RegularHoldsAtom redirect slotAllowed root rules assignment atom) →
    ∃ atom ∈ clause.head,
      state.RegularHoldsAtom redirect slotAllowed root rules assignment atom

def State.RegularSaturatedFor
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role)
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∀ clause ∈ ontology,
    state.RegularDischarges redirect slotAllowed root rules clause

theorem State.regularUnravelling_regularHoldsAtom
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role)
    (hclash : state.ClashFree)
    (hwitness : state.WitnessComplete)
    (hobligationRedirect : ∀ node role filler,
      state.obligation role filler node →
        state.obligation role filler (redirect node))
    (hslot : ∀ source role target,
      state.edge role (redirect source) target →
        slotAllowed source role target 0)
    (assignment : Variable → UnravellingDomain state redirect slotAllowed root)
    (atom : Atom Variable Concept Role)
    (hholds : state.RegularHoldsAtom redirect slotAllowed root rules
      assignment atom) :
    (state.regularUnravelling redirect slotAllowed root rules).satAtom
      assignment atom := by
  cases atom with
  | concept lit node =>
      exact state.regularUnravelling_sat_label redirect slotAllowed root rules
        hclash (assignment node) lit hholds
  | role role source target => exact hholds
  | exists_ role filler node =>
      obtain ⟨target, hrole, hfiller, _⟩ :=
        state.regularUnravelling_obligation_witness redirect slotAllowed root
          rules hclash hwitness hobligationRedirect (assignment node) role filler
          (hslot (assignment node).1 role) hholds
      exact ⟨target, hrole, hfiller⟩
  | eq left right => exact hholds

theorem State.regularUnravelling_body_holds
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role)
    (assignment : Variable → UnravellingDomain state redirect slotAllowed root)
    (atom : Atom Variable Concept Role)
    (hbodyAtom : BodyAtom atom)
    (hsat : (state.regularUnravelling redirect slotAllowed root rules).satAtom
      assignment atom) :
    state.RegularHoldsAtom redirect slotAllowed root rules assignment atom := by
  cases atom with
  | concept lit node =>
      rcases lit with ⟨concept, neg⟩
      cases neg with
      | false => exact hsat
      | true => contradiction
  | role role source target => exact hsat
  | exists_ role filler node => contradiction
  | eq left right => exact hsat

/-- A clash-free, witness-complete regular path saturation is a genuine model.
This is the unravelling analogue of `canonical_models_of_saturated`; its
saturation premise includes role matches introduced by the regular role
closure, which a finite one-round fold cannot in general see. -/
theorem regularUnravelling_models_of_saturated
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (rules : UnravellingRoleRules Role)
    (ontology : List (Clause Variable Concept Role))
    (hguarded : ∀ clause ∈ ontology, clause.GuardedBody)
    (hclash : state.ClashFree)
    (hwitness : state.WitnessComplete)
    (hobligationRedirect : ∀ node role filler,
      state.obligation role filler node →
        state.obligation role filler (redirect node))
    (hslot : ∀ source role target,
      state.edge role (redirect source) target →
        slotAllowed source role target 0)
    (hsaturated : state.RegularSaturatedFor redirect slotAllowed root rules
      ontology) :
    (state.regularUnravelling redirect slotAllowed root rules).models ontology := by
  intro clause hclause assignment hsemanticBody
  have hsyntacticBody : ∀ atom ∈ clause.body,
      state.RegularHoldsAtom redirect slotAllowed root rules assignment atom := by
    intro atom hatom
    exact state.regularUnravelling_body_holds redirect slotAllowed root rules
      assignment atom (hguarded clause hclause atom hatom)
      (hsemanticBody atom hatom)
  rcases hsaturated clause hclause assignment hsyntacticBody with
    ⟨atom, hatom, hholds⟩
  exact ⟨atom, hatom,
    state.regularUnravelling_regularHoldsAtom redirect slotAllowed root rules
      hclash hwitness hobligationRedirect hslot assignment atom hholds⟩

/-- Distinct witness slots denote distinct path-domain values, even if their
finite completion-graph targets coincide. -/
theorem State.unravelling_minimum_witnesses
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (hclash : state.ClashFree)
    (source : UnravellingDomain state redirect slotAllowed root)
    (role : Role) (filler : Lit Concept) (count : Nat)
    (witness : Fin count → Node)
    (hedge : ∀ index,
      state.edge role (redirect source.1) (witness index))
    (hslot : ∀ index,
      slotAllowed source.1 role (witness index) index.1)
    (hlabel : ∀ index, state.label (witness index) filler) :
    ∃ target : Fin count → UnravellingDomain state redirect slotAllowed root,
      Function.Injective target ∧
      ∀ index,
        (state.unravelling redirect slotAllowed root).role role source (target index) ∧
        (state.unravelling redirect slotAllowed root).satLit filler (target index) := by
  let target (index : Fin count) :
      UnravellingDomain state redirect slotAllowed root :=
    ⟨witness index,
      UnravellingPath.step source.2 index.1 role (hedge index) (hslot index)⟩
  refine ⟨target, ?_, ?_⟩
  · intro left right hequal
    have hslot := congrArg UnravellingDomain.lastSlot hequal
    simp [target, UnravellingDomain.lastSlot, UnravellingPath.lastSlot] at hslot
    exact Fin.ext hslot
  · intro index
    refine ⟨?_, state.unravelling_sat_label redirect slotAllowed root hclash
      (target index) filler (hlabel index)⟩
    exact UnravellingDirectRole.step source.2 index.1 (hedge index) (hslot index)

abbrev UnravellingDirectSuccessor
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (source : UnravellingDomain state redirect slotAllowed root) (role : Role) :=
  {target // UnravellingDirectRole state redirect slotAllowed root role source target}

def UnravellingDirectSuccessor.key
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root : Node}
    {source : UnravellingDomain state redirect slotAllowed root} {role : Role}
    (successor : UnravellingDirectSuccessor
      state redirect slotAllowed root source role) : Node × Nat := by
  exact (successor.1.1, successor.1.lastSlot.getD 0)

def UnravellingAuthorizedKey
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop)
    (source : Node) (role : Role) (key : Node × Nat) : Prop :=
  state.edge role (redirect source) key.1 ∧
    slotAllowed source role key.1 key.2

theorem UnravellingDirectSuccessor.key_authorized
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root : Node}
    {source : UnravellingDomain state redirect slotAllowed root} {role : Role}
    (successor : UnravellingDirectSuccessor
      state redirect slotAllowed root source role) :
    UnravellingAuthorizedKey state redirect slotAllowed source.1 role
      successor.key := by
  rcases successor with ⟨target, hedge⟩
  cases hedge
  exact ⟨‹state.edge _ _ _›, ‹slotAllowed _ _ _ _›⟩

/-- Direct semantic successors inject into their authorized finite
`(target-node, slot)` keys. Consequently an at-most checker only needs to bound
that finite key set; unravelling itself introduces no additional direct
successors. -/
theorem UnravellingDirectSuccessor.key_injective
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {root : Node}
    {source : UnravellingDomain state redirect slotAllowed root} {role : Role} :
    Function.Injective
      (UnravellingDirectSuccessor.key (Node := Node)
        (Concept := Concept) (Role := Role) :
        UnravellingDirectSuccessor state redirect slotAllowed root source role →
          Node × Nat) := by
  rintro ⟨left, hleft⟩ ⟨right, hright⟩ hkey
  cases hleft
  cases hright
  simp only [UnravellingDirectSuccessor.key, UnravellingDomain.lastSlot,
    UnravellingPath.lastSlot, Option.getD_some, Prod.mk.injEq] at hkey
  rcases hkey with ⟨rfl, rfl⟩
  rfl

/-- A finite bound on authorized successor keys is inherited by the direct
role successors of every path ending at that finite source node. -/
theorem State.unravelling_direct_hasAtMost
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (source : UnravellingDomain state redirect slotAllowed root)
    (role : Role) (bound : Nat)
    (hbound : HasAtMost bound
      (UnravellingAuthorizedKey state redirect slotAllowed source.1 role)) :
    HasAtMost bound
      (fun target => (state.unravelling redirect slotAllowed root).role
        role source target) := by
  intro hatLeast
  rcases hatLeast with ⟨witness, hinjective, hrole⟩
  let successor (index : Fin (bound + 1)) : UnravellingDirectSuccessor
      state redirect slotAllowed root source role :=
    ⟨witness index, hrole index⟩
  let keyed (index : Fin (bound + 1)) : Node × Nat :=
    UnravellingDirectSuccessor.key (successor index)
  apply hbound
  refine ⟨keyed, ?_, ?_⟩
  · intro left right hequal
    have hsuccessor :
        successor left = successor right :=
      UnravellingDirectSuccessor.key_injective (by
        simpa [keyed] using hequal)
    exact hinjective (congrArg Subtype.val hsuccessor)
  · intro index
    simpa [keyed] using
      UnravellingDirectSuccessor.key_authorized (successor index)

/-- Finite slot closure for one cardinality marker is exactly enough to make
the regular path interpretation satisfy that definition. Minimum definitions
provide authorized witnesses; maximum definitions bound all authorized keys.
-/
theorem State.unravelling_modelsCardinalityDef
    {Node : Type u} {Concept Role : Type}
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (hclash : state.ClashFree)
    (definition : CardinalityDef Concept Role)
    (hminimum : definition.kind = .minimum → ∀ node,
      state.label node (.pos definition.marker) →
      ∃ witness : Fin definition.bound → Node,
        (∀ index,
          state.edge definition.role (redirect node) (witness index)) ∧
        (∀ index,
          slotAllowed node definition.role (witness index) index.1) ∧
        (∀ index, state.label (witness index) (.pos definition.filler)))
    (hmaximum : definition.kind = .maximum → ∀ node,
      state.label node (.pos definition.marker) →
      HasAtMost definition.bound
        (UnravellingAuthorizedKey state redirect slotAllowed node
          definition.role)) :
    (state.unravelling redirect slotAllowed root).modelsCardinalityDef
      definition := by
  intro source hmarker
  cases hkind : definition.kind with
  | minimum =>
      obtain ⟨witness, hedge, hslot, hlabel⟩ :=
        hminimum hkind source.1 hmarker
      obtain ⟨target, hinjective, htarget⟩ :=
        state.unravelling_minimum_witnesses redirect slotAllowed root hclash
          source definition.role (.pos definition.filler) definition.bound
          witness hedge hslot hlabel
      refine ⟨target, hinjective, ?_⟩
      intro index
      rcases htarget index with ⟨hrole, hfiller⟩
      exact ⟨hrole, hfiller⟩
  | maximum =>
      have hdirect := state.unravelling_direct_hasAtMost
        redirect slotAllowed root source definition.role definition.bound
        (hmaximum hkind source.1 hmarker)
      intro hatLeast
      apply hdirect
      rcases hatLeast with ⟨witness, hinjective, hsuccessor⟩
      exact ⟨witness, hinjective, fun index => (hsuccessor index).1⟩

theorem State.unravelling_modelsCardinalityDefs
    {Node : Type u} {Concept Role : Type}
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (root : Node)
    (hclash : state.ClashFree)
    (definitions : List (CardinalityDef Concept Role))
    (hminimum : ∀ definition ∈ definitions,
      definition.kind = .minimum → ∀ node,
      state.label node (.pos definition.marker) →
      ∃ witness : Fin definition.bound → Node,
        (∀ index,
          state.edge definition.role (redirect node) (witness index)) ∧
        (∀ index,
          slotAllowed node definition.role (witness index) index.1) ∧
        (∀ index, state.label (witness index) (.pos definition.filler)))
    (hmaximum : ∀ definition ∈ definitions,
      definition.kind = .maximum → ∀ node,
      state.label node (.pos definition.marker) →
      HasAtMost definition.bound
        (UnravellingAuthorizedKey state redirect slotAllowed node
          definition.role)) :
    (state.unravelling redirect slotAllowed root).modelsCardinalityDefs
      definitions := by
  intro definition hdefinition
  exact state.unravelling_modelsCardinalityDef redirect slotAllowed root hclash
    definition (hminimum definition hdefinition) (hmaximum definition hdefinition)

#print axioms UnravellingDirectRole.target_depth
#print axioms UnravellingDirectRole.ne
#print axioms State.unravelling_sat_label
#print axioms State.unravelling_obligation_witness
#print axioms State.unravelling_minimum_witnesses
#print axioms UnravellingDirectSuccessor.key_injective
#print axioms State.unravelling_direct_hasAtMost
#print axioms State.unravelling_modelsCardinalityDef
#print axioms State.unravelling_modelsCardinalityDefs
#print axioms State.regularUnravelling_direct
#print axioms State.regularUnravelling_subRole
#print axioms State.regularUnravelling_inverseRole
#print axioms State.regularUnravelling_chain
#print axioms State.regularUnravelling_reflexive
#print axioms State.regularUnravelling_modelsCardinalityDef_of_direct
#print axioms State.regularUnravelling_modelsCardinalityDefs_of_direct
#print axioms State.regularUnravelling_sat_label
#print axioms State.regularUnravelling_obligation_witness
#print axioms State.regularUnravelling_regularHoldsAtom
#print axioms State.regularUnravelling_body_holds
#print axioms regularUnravelling_models_of_saturated

end ContextCalculus.Hypertableau
