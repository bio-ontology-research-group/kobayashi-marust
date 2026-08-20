import ContextCalculus.HypertableauUnravelling

/-!
# Canonical roots for nominal-aware regular unravellings

Ordinary path unravelling creates a fresh domain value for every path. That is
correct for anonymous blocked witnesses, but it is not correct for nominals:
all paths reaching one nominal representative must denote one domain value.

This module defines the rooted-forest domain used by the equality-aware regular
model. Anonymous endpoints retain their full path identity. A designated anchor
endpoint is represented only by its canonical root. The central theorem
`AnchoredForestDomain.eq_root_of_anchor` states the singleton invariant without
assuming decidable equality of paths or quotienting proof terms.
-/

namespace ContextCalculus.Hypertableau

universe u v w

variable {Node : Type u} {Concept : Type v} {Role : Type w}

/-- A forest path may start at any finite root. Successor steps still read
outgoing edges from the redirected finite endpoint. -/
inductive ForestPath
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) : Node → Type (max u w) where
  | root (node : Node) : ForestPath state redirect slotAllowed node
  | step {source target : Node}
      (parent : ForestPath state redirect slotAllowed source)
      (slot : Nat) (role : Role)
      (edge : state.edge role (redirect source) target)
      (allowed : slotAllowed source role target slot) :
      ForestPath state redirect slotAllowed target

abbrev ForestDomain
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) :=
  Σ endpoint, ForestPath state redirect slotAllowed endpoint

/-- Canonical values retain arbitrary paths only for anonymous endpoints.
Every anchored endpoint must carry the root path. -/
def AnchoredForestDomain
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop) :=
  { value : ForestDomain state redirect slotAllowed //
      anchor value.1 → value.2 = ForestPath.root value.1 }

namespace AnchoredForestDomain

def endpoint
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {anchor : Node → Prop}
    (value : AnchoredForestDomain state redirect slotAllowed anchor) : Node :=
  value.1.1

def root
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    (node : Node) : AnchoredForestDomain state redirect slotAllowed anchor :=
  ⟨⟨node, ForestPath.root node⟩, fun _ => rfl⟩

/-- Every value whose endpoint is anchored is the unique canonical root for
that endpoint. This is the semantic singleton property required for nominals. -/
theorem eq_root_of_anchor
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {anchor : Node → Prop}
    (value : AnchoredForestDomain state redirect slotAllowed anchor)
    (hanchor : anchor value.endpoint) :
    value = root state redirect slotAllowed anchor value.endpoint := by
  rcases value with ⟨⟨endpoint, path⟩, canonical⟩
  have hpath : path = ForestPath.root endpoint := canonical hanchor
  subst path
  rfl

theorem eq_of_same_anchored_endpoint
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {anchor : Node → Prop}
    (left right : AnchoredForestDomain state redirect slotAllowed anchor)
    (hleft : anchor left.endpoint) (hendpoint : left.endpoint = right.endpoint) :
    left = right := by
  calc
    left = root state redirect slotAllowed anchor left.endpoint :=
      left.eq_root_of_anchor hleft
    _ = root state redirect slotAllowed anchor right.endpoint := by rw [hendpoint]
    _ = right := (right.eq_root_of_anchor (hendpoint ▸ hleft)).symm

/-- Extend an anonymous path normally, but redirect every edge into an anchor
to that anchor's canonical root. -/
def successor
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor]
    (source : AnchoredForestDomain state redirect slotAllowed anchor)
    (slot : Nat) (role : Role) (target : Node)
    (edge : state.edge role (redirect source.endpoint) target)
    (allowed : slotAllowed source.endpoint role target slot) :
    AnchoredForestDomain state redirect slotAllowed anchor :=
  if hanchor : anchor target then
    root state redirect slotAllowed anchor target
  else
    ⟨⟨target, ForestPath.step source.1.2 slot role edge allowed⟩,
      fun h => (hanchor h).elim⟩

@[simp] theorem endpoint_root
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    (node : Node) :
    (root state redirect slotAllowed anchor node).endpoint = node := rfl

@[simp] theorem endpoint_successor
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor]
    (source : AnchoredForestDomain state redirect slotAllowed anchor)
    (slot : Nat) (role : Role) (target : Node)
    (edge : state.edge role (redirect source.endpoint) target)
    (allowed : slotAllowed source.endpoint role target slot) :
    (successor state redirect slotAllowed anchor source slot role target edge allowed).endpoint =
      target := by
  simp only [successor, endpoint]
  split <;> rfl

theorem successor_eq_root_of_anchor
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor]
    (source : AnchoredForestDomain state redirect slotAllowed anchor)
    (slot : Nat) (role : Role) (target : Node)
    (edge : state.edge role (redirect source.endpoint) target)
    (allowed : slotAllowed source.endpoint role target slot)
    (hanchor : anchor target) :
    successor state redirect slotAllowed anchor source slot role target edge allowed =
      root state redirect slotAllowed anchor target := by
  simp [successor, hanchor]

/-- Concept interpretation for the future nominal-aware regular model.
Ordinary concepts are read from endpoint labels. A concept selected as a
nominal denotes exactly its selected canonical root. -/
def concept
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    (nominalRoot : Concept → Option Node) (name : Concept)
    (value : AnchoredForestDomain state redirect slotAllowed anchor) : Prop :=
  match nominalRoot name with
  | none => state.label value.endpoint (.pos name)
  | some node => value = root state redirect slotAllowed anchor node

theorem concept_nominal_iff
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    (nominalRoot : Concept → Option Node) (name : Concept) (node : Node)
    (hnominal : nominalRoot name = some node)
    (value : AnchoredForestDomain state redirect slotAllowed anchor) :
    concept state redirect slotAllowed anchor nominalRoot name value ↔
      value = root state redirect slotAllowed anchor node := by
  simp [concept, hnominal]

/-- Every selected nominal concept has a singleton extension, witnessed by its
canonical root. -/
theorem concept_nominal_singleton
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    (nominalRoot : Concept → Option Node) (name : Concept) (node : Node)
    (hnominal : nominalRoot name = some node) :
    ∃ unique : AnchoredForestDomain state redirect slotAllowed anchor,
      ∀ value, concept state redirect slotAllowed anchor nominalRoot name value ↔
        value = unique := by
  exact ⟨root state redirect slotAllowed anchor node,
    fun value => concept_nominal_iff state redirect slotAllowed anchor
      nominalRoot name node hnominal value⟩

/-- Direct forest edges use `successor`, so an edge entering an anchor lands on
the unique canonical root rather than creating another nominal copy. -/
inductive DirectRole
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] : Role →
      AnchoredForestDomain state redirect slotAllowed anchor →
      AnchoredForestDomain state redirect slotAllowed anchor → Prop where
  | step (source : AnchoredForestDomain state redirect slotAllowed anchor)
      (slot : Nat) (role : Role) (target : Node)
      (edge : state.edge role (redirect source.endpoint) target)
      (allowed : slotAllowed source.endpoint role target slot) :
      DirectRole state redirect slotAllowed anchor role source
        (successor state redirect slotAllowed anchor source slot role target edge allowed)

/-- Role closure over anchored direct edges. This is the same exact normalized
RBox closure used by the equality-free regular model. -/
inductive RoleClosure
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role) : Role →
      AnchoredForestDomain state redirect slotAllowed anchor →
      AnchoredForestDomain state redirect slotAllowed anchor → Prop where
  | direct {role source target}
      (edge : DirectRole state redirect slotAllowed anchor role source target) :
      RoleClosure state redirect slotAllowed anchor rules role source target
  | sub {premise conclusion source target}
      (rule : rules.subRole premise conclusion)
      (edge : RoleClosure state redirect slotAllowed anchor rules premise source target) :
      RoleClosure state redirect slotAllowed anchor rules conclusion source target
  | inverse {premise conclusion source target}
      (rule : rules.inverseRole premise conclusion)
      (edge : RoleClosure state redirect slotAllowed anchor rules premise source target) :
      RoleClosure state redirect slotAllowed anchor rules conclusion target source
  | chain {first second conclusion source middle target}
      (rule : rules.chain first second conclusion)
      (left : RoleClosure state redirect slotAllowed anchor rules first source middle)
      (right : RoleClosure state redirect slotAllowed anchor rules second middle target) :
      RoleClosure state redirect slotAllowed anchor rules conclusion source target
  | refl {role source} (rule : rules.reflexive role) :
      RoleClosure state redirect slotAllowed anchor rules role source source

theorem RoleClosure.endpoint
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {anchor : Node → Prop}
    [DecidablePred anchor] {rules : UnravellingRoleRules Role} {role : Role}
    {source target : AnchoredForestDomain state redirect slotAllowed anchor}
    (edge : RoleClosure state redirect slotAllowed anchor rules role source target) :
    EndpointRole state redirect rules role source.endpoint target.endpoint := by
  induction edge with
  | direct edge =>
      cases edge with
      | step source slot role target raw allowed =>
          simpa using (EndpointRole.direct raw)
  | sub rule edge ih => exact EndpointRole.sub rule ih
  | inverse rule edge ih => exact EndpointRole.inverse rule ih
  | chain rule left right ihLeft ihRight =>
      exact EndpointRole.chain rule ihLeft ihRight
  | refl rule => exact EndpointRole.refl rule

/-- The nominal-aware regular interpretation. -/
def interpretation
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node) :
    Interp (AnchoredForestDomain state redirect slotAllowed anchor) Concept Role where
  concept := concept state redirect slotAllowed anchor nominalRoot
  role := RoleClosure state redirect slotAllowed anchor rules

/-- Certificate-side coherence for nominal labels. Positive nominal labels
occur exactly at the selected root, negative labels exclude that root, and the
selected root is an anchor. -/
def NominalLabelCoherent
    (state : State Node Concept Role) (anchor : Node → Prop)
    (nominalRoot : Concept → Option Node) : Prop :=
  ∀ name root, nominalRoot name = some root →
    anchor root ∧
      (∀ node, state.label node (.pos name) ↔ node = root) ∧
      (∀ node, state.label node (.negated name) → node ≠ root)

def HoldsAtom
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (assignment : Variable → AnchoredForestDomain state redirect slotAllowed anchor) :
    Atom Variable Concept Role → Prop
  | .concept lit node => state.label (assignment node).endpoint lit
  | .role role source target =>
      RoleClosure state redirect slotAllowed anchor rules role
        (assignment source) (assignment target)
  | .exists_ role filler node =>
      state.obligation role filler (assignment node).endpoint
  | .eq left right => assignment left = assignment right

/-- Redirected witness completion is the finite premise required by a regular
model: obligations at an endpoint read outgoing witnesses from its blocker. -/
def RedirectWitnessComplete
    (state : State Node Concept Role) (redirect : Node → Node) : Prop :=
  ∀ node role filler, state.obligation role filler node →
    ∃ target, state.edge role (redirect node) target ∧ state.label target filler

def Discharges
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (clause : Clause Variable Concept Role) : Prop :=
  ∀ assignment,
    (∀ atom ∈ clause.body,
      HoldsAtom state redirect slotAllowed anchor rules assignment atom) →
    ∃ atom ∈ clause.head,
      HoldsAtom state redirect slotAllowed anchor rules assignment atom

def SaturatedFor
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∀ clause ∈ ontology,
    Discharges state redirect slotAllowed anchor rules clause

theorem interpretation_sat_label
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    (hclash : state.ClashFree)
    (hcoherent : NominalLabelCoherent state anchor nominalRoot)
    (value : AnchoredForestDomain state redirect slotAllowed anchor)
    (lit : Lit Concept) (hlabel : state.label value.endpoint lit) :
    (interpretation state redirect slotAllowed anchor rules nominalRoot).satLit lit value := by
  rcases lit with ⟨name, negated⟩
  cases hroot : nominalRoot name with
  | none =>
      cases negated with
      | false => simpa [Interp.satLit, interpretation, concept, hroot] using hlabel
      | true =>
          simp only [Interp.satLit, interpretation, concept, hroot]
          intro hpositive
          exact hclash value.endpoint name ⟨hpositive, hlabel⟩
  | some rootNode =>
      have coherent := hcoherent name rootNode hroot
      cases negated with
      | false =>
          have hendpoint : value.endpoint = rootNode :=
            (coherent.2.1 value.endpoint).mp hlabel
          have hanchor : anchor value.endpoint := hendpoint ▸ coherent.1
          have hvalue := value.eq_root_of_anchor hanchor
          simpa [Interp.satLit, interpretation, concept, hroot, hendpoint] using hvalue
      | true =>
          simp only [Interp.satLit, interpretation, concept, hroot]
          intro hvalue
          have hendpoint : value.endpoint = rootNode := by
            simpa using congrArg endpoint hvalue
          exact coherent.2.2 value.endpoint hlabel hendpoint

theorem interpretation_sat_holdsAtom
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    (hclash : state.ClashFree)
    (hcoherent : NominalLabelCoherent state anchor nominalRoot)
    (hwitness : RedirectWitnessComplete state redirect)
    (hslot : ∀ node role target, state.edge role (redirect node) target →
      slotAllowed node role target 0)
    (assignment : Variable → AnchoredForestDomain state redirect slotAllowed anchor)
    (atom : Atom Variable Concept Role)
    (hholds : HoldsAtom state redirect slotAllowed anchor rules assignment atom) :
    (interpretation state redirect slotAllowed anchor rules nominalRoot).satAtom
      assignment atom := by
  cases atom with
  | concept lit node =>
      exact interpretation_sat_label state redirect slotAllowed anchor rules
        nominalRoot hclash hcoherent (assignment node) lit hholds
  | role role source target => exact hholds
  | exists_ role filler node =>
      rcases hwitness (assignment node).endpoint role filler hholds with
        ⟨target, hedge, hlabel⟩
      let witness := successor state redirect slotAllowed anchor (assignment node)
        0 role target hedge (hslot (assignment node).endpoint role target hedge)
      refine ⟨witness, ?_, ?_⟩
      · exact RoleClosure.direct (.step (assignment node) 0 role target hedge
          (hslot (assignment node).endpoint role target hedge))
      · exact interpretation_sat_label state redirect slotAllowed anchor rules
          nominalRoot hclash hcoherent witness filler (by
            simpa [witness] using hlabel)
  | eq left right => exact hholds

theorem interpretation_body_holds
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    (hcoherent : NominalLabelCoherent state anchor nominalRoot)
    (assignment : Variable → AnchoredForestDomain state redirect slotAllowed anchor)
    (atom : Atom Variable Concept Role) (hbodyAtom : BodyAtom atom)
    (hsat : (interpretation state redirect slotAllowed anchor rules nominalRoot).satAtom
      assignment atom) :
    HoldsAtom state redirect slotAllowed anchor rules assignment atom := by
  cases atom with
  | concept lit node =>
      rcases lit with ⟨name, negated⟩
      cases negated with
      | true => contradiction
      | false =>
          cases hroot : nominalRoot name with
          | none =>
              simpa [Interp.satAtom, Interp.satLit, interpretation, concept, hroot]
                using hsat
          | some rootNode =>
              have hvalue : assignment node =
                  root state redirect slotAllowed anchor rootNode := by
                simpa [Interp.satAtom, Interp.satLit, interpretation, concept, hroot]
                  using hsat
              have hendpoint : (assignment node).endpoint = rootNode := by
                simpa using congrArg endpoint hvalue
              have coherent := hcoherent name rootNode hroot
              exact (coherent.2.1 (assignment node).endpoint).mpr hendpoint
  | role role source target => exact hsat
  | exists_ role filler node => contradiction
  | eq left right => exact hsat

theorem interpretation_models_of_saturated
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    (ontology : List (Clause Variable Concept Role))
    (hguarded : ∀ clause ∈ ontology, clause.GuardedBody)
    (hclash : state.ClashFree)
    (hcoherent : NominalLabelCoherent state anchor nominalRoot)
    (hwitness : RedirectWitnessComplete state redirect)
    (hslot : ∀ node role target, state.edge role (redirect node) target →
      slotAllowed node role target 0)
    (hsaturated : SaturatedFor state redirect slotAllowed anchor rules ontology) :
    (interpretation state redirect slotAllowed anchor rules nominalRoot).models ontology := by
  intro clause hclause assignment hbody
  have hfiniteBody : ∀ atom ∈ clause.body,
      HoldsAtom state redirect slotAllowed anchor rules assignment atom := by
    intro atom hatom
    exact interpretation_body_holds state redirect slotAllowed anchor rules
      nominalRoot hcoherent assignment atom (hguarded clause hclause atom hatom)
      (hbody atom hatom)
  rcases hsaturated clause hclause assignment hfiniteBody with
    ⟨atom, hatom, hholds⟩
  exact ⟨atom, hatom, interpretation_sat_holdsAtom state redirect slotAllowed
    anchor rules nominalRoot hclash hcoherent hwitness hslot assignment atom hholds⟩

/-- Every anchored atom match projects to the finite endpoint cover used by the
regular certificate checker. -/
theorem holdsAtom_cover
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (cover : Role → Node → Node → Prop)
    (hcover : EndpointRoleCovered state redirect rules cover)
    (assignment : Variable → AnchoredForestDomain state redirect slotAllowed anchor)
    (atom : Atom Variable Concept Role)
    (hholds : HoldsAtom state redirect slotAllowed anchor rules assignment atom) :
    state.CoverHoldsAtom cover (fun node => (assignment node).endpoint) atom := by
  cases atom with
  | concept => exact hholds
  | role role source target =>
      exact hcover role _ _ hholds.endpoint
  | exists_ => exact hholds
  | eq left right => exact congrArg endpoint hholds

/-- Concept and existential heads depend only on endpoints, so a finite cover
head lifts back to every anchored assignment with those endpoints. -/
theorem coverHoldsAtom_lift
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (cover : Role → Node → Node → Prop)
    (assignment : Variable → AnchoredForestDomain state redirect slotAllowed anchor)
    (atom : Atom Variable Concept Role) (hliftable : PathLiftableHead atom)
    (hholds : state.CoverHoldsAtom cover
      (fun node => (assignment node).endpoint) atom) :
    HoldsAtom state redirect slotAllowed anchor rules assignment atom := by
  cases atom with
  | concept => exact hholds
  | role => contradiction
  | exists_ => exact hholds
  | eq => contradiction

/-- Equality heads lift from endpoint equality when one side is constrained by
a positive nominal body atom. Nominal coherence then proves that endpoint is
an anchor, where endpoint equality implies equality of anchored values. -/
def AnchoredHeadLiftable
    (nominalRoot : Concept → Option Node)
    (clause : Clause Variable Concept Role) :
    Atom Variable Concept Role → Prop
  | .concept .. => True
  | .exists_ .. => True
  | .role .. => False
  | .eq left right =>
      left = right ∨
      (∃ name root, nominalRoot name = some root ∧
        Atom.concept (.pos name) left ∈ clause.body) ∨
      (∃ name root, nominalRoot name = some root ∧
        Atom.concept (.pos name) right ∈ clause.body)

theorem coverHoldsAtom_lift_anchored
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    (hcoherent : NominalLabelCoherent state anchor nominalRoot)
    (cover : Role → Node → Node → Prop)
    (clause : Clause Variable Concept Role)
    (assignment : Variable → AnchoredForestDomain state redirect slotAllowed anchor)
    (hbody : ∀ atom ∈ clause.body,
      HoldsAtom state redirect slotAllowed anchor rules assignment atom)
    (atom : Atom Variable Concept Role)
    (hliftable : AnchoredHeadLiftable nominalRoot clause atom)
    (hholds : state.CoverHoldsAtom cover
      (fun node => (assignment node).endpoint) atom) :
    HoldsAtom state redirect slotAllowed anchor rules assignment atom := by
  cases atom with
  | concept => exact hholds
  | role => contradiction
  | exists_ => exact hholds
  | eq left right =>
      rcases hliftable with heq | hleft | hright
      · subst right
        rfl
      · rcases hleft with ⟨name, rootNode, hroot, hguard⟩
        have hlabel := hbody (.concept (.pos name) left) hguard
        have hanchor : anchor (assignment left).endpoint := by
          have hc := hcoherent name rootNode hroot
          exact ((hc.2.1 _).mp hlabel) ▸ hc.1
        exact eq_of_same_anchored_endpoint (assignment left) (assignment right)
          hanchor hholds
      · rcases hright with ⟨name, rootNode, hroot, hguard⟩
        have hlabel := hbody (.concept (.pos name) right) hguard
        have hanchor : anchor (assignment right).endpoint := by
          have hc := hcoherent name rootNode hroot
          exact ((hc.2.1 _).mp hlabel) ▸ hc.1
        exact (eq_of_same_anchored_endpoint (assignment right) (assignment left)
          hanchor hholds.symm).symm

theorem discharges_of_cover_anchored
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    (hcoherent : NominalLabelCoherent state anchor nominalRoot)
    (cover : Role → Node → Node → Prop)
    (hcover : EndpointRoleCovered state redirect rules cover)
    (clause : Clause Variable Concept Role)
    (hheads : ∀ atom ∈ clause.head, AnchoredHeadLiftable nominalRoot clause atom)
    (hdischarges : state.CoverDischarges cover clause) :
    Discharges state redirect slotAllowed anchor rules clause := by
  intro assignment hbody
  have hcoverBody : ∀ atom ∈ clause.body,
      state.CoverHoldsAtom cover (fun node => (assignment node).endpoint) atom := by
    intro atom hatom
    exact holdsAtom_cover state redirect slotAllowed anchor rules cover hcover
      assignment atom (hbody atom hatom)
  rcases hdischarges (fun node => (assignment node).endpoint) hcoverBody with
    ⟨atom, hatom, hholds⟩
  exact ⟨atom, hatom, coverHoldsAtom_lift_anchored state redirect slotAllowed
    anchor rules nominalRoot hcoherent cover clause assignment hbody atom
    (hheads atom hatom) hholds⟩

theorem saturatedFor_of_cover_anchored
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    (hcoherent : NominalLabelCoherent state anchor nominalRoot)
    (cover : Role → Node → Node → Prop)
    (hcover : EndpointRoleCovered state redirect rules cover)
    (ontology : List (Clause Variable Concept Role))
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head,
      AnchoredHeadLiftable nominalRoot clause atom)
    (hdischarges : ∀ clause ∈ ontology,
      state.CoverDischarges cover clause) :
    SaturatedFor state redirect slotAllowed anchor rules ontology := by
  intro clause hclause
  exact discharges_of_cover_anchored state redirect slotAllowed anchor rules
    nominalRoot hcoherent cover hcover clause (hheads clause hclause)
    (hdischarges clause hclause)

theorem discharges_of_cover
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (cover : Role → Node → Node → Prop)
    (hcover : EndpointRoleCovered state redirect rules cover)
    (clause : Clause Variable Concept Role)
    (hheads : ∀ atom ∈ clause.head, PathLiftableHead atom)
    (hdischarges : state.CoverDischarges cover clause) :
    Discharges state redirect slotAllowed anchor rules clause := by
  intro assignment hbody
  have hcoverBody : ∀ atom ∈ clause.body,
      state.CoverHoldsAtom cover (fun node => (assignment node).endpoint) atom := by
    intro atom hatom
    exact holdsAtom_cover state redirect slotAllowed anchor rules cover hcover
      assignment atom (hbody atom hatom)
  rcases hdischarges (fun node => (assignment node).endpoint) hcoverBody with
    ⟨atom, hatom, hholds⟩
  exact ⟨atom, hatom, coverHoldsAtom_lift state redirect slotAllowed anchor rules
    cover assignment atom (hheads atom hatom) hholds⟩

theorem saturatedFor_of_cover
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (cover : Role → Node → Node → Prop)
    (hcover : EndpointRoleCovered state redirect rules cover)
    (ontology : List (Clause Variable Concept Role))
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head,
      PathLiftableHead atom)
    (hdischarges : ∀ clause ∈ ontology,
      state.CoverDischarges cover clause) :
    SaturatedFor state redirect slotAllowed anchor rules ontology := by
  intro clause hclause
  exact discharges_of_cover state redirect slotAllowed anchor rules cover hcover
    clause (hheads clause hclause) (hdischarges clause hclause)

theorem anchoredRoleClause_models
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    (rule : NormalizedRoleClause Variable Role)
    (hauthorized : rule.Authorized rules) :
    (interpretation state redirect slotAllowed anchor rules nominalRoot).modelsClause
      (rule.toClause (Concept := Concept)) := by
  intro assignment hbody
  cases rule with
  | subRole premise conclusion source target =>
      refine ⟨.role conclusion source target, by simp [NormalizedRoleClause.toClause], ?_⟩
      exact RoleClosure.sub hauthorized
        (hbody (.role premise source target) (by simp [NormalizedRoleClause.toClause]))
  | inverseRole premise conclusion source target =>
      refine ⟨.role conclusion target source, by simp [NormalizedRoleClause.toClause], ?_⟩
      exact RoleClosure.inverse hauthorized
        (hbody (.role premise source target) (by simp [NormalizedRoleClause.toClause]))
  | chain first second conclusion source middle target =>
      refine ⟨.role conclusion source target, by simp [NormalizedRoleClause.toClause], ?_⟩
      exact RoleClosure.chain hauthorized
        (hbody (.role first source middle) (by simp [NormalizedRoleClause.toClause]))
        (hbody (.role second middle target) (by simp [NormalizedRoleClause.toClause]))
  | reflexive role source =>
      refine ⟨.role role source source, by simp [NormalizedRoleClause.toClause], ?_⟩
      exact RoleClosure.refl hauthorized

/-- The existing finite regular certificate proves both partitions of the
nominal-aware model: normalized RBox clauses by role closure and residual
clauses by endpoint-cover discharge. -/
theorem interpretation_models_partition_of_cover
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    (cover : Role → Node → Node → Prop)
    (roleClauses : List (NormalizedRoleClause Variable Role))
    (residual : List (Clause Variable Concept Role))
    (hauthorized : ∀ rule ∈ roleClauses, rule.Authorized rules)
    (hguarded : ∀ clause ∈ residual, clause.GuardedBody)
    (hheads : ∀ clause ∈ residual, ∀ atom ∈ clause.head, PathLiftableHead atom)
    (hclash : state.ClashFree)
    (hcoherent : NominalLabelCoherent state anchor nominalRoot)
    (hwitness : RedirectWitnessComplete state redirect)
    (hslot : ∀ node role target, state.edge role (redirect node) target →
      slotAllowed node role target 0)
    (hcover : EndpointRoleCovered state redirect rules cover)
    (hdischarges : ∀ clause ∈ residual, state.CoverDischarges cover clause) :
    (interpretation state redirect slotAllowed anchor rules nominalRoot).models
      (roleClauses.map (NormalizedRoleClause.toClause (Concept := Concept)) ++
        residual) := by
  intro clause hclause
  rcases List.mem_append.mp hclause with hrole | hresidual
  · simp only [List.mem_map] at hrole
    obtain ⟨rule, hrule, rfl⟩ := hrole
    exact anchoredRoleClause_models state redirect slotAllowed anchor rules
      nominalRoot rule (hauthorized rule hrule)
  · exact interpretation_models_of_saturated state redirect slotAllowed anchor
      rules nominalRoot residual hguarded hclash hcoherent hwitness hslot
      (saturatedFor_of_cover state redirect slotAllowed anchor rules cover hcover
        residual hheads hdischarges) clause hresidual

/-- Nominal-aware partition theorem that additionally admits equality heads
guarded by a positive nominal body atom. -/
theorem interpretation_models_partition_of_cover_anchored
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    (cover : Role → Node → Node → Prop)
    (roleClauses : List (NormalizedRoleClause Variable Role))
    (residual : List (Clause Variable Concept Role))
    (hauthorized : ∀ rule ∈ roleClauses, rule.Authorized rules)
    (hguarded : ∀ clause ∈ residual, clause.GuardedBody)
    (hheads : ∀ clause ∈ residual, ∀ atom ∈ clause.head,
      AnchoredHeadLiftable nominalRoot clause atom)
    (hclash : state.ClashFree)
    (hcoherent : NominalLabelCoherent state anchor nominalRoot)
    (hwitness : RedirectWitnessComplete state redirect)
    (hslot : ∀ node role target, state.edge role (redirect node) target →
      slotAllowed node role target 0)
    (hcover : EndpointRoleCovered state redirect rules cover)
    (hdischarges : ∀ clause ∈ residual, state.CoverDischarges cover clause) :
    (interpretation state redirect slotAllowed anchor rules nominalRoot).models
      (roleClauses.map (NormalizedRoleClause.toClause (Concept := Concept)) ++
        residual) := by
  intro clause hclause
  rcases List.mem_append.mp hclause with hrole | hresidual
  · simp only [List.mem_map] at hrole
    obtain ⟨rule, hrule, rfl⟩ := hrole
    exact anchoredRoleClause_models state redirect slotAllowed anchor rules
      nominalRoot rule (hauthorized rule hrule)
  · exact interpretation_models_of_saturated state redirect slotAllowed anchor
      rules nominalRoot residual hguarded hclash hcoherent hwitness hslot
      (saturatedFor_of_cover_anchored state redirect slotAllowed anchor rules
        nominalRoot hcoherent cover hcover residual hheads hdischarges)
      clause hresidual

theorem interpretation_direct
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    {role : Role} {source target : AnchoredForestDomain state redirect slotAllowed anchor}
    (edge : DirectRole state redirect slotAllowed anchor role source target) :
    (interpretation state redirect slotAllowed anchor rules nominalRoot).role
      role source target :=
  RoleClosure.direct edge

theorem interpretation_witness
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    (source : AnchoredForestDomain state redirect slotAllowed anchor)
    (slot : Nat) (role : Role) (target : Node)
    (edge : state.edge role (redirect source.endpoint) target)
    (allowed : slotAllowed source.endpoint role target slot) :
    ∃ witness : AnchoredForestDomain state redirect slotAllowed anchor,
      (interpretation state redirect slotAllowed anchor rules nominalRoot).role
        role source witness ∧ witness.endpoint = target := by
  let witness := successor state redirect slotAllowed anchor source slot role target edge allowed
  exact ⟨witness, RoleClosure.direct (.step source slot role target edge allowed),
    endpoint_successor state redirect slotAllowed anchor source slot role target edge allowed⟩

theorem interpretation_anchor_witness
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    (source : AnchoredForestDomain state redirect slotAllowed anchor)
    (slot : Nat) (role : Role) (target : Node)
    (edge : state.edge role (redirect source.endpoint) target)
    (allowed : slotAllowed source.endpoint role target slot)
    (hanchor : anchor target) :
    (interpretation state redirect slotAllowed anchor rules nominalRoot).role role source
      (root state redirect slotAllowed anchor target) := by
  rw [← successor_eq_root_of_anchor state redirect slotAllowed anchor source slot
    role target edge allowed hanchor]
  exact RoleClosure.direct (.step source slot role target edge allowed)

theorem interpretation_subRole
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    {premise conclusion : Role} (rule : rules.subRole premise conclusion) :
    ∀ source target,
      (interpretation state redirect slotAllowed anchor rules nominalRoot).role
        premise source target →
      (interpretation state redirect slotAllowed anchor rules nominalRoot).role
        conclusion source target :=
  fun _ _ edge => RoleClosure.sub rule edge

theorem interpretation_inverseRole
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    {premise conclusion : Role} (rule : rules.inverseRole premise conclusion) :
    ∀ source target,
      (interpretation state redirect slotAllowed anchor rules nominalRoot).role
        premise source target →
      (interpretation state redirect slotAllowed anchor rules nominalRoot).role
        conclusion target source :=
  fun _ _ edge => RoleClosure.inverse rule edge

theorem interpretation_chain
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    {first second conclusion : Role} (rule : rules.chain first second conclusion) :
    ∀ source middle target,
      (interpretation state redirect slotAllowed anchor rules nominalRoot).role
        first source middle →
      (interpretation state redirect slotAllowed anchor rules nominalRoot).role
        second middle target →
      (interpretation state redirect slotAllowed anchor rules nominalRoot).role
        conclusion source target :=
  fun _ _ _ left right => RoleClosure.chain rule left right

theorem interpretation_reflexive
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    {role : Role} (rule : rules.reflexive role) :
    ∀ source, (interpretation state redirect slotAllowed anchor rules nominalRoot).role
      role source source :=
  fun _ => RoleClosure.refl rule

theorem interpretation_nominal_singleton
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node) (name : Concept) (node : Node)
    (hnominal : nominalRoot name = some node) :
    ∃ unique : AnchoredForestDomain state redirect slotAllowed anchor,
      ∀ value,
        (interpretation state redirect slotAllowed anchor rules nominalRoot).concept
          name value ↔ value = unique :=
  concept_nominal_singleton state redirect slotAllowed anchor nominalRoot
    name node hnominal

#print axioms eq_root_of_anchor
#print axioms eq_of_same_anchored_endpoint
#print axioms successor_eq_root_of_anchor
#print axioms concept_nominal_singleton
#print axioms interpretation_direct
#print axioms interpretation_sat_label
#print axioms RoleClosure.endpoint
#print axioms interpretation_sat_holdsAtom
#print axioms interpretation_body_holds
#print axioms interpretation_models_of_saturated
#print axioms interpretation_witness
#print axioms interpretation_anchor_witness
#print axioms interpretation_subRole
#print axioms interpretation_inverseRole
#print axioms interpretation_chain
#print axioms interpretation_reflexive
#print axioms interpretation_nominal_singleton

end AnchoredForestDomain

end ContextCalculus.Hypertableau
