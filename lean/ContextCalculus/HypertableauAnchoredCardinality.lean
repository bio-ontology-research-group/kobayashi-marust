import ContextCalculus.HypertableauAnchoredUnravelling
import ContextCalculus.HypertableauCardinality

/-!
# Cardinality semantics for nominal-anchored HT models

Anchoring collapses every path ending at a nominal node to one canonical root.
Minimum witnesses therefore need one additional premise: two selected witness
indices may target the same finite node only when that node is not anchored.
Anonymous repeated targets remain distinct because their path slots differ.
-/

namespace ContextCalculus.Hypertableau
namespace AnchoredForestDomain

def AnchorSafeWitnesses
    (anchor : Node → Prop) (witness : Fin count → Node) : Prop :=
  ∀ left right, anchor (witness left) → witness left = witness right → left = right

private def ForestPath.lastSlot? :
    {node : Node} → ForestPath state redirect slotAllowed node → Option Nat
  | _, .root _ => none
  | _, .step _ slot _ _ _ => some slot

private theorem ForestPath.lastSlot?_successor_of_not_anchor
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor]
    (source : AnchoredForestDomain state redirect slotAllowed anchor)
    (slot : Nat) (role : Role) (target : Node)
    (edge : state.edge role (redirect source.endpoint) target)
    (allowed : slotAllowed source.endpoint role target slot)
    (hanchor : ¬anchor target) :
    ForestPath.lastSlot?
      (successor state redirect slotAllowed anchor source slot role target edge allowed).1.2 =
        some slot := by
  unfold successor
  rw [dif_neg hanchor]
  rfl

/-- Selected minimum witnesses remain distinct in the anchored forest. Paths
to anonymous endpoints are distinguished by their slot index; paths to an
anchor are distinct only when their finite endpoints are distinct. -/
theorem interpretation_minimum_witnesses
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    (hclash : state.ClashFree)
    (hcoherent : NominalLabelCoherent state anchor nominalRoot)
    (source : AnchoredForestDomain state redirect slotAllowed anchor)
    (role : Role) (filler : Lit Concept) (count : Nat)
    (witness : Fin count → Node)
    (hedge : ∀ index,
      state.edge role (redirect source.endpoint) (witness index))
    (hslot : ∀ index,
      slotAllowed source.endpoint role (witness index) index.1)
    (hlabel : ∀ index, state.label (witness index) filler)
    (hsafe : AnchorSafeWitnesses anchor witness) :
    ∃ target : Fin count → AnchoredForestDomain state redirect slotAllowed anchor,
      Function.Injective target ∧
      ∀ index,
        (interpretation state redirect slotAllowed anchor rules nominalRoot).role
          role source (target index) ∧
        (interpretation state redirect slotAllowed anchor rules nominalRoot).satLit
          filler (target index) := by
  let target (index : Fin count) :=
    successor state redirect slotAllowed anchor source index.1 role
      (witness index) (hedge index) (hslot index)
  refine ⟨target, ?_, ?_⟩
  · intro left right hequal
    have hendpoint : witness left = witness right := by
      simpa [target] using congrArg endpoint hequal
    by_cases hanchor : anchor (witness left)
    · exact hsafe left right hanchor hendpoint
    · have hpath := congrArg (fun value => ForestPath.lastSlot? value.1.2) hequal
      have hanchorRight : ¬anchor (witness right) := by
        simpa [hendpoint] using hanchor
      have hleft : ForestPath.lastSlot? (target left).1.2 = some left.1 := by
        dsimp [target]
        exact ForestPath.lastSlot?_successor_of_not_anchor state redirect slotAllowed
          anchor source left.1 role (witness left) (hedge left) (hslot left) hanchor
      have hright : ForestPath.lastSlot? (target right).1.2 = some right.1 := by
        dsimp [target]
        exact ForestPath.lastSlot?_successor_of_not_anchor state redirect slotAllowed
          anchor source right.1 role (witness right) (hedge right) (hslot right)
            hanchorRight
      change ForestPath.lastSlot? (target left).1.2 =
        ForestPath.lastSlot? (target right).1.2 at hpath
      rw [hleft, hright] at hpath
      exact Fin.ext (Option.some.inj hpath)
  · intro index
    refine ⟨RoleClosure.direct (.step source index.1 role (witness index)
      (hedge index) (hslot index)), ?_⟩
    apply interpretation_sat_label state redirect slotAllowed anchor rules
      nominalRoot hclash hcoherent (target index) filler
    simpa [target] using hlabel index

/-- Satisfaction of a positive concept in a nominal-coherent anchored model
always reflects a positive label at the finite endpoint. -/
theorem concept_imp_endpoint_label
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    (nominalRoot : Concept → Option Node)
    (hcoherent : NominalLabelCoherent state anchor nominalRoot)
    (value : AnchoredForestDomain state redirect slotAllowed anchor)
    (name : Concept)
    (hconcept : concept state redirect slotAllowed anchor nominalRoot name value) :
    state.label value.endpoint (.pos name) := by
  cases hroot : nominalRoot name with
  | none => simpa [concept, hroot] using hconcept
  | some rootNode =>
      have hvalue : value = root state redirect slotAllowed anchor rootNode := by
        simpa [concept, hroot] using hconcept
      have hlabel := (hcoherent name rootNode hroot).2.1 rootNode
      rw [hvalue]
      exact hlabel.mpr rfl

def AuthorizedTarget
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {anchor : Node → Prop}
    [DecidablePred anchor]
    {source : AnchoredForestDomain state redirect slotAllowed anchor} {role : Role}
    (target : AnchoredForestDomain state redirect slotAllowed anchor)
    (key : Node × Nat) : Prop :=
  ∃ (edge : state.edge role (redirect source.endpoint) key.1)
      (allowed : slotAllowed source.endpoint role key.1 key.2),
    target = successor state redirect slotAllowed anchor source key.2 role key.1
      edge allowed

theorem DirectRole.exists_authorizedTarget
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {anchor : Node → Prop}
    [DecidablePred anchor]
    {source target : AnchoredForestDomain state redirect slotAllowed anchor} {role : Role}
    (successorEdge : DirectRole state redirect slotAllowed anchor role source target) :
    ∃ key, AuthorizedTarget (source := source) (role := role) target key := by
  cases successorEdge with
  | step source slot role finiteTarget raw allowed =>
      exact ⟨(finiteTarget, slot), raw, allowed, rfl⟩

theorem AuthorizedTarget.target_eq
    {state : State Node Concept Role} {redirect : Node → Node}
    {slotAllowed : Node → Role → Node → Nat → Prop} {anchor : Node → Prop}
    [DecidablePred anchor]
    {source : AnchoredForestDomain state redirect slotAllowed anchor} {role : Role}
    {left right : AnchoredForestDomain state redirect slotAllowed anchor}
    {key : Node × Nat}
    (hleft : AuthorizedTarget (source := source) (role := role) left key)
    (hright : AuthorizedTarget (source := source) (role := role) right key) :
    left = right := by
  rcases hleft with ⟨leftEdge, leftAllowed, hleft⟩
  rcases hright with ⟨rightEdge, rightAllowed, hright⟩
  rw [hleft, hright]

/-- A finite authorized-key upper bound also bounds anchored direct
successors. Nominal collapse can only identify successors, never create an
additional authorized key. -/
theorem interpretation_direct_hasAtMost
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor]
    (source : AnchoredForestDomain state redirect slotAllowed anchor)
    (role : Role) (bound : Nat)
    (hbound : HasAtMost bound
      (UnravellingAuthorizedKey state redirect slotAllowed source.endpoint role)) :
    HasAtMost bound (fun target =>
      DirectRole state redirect slotAllowed anchor role source target) := by
  intro hatLeast
  rcases hatLeast with ⟨witness, hinjective, hrole⟩
  choose keyed hkeyed using fun index =>
    DirectRole.exists_authorizedTarget (hrole index)
  apply hbound
  refine ⟨keyed, ?_, ?_⟩
  · intro left right hequal
    apply hinjective
    apply AuthorizedTarget.target_eq (hkeyed left)
    exact hequal.symm ▸ hkeyed right
  · intro index
    rcases hkeyed index with ⟨edge, allowed, _⟩
    exact ⟨edge, allowed⟩

def AnchoredSimpleExact
    (rules : UnravellingRoleRules Role)
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (role : Role) : Prop :=
  ∀ source target,
    RoleClosure state redirect slotAllowed anchor rules role source target →
      DirectRole state redirect slotAllowed anchor role source target

theorem anchoredSimpleExact_of_syntacticallySimple
    (rules : UnravellingRoleRules Role)
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (role : Role) (hsimple : rules.SyntacticallySimple role) :
    AnchoredSimpleExact rules state redirect slotAllowed anchor role := by
  intro source target edge
  cases edge with
  | direct edge => exact edge
  | sub rule edge => exact False.elim (hsimple.1 _ rule)
  | inverse rule edge => exact False.elim (hsimple.2.1 _ rule)
  | chain rule left right => exact False.elim (hsimple.2.2.1 _ _ rule)
  | refl rule => exact False.elim (hsimple.2.2.2 rule)

theorem interpretation_modelsCardinalityDef
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    (hclash : state.ClashFree)
    (hcoherent : NominalLabelCoherent state anchor nominalRoot)
    (definition : CardinalityDef Concept Role)
    (hminimum : definition.kind = .minimum → ∀ node,
      state.label node (.pos definition.marker) →
      ∃ witness : Fin definition.bound → Node,
        (∀ index, state.edge definition.role (redirect node) (witness index)) ∧
        (∀ index, slotAllowed node definition.role (witness index) index.1) ∧
        (∀ index, state.label (witness index) (.pos definition.filler)) ∧
        AnchorSafeWitnesses anchor witness)
    (hmaximum : definition.kind = .maximum → ∀ node,
      state.label node (.pos definition.marker) →
      HasAtMost definition.bound
        (UnravellingAuthorizedKey state redirect slotAllowed node definition.role))
    (hsimple : definition.kind = .maximum →
      rules.SyntacticallySimple definition.role) :
    (interpretation state redirect slotAllowed anchor rules nominalRoot).modelsCardinalityDef
      definition := by
  intro source hmarker
  have hmarkerLabel : state.label source.endpoint (.pos definition.marker) :=
    concept_imp_endpoint_label state redirect slotAllowed anchor nominalRoot
      hcoherent source definition.marker hmarker
  cases hkind : definition.kind with
  | minimum =>
      obtain ⟨witness, hedge, hslot, hlabel, hsafe⟩ :=
        hminimum hkind source.endpoint hmarkerLabel
      obtain ⟨target, hinjective, htarget⟩ :=
        interpretation_minimum_witnesses state redirect slotAllowed anchor rules
          nominalRoot hclash hcoherent source definition.role
          (.pos definition.filler) definition.bound witness hedge hslot hlabel hsafe
      refine ⟨target, hinjective, ?_⟩
      intro index
      rcases htarget index with ⟨hrole, hfiller⟩
      exact ⟨hrole, hfiller⟩
  | maximum =>
      have hdirect := interpretation_direct_hasAtMost state redirect slotAllowed
        anchor source definition.role definition.bound
        (hmaximum hkind source.endpoint hmarkerLabel)
      intro hatLeast
      apply hdirect
      rcases hatLeast with ⟨witness, hinjective, hsuccessor⟩
      refine ⟨witness, hinjective, ?_⟩
      intro index
      exact anchoredSimpleExact_of_syntacticallySimple rules state redirect
        slotAllowed anchor definition.role (hsimple hkind) source (witness index)
          (hsuccessor index).1

theorem interpretation_modelsCardinalityDefs
    (state : State Node Concept Role) (redirect : Node → Node)
    (slotAllowed : Node → Role → Node → Nat → Prop) (anchor : Node → Prop)
    [DecidablePred anchor] (rules : UnravellingRoleRules Role)
    (nominalRoot : Concept → Option Node)
    (hclash : state.ClashFree)
    (hcoherent : NominalLabelCoherent state anchor nominalRoot)
    (definitions : List (CardinalityDef Concept Role))
    (hminimum : ∀ definition ∈ definitions,
      definition.kind = .minimum → ∀ node,
      state.label node (.pos definition.marker) →
      ∃ witness : Fin definition.bound → Node,
        (∀ index, state.edge definition.role (redirect node) (witness index)) ∧
        (∀ index, slotAllowed node definition.role (witness index) index.1) ∧
        (∀ index, state.label (witness index) (.pos definition.filler)) ∧
        AnchorSafeWitnesses anchor witness)
    (hmaximum : ∀ definition ∈ definitions,
      definition.kind = .maximum → ∀ node,
      state.label node (.pos definition.marker) →
      HasAtMost definition.bound
        (UnravellingAuthorizedKey state redirect slotAllowed node definition.role))
    (hsimple : ∀ definition ∈ definitions,
      definition.kind = .maximum → rules.SyntacticallySimple definition.role) :
    (interpretation state redirect slotAllowed anchor rules nominalRoot).modelsCardinalityDefs
      definitions := by
  intro definition hdefinition
  exact interpretation_modelsCardinalityDef state redirect slotAllowed anchor rules
    nominalRoot hclash hcoherent definition (hminimum definition hdefinition)
      (hmaximum definition hdefinition) (hsimple definition hdefinition)

#print axioms interpretation_minimum_witnesses
#print axioms concept_imp_endpoint_label
#print axioms DirectRole.exists_authorizedTarget
#print axioms interpretation_direct_hasAtMost
#print axioms anchoredSimpleExact_of_syntacticallySimple
#print axioms interpretation_modelsCardinalityDef
#print axioms interpretation_modelsCardinalityDefs

end AnchoredForestDomain
end ContextCalculus.Hypertableau
