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

#print axioms interpretation_minimum_witnesses

end AnchoredForestDomain
end ContextCalculus.Hypertableau
