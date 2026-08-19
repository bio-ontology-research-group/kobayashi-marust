import ContextCalculus.HypertableauCardinalityRefutation

/-!
# Equality states with explicit cardinality disequalities

Minimum restrictions allocate pairwise-distinct witnesses.  This wrapper keeps
that information as an `apart` relation instead of relying on a unique-name
assumption.  A realization must map every apart pair to different domain
elements.  Equality closure meeting an apart pair is therefore a certified
clash.
-/

namespace ContextCalculus.Hypertableau

structure DistinctEqState (Node Concept Role : Type) where
  base : EqState Node Concept Role
  apart : Node → Node → Prop

def DistinctEqState.RealizedBy (state : DistinctEqState Node Concept Role)
    (I : Interp Domain Concept Role) (value : Node → Domain) : Prop :=
  state.base.RealizedBy I value ∧
    ∀ left right, state.apart left right → value left ≠ value right

def DistinctEqState.RealizableWithCardinality
    (state : DistinctEqState Node Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role) (value : Node → Domain),
    I.models ontology ∧ I.modelsCardinalityDefs definitions ∧
      state.RealizedBy I value

def DistinctEqState.Fresh (state : DistinctEqState Node Concept Role)
    (target : Node) : Prop :=
  state.base.Fresh target ∧
    ∀ node, ¬state.apart target node ∧ ¬state.apart node target

def DistinctEqState.FreshFamily (state : DistinctEqState Node Concept Role)
    (targets : Fin count → Node) : Prop :=
  Function.Injective targets ∧ ∀ index, state.Fresh (targets index)

def DistinctEqState.merge (state : DistinctEqState Node Concept Role)
    (left right : Node) : DistinctEqState Node Concept Role where
  base := state.base.merge left right
  apart := state.apart

def DistinctEqState.materializeMinimum (state : DistinctEqState Node Concept Role)
    (source : Node) (targets : Fin count → Node) (role : Role) (filler : Concept) :
    DistinctEqState Node Concept Role where
  base := state.base.materializeMinimum source targets role filler
  apart left right := state.apart left right ∨
    ∃ first second, first ≠ second ∧
      left = targets first ∧ right = targets second

theorem DistinctEqState.equality_apart_clash
    (state : DistinctEqState Node Concept Role)
    (left right : Node) (hequal : state.base.equiv left right)
    (hapart : state.apart left right) :
    ¬state.RealizableWithCardinality ontology definitions := by
  rintro ⟨Domain, I, value, _, _, hrealized⟩
  exact hrealized.2 left right hapart (hrealized.1.2 left right hequal)

theorem DistinctEqState.merge_realized
    (state : DistinctEqState Node Concept Role)
    (I : Interp Domain Concept Role) (value : Node → Domain)
    (hrealized : state.RealizedBy I value) (left right : Node)
    (hequal : value left = value right) :
    (state.merge left right).RealizedBy I value := by
  exact ⟨state.base.merge_realized I value hrealized.1 left right hequal, hrealized.2⟩

theorem DistinctEqState.materializeMinimum_realized
    (state : DistinctEqState Node Concept Role)
    (I : Interp Domain Concept Role) (value : Node → Domain)
    (hrealized : state.RealizedBy I value)
    (source : Node) (targets : Fin count → Node) (role : Role) (filler marker : Concept)
    (hmarker : state.base.base.label source (.pos marker))
    (hfresh : state.FreshFamily targets)
    (witnesses : Fin count → Domain) (hinjective : Function.Injective witnesses)
    (hsuccessors : ∀ index, I.role role (value source) (witnesses index) ∧
      I.concept filler (witnesses index)) :
    ∃ value', (state.materializeMinimum source targets role filler).RealizedBy I value' := by
  rcases state.base.materializeMinimum_realized I value hrealized.1 source targets role
      filler marker hmarker ⟨hfresh.1, fun index => (hfresh.2 index).1⟩ witnesses
      hinjective hsuccessors with ⟨value', hbase, htargets, hold⟩
  refine ⟨value', hbase, ?_⟩
  intro left right hapart
  rcases hapart with hapart | ⟨first, second, hne, rfl, rfl⟩
  · have hleft : ∀ index, targets index ≠ left := by
      intro index heq
      exact ((hfresh.2 index).2 right).1 (heq.symm ▸ hapart)
    have hright : ∀ index, targets index ≠ right := by
      intro index heq
      exact ((hfresh.2 index).2 left).2 (heq.symm ▸ hapart)
    rw [hold left hleft, hold right hright]
    exact hrealized.2 left right hapart
  · exact fun hequal => hne (htargets hequal)

#print axioms DistinctEqState.equality_apart_clash
#print axioms DistinctEqState.merge_realized
#print axioms DistinctEqState.materializeMinimum_realized

end ContextCalculus.Hypertableau
