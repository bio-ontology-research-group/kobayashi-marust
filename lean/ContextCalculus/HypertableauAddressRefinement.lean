import ContextCalculus.HypertableauRuntimeSearch
import ContextCalculus.HypertableauFrontierWire

/-!
# Executable rooted-address refinement checker

This module checks the semantic correspondence between a finite HT state and
the rooted witness addresses reconstructed from KM's predecessor metadata.
The check is stronger than address-frontier uniqueness: every occupied
canonical existential slot must carry the exact role edge and filler label.
-/

namespace ContextCalculus.Hypertableau

/-- A decidable finite presentation of `State.RootedAddressRefines`. The
dependent depth proof is selected by the `if`, avoiding an existential over
proof terms while retaining exactly the same proposition. -/
def State.RootedAddressRefinesDirect
    {Root Node Concept Role : Type}
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role)
    (address : Node → WitnessAddress Root Concept Role) : Prop :=
  Function.Injective address ∧
  ∀ source role filler, state.obligation role filler source →
    if hdepth : (address source).2.1.length <
        Fintype.card (RoleBlockingSignature Concept Role) then
      let target := (address source).extend (role, filler) hdepth
      ∀ targetNode, address targetNode = target →
        state.edge role source targetNode ∧ state.label targetNode filler
    else
      False

theorem State.rootedAddressRefinesDirect_iff
    {Root Node Concept Role : Type}
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role)
    (address : Node → WitnessAddress Root Concept Role) :
    state.RootedAddressRefinesDirect address ↔
      state.RootedAddressRefines address := by
  constructor
  · rintro ⟨hinjective, hrefines⟩
    refine ⟨hinjective, ?_⟩
    intro source role filler hobligation
    have h := hrefines source role filler hobligation
    split at h
    next hdepth => exact ⟨hdepth, h⟩
    next hdepth => exact False.elim h
  · rintro ⟨hinjective, hrefines⟩
    refine ⟨hinjective, ?_⟩
    intro source role filler hobligation
    obtain ⟨hdepth, hoccupied⟩ := hrefines source role filler hobligation
    split
    next hdepth' =>
      simpa only [Subsingleton.elim hdepth' hdepth] using hoccupied
    next hdepth' => exact False.elim (hdepth' hdepth)

/-- The specialized computable-bound presentation used by KM's finite `Fin`
worker. Its numeric bound is definitionally executable; the embedded proof is
transported to the canonical finite-signature cardinality expected by witness
addresses. -/
def State.RootedAddressRefinesComputable
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    (address : Fin nodeCount →
      WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount)) : Prop :=
  Function.Injective address ∧
  ∀ source role filler, state.obligation role filler source →
    if hdepth : (address source).2.1.length <
        roleBlockingSignatureCard conceptCount roleCount then
      let hdepth' : (address source).2.1.length <
          Fintype.card (RoleBlockingSignature (Fin conceptCount)
            (Fin roleCount)) := by
        simpa only [card_roleBlockingSignature_fin] using hdepth
      let target := (address source).extend (role, filler) hdepth'
      ∀ targetNode, address targetNode = target →
        state.edge role source targetNode ∧ state.label targetNode filler
    else
      False

theorem State.rootedAddressRefinesComputable_iff
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    (address : Fin nodeCount →
      WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount)) :
    state.RootedAddressRefinesComputable address ↔
      state.RootedAddressRefines address := by
  constructor
  · rintro ⟨hinjective, hrefines⟩
    refine ⟨hinjective, ?_⟩
    intro source role filler hobligation
    have h := hrefines source role filler hobligation
    split at h
    next hdepth =>
      let hdepth' : (address source).2.1.length <
          Fintype.card (RoleBlockingSignature (Fin conceptCount)
            (Fin roleCount)) := by
        simpa only [card_roleBlockingSignature_fin] using hdepth
      exact ⟨hdepth', h⟩
    next hdepth => exact False.elim h
  · rintro ⟨hinjective, hrefines⟩
    refine ⟨hinjective, ?_⟩
    intro source role filler hobligation
    obtain ⟨hdepth, hoccupied⟩ := hrefines source role filler hobligation
    have hbound : (address source).2.1.length <
        roleBlockingSignatureCard conceptCount roleCount := by
      simpa only [← card_roleBlockingSignature_fin] using hdepth
    split
    next hdepth' =>
      simpa only [Subsingleton.elim
        (show (address source).2.1.length <
          Fintype.card (RoleBlockingSignature (Fin conceptCount)
            (Fin roleCount)) from by
              simpa only [card_roleBlockingSignature_fin] using hdepth')
        hdepth] using hoccupied
    next hdepth' => exact False.elim (hdepth' hbound)

/-- Executable checker used at the Rust/Lean frontier boundary. -/
def State.checkRootedAddressRefines
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    [DecidableState state]
    (address : Fin nodeCount →
      WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount)) : Bool :=
  letI : ∀ node literal, Decidable (state.label node literal) :=
    DecidableState.label (state := state)
  letI : ∀ role source target, Decidable (state.edge role source target) :=
    DecidableState.edge (state := state)
  letI : ∀ role filler node, Decidable (state.obligation role filler node) :=
    DecidableState.obligation (state := state)
  let nodes := List.finRange nodeCount
  let roles := List.finRange roleCount
  let concepts := List.finRange conceptCount
  let literals := concepts.map Lit.pos ++ concepts.map Lit.negated
  (nodes.all fun left => nodes.all fun right =>
    decide (address left = address right → left = right)) &&
  (nodes.all fun source => roles.all fun role => literals.all fun filler =>
    if hobligation : state.obligation role filler source then
      if hdepth : (address source).2.1.length <
          roleBlockingSignatureCard conceptCount roleCount then
        let hdepth' : (address source).2.1.length <
            Fintype.card (RoleBlockingSignature (Fin conceptCount)
              (Fin roleCount)) := by
          simpa only [card_roleBlockingSignature_fin] using hdepth
        let target := (address source).extend (role, filler) hdepth'
        nodes.all fun targetNode => decide
          (address targetNode = target →
            state.edge role source targetNode ∧ state.label targetNode filler)
      else
        false
    else
      true)

theorem State.checkRootedAddressRefines_eq_true_iff
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    [DecidableState state]
    (address : Fin nodeCount →
      WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount)) :
    state.checkRootedAddressRefines address = true ↔
      state.RootedAddressRefines address := by
  rw [← state.rootedAddressRefinesComputable_iff address]
  letI : ∀ node literal, Decidable (state.label node literal) :=
    DecidableState.label (state := state)
  letI : ∀ role source target, Decidable (state.edge role source target) :=
    DecidableState.edge (state := state)
  letI : ∀ role filler node, Decidable (state.obligation role filler node) :=
    DecidableState.obligation (state := state)
  constructor
  · intro hcheck
    simp only [State.checkRootedAddressRefines, Bool.and_eq_true] at hcheck
    refine ⟨?_, ?_⟩
    · intro left right hequal
      have hleft := (List.all_eq_true.mp hcheck.1) left
        (List.mem_finRange left)
      have hright := (List.all_eq_true.mp hleft) right
        (List.mem_finRange right)
      exact (decide_eq_true_eq.mp hright) hequal
    · intro source role filler hobligation
      have hsource := (List.all_eq_true.mp hcheck.2) source
        (List.mem_finRange source)
      have hrole := (List.all_eq_true.mp hsource) role
        (List.mem_finRange role)
      have hfillerMem : filler ∈
          (List.finRange conceptCount).map Lit.pos ++
            (List.finRange conceptCount).map Lit.negated := by
        rcases filler with ⟨concept, polarity⟩
        cases polarity
        · apply List.mem_append.mpr
          left
          exact List.mem_map.mpr ⟨concept, List.mem_finRange concept, rfl⟩
        · apply List.mem_append.mpr
          right
          exact List.mem_map.mpr ⟨concept, List.mem_finRange concept, rfl⟩
      have hfiller := (List.all_eq_true.mp hrole) filler hfillerMem
      by_cases hdepth : (address source).2.1.length <
          roleBlockingSignatureCard conceptCount roleCount
      · simp only [hobligation, hdepth, ↓reduceDIte] at hfiller ⊢
        intro targetNode hequal
        have htarget := (List.all_eq_true.mp hfiller) targetNode
          (List.mem_finRange targetNode)
        exact (decide_eq_true_eq.mp htarget) hequal
      · simp [hobligation, hdepth] at hfiller
  · intro hrefines
    simp only [State.checkRootedAddressRefines, Bool.and_eq_true]
    constructor
    · rw [List.all_eq_true]
      intro left _
      rw [List.all_eq_true]
      intro right _
      exact decide_eq_true (fun hequal => hrefines.1 hequal)
    · rw [List.all_eq_true]
      intro source _
      rw [List.all_eq_true]
      intro role _
      rw [List.all_eq_true]
      intro filler _
      by_cases hobligation : state.obligation role filler source
      · have h := hrefines.2 source role filler hobligation
        by_cases hdepth : (address source).2.1.length <
            roleBlockingSignatureCard conceptCount roleCount
        · simp only [hdepth, ↓reduceDIte] at h
          simp only [hobligation, hdepth, ↓reduceDIte, List.all_eq_true]
          intro targetNode _
          exact decide_eq_true (h targetNode)
        · simp [hdepth] at h
      · simp [hobligation]

theorem State.checkRootedAddressRefines_sound
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    [DecidableState state]
    (address : Fin nodeCount →
      WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount))
    (hcheck : state.checkRootedAddressRefines address = true) :
    state.RootedAddressRefines address :=
  (state.checkRootedAddressRefines_eq_true_iff address).mp hcheck

#print axioms State.rootedAddressRefinesDirect_iff
#print axioms State.rootedAddressRefinesComputable_iff
#print axioms State.checkRootedAddressRefines_eq_true_iff
#print axioms State.checkRootedAddressRefines_sound

end ContextCalculus.Hypertableau
