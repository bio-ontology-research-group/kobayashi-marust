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

structure DistinctEqState (Node : Type u) (Concept Role : Type) where
  base : EqState Node Concept Role
  apart : Node → Node → Prop

@[ext] theorem DistinctEqState.ext
    {left right : DistinctEqState Node Concept Role}
    (hbase : left.base = right.base) (hapart : left.apart = right.apart) :
    left = right := by
  cases left
  cases right
  simp_all

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

def DistinctEqState.assertAtom (state : DistinctEqState Node Concept Role)
    (assignment : Variable → Node) (atom : Atom Variable Concept Role) :
    DistinctEqState Node Concept Role where
  base := state.base.assertAtom assignment atom
  apart := state.apart

def DistinctEqState.materializeWitness (state : DistinctEqState Node Concept Role)
    (source target : Node) (role : Role) (filler : Lit Concept) :
    DistinctEqState Node Concept Role where
  base := state.base.materializeWitness source target role filler
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

theorem DistinctEqState.materializeWitness_realized
    (state : DistinctEqState Node Concept Role) (I : Interp Domain Concept Role)
    (value : Node → Domain) (hrealized : state.RealizedBy I value)
    (source target : Node) (role : Role) (filler : Lit Concept)
    (hobligation : state.base.base.obligation role filler source)
    (hfresh : state.Fresh target) :
    ∃ value', (state.materializeWitness source target role filler).RealizedBy I value' := by
  classical
  rcases hrealized.1.1.2.2 role filler source hobligation with
    ⟨witness, hedge, hfiller⟩
  have hsource : source ≠ target := by
    intro heq
    subst source
    exact hfresh.1.1.2.2 role filler hobligation
  let value' := Function.update value target witness
  refine ⟨value', ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro node lit hlabel
    rcases hlabel with hlabel | ⟨rfl, rfl⟩
    · have hnode : node ≠ target := by
        intro heq
        subst node
        exact hfresh.1.1.1 lit hlabel
      simpa [value', Function.update_of_ne hnode] using
        hrealized.1.1.1 node lit hlabel
    · simpa [value'] using hfiller
  · intro candidateRole candidateSource candidateTarget hedge'
    rcases hedge' with hedge' | ⟨rfl, rfl, rfl⟩
    · have hsource' : candidateSource ≠ target := by
        intro heq
        subst candidateSource
        exact (hfresh.1.1.2.1 candidateRole candidateTarget).1 hedge'
      have htarget' : candidateTarget ≠ target := by
        intro heq
        subst candidateTarget
        exact (hfresh.1.1.2.1 candidateRole candidateSource).2 hedge'
      simpa [value', Function.update_of_ne hsource', Function.update_of_ne htarget'] using
        hrealized.1.1.2.1 candidateRole candidateSource candidateTarget hedge'
    · simpa [value', Function.update_of_ne hsource] using hedge
  · intro candidateRole candidateFiller node hobligation'
    have hnode : node ≠ target := by
      intro heq
      subst node
      exact hfresh.1.1.2.2 candidateRole candidateFiller hobligation'
    rcases hrealized.1.1.2.2 candidateRole candidateFiller node hobligation' with
      ⟨witness', hedge', hfiller'⟩
    exact ⟨witness', by
      simpa [value', Function.update_of_ne hnode] using hedge', hfiller'⟩
  · intro left right hequiv
    by_cases hleft : left = target
    · subst left
      have hright := hfresh.1.2 right hequiv
      subst right
      rfl
    · by_cases hright : right = target
      · subst right
        have hleftTarget := hfresh.1.2 left
          (state.base.equiv_equivalence.2 hequiv)
        exact (hleft hleftTarget).elim
      · have hold := hrealized.1.2 left right hequiv
        simpa [value', Function.update_of_ne hleft, Function.update_of_ne hright] using hold
  · intro left right hapart
    have hleft : left ≠ target := by
      intro heq
      subst left
      exact (hfresh.2 right).1 hapart
    have hright : right ≠ target := by
      intro heq
      subst right
      exact (hfresh.2 left).2 hapart
    simpa [value', Function.update_of_ne hleft, Function.update_of_ne hright] using
      hrealized.2 left right hapart

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

inductive DistinctCardinalityRefutes (Node : Type u)
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) :
    DistinctEqState Node Concept Role → Prop where
  | equality (state) (tree : EqRefutes Node ontology state.base) :
      DistinctCardinalityRefutes Node ontology definitions state
  | clash (state)
      (hclash : ∃ positiveNode negativeNode concept,
        state.base.equiv positiveNode negativeNode ∧
          state.base.base.label positiveNode (.pos concept) ∧
          state.base.base.label negativeNode (.negated concept)) :
      DistinctCardinalityRefutes Node ontology definitions state
  | branch (state) (clause : Clause Variable Concept Role)
      (hclause : clause ∈ ontology) (assignment : Variable → Node)
      (hbody : ∀ atom ∈ clause.body, state.base.holdsAtom assignment atom)
      (children : ∀ atom, atom ∈ clause.head →
        DistinctCardinalityRefutes Node ontology definitions
          (state.assertAtom assignment atom)) :
      DistinctCardinalityRefutes Node ontology definitions state
  | witness (state) (source target : Node) (role : Role) (filler : Lit Concept)
      (hobligation : state.base.base.obligation role filler source)
      (hfresh : state.Fresh target)
      (child : DistinctCardinalityRefutes Node ontology definitions
        (state.materializeWitness source target role filler)) :
      DistinctCardinalityRefutes Node ontology definitions state
  | equalityApart (state) (left right : Node)
      (hequal : state.base.equiv left right)
      (hapart : state.apart left right) :
      DistinctCardinalityRefutes Node ontology definitions state
  | maximum (state) (definition : CardinalityDef Concept Role)
      (hdefinition : definition ∈ definitions)
      (hkind : definition.kind = .maximum)
      (source : Node) (hmarker : state.base.base.label source (.pos definition.marker))
      (witnesses : Fin (definition.bound + 1) → Node)
      (hedge : ∀ index,
        state.base.base.edge definition.role source (witnesses index))
      (hfiller : ∀ index,
        state.base.base.label (witnesses index) (.pos definition.filler))
      (children : ∀ left right, left ≠ right →
        DistinctCardinalityRefutes Node ontology definitions
          (state.merge (witnesses left) (witnesses right))) :
      DistinctCardinalityRefutes Node ontology definitions state
  | minimum (state) (definition : CardinalityDef Concept Role)
      (hdefinition : definition ∈ definitions)
      (hkind : definition.kind = .minimum)
      (source : Node) (hmarker : state.base.base.label source (.pos definition.marker))
      (targets : Fin definition.bound → Node)
      (hfresh : state.FreshFamily targets)
      (child : DistinctCardinalityRefutes Node ontology definitions
        (state.materializeMinimum source targets definition.role definition.filler)) :
      DistinctCardinalityRefutes Node ontology definitions state

theorem DistinctCardinalityRefutes.sound
    (hrefutes : DistinctCardinalityRefutes Node ontology definitions state) :
    ¬state.RealizableWithCardinality ontology definitions := by
  induction hrefutes with
  | equality state tree =>
      rintro ⟨Domain, I, value, hmodels, _, hrealized⟩
      exact tree.sound ⟨Domain, I, value, hmodels, hrealized.1⟩
  | clash state hclash =>
      rintro ⟨Domain, I, value, _, _, hrealized⟩
      rcases hclash with
        ⟨positiveNode, negativeNode, concept, hequiv, hpositive, hnegative⟩
      have hpositiveSat := hrealized.1.1.1 positiveNode (.pos concept) hpositive
      have hnegativeSat := hrealized.1.1.1 negativeNode (.negated concept) hnegative
      rw [← hrealized.1.2 positiveNode negativeNode hequiv] at hnegativeSat
      exact hnegativeSat hpositiveSat
  | branch state clause hclause assignment hbody children ih =>
      rintro ⟨Domain, I, value, hmodels, hcardinality, hrealized⟩
      rcases state.base.hyper_branch_sound I value hrealized.1 clause
          (hmodels clause hclause) assignment hbody with ⟨atom, hatom, hchild⟩
      exact ih atom hatom ⟨Domain, I, value, hmodels, hcardinality, hchild, hrealized.2⟩
  | witness state source target role filler hobligation hfresh child ih =>
      rintro ⟨Domain, I, value, hmodels, hcardinality, hrealized⟩
      rcases state.materializeWitness_realized I value hrealized source target role filler
          hobligation hfresh with ⟨value', hchild⟩
      exact ih ⟨Domain, I, value', hmodels, hcardinality, hchild⟩
  | equalityApart state left right hequal hapart =>
      exact state.equality_apart_clash left right hequal hapart
  | maximum state definition hdefinition hkind source hmarker witnesses
      hedge hfiller children ih =>
      rintro ⟨Domain, I, value, hmodels, hcardinality, hrealized⟩
      have hmarkerSat : I.concept definition.marker (value source) :=
        hrealized.1.1.1 source (.pos definition.marker) hmarker
      have hdefinitionModels : I.modelsCardinalityDef definition :=
        hcardinality definition hdefinition
      have hsuccessors : ∀ index,
          I.cardinalitySuccessor definition (value source) (value (witnesses index)) := by
        intro index
        exact ⟨hrealized.1.1.2.1 definition.role source (witnesses index) (hedge index),
          hrealized.1.1.1 (witnesses index) (.pos definition.filler) (hfiller index)⟩
      have hnotInjective :
          ¬Function.Injective (fun index => value (witnesses index)) :=
        Interp.maximum_forces_merge (I := I) definition hkind
          hdefinitionModels (value source) hmarkerSat
          (fun index => value (witnesses index)) hsuccessors
      have hpair : ∃ left right, left ≠ right ∧
          value (witnesses left) = value (witnesses right) := by
        by_contra hnone
        push Not at hnone
        apply hnotInjective
        intro left right hequal
        by_contra hne
        exact hnone left right hne hequal
      rcases hpair with ⟨left, right, hne, hequal⟩
      exact ih left right hne ⟨Domain, I, value, hmodels, hcardinality,
        state.merge_realized I value hrealized (witnesses left) (witnesses right) hequal⟩
  | minimum state definition hdefinition hkind source hmarker targets hfresh child ih =>
      rintro ⟨Domain, I, value, hmodels, hcardinality, hrealized⟩
      have hmarkerSat : I.concept definition.marker (value source) :=
        hrealized.1.1.1 source (.pos definition.marker) hmarker
      have hdefinitionModels : I.modelsCardinalityDef definition :=
        hcardinality definition hdefinition
      rcases I.minimum_witnesses definition hkind hdefinitionModels (value source)
          hmarkerSat with ⟨witnesses, hinjective, hsuccessors⟩
      rcases state.materializeMinimum_realized I value hrealized source targets
          definition.role definition.filler definition.marker hmarker hfresh witnesses
          hinjective hsuccessors with ⟨value', hchild⟩
      exact ih ⟨Domain, I, value', hmodels, hcardinality, hchild⟩

def minimumDefinition (marker : Concept) (bound : Nat) (role : Role)
    (filler : Concept) : CardinalityDef Concept Role :=
  { marker, kind := .minimum, bound, role, filler }

def maximumDefinition (marker : Concept) (bound : Nat) (role : Role)
    (filler : Concept) : CardinalityDef Concept Role :=
  { marker, kind := .maximum, bound, role, filler }

/-- The pure pigeonhole contradiction: an active `≥ n+1 R.C` and `≤ n R.C`
restriction has a finite distinct-aware HT refutation. -/
theorem DistinctCardinalityRefutes.pigeonhole
    (state : DistinctEqState Node Concept Role)
    (source : Node) (marker filler : Concept) (role : Role) (bound : Nat)
    (targets : Fin (bound + 1) → Node)
    (hmarker : state.base.base.label source (.pos marker))
    (hfresh : state.FreshFamily targets) :
    DistinctCardinalityRefutes Node ontology
      [minimumDefinition marker (bound + 1) role filler,
       maximumDefinition marker bound role filler] state := by
  refine DistinctCardinalityRefutes.minimum state
    (minimumDefinition marker (bound + 1) role filler) (by simp) rfl
    source hmarker targets hfresh ?_
  refine DistinctCardinalityRefutes.maximum _
    (maximumDefinition marker bound role filler) (by simp) rfl
    source (Or.inl hmarker) targets ?_ ?_ ?_
  · intro index
    exact Or.inr ⟨index, rfl, rfl, rfl⟩
  · intro index
    exact Or.inr ⟨index, rfl, rfl⟩
  · intro left right hne
    apply DistinctCardinalityRefutes.equalityApart _ (targets left) (targets right)
    · exact EqState.merge_pair _ _ _
    · exact Or.inr ⟨left, right, hne, rfl, rfl⟩

#print axioms DistinctEqState.equality_apart_clash
#print axioms DistinctEqState.merge_realized
#print axioms DistinctEqState.materializeWitness_realized
#print axioms DistinctEqState.materializeMinimum_realized
#print axioms DistinctCardinalityRefutes.sound
#print axioms DistinctCardinalityRefutes.pigeonhole

end ContextCalculus.Hypertableau
