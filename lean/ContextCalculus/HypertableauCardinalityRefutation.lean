import ContextCalculus.HypertableauCardinality

/-!
# Cardinality-aware hypertableau refutations

An active maximum restriction with `n + 1` qualifying successors forces at
least one pair to denote the same domain element.  A refutation must therefore
close every possible unequal-index merge.  This is the semantic rule checked
by the finite cardinality refutation certificate.
-/

namespace ContextCalculus.Hypertableau

def State.materializeMinimum (state : State Node Concept Role)
    (source : Node) (targets : Fin count → Node) (role : Role) (filler : Concept) :
    State Node Concept Role where
  label node lit := state.label node lit ∨
    ∃ index, node = targets index ∧ lit = .pos filler
  edge candidateRole candidateSource candidateTarget :=
    state.edge candidateRole candidateSource candidateTarget ∨
    ∃ index, candidateRole = role ∧ candidateSource = source ∧
      candidateTarget = targets index
  obligation := state.obligation

def EqState.materializeMinimum (state : EqState Node Concept Role)
    (source : Node) (targets : Fin count → Node) (role : Role) (filler : Concept) :
    EqState Node Concept Role :=
  { state with base := state.base.materializeMinimum source targets role filler }

def EqState.FreshFamily (state : EqState Node Concept Role)
    (targets : Fin count → Node) : Prop :=
  Function.Injective targets ∧ ∀ index, state.Fresh (targets index)

theorem EqState.materializeMinimum_realized
    (state : EqState Node Concept Role) (I : Interp Domain Concept Role)
    (value : Node → Domain) (hrealized : state.RealizedBy I value)
    (source : Node) (targets : Fin count → Node) (role : Role) (filler marker : Concept)
    (hmarker : state.base.label source (.pos marker))
    (hfresh : state.FreshFamily targets)
    (witnesses : Fin count → Domain)
    (hsuccessors : ∀ index, I.role role (value source) (witnesses index) ∧
      I.concept filler (witnesses index)) :
    ∃ value', (state.materializeMinimum source targets role filler).RealizedBy I value' := by
  classical
  let value' : Node → Domain := fun node =>
    if h : ∃ index, targets index = node then witnesses (Classical.choose h) else value node
  have htarget (index : Fin count) : value' (targets index) = witnesses index := by
    simp only [value']
    split
    next h =>
      have hchosen := Classical.choose_spec h
      exact congrArg witnesses (hfresh.1 hchosen)
    next h => exact (h ⟨index, rfl⟩).elim
  have hold (node : Node) (hnode : ∀ index, targets index ≠ node) : value' node = value node := by
    simp only [value']
    split
    next h =>
      rcases h with ⟨index, heq⟩
      exact (hnode index heq).elim
    next => rfl
  have hsource (index : Fin count) : targets index ≠ source := by
    intro heq
    exact (hfresh.2 index).1.1 (.pos marker) (by simpa [heq] using hmarker)
  refine ⟨value', ⟨?_, ?_⟩⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro node lit hlabel
      rcases hlabel with hlabel | ⟨index, rfl, rfl⟩
      · rw [hold node]
        · exact hrealized.1.1 node lit hlabel
        · intro index heq
          subst node
          exact hfresh.2 index |>.1.1 lit hlabel
      · rw [htarget index]
        exact (hsuccessors index).2
    · intro candidateRole candidateSource candidateTarget hedge
      rcases hedge with hedge | ⟨index, hrole, hsourceEq, htargetEq⟩
      · have hcandidateSource : ∀ index, targets index ≠ candidateSource := by
          intro index heq
          exact ((hfresh.2 index).1.2.1 candidateRole candidateTarget).1
            (by simpa [heq] using hedge)
        have hcandidateTarget : ∀ index, targets index ≠ candidateTarget := by
          intro index heq
          exact ((hfresh.2 index).1.2.1 candidateRole candidateSource).2
            (by simpa [heq] using hedge)
        rw [hold candidateSource hcandidateSource, hold candidateTarget hcandidateTarget]
        exact hrealized.1.2.1 candidateRole candidateSource candidateTarget hedge
      · rw [hrole, hsourceEq, htargetEq]
        rw [hold source hsource, htarget index]
        exact (hsuccessors index).1
    · intro candidateRole candidateFiller node hobligation
      rcases hrealized.1.2.2 candidateRole candidateFiller node hobligation with
        ⟨witness, hedge, hfiller⟩
      refine ⟨witness, ?_, hfiller⟩
      have hnode : ∀ index, targets index ≠ node := by
        intro index heq
        exact (hfresh.2 index).1.2.2 candidateRole candidateFiller
          (by simpa [heq] using hobligation)
      rw [hold node hnode]
      exact hedge
  · intro left right hequiv
    by_cases hleft : ∃ index, targets index = left
    · rcases hleft with ⟨index, hindex⟩
      have hright : right = left := by
        rw [← hindex]
        exact (hfresh.2 index).2 right (by simpa [hindex] using hequiv)
      subst right
      rfl
    · by_cases hright : ∃ index, targets index = right
      · rcases hright with ⟨index, hindex⟩
        have hleftEq : left = right := by
          rw [← hindex]
          exact (hfresh.2 index).2 left
            (by simpa [hindex] using state.equiv_equivalence.2 hequiv)
        rw [hleftEq]
      · have hleftOld : ∀ index, targets index ≠ left := by
          intro index heq; exact hleft ⟨index, heq⟩
        have hrightOld : ∀ index, targets index ≠ right := by
          intro index heq; exact hright ⟨index, heq⟩
        rw [hold left hleftOld, hold right hrightOld]
        exact hrealized.2 left right hequiv

def EqState.RealizableWithCardinality
    (state : EqState Node Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role) (value : Node → Domain),
    I.models ontology ∧ I.modelsCardinalityDefs definitions ∧
      state.RealizedBy I value

inductive CardinalityEqRefutes (Node : Type u)
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) :
    EqState Node Concept Role → Prop where
  | equality (state) (tree : EqRefutes Node ontology state) :
      CardinalityEqRefutes Node ontology definitions state
  | clash (state)
      (hclash : ∃ positiveNode negativeNode concept,
        state.equiv positiveNode negativeNode ∧
          state.base.label positiveNode (.pos concept) ∧
          state.base.label negativeNode (.negated concept)) :
      CardinalityEqRefutes Node ontology definitions state
  | branch (state) (clause : Clause Variable Concept Role)
      (hclause : clause ∈ ontology) (assignment : Variable → Node)
      (hbody : ∀ atom ∈ clause.body, state.holdsAtom assignment atom)
      (children : ∀ atom, atom ∈ clause.head →
        CardinalityEqRefutes Node ontology definitions
          (state.assertAtom assignment atom)) :
      CardinalityEqRefutes Node ontology definitions state
  | witness (state) (source target : Node) (role : Role) (filler : Lit Concept)
      (hobligation : state.base.obligation role filler source)
      (hfresh : state.Fresh target)
      (child : CardinalityEqRefutes Node ontology definitions
        (state.materializeWitness source target role filler)) :
      CardinalityEqRefutes Node ontology definitions state
  | maximum (state) (definition : CardinalityDef Concept Role)
      (hdefinition : definition ∈ definitions)
      (hkind : definition.kind = .maximum)
      (source : Node) (hmarker : state.base.label source (.pos definition.marker))
      (witnesses : Fin (definition.bound + 1) → Node)
      (hedge : ∀ index,
        state.base.edge definition.role source (witnesses index))
      (hfiller : ∀ index,
        state.base.label (witnesses index) (.pos definition.filler))
      (children : ∀ left right, left ≠ right →
        CardinalityEqRefutes Node ontology definitions
          (state.merge (witnesses left) (witnesses right))) :
      CardinalityEqRefutes Node ontology definitions state
  | minimum (state) (definition : CardinalityDef Concept Role)
      (hdefinition : definition ∈ definitions)
      (hkind : definition.kind = .minimum)
      (source : Node) (hmarker : state.base.label source (.pos definition.marker))
      (targets : Fin definition.bound → Node)
      (hfresh : state.FreshFamily targets)
      (child : CardinalityEqRefutes Node ontology definitions
        (state.materializeMinimum source targets definition.role definition.filler)) :
      CardinalityEqRefutes Node ontology definitions state

theorem CardinalityEqRefutes.sound
    (hrefutes : CardinalityEqRefutes Node ontology definitions state) :
    ¬state.RealizableWithCardinality ontology definitions := by
  induction hrefutes with
  | equality state tree =>
      rintro ⟨Domain, I, value, hmodels, _, hrealized⟩
      exact tree.sound ⟨Domain, I, value, hmodels, hrealized⟩
  | clash state hclash =>
      rintro ⟨Domain, I, value, _, _, hrealized⟩
      rcases hclash with
        ⟨positiveNode, negativeNode, concept, hequiv, hpositive, hnegative⟩
      have hpositiveSat := hrealized.1.1 positiveNode (.pos concept) hpositive
      have hnegativeSat := hrealized.1.1 negativeNode (.negated concept) hnegative
      have hvalue := hrealized.2 positiveNode negativeNode hequiv
      rw [← hvalue] at hnegativeSat
      exact hnegativeSat hpositiveSat
  | branch state clause hclause assignment hbody children ih =>
      rintro ⟨Domain, I, value, hmodels, hcardinality, hrealized⟩
      rcases state.hyper_branch_sound I value hrealized clause
          (hmodels clause hclause) assignment hbody with
        ⟨atom, hatom, hchild⟩
      exact ih atom hatom ⟨Domain, I, value, hmodels, hcardinality, hchild⟩
  | witness state source target role filler hobligation hfresh child ih =>
      rintro ⟨Domain, I, value, hmodels, hcardinality, hrealized⟩
      rcases state.materializeWitness_realized I value hrealized source target
          role filler hobligation hfresh with ⟨value', hchild⟩
      exact ih ⟨Domain, I, value', hmodels, hcardinality, hchild⟩
  | maximum state definition hdefinition hkind source hmarker witnesses
      hedge hfiller children ih =>
      rintro ⟨Domain, I, value, hmodels, hcardinality, hrealized⟩
      have hmarkerSat : I.concept definition.marker (value source) :=
        hrealized.1.1 source (.pos definition.marker) hmarker
      have hdefinitionModels : I.modelsCardinalityDef definition :=
        hcardinality definition hdefinition
      have hsuccessors : ∀ index,
          I.cardinalitySuccessor definition (value source) (value (witnesses index)) := by
        intro index
        exact ⟨hrealized.1.2.1 definition.role source (witnesses index) (hedge index),
          hrealized.1.1 (witnesses index) (.pos definition.filler) (hfiller index)⟩
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
        hrealized.1.1 source (.pos definition.marker) hmarker
      have hdefinitionModels : I.modelsCardinalityDef definition :=
        hcardinality definition hdefinition
      rcases I.minimum_witnesses definition hkind hdefinitionModels (value source)
          hmarkerSat with ⟨witnesses, _hinjective, hsuccessors⟩
      rcases state.materializeMinimum_realized I value hrealized source targets
          definition.role definition.filler definition.marker hmarker hfresh witnesses
          hsuccessors with ⟨value', hchild⟩
      exact ih ⟨Domain, I, value', hmodels, hcardinality, hchild⟩

#print axioms CardinalityEqRefutes.sound
#print axioms EqState.materializeMinimum_realized

end ContextCalculus.Hypertableau
