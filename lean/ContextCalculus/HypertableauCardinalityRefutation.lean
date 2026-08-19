import ContextCalculus.HypertableauCardinality

/-!
# Cardinality-aware hypertableau refutations

An active maximum restriction with `n + 1` qualifying successors forces at
least one pair to denote the same domain element.  A refutation must therefore
close every possible unequal-index merge.  This is the semantic rule checked
by the finite cardinality refutation certificate.
-/

namespace ContextCalculus.Hypertableau

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

#print axioms CardinalityEqRefutes.sound

end ContextCalculus.Hypertableau
