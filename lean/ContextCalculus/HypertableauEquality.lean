import ContextCalculus.Hypertableau
import Mathlib.Logic.Relation

/-!
# Equality-aware hypertableau branch states

An equality head does not add an ordinary branch fact. It identifies two
completion-graph nodes. This module gives that operation its semantic meaning:
an equality-aware state carries an equivalence relation, and every realization
must map equivalent nodes to the same domain element. Adding one equality takes
the equivalence closure of the old relation and the new pair.

The main theorem, `EqState.assertAtom_realized`, covers every HT head atom,
including equality. It is the semantic target for a finite union-find checker;
representative selection, path compression, and merge direction remain
implementation details outside the trusted calculus.
-/

namespace ContextCalculus.Hypertableau

universe u v w x

structure EqState (Node : Type u) (Concept : Type v) (Role : Type w) where
  base : State Node Concept Role
  equiv : Node → Node → Prop
  equiv_equivalence : Equivalence equiv

@[ext] theorem EqState.ext
    {left right : EqState Node Concept Role}
    (hbase : left.base = right.base)
    (hequiv : left.equiv = right.equiv) : left = right := by
  cases left
  cases right
  simp_all

def EqState.holdsAtom (state : EqState Node Concept Role)
    (assignment : Variable → Node) : Atom Variable Concept Role → Prop
  | .eq left right => state.equiv (assignment left) (assignment right)
  | atom => state.base.holdsAtom assignment atom

def EqState.RealizedBy (state : EqState Node Concept Role)
    (I : Interp Domain Concept Role) (value : Node → Domain) : Prop :=
  state.base.RealizedBy I value ∧
    ∀ left right, state.equiv left right → value left = value right

theorem EqState.realized_holdsAtom
    (state : EqState Node Concept Role) (I : Interp Domain Concept Role)
    (value : Node → Domain) (hrealized : state.RealizedBy I value)
    (assignment : Variable → Node) (atom : Atom Variable Concept Role)
    (hholds : state.holdsAtom assignment atom) :
    I.satAtom (value ∘ assignment) atom := by
  cases atom with
  | concept lit node =>
      exact state.base.realized_holdsAtom I value hrealized.1 assignment
        (.concept lit node) hholds
  | role role source target =>
      exact state.base.realized_holdsAtom I value hrealized.1 assignment
        (.role role source target) hholds
  | exists_ role filler node =>
      exact state.base.realized_holdsAtom I value hrealized.1 assignment
        (.exists_ role filler node) hholds
  | eq left right =>
      simpa [Interp.satAtom, Function.comp_apply] using
        hrealized.2 (assignment left) (assignment right) hholds

def EqState.merge (state : EqState Node Concept Role) (left right : Node) :
    EqState Node Concept Role where
  base := state.base
  equiv := Relation.EqvGen fun x y =>
    state.equiv x y ∨ (x = left ∧ y = right)
  equiv_equivalence := Relation.EqvGen.is_equivalence _

theorem EqState.merge_old
    (state : EqState Node Concept Role) (left right x y : Node)
    (hxy : state.equiv x y) :
    (state.merge left right).equiv x y :=
  Relation.EqvGen.rel _ _ (Or.inl hxy)

theorem EqState.merge_pair
    (state : EqState Node Concept Role) (left right : Node) :
    (state.merge left right).equiv left right :=
  Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩)

theorem EqState.merge_realized
    (state : EqState Node Concept Role) (I : Interp Domain Concept Role)
    (value : Node → Domain) (hrealized : state.RealizedBy I value)
    (left right : Node) (hequal : value left = value right) :
    (state.merge left right).RealizedBy I value := by
  refine ⟨hrealized.1, ?_⟩
  intro x y hxy
  induction hxy with
  | rel x y hstep =>
      rcases hstep with hold | ⟨rfl, rfl⟩
      · exact hrealized.2 x y hold
      · exact hequal
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ hxy hyz => exact hxy.trans hyz

def EqState.assertAtom (state : EqState Node Concept Role)
    (assignment : Variable → Node) : Atom Variable Concept Role →
    EqState Node Concept Role
  | .eq left right => state.merge (assignment left) (assignment right)
  | atom => { state with base := state.base.assertAtom assignment atom }

/-- Every semantically true HT head, including equality, can be asserted while
preserving the realizing model. -/
theorem EqState.assertAtom_realized
    (state : EqState Node Concept Role) (I : Interp Domain Concept Role)
    (value : Node → Domain) (hrealized : state.RealizedBy I value)
    (assignment : Variable → Node) (atom : Atom Variable Concept Role)
    (hsat : I.satAtom (value ∘ assignment) atom) :
    (state.assertAtom assignment atom).RealizedBy I value := by
  cases atom with
  | concept lit node =>
      exact ⟨state.base.assertAtom_realized I value hrealized.1 assignment
          (.concept lit node) trivial hsat,
        hrealized.2⟩
  | role role source target =>
      exact ⟨state.base.assertAtom_realized I value hrealized.1 assignment
          (.role role source target) trivial hsat,
        hrealized.2⟩
  | exists_ role filler node =>
      exact ⟨state.base.assertAtom_realized I value hrealized.1 assignment
          (.exists_ role filler node) trivial hsat,
        hrealized.2⟩
  | eq left right =>
      apply state.merge_realized I value hrealized
      simpa [Interp.satAtom, Function.comp_apply] using hsat

/-- Equality-aware form of exhaustive HT head branching: one asserted child
preserves every realizing model, with no restriction on equality heads. -/
theorem EqState.hyper_branch_sound
    (state : EqState Node Concept Role) (I : Interp Domain Concept Role)
    (value : Node → Domain) (hrealized : state.RealizedBy I value)
    (clause : Clause Variable Concept Role)
    (hclause : I.modelsClause clause)
    (assignment : Variable → Node)
    (hbody : ∀ atom ∈ clause.body, state.holdsAtom assignment atom) :
    ∃ atom ∈ clause.head,
      (state.assertAtom assignment atom).RealizedBy I value := by
  have hsemanticBody : ∀ atom ∈ clause.body,
      I.satAtom (value ∘ assignment) atom := by
    intro atom hatom
    exact state.realized_holdsAtom I value hrealized assignment atom
      (hbody atom hatom)
  rcases hclause (value ∘ assignment) hsemanticBody with ⟨atom, hatom, hsat⟩
  exact ⟨atom, hatom, state.assertAtom_realized I value hrealized assignment atom hsat⟩

def EqState.Fresh (state : EqState Node Concept Role) (target : Node) : Prop :=
  state.base.Fresh target ∧
    ∀ node, state.equiv target node → node = target

def EqState.materializeWitness (state : EqState Node Concept Role)
    (source target : Node) (role : Role) (filler : Lit Concept) :
    EqState Node Concept Role :=
  { state with base := state.base.materializeWitness source target role filler }

theorem EqState.materializeWitness_realized
    (state : EqState Node Concept Role) (I : Interp Domain Concept Role)
    (value : Node → Domain) (hrealized : state.RealizedBy I value)
    (source target : Node) (role : Role) (filler : Lit Concept)
    (hobligation : state.base.obligation role filler source)
    (hfresh : state.Fresh target) :
    ∃ value', (state.materializeWitness source target role filler).RealizedBy I value' := by
  classical
  rcases hrealized.1.2.2 role filler source hobligation with
    ⟨witness, hedge, hfiller⟩
  have hsource : source ≠ target := by
    intro heq
    subst source
    exact hfresh.1.2.2 role filler hobligation
  let value' := Function.update value target witness
  refine ⟨value', ⟨?_, ?_, ?_⟩, ?_⟩
  · intro node lit hlabel
    rcases hlabel with hlabel | ⟨rfl, rfl⟩
    · have hnode : node ≠ target := by
        intro heq
        subst node
        exact hfresh.1.1 lit hlabel
      simpa [value', Function.update_of_ne hnode] using
        hrealized.1.1 node lit hlabel
    · simpa [value'] using hfiller
  · intro candidateRole candidateSource candidateTarget hedge'
    rcases hedge' with hedge' | ⟨rfl, rfl, rfl⟩
    · have hsource' : candidateSource ≠ target := by
        intro heq
        subst candidateSource
        exact (hfresh.1.2.1 candidateRole candidateTarget).1 hedge'
      have htarget' : candidateTarget ≠ target := by
        intro heq
        subst candidateTarget
        exact (hfresh.1.2.1 candidateRole candidateSource).2 hedge'
      simpa [value', Function.update_of_ne hsource', Function.update_of_ne htarget'] using
        hrealized.1.2.1 candidateRole candidateSource candidateTarget hedge'
    · simpa [value', Function.update_of_ne hsource] using hedge
  · intro candidateRole candidateFiller node hobligation'
    have hnode : node ≠ target := by
      intro heq
      subst node
      exact hfresh.1.2.2 candidateRole candidateFiller hobligation'
    rcases hrealized.1.2.2 candidateRole candidateFiller node hobligation' with
      ⟨witness', hedge', hfiller'⟩
    exact ⟨witness', by
      simpa [value', Function.update_of_ne hnode] using hedge', hfiller'⟩
  intro left right hequiv
  by_cases hleft : left = target
  · subst left
    have hright := hfresh.2 right hequiv
    subst right
    rfl
  · by_cases hright : right = target
    · subst right
      have hleftTarget := hfresh.2 left
        (state.equiv_equivalence.2 hequiv)
      exact (hleft hleftTarget).elim
    · have hold := hrealized.2 left right hequiv
      simpa [value', Function.update_of_ne hleft, Function.update_of_ne hright] using hold

def EqState.RealizableWith (state : EqState Node Concept Role)
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∃ (Domain : Type x) (I : Interp Domain Concept Role) (value : Node → Domain),
    I.models ontology ∧ state.RealizedBy I value

/-- Exhaustive HT refutations with equality merges. Unlike the equality-free
core, every head is branchable: equality children extend the node quotient. -/
inductive EqRefutes (Node : Type u)
    (ontology : List (Clause Variable Concept Role)) :
    EqState Node Concept Role → Prop where
  | clash (state)
      (hclash : ∃ positiveNode negativeNode concept,
        state.equiv positiveNode negativeNode ∧
          state.base.label positiveNode (.pos concept) ∧
          state.base.label negativeNode (.negated concept)) :
      EqRefutes Node ontology state
  | branch (state) (clause : Clause Variable Concept Role)
      (hclause : clause ∈ ontology) (assignment : Variable → Node)
      (hbody : ∀ atom ∈ clause.body, state.holdsAtom assignment atom)
      (children : ∀ atom, atom ∈ clause.head →
        EqRefutes Node ontology (state.assertAtom assignment atom)) :
      EqRefutes Node ontology state
  | witness (state) (source target : Node) (role : Role) (filler : Lit Concept)
      (hobligation : state.base.obligation role filler source)
      (hfresh : state.Fresh target)
      (child : EqRefutes Node ontology
        (state.materializeWitness source target role filler)) :
      EqRefutes Node ontology state

theorem EqRefutes.sound
    (hrefutes : EqRefutes Node ontology state) :
    ¬state.RealizableWith ontology := by
  induction hrefutes with
  | clash state hclash =>
      rintro ⟨Domain, I, value, _, hrealized⟩
      rcases hclash with
        ⟨positiveNode, negativeNode, concept, hequiv, hpositive, hnegative⟩
      have hpositiveSat := hrealized.1.1 positiveNode (.pos concept) hpositive
      have hnegativeSat := hrealized.1.1 negativeNode (.negated concept) hnegative
      have hvalue := hrealized.2 positiveNode negativeNode hequiv
      rw [← hvalue] at hnegativeSat
      exact hnegativeSat hpositiveSat
  | branch state clause hclause assignment hbody children ih =>
      rintro ⟨Domain, I, value, hmodels, hrealized⟩
      rcases state.hyper_branch_sound I value hrealized clause
          (hmodels clause hclause) assignment hbody with
        ⟨atom, hatom, hchild⟩
      exact ih atom hatom ⟨Domain, I, value, hmodels, hchild⟩
  | witness state source target role filler hobligation hfresh child ih =>
      rintro ⟨Domain, I, value, hmodels, hrealized⟩
      rcases state.materializeWitness_realized I value hrealized source target
          role filler hobligation hfresh with ⟨value', hchild⟩
      exact ih ⟨Domain, I, value', hmodels, hchild⟩

#print axioms EqState.merge_realized
#print axioms EqState.assertAtom_realized
#print axioms EqState.hyper_branch_sound
#print axioms EqState.materializeWitness_realized
#print axioms EqRefutes.sound

end ContextCalculus.Hypertableau
