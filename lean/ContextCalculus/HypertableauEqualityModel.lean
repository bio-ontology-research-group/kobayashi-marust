import ContextCalculus.HypertableauEquality

/-!
# Canonical quotient models for equality-aware hypertableau states

Equality closes every branch fact, not only equality atoms. Labels, edges, and
existential obligations are therefore read modulo the complete node relation.
The endpoint theorem constructs a model on equivalence classes.
-/

namespace ContextCalculus.Hypertableau

def EqState.nodeSetoid (state : EqState Node Concept Role) : Setoid Node where
  r := state.equiv
  iseqv := state.equiv_equivalence

abbrev EqState.QuotientDomain (state : EqState Node Concept Role) : Type _ :=
  Quotient state.nodeSetoid

def EqState.closedLabel (state : EqState Node Concept Role)
    (node : Node) (lit : Lit Concept) : Prop :=
  ∃ source, state.equiv source node ∧ state.base.label source lit

def EqState.closedEdge (state : EqState Node Concept Role)
    (role : Role) (source target : Node) : Prop :=
  ∃ edgeSource edgeTarget,
    state.equiv edgeSource source ∧ state.equiv edgeTarget target ∧
      state.base.edge role edgeSource edgeTarget

def EqState.closedObligation (state : EqState Node Concept Role)
    (role : Role) (filler : Lit Concept) (node : Node) : Prop :=
  ∃ source, state.equiv source node ∧ state.base.obligation role filler source

theorem EqState.closedLabel_congr (state : EqState Node Concept Role)
    {left right : Node} (hrelated : state.equiv left right) (lit : Lit Concept) :
    state.closedLabel left lit ↔ state.closedLabel right lit := by
  constructor
  · rintro ⟨source, hsource, hlabel⟩
    exact ⟨source, state.equiv_equivalence.trans hsource hrelated, hlabel⟩
  · rintro ⟨source, hsource, hlabel⟩
    exact ⟨source, state.equiv_equivalence.trans hsource
      (state.equiv_equivalence.symm hrelated), hlabel⟩

theorem EqState.closedEdge_congr (state : EqState Node Concept Role)
    (role : Role) {source source' target target' : Node}
    (hsource : state.equiv source source')
    (htarget : state.equiv target target') :
    state.closedEdge role source target ↔ state.closedEdge role source' target' := by
  constructor
  · rintro ⟨edgeSource, edgeTarget, hedgeSource, hedgeTarget, hedge⟩
    exact ⟨edgeSource, edgeTarget,
      state.equiv_equivalence.trans hedgeSource hsource,
      state.equiv_equivalence.trans hedgeTarget htarget, hedge⟩
  · rintro ⟨edgeSource, edgeTarget, hedgeSource, hedgeTarget, hedge⟩
    exact ⟨edgeSource, edgeTarget,
      state.equiv_equivalence.trans hedgeSource
        (state.equiv_equivalence.symm hsource),
      state.equiv_equivalence.trans hedgeTarget
        (state.equiv_equivalence.symm htarget), hedge⟩

def EqState.closedHoldsAtom (state : EqState Node Concept Role)
    (assignment : Variable → Node) : Atom Variable Concept Role → Prop
  | .concept lit node => state.closedLabel (assignment node) lit
  | .role role source target =>
      state.closedEdge role (assignment source) (assignment target)
  | .exists_ role filler node =>
      state.closedObligation role filler (assignment node)
  | .eq left right => state.equiv (assignment left) (assignment right)

def EqState.ClosedClashFree (state : EqState Node Concept Role) : Prop :=
  ∀ positiveNode negativeNode concept, state.equiv positiveNode negativeNode →
    ¬(state.base.label positiveNode (.pos concept) ∧
      state.base.label negativeNode (.negated concept))

def EqState.ClosedWitnessComplete (state : EqState Node Concept Role) : Prop :=
  ∀ node role filler, state.base.obligation role filler node →
    ∃ witness, state.base.edge role node witness ∧ state.base.label witness filler

def EqState.ClosedSaturatedFor (state : EqState Node Concept Role)
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∀ clause ∈ ontology, ∀ assignment,
    (∀ atom ∈ clause.body, state.closedHoldsAtom assignment atom) →
    ∃ atom ∈ clause.head, state.closedHoldsAtom assignment atom

def EqState.quotientCanonical (state : EqState Node Concept Role) :
    Interp state.QuotientDomain Concept Role where
  concept concept value := ∃ node,
    Quotient.mk state.nodeSetoid node = value ∧ state.base.label node (.pos concept)
  role role source target := ∃ sourceNode targetNode,
    Quotient.mk state.nodeSetoid sourceNode = source ∧
      Quotient.mk state.nodeSetoid targetNode = target ∧
      state.base.edge role sourceNode targetNode

theorem EqState.quotientCanonical_sat_closedLabel
    (state : EqState Node Concept Role) (hclash : state.ClosedClashFree)
    (node : Node) (lit : Lit Concept) (hlabel : state.closedLabel node lit) :
    state.quotientCanonical.satLit lit (Quotient.mk state.nodeSetoid node) := by
  rcases hlabel with ⟨source, hequiv, hlabel⟩
  rcases lit with ⟨concept, neg⟩
  cases neg with
  | false => exact ⟨source, Quotient.sound hequiv, hlabel⟩
  | true =>
      intro hpositive
      rcases hpositive with ⟨positiveNode, heq, hpositive⟩
      have hrelated : state.equiv positiveNode source :=
        Quotient.exact (heq.trans (Quotient.sound hequiv).symm)
      exact hclash positiveNode source concept hrelated ⟨hpositive, hlabel⟩

theorem EqState.quotientCanonical_sat_closedAtom
    (state : EqState Node Concept Role) (hclash : state.ClosedClashFree)
    (hwitness : state.ClosedWitnessComplete)
    (assignment : Variable → Node) (atom : Atom Variable Concept Role)
    (hholds : state.closedHoldsAtom assignment atom) :
    state.quotientCanonical.satAtom
      (fun v => Quotient.mk state.nodeSetoid (assignment v)) atom := by
  cases atom with
  | concept lit node =>
      exact state.quotientCanonical_sat_closedLabel hclash _ _ hholds
  | role role source target =>
      rcases hholds with ⟨edgeSource, edgeTarget, hsource, htarget, hedge⟩
      exact ⟨edgeSource, edgeTarget, Quotient.sound hsource,
        Quotient.sound htarget, hedge⟩
  | exists_ role filler node =>
      rcases hholds with ⟨source, hsource, hobligation⟩
      rcases hwitness source role filler hobligation with ⟨target, hedge, hlabel⟩
      refine ⟨Quotient.mk state.nodeSetoid target, ?_, ?_⟩
      · exact ⟨source, target, Quotient.sound hsource, rfl, hedge⟩
      · exact state.quotientCanonical_sat_closedLabel hclash target filler
          ⟨target, state.equiv_equivalence.1 target, hlabel⟩
  | eq left right => exact Quotient.sound hholds

theorem EqState.closedPositive_of_canonical
    (state : EqState Node Concept Role) (node : Node) (concept : Concept)
    (hsat : state.quotientCanonical.concept concept
      (Quotient.mk state.nodeSetoid node)) :
    state.closedLabel node (.pos concept) := by
  rcases hsat with ⟨source, heq, hlabel⟩
  exact ⟨source, Quotient.exact heq, hlabel⟩

theorem EqState.closedEdge_of_canonical
    (state : EqState Node Concept Role) (role : Role) (source target : Node)
    (hsat : state.quotientCanonical.role role
      (Quotient.mk state.nodeSetoid source)
      (Quotient.mk state.nodeSetoid target)) :
    state.closedEdge role source target := by
  rcases hsat with ⟨edgeSource, edgeTarget, hsource, htarget, hedge⟩
  exact ⟨edgeSource, edgeTarget, Quotient.exact hsource,
    Quotient.exact htarget, hedge⟩

theorem EqState.quotientCanonical_models_of_closed_saturated
    (state : EqState Node Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (hguarded : ∀ clause ∈ ontology, clause.GuardedBody)
    (hclash : state.ClosedClashFree)
    (hwitness : state.ClosedWitnessComplete)
    (hsaturated : state.ClosedSaturatedFor ontology) :
    state.quotientCanonical.models ontology := by
  intro clause hclause semanticAssignment hbody
  have representatives : ∀ v, ∃ node,
      Quotient.mk state.nodeSetoid node = semanticAssignment v :=
    fun v => Quotient.exists_rep (semanticAssignment v)
  choose assignment hassignment using representatives
  have hclosedBody : ∀ atom ∈ clause.body,
      state.closedHoldsAtom assignment atom := by
    intro atom hatom
    have hsat : state.quotientCanonical.satAtom
        (fun v => Quotient.mk state.nodeSetoid (assignment v)) atom := by
      simpa only [hassignment] using hbody atom hatom
    cases atom with
    | concept lit node =>
        have hguard := hguarded clause hclause (.concept lit node) hatom
        rcases lit with ⟨concept, neg⟩
        cases neg with
        | false => exact state.closedPositive_of_canonical _ _ hsat
        | true => simp [BodyAtom] at hguard
    | role role source target =>
        exact state.closedEdge_of_canonical role _ _ hsat
    | exists_ role filler node =>
        have hguard := hguarded clause hclause (.exists_ role filler node) hatom
        simp [BodyAtom] at hguard
    | eq left right => exact Quotient.exact hsat
  rcases hsaturated clause hclause assignment hclosedBody with
    ⟨atom, hatom, hholds⟩
  refine ⟨atom, hatom, ?_⟩
  have hsat := state.quotientCanonical_sat_closedAtom hclash hwitness
    assignment atom hholds
  simpa only [hassignment] using hsat

#print axioms EqState.closedLabel_congr
#print axioms EqState.closedEdge_congr
#print axioms EqState.quotientCanonical_models_of_closed_saturated

end ContextCalculus.Hypertableau
