import Mathlib.Data.List.Basic

/-!
# Hypertableau semantic core

This module gives the semantic endpoint for KM's guarded hypertableau.  It
separates the calculus from dependency sets, indexes, scheduling, backjumping,
and blocking, which are implementation devices and receive refinement proofs in
later modules.

The core atoms are signed concepts, roles, existential obligations, and
equality.  The main results are:

* `hyper_unit_sound`: a forced unit head is true in every realizing model;
* `hyper_branch_sound`: when a body matches, some head branch preserves every
  realizing model;
* `canonical_models_of_saturated`: a clash-free branch with witnesses for all
  existential obligations and every guarded clause discharged has a canonical
  model.

The completeness theorem deliberately states the exact saturation obligations.
It does not assume that the Rust search establishes them; that correspondence is
the next certification boundary.
-/

namespace ContextCalculus.Hypertableau

universe u v w x

structure Lit (Concept : Type u) where
  concept : Concept
  neg : Bool
deriving DecidableEq, Repr

def Lit.pos (concept : Concept) : Lit Concept := ⟨concept, false⟩
def Lit.negated (concept : Concept) : Lit Concept := ⟨concept, true⟩

def Lit.complement (lit : Lit Concept) : Lit Concept :=
  ⟨lit.concept, !lit.neg⟩

structure Interp (Domain : Type u) (Concept : Type v) (Role : Type w) where
  concept : Concept → Domain → Prop
  role : Role → Domain → Domain → Prop

def Interp.satLit (I : Interp Domain Concept Role)
    (lit : Lit Concept) (value : Domain) : Prop :=
  if lit.neg then ¬I.concept lit.concept value
  else I.concept lit.concept value

inductive Atom (Variable : Type u) (Concept : Type v) (Role : Type w) where
  | concept (lit : Lit Concept) (node : Variable)
  | role (role : Role) (source target : Variable)
  | exists_ (role : Role) (filler : Lit Concept) (node : Variable)
  | eq (left right : Variable)
deriving DecidableEq, Repr

structure Clause (Variable : Type u) (Concept : Type v) (Role : Type w) where
  body : List (Atom Variable Concept Role)
  head : List (Atom Variable Concept Role)
deriving DecidableEq, Repr

def Interp.satAtom (I : Interp Domain Concept Role)
    (assignment : Variable → Domain) : Atom Variable Concept Role → Prop
  | .concept lit node => I.satLit lit (assignment node)
  | .role role source target => I.role role (assignment source) (assignment target)
  | .exists_ role filler node =>
      ∃ value, I.role role (assignment node) value ∧ I.satLit filler value
  | .eq left right => assignment left = assignment right

def Interp.modelsClause (I : Interp Domain Concept Role)
    (clause : Clause Variable Concept Role) : Prop :=
  ∀ assignment,
    (∀ atom ∈ clause.body, I.satAtom assignment atom) →
    ∃ atom ∈ clause.head, I.satAtom assignment atom

def Interp.models (I : Interp Domain Concept Role)
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∀ clause ∈ ontology, I.modelsClause clause

structure State (Node : Type u) (Concept : Type v) (Role : Type w) where
  label : Node → Lit Concept → Prop
  edge : Role → Node → Node → Prop
  obligation : Role → Lit Concept → Node → Prop

@[ext] theorem State.ext
    {left right : State Node Concept Role}
    (hlabel : left.label = right.label)
    (hedge : left.edge = right.edge)
    (hobligation : left.obligation = right.obligation) : left = right := by
  cases left
  cases right
  simp_all

def State.holdsAtom (state : State Node Concept Role)
    (assignment : Variable → Node) : Atom Variable Concept Role → Prop
  | .concept lit node => state.label (assignment node) lit
  | .role role source target => state.edge role (assignment source) (assignment target)
  | .exists_ role filler node => state.obligation role filler (assignment node)
  | .eq left right => assignment left = assignment right

def State.ClashFree (state : State Node Concept Role) : Prop :=
  ∀ node concept,
    ¬(state.label node (.pos concept) ∧ state.label node (.negated concept))

def State.WitnessComplete (state : State Node Concept Role) : Prop :=
  ∀ node role filler, state.obligation role filler node →
    ∃ witness, state.edge role node witness ∧ state.label witness filler

/-- A node is fresh when no existing branch fact constrains its interpretation. -/
def State.Fresh (state : State Node Concept Role) (target : Node) : Prop :=
  (∀ lit, ¬state.label target lit) ∧
  (∀ role node, ¬state.edge role target node ∧ ¬state.edge role node target) ∧
  (∀ role filler, ¬state.obligation role filler target)

/-- Materialize one existential obligation at a fresh branch node. -/
def State.materializeWitness (state : State Node Concept Role)
    (source target : Node) (role : Role) (filler : Lit Concept) :
    State Node Concept Role where
  label node lit := state.label node lit ∨ (node = target ∧ lit = filler)
  edge candidateRole candidateSource candidateTarget :=
    state.edge candidateRole candidateSource candidateTarget ∨
      (candidateRole = role ∧ candidateSource = source ∧ candidateTarget = target)
  obligation := state.obligation

def State.RealizedBy (state : State Node Concept Role)
    (I : Interp Domain Concept Role) (value : Node → Domain) : Prop :=
  (∀ node lit, state.label node lit → I.satLit lit (value node)) ∧
  (∀ role source target, state.edge role source target →
    I.role role (value source) (value target)) ∧
  (∀ role filler node, state.obligation role filler node →
    ∃ witness, I.role role (value node) witness ∧ I.satLit filler witness)

theorem State.realized_holdsAtom
    (state : State Node Concept Role) (I : Interp Domain Concept Role)
    (value : Node → Domain) (hrealized : state.RealizedBy I value)
    (assignment : Variable → Node) (atom : Atom Variable Concept Role)
    (hholds : state.holdsAtom assignment atom) :
    I.satAtom (value ∘ assignment) atom := by
  cases atom with
  | concept lit node => exact hrealized.1 _ _ hholds
  | role role source target => exact hrealized.2.1 _ _ _ hholds
  | exists_ role filler node => exact hrealized.2.2 _ _ _ hholds
  | eq left right => simpa [Function.comp_apply] using congrArg value hholds

/-- A realized branch cannot contain complementary concept assertions. -/
theorem State.realized_clashFree
    (state : State Node Concept Role) (I : Interp Domain Concept Role)
    (value : Node → Domain) (hrealized : state.RealizedBy I value) :
    state.ClashFree := by
  intro node concept hclash
  have hpositive := hrealized.1 node (.pos concept) hclash.1
  have hnegative := hrealized.1 node (.negated concept) hclash.2
  exact hnegative hpositive

/-- Detecting complementary labels is sound: a clashing branch has no
realization in any interpretation. -/
theorem State.clash_sound
    (state : State Node Concept Role)
    (hclash : ∃ node concept,
      state.label node (.pos concept) ∧ state.label node (.negated concept)) :
    ¬∃ (Domain : Type x) (I : Interp Domain Concept Role) (value : Node → Domain),
      state.RealizedBy I value := by
  rintro ⟨Domain, I, value, hrealized⟩
  rcases hclash with ⟨node, concept, hpositive, hnegative⟩
  exact state.realized_clashFree I value hrealized node concept
    ⟨hpositive, hnegative⟩

/-- Every realized existential obligation has a semantic witness. This is the
soundness premise used when the implementation allocates a fresh successor. -/
theorem State.realized_obligation_witness
    (state : State Node Concept Role) (I : Interp Domain Concept Role)
    (value : Node → Domain) (hrealized : state.RealizedBy I value)
    (node : Node) (role : Role) (filler : Lit Concept)
    (hobligation : state.obligation role filler node) :
    ∃ witness, I.role role (value node) witness ∧ I.satLit filler witness :=
  hrealized.2.2 role filler node hobligation

/-- A semantic witness for an obligation can be assigned to a completely fresh
finite branch node while preserving every existing branch fact. -/
theorem State.materializeWitness_realized
    (state : State Node Concept Role) (I : Interp Domain Concept Role)
    (value : Node → Domain) (hrealized : state.RealizedBy I value)
    (source target : Node) (role : Role) (filler : Lit Concept)
    (hobligation : state.obligation role filler source)
    (hfresh : state.Fresh target) :
    ∃ value', (state.materializeWitness source target role filler).RealizedBy I value' := by
  classical
  rcases hrealized.2.2 role filler source hobligation with
    ⟨witness, hedge, hfiller⟩
  have hsource : source ≠ target := by
    intro heq
    subst source
    exact hfresh.2.2 role filler hobligation
  let value' := Function.update value target witness
  refine ⟨value', ?_, ?_, ?_⟩
  · intro node lit hlabel
    rcases hlabel with hlabel | ⟨rfl, rfl⟩
    · have hnode : node ≠ target := by
        intro heq
        subst node
        exact hfresh.1 lit hlabel
      simpa [value', Function.update_of_ne hnode] using hrealized.1 node lit hlabel
    · simpa [value'] using hfiller
  · intro candidateRole candidateSource candidateTarget hedge'
    rcases hedge' with hedge' | ⟨rfl, rfl, rfl⟩
    · have hsource' : candidateSource ≠ target := by
        intro heq
        subst candidateSource
        exact (hfresh.2.1 candidateRole candidateTarget).1 hedge'
      have htarget' : candidateTarget ≠ target := by
        intro heq
        subst candidateTarget
        exact (hfresh.2.1 candidateRole candidateSource).2 hedge'
      simpa [value', Function.update_of_ne hsource', Function.update_of_ne htarget'] using
        hrealized.2.1 candidateRole candidateSource candidateTarget hedge'
    · simpa [value', Function.update_of_ne hsource] using hedge
  · intro candidateRole candidateFiller node hobligation'
    have hnode : node ≠ target := by
      intro heq
      subst node
      exact hfresh.2.2 candidateRole candidateFiller hobligation'
    rcases hrealized.2.2 candidateRole candidateFiller node hobligation' with
      ⟨witness', hedge', hfiller'⟩
    exact ⟨witness', by simpa [value', Function.update_of_ne hnode] using hedge', hfiller'⟩

/-- A unit hyper-rule conclusion is semantically forced by a matched body. -/
theorem hyper_unit_sound
    (state : State Node Concept Role) (I : Interp Domain Concept Role)
    (value : Node → Domain) (hrealized : state.RealizedBy I value)
    (body : List (Atom Variable Concept Role))
    (head : Atom Variable Concept Role)
    (hclause : I.modelsClause ⟨body, [head]⟩)
    (assignment : Variable → Node)
    (hbody : ∀ atom ∈ body, state.holdsAtom assignment atom) :
    I.satAtom (value ∘ assignment) head := by
  have hsemanticBody : ∀ atom ∈ body,
      I.satAtom (value ∘ assignment) atom := by
    intro atom hatom
    exact state.realized_holdsAtom I value hrealized assignment atom (hbody atom hatom)
  rcases hclause (value ∘ assignment) hsemanticBody with ⟨atom, hatom, hsat⟩
  simp only [List.mem_singleton] at hatom
  subst atom
  exact hsat

/-- A matched disjunctive clause always has at least one model-preserving head
choice. This is the semantic basis of exhaustive DFS branching. -/
theorem hyper_branch_sound
    (state : State Node Concept Role) (I : Interp Domain Concept Role)
    (value : Node → Domain) (hrealized : state.RealizedBy I value)
    (clause : Clause Variable Concept Role)
    (hclause : I.modelsClause clause)
    (assignment : Variable → Node)
    (hbody : ∀ atom ∈ clause.body, state.holdsAtom assignment atom) :
    ∃ atom ∈ clause.head, I.satAtom (value ∘ assignment) atom := by
  apply hclause (value ∘ assignment)
  intro atom hatom
  exact state.realized_holdsAtom I value hrealized assignment atom (hbody atom hatom)

/-- Equality heads require node merging and are certified separately. Concept,
role, and existential heads can be asserted monotonically on one branch. -/
def Branchable : Atom Variable Concept Role → Prop
  | .eq .. => False
  | _ => True

def State.assertAtom (state : State Node Concept Role)
    (assignment : Variable → Node) : Atom Variable Concept Role →
    State Node Concept Role
  | .concept lit node =>
      { state with label := fun candidate candidateLit =>
          state.label candidate candidateLit ∨
            (candidate = assignment node ∧ candidateLit = lit) }
  | .role role source target =>
      { state with edge := fun candidateRole candidateSource candidateTarget =>
          state.edge candidateRole candidateSource candidateTarget ∨
            (candidateRole = role ∧ candidateSource = assignment source ∧
              candidateTarget = assignment target) }
  | .exists_ role filler node =>
      { state with obligation := fun candidateRole candidateFiller candidateNode =>
          state.obligation candidateRole candidateFiller candidateNode ∨
            (candidateRole = role ∧ candidateFiller = filler ∧
              candidateNode = assignment node) }
  | .eq .. => state

/-- Adding a semantically true branch head preserves realization. -/
theorem State.assertAtom_realized
    (state : State Node Concept Role) (I : Interp Domain Concept Role)
    (value : Node → Domain) (hrealized : state.RealizedBy I value)
    (assignment : Variable → Node) (atom : Atom Variable Concept Role)
    (hbranchable : Branchable atom)
    (hsat : I.satAtom (value ∘ assignment) atom) :
    (state.assertAtom assignment atom).RealizedBy I value := by
  cases atom with
  | concept lit node =>
      refine ⟨?_, hrealized.2.1, hrealized.2.2⟩
      intro candidate candidateLit hlabel
      rcases hlabel with hlabel | ⟨rfl, rfl⟩
      · exact hrealized.1 _ _ hlabel
      · exact hsat
  | role role source target =>
      refine ⟨hrealized.1, ?_, hrealized.2.2⟩
      intro candidateRole candidateSource candidateTarget hedge
      rcases hedge with hedge | ⟨rfl, rfl, rfl⟩
      · exact hrealized.2.1 _ _ _ hedge
      · exact hsat
  | exists_ role filler node =>
      refine ⟨hrealized.1, hrealized.2.1, ?_⟩
      intro candidateRole candidateFiller candidateNode hobligation
      rcases hobligation with hobligation | ⟨rfl, rfl, rfl⟩
      · exact hrealized.2.2 _ _ _ hobligation
      · exact hsat
  | eq left right => contradiction

def State.RealizableWith (state : State Node Concept Role)
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∃ (Domain : Type x) (I : Interp Domain Concept Role) (value : Node → Domain),
    I.models ontology ∧ state.RealizedBy I value

/-- An exhaustive refutation tree for the monotone guarded HT core. A branch
node has one refuting child for every head disjunct of a matched ontology
clause. Dependency sets and branch order do not occur because they can change
search order but not this exhaustive semantic tree. -/
inductive Refutes (Node : Type u)
    (ontology : List (Clause Variable Concept Role)) :
    State Node Concept Role → Prop where
  | clash (state)
      (hclash : ∃ node concept,
        state.label node (.pos concept) ∧ state.label node (.negated concept)) :
      Refutes Node ontology state
  | branch (state) (clause : Clause Variable Concept Role)
      (hclause : clause ∈ ontology) (assignment : Variable → Node)
      (hbody : ∀ atom ∈ clause.body, state.holdsAtom assignment atom)
      (hbranchable : ∀ atom ∈ clause.head, Branchable atom)
      (children : ∀ atom, atom ∈ clause.head →
        Refutes Node ontology (state.assertAtom assignment atom)) :
      Refutes Node ontology state
  | witness (state) (source target : Node) (role : Role) (filler : Lit Concept)
      (hobligation : state.obligation role filler source)
      (hfresh : state.Fresh target)
      (child : Refutes Node ontology
        (state.materializeWitness source target role filler)) :
      Refutes Node ontology state

/-- Soundness of a complete HT branch-refutation tree. -/
theorem Refutes.sound
    (hrefutes : Refutes Node ontology state) :
    ¬state.RealizableWith ontology := by
  induction hrefutes with
  | clash state hclash =>
      rintro ⟨Domain, I, value, _, hrealized⟩
      exact state.clash_sound hclash ⟨Domain, I, value, hrealized⟩
  | branch state clause hclause assignment hbody hbranchable children ih =>
      rintro ⟨Domain, I, value, hmodels, hrealized⟩
      rcases hyper_branch_sound state I value hrealized clause
          (hmodels clause hclause) assignment hbody with ⟨atom, hatom, hsat⟩
      exact ih atom hatom ⟨Domain, I, value, hmodels,
        state.assertAtom_realized I value hrealized assignment atom
          (hbranchable atom hatom) hsat⟩
  | witness state source target role filler hobligation hfresh child ih =>
      rintro ⟨Domain, I, value, hmodels, hrealized⟩
      rcases state.materializeWitness_realized I value hrealized source target role filler
          hobligation hfresh with ⟨value', hmaterialized⟩
      exact ih ⟨Domain, I, value', hmodels, hmaterialized⟩

/-- The canonical interpretation of a completion branch uses positive labels
as concept extensions and graph edges as role extensions. -/
def State.canonical (state : State Node Concept Role) :
    Interp Node Concept Role where
  concept concept node := state.label node (.pos concept)
  role := state.edge

theorem State.canonical_satLit
    (state : State Node Concept Role) (hclash : state.ClashFree)
    (node : Node) (lit : Lit Concept) (hlabel : state.label node lit) :
    state.canonical.satLit lit node := by
  rcases lit with ⟨concept, neg⟩
  cases neg with
  | false => exact hlabel
  | true =>
      intro hpositive
      exact hclash node concept ⟨hpositive, hlabel⟩

theorem State.canonical_realizes
    (state : State Node Concept Role)
    (hclash : state.ClashFree) (hwitness : state.WitnessComplete) :
    state.RealizedBy state.canonical id := by
  refine ⟨?_, ?_, ?_⟩
  · intro node lit hlabel
    simpa using state.canonical_satLit hclash node lit hlabel
  · intro role source target hedge
    exact hedge
  · intro role filler node hobligation
    rcases hwitness node role filler hobligation with ⟨witness, hedge, hlabel⟩
    exact ⟨witness, hedge, state.canonical_satLit hclash witness filler hlabel⟩

/-- Atoms allowed in guarded clause bodies. Positive concept and role atoms are
read directly from the canonical branch; equality is syntactic node identity.
Existential tests and negative concept tests require separate absorption rules
and are excluded from this core body fragment. -/
def BodyAtom : Atom Variable Concept Role → Prop
  | .concept lit _ => lit.neg = false
  | .role .. => True
  | .exists_ .. => False
  | .eq .. => True

theorem State.canonical_body_holds
    (state : State Node Concept Role)
    (assignment : Variable → Node) (atom : Atom Variable Concept Role)
    (hbodyAtom : BodyAtom atom)
    (hsat : state.canonical.satAtom assignment atom) :
    state.holdsAtom assignment atom := by
  cases atom with
  | concept lit node =>
      rcases lit with ⟨concept, neg⟩
      cases neg with
      | false => exact hsat
      | true => contradiction
  | role role source target => exact hsat
  | exists_ role filler node => contradiction
  | eq left right => exact hsat

def Clause.GuardedBody (clause : Clause Variable Concept Role) : Prop :=
  ∀ atom ∈ clause.body, BodyAtom atom

def State.Discharges (state : State Node Concept Role)
    (clause : Clause Variable Concept Role) : Prop :=
  ∀ assignment,
    (∀ atom ∈ clause.body, state.holdsAtom assignment atom) →
    ∃ atom ∈ clause.head, state.holdsAtom assignment atom

def State.SaturatedFor (state : State Node Concept Role)
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∀ clause ∈ ontology, state.Discharges clause

/-- Canonical-model completeness of a saturated guarded HT branch. -/
theorem canonical_models_of_saturated
    (state : State Node Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (hguarded : ∀ clause ∈ ontology, clause.GuardedBody)
    (hclash : state.ClashFree)
    (hwitness : state.WitnessComplete)
    (hsaturated : state.SaturatedFor ontology) :
    state.canonical.models ontology := by
  intro clause hclause assignment hsemanticBody
  have hsyntacticBody : ∀ atom ∈ clause.body,
      state.holdsAtom assignment atom := by
    intro atom hatom
    exact state.canonical_body_holds assignment atom
      (hguarded clause hclause atom hatom) (hsemanticBody atom hatom)
  rcases hsaturated clause hclause assignment hsyntacticBody with
    ⟨atom, hatom, hholds⟩
  exact ⟨atom, hatom,
    state.realized_holdsAtom state.canonical id
      (state.canonical_realizes hclash hwitness) assignment atom hholds⟩

/-- A saturated clash-free guarded branch exists exactly when the ontology has
the canonical model represented by that branch. This is the model-existence
direction used by HT refutational completeness. -/
theorem saturated_branch_satisfiable
    (state : State Node Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (hguarded : ∀ clause ∈ ontology, clause.GuardedBody)
    (hclash : state.ClashFree)
    (hwitness : state.WitnessComplete)
    (hsaturated : state.SaturatedFor ontology) :
    ∃ I : Interp Node Concept Role, I.models ontology := by
  exact ⟨state.canonical,
    canonical_models_of_saturated state ontology hguarded hclash hwitness hsaturated⟩

/-- Refutational-completeness endpoint: if no interpretation over the branch's
node domain models the guarded ontology, then no branch can simultaneously be
clash-free, witness-complete, and clause-saturated. An executable search proves
full refutational completeness by showing that every terminal open branch has
exactly these properties. -/
theorem no_saturated_branch_of_no_model
    (state : State Node Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (hguarded : ∀ clause ∈ ontology, clause.GuardedBody)
    (hnomodel : ¬∃ I : Interp Node Concept Role, I.models ontology) :
    ¬(state.ClashFree ∧ state.WitnessComplete ∧ state.SaturatedFor ontology) := by
  rintro ⟨hclash, hwitness, hsaturated⟩
  exact hnomodel (saturated_branch_satisfiable state ontology
    hguarded hclash hwitness hsaturated)

#print axioms State.realized_clashFree
#print axioms State.clash_sound
#print axioms State.realized_obligation_witness
#print axioms State.materializeWitness_realized
#print axioms hyper_unit_sound
#print axioms hyper_branch_sound
#print axioms State.assertAtom_realized
#print axioms Refutes.sound
#print axioms canonical_models_of_saturated
#print axioms saturated_branch_satisfiable
#print axioms no_saturated_branch_of_no_model

end ContextCalculus.Hypertableau
