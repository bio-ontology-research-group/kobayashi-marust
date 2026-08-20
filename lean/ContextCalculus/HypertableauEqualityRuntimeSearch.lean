import ContextCalculus.HypertableauRuntimeSearch
import ContextCalculus.HypertableauEqualitySearch
import ContextCalculus.HypertableauEqualityBlocking

/-!
# Executable equality-aware hypertableau runtime selection

This module mirrors the first two controls of Rust's equality-aware recursive
search.  It first scans for a clash modulo the complete node equivalence, then
scans clauses in ontology order and finite assignments in enumeration order.
-/

namespace ContextCalculus.Hypertableau

/-- Exhaustive equality-aware refutations whose branch bodies use the complete
quotient closure. This is the semantic recursion implemented by Rust's
`closed_holds` grounding test. -/
inductive ClosedEqRefutes (Node : Type u)
    (ontology : List (Clause Variable Concept Role)) :
    EqState Node Concept Role → Prop where
  | clash (state)
      (hclash : ∃ positiveNode negativeNode concept,
        state.equiv positiveNode negativeNode ∧
          state.base.label positiveNode (.pos concept) ∧
          state.base.label negativeNode (.negated concept)) :
      ClosedEqRefutes Node ontology state
  | branch (state) (clause : Clause Variable Concept Role)
      (hclause : clause ∈ ontology) (assignment : Variable → Node)
      (hbody : ∀ atom ∈ clause.body,
        state.closedHoldsAtom assignment atom)
      (children : ∀ atom, atom ∈ clause.head →
        ClosedEqRefutes Node ontology (state.assertAtom assignment atom)) :
      ClosedEqRefutes Node ontology state
  | witness (state) (source target : Node) (role : Role) (filler : Lit Concept)
      (hobligation : state.base.obligation role filler source)
      (hfresh : state.Fresh target)
      (child : ClosedEqRefutes Node ontology
        (state.materializeWitness source target role filler)) :
      ClosedEqRefutes Node ontology state

theorem ClosedEqRefutes.sound
    (hrefutes : ClosedEqRefutes Node ontology state) :
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
      have hsemanticBody : ∀ atom ∈ clause.body,
          I.satAtom (value ∘ assignment) atom := by
        intro atom hatom
        exact state.realized_closedHoldsAtom I value hrealized assignment atom
          (hbody atom hatom)
      rcases hmodels clause hclause (value ∘ assignment) hsemanticBody with
        ⟨atom, hatom, hsat⟩
      exact ih atom hatom ⟨Domain, I, value, hmodels,
        state.assertAtom_realized I value hrealized assignment atom hsat⟩
  | witness state source target role filler hobligation hfresh child ih =>
      rintro ⟨Domain, I, value, hmodels, hrealized⟩
      rcases state.materializeWitness_realized I value hrealized source target
          role filler hobligation hfresh with ⟨value', hchild⟩
      exact ih ⟨Domain, I, value', hmodels, hchild⟩

theorem EqRefutes.toClosed
    (hrefutes : EqRefutes Node ontology state) :
    ClosedEqRefutes Node ontology state := by
  induction hrefutes with
  | clash state hclash => exact .clash state hclash
  | branch state clause hclause assignment hbody children ih =>
      exact .branch state clause hclause assignment
        (fun atom hatom => state.holdsAtom_implies_closedHoldsAtom assignment atom
          (hbody atom hatom)) ih
  | witness state source target role filler hobligation hfresh child ih =>
      exact .witness state source target role filler hobligation hfresh ih

abbrev EqClashCandidate (Node Concept : Type) := Node × Node × Concept

noncomputable def allEqClashCandidates
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept] :
    List (EqClashCandidate Node Concept) := by
  classical
  exact (Finset.univ.toList : List Node).flatMap fun positiveNode =>
    (Finset.univ.toList : List Node).flatMap fun negativeNode =>
      (Finset.univ.toList : List Concept).map fun concept =>
        (positiveNode, negativeNode, concept)

theorem mem_allEqClashCandidates
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (candidate : EqClashCandidate Node Concept) :
    candidate ∈ allEqClashCandidates := by
  classical
  rcases candidate with ⟨positiveNode, negativeNode, concept⟩
  simp [allEqClashCandidates]

noncomputable def eqClashCandidateBool
    (state : EqState Node Concept Role)
    (candidate : EqClashCandidate Node Concept) : Bool := by
  classical
  exact decide (state.equiv candidate.1 candidate.2.1) &&
    decide (state.base.label candidate.1 (.pos candidate.2.2)) &&
    decide (state.base.label candidate.2.1 (.negated candidate.2.2))

theorem eqClashCandidateBool_eq_true_iff
    (state : EqState Node Concept Role)
    (candidate : EqClashCandidate Node Concept) :
    eqClashCandidateBool state candidate = true ↔
      state.equiv candidate.1 candidate.2.1 ∧
      state.base.label candidate.1 (.pos candidate.2.2) ∧
      state.base.label candidate.2.1 (.negated candidate.2.2) := by
  simp [eqClashCandidateBool, and_assoc]

noncomputable def selectEqClash
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (state : EqState Node Concept Role) :
    Option (EqClashCandidate Node Concept) :=
  firstMatch (eqClashCandidateBool state) allEqClashCandidates

theorem selectEqClash_eq_none_iff
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (state : EqState Node Concept Role) :
    selectEqClash state = none ↔ state.ClosedClashFree := by
  classical
  rw [selectEqClash, firstMatch_eq_none_iff]
  constructor
  · intro hscan positiveNode negativeNode concept hequiv hlabels
    have hfalse := hscan (positiveNode, negativeNode, concept)
      (mem_allEqClashCandidates (positiveNode, negativeNode, concept))
    rw [(eqClashCandidateBool_eq_true_iff state _).mpr
      ⟨hequiv, hlabels⟩] at hfalse
    contradiction
  · intro hfree candidate _
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hclash := (eqClashCandidateBool_eq_true_iff state candidate).mp htrue
    exact hfree candidate.1 candidate.2.1 candidate.2.2 hclash.1 hclash.2

theorem selectEqClash_refutes
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (ontology : List (Clause Variable Concept Role))
    (state : EqState Node Concept Role)
    {candidate : EqClashCandidate Node Concept}
    (hselect : selectEqClash state = some candidate) :
    EqRefutes Node ontology state := by
  classical
  have hfound := firstMatch_eq_some_mem (by simpa [selectEqClash] using hselect)
  have hclash := (eqClashCandidateBool_eq_true_iff state candidate).mp hfound.2
  exact .clash state ⟨candidate.1, candidate.2.1, candidate.2.2,
    hclash.1, hclash.2.1, hclash.2.2⟩

theorem selectEqClash_closedRefutes
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (ontology : List (Clause Variable Concept Role))
    (state : EqState Node Concept Role)
    {candidate : EqClashCandidate Node Concept}
    (hselect : selectEqClash state = some candidate) :
    ClosedEqRefutes Node ontology state :=
  (selectEqClash_refutes ontology state hselect).toClosed

noncomputable def closedHoldsAtomBool
    (state : EqState Node Concept Role)
    (assignment : Variable → Node) (atom : Atom Variable Concept Role) : Bool := by
  classical
  exact decide (state.closedHoldsAtom assignment atom)

@[simp] theorem closedHoldsAtomBool_eq_true_iff
    (state : EqState Node Concept Role)
    (assignment : Variable → Node) (atom : Atom Variable Concept Role) :
    closedHoldsAtomBool state assignment atom = true ↔
      state.closedHoldsAtom assignment atom := by
  simp [closedHoldsAtomBool]

@[simp] theorem closedHoldsAtomBool_eq_false_iff
    (state : EqState Node Concept Role)
    (assignment : Variable → Node) (atom : Atom Variable Concept Role) :
    closedHoldsAtomBool state assignment atom = false ↔
      ¬state.closedHoldsAtom assignment atom := by
  rw [Bool.eq_false_iff]
  simp

noncomputable def eqGroundingUndischarged
    (state : EqState Node Concept Role)
    (grounding : Grounding Variable Node Concept Role) : Bool :=
  grounding.1.body.all (closedHoldsAtomBool state grounding.2) &&
    grounding.1.head.all fun atom => !(closedHoldsAtomBool state grounding.2 atom)

theorem eqGroundingUndischarged_eq_true_iff
    {state : EqState Node Concept Role}
    {grounding : Grounding Variable Node Concept Role} :
    eqGroundingUndischarged state grounding = true ↔
      (∀ atom ∈ grounding.1.body, state.closedHoldsAtom grounding.2 atom) ∧
      ∀ atom ∈ grounding.1.head, ¬state.closedHoldsAtom grounding.2 atom := by
  simp [eqGroundingUndischarged, List.all_eq_true]

theorem quotientClosedHoldsAtomB_eq_closedHoldsAtomBool
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) :
    certificate.quotientClosedHoldsAtomB assignment atom =
      closedHoldsAtomBool certificate.state assignment atom := by
  apply Bool.eq_iff_iff.mpr
  rw [certificate.quotientClosedHoldsAtomB_eq_true hvalid]
  exact (closedHoldsAtomBool_eq_true_iff certificate.state assignment atom).symm

def eqCertificateGroundingUndischarged
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (grounding : Grounding (Fin variableCount) (Fin nodeCount)
      (Fin conceptCount) (Fin roleCount)) : Bool :=
  grounding.1.body.all
      (certificate.quotientClosedHoldsAtomB grounding.2) &&
    grounding.1.head.all fun atom =>
      !(certificate.quotientClosedHoldsAtomB grounding.2 atom)

theorem eqCertificateGroundingUndischarged_eq_runtime
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (grounding : Grounding (Fin variableCount) (Fin nodeCount)
      (Fin conceptCount) (Fin roleCount)) :
    eqCertificateGroundingUndischarged certificate grounding =
      eqGroundingUndischarged certificate.state grounding := by
  unfold eqCertificateGroundingUndischarged eqGroundingUndischarged
  have hfunction : certificate.quotientClosedHoldsAtomB grounding.2 =
      closedHoldsAtomBool certificate.state grounding.2 := by
    funext atom
    exact quotientClosedHoldsAtomB_eq_closedHoldsAtomBool
      certificate hvalid grounding.2 atom
  rw [hfunction]

noncomputable def selectEqCertificateClauseGrounding
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount) :
    Option (Grounding (Fin variableCount) (Fin nodeCount)
      (Fin conceptCount) (Fin roleCount)) :=
  firstMatch (eqCertificateGroundingUndischarged certificate)
    (allGroundings certificate.base.ontology)

theorem selectEqCertificateClauseGrounding_eq_runtime
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true) :
    selectEqCertificateClauseGrounding certificate =
      firstMatch (eqGroundingUndischarged certificate.state)
        (allGroundings certificate.base.ontology) := by
  unfold selectEqCertificateClauseGrounding
  apply congrArg (fun predicate => firstMatch predicate
    (allGroundings certificate.base.ontology))
  funext grounding
  exact eqCertificateGroundingUndischarged_eq_runtime certificate hvalid grounding

noncomputable def selectEqClauseGrounding
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role))
    (state : EqState Node Concept Role) :
    Option (Grounding Variable Node Concept Role) :=
  firstMatch (eqGroundingUndischarged state) (allGroundings ontology)

def EqState.HasClosedUndischarged
    (state : EqState Node Concept Role)
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∃ clause ∈ ontology, ∃ assignment,
    (∀ atom ∈ clause.body, state.closedHoldsAtom assignment atom) ∧
    ∀ atom ∈ clause.head, ¬state.closedHoldsAtom assignment atom

theorem selectEqClauseGrounding_eq_none_iff
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role))
    (state : EqState Node Concept Role) :
    selectEqClauseGrounding ontology state = none ↔
      ¬state.HasClosedUndischarged ontology := by
  classical
  rw [selectEqClauseGrounding, firstMatch_eq_none_iff]
  constructor
  · intro hscan hundischarged
    rcases hundischarged with ⟨clause, hclause, assignment, hbody, hhead⟩
    have hfalse := hscan (clause, assignment)
      ((mem_allGroundings).mpr hclause)
    rw [(eqGroundingUndischarged_eq_true_iff).mpr ⟨hbody, hhead⟩] at hfalse
    contradiction
  · intro hnone grounding hmem
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hgrounding := eqGroundingUndischarged_eq_true_iff.mp htrue
    exact hnone ⟨grounding.1, (mem_allGroundings.mp hmem), grounding.2,
      hgrounding.1, hgrounding.2⟩

theorem selectEqClauseGrounding_closedRefutes
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role))
    (state : EqState Node Concept Role)
    {grounding : Grounding Variable Node Concept Role}
    (hselect : selectEqClauseGrounding ontology state = some grounding)
    (children : ∀ atom, atom ∈ grounding.1.head →
      ClosedEqRefutes Node ontology (state.assertAtom grounding.2 atom)) :
    ClosedEqRefutes Node ontology state := by
  classical
  have hfound := firstMatch_eq_some_mem
    (by simpa [selectEqClauseGrounding] using hselect)
  have hproperties := eqGroundingUndischarged_eq_true_iff.mp hfound.2
  exact .branch state grounding.1 (mem_allGroundings.mp hfound.1)
    grounding.2 hproperties.1 children

/-- The runtime presents ancestors nearest-first. Blocking succeeds exactly
when that finite list contains an ancestor with the same complete quotient
pairwise signature. -/
noncomputable def quotientBlockedBool
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : EqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node)
    (source : Node) : Bool := by
  classical
  exact (ancestors source).any fun candidate =>
    decide (state.quotientRoleBlockingSignature parent candidate =
      state.quotientRoleBlockingSignature parent source)

theorem quotientBlockedBool_eq_true_iff
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : EqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node)
    (source : Node) :
    quotientBlockedBool state parent ancestors source = true ↔
      ∃ blocker ∈ ancestors source,
        state.quotientRoleBlockingSignature parent blocker =
          state.quotientRoleBlockingSignature parent source := by
  classical
  simp [quotientBlockedBool, List.any_eq_true]

noncomputable def eqUnblockedWitnessCandidateBool
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : EqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node)
    (candidate : WitnessCandidate Node Concept Role) : Bool := by
  classical
  exact decide (state.base.obligation candidate.1 candidate.2.1 candidate.2.2) &&
    decide (∀ witness, ¬(state.base.edge candidate.1 candidate.2.2 witness ∧
      state.base.label witness candidate.2.1)) &&
    !(quotientBlockedBool state parent ancestors candidate.2.2)

theorem eqUnblockedWitnessCandidateBool_eq_true_iff
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : EqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node)
    (candidate : WitnessCandidate Node Concept Role) :
    eqUnblockedWitnessCandidateBool state parent ancestors candidate = true ↔
      state.base.obligation candidate.1 candidate.2.1 candidate.2.2 ∧
      (∀ witness, ¬(state.base.edge candidate.1 candidate.2.2 witness ∧
        state.base.label witness candidate.2.1)) ∧
      quotientBlockedBool state parent ancestors candidate.2.2 = false := by
  classical
  simp [eqUnblockedWitnessCandidateBool, and_assoc]

noncomputable def selectEqUnblockedUnwitnessed
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : EqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node) :
    Option (WitnessCandidate Node Concept Role) :=
  firstMatch (eqUnblockedWitnessCandidateBool state parent ancestors)
    allWitnessCandidates

def EqState.HasUnblockedUnwitnessed
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : EqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node) : Prop :=
  ∃ source role filler,
    state.base.obligation role filler source ∧
    (∀ witness, ¬(state.base.edge role source witness ∧
      state.base.label witness filler)) ∧
    quotientBlockedBool state parent ancestors source = false

theorem selectEqUnblockedUnwitnessed_eq_none_iff
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : EqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node) :
    selectEqUnblockedUnwitnessed state parent ancestors = none ↔
      ¬state.HasUnblockedUnwitnessed parent ancestors := by
  classical
  rw [selectEqUnblockedUnwitnessed, firstMatch_eq_none_iff]
  constructor
  · intro hscan hexists
    rcases hexists with ⟨source, role, filler, hobligation, hnowitness, hunblocked⟩
    have hfalse := hscan (role, filler, source)
      (mem_allWitnessCandidates (role, filler, source))
    rw [(eqUnblockedWitnessCandidateBool_eq_true_iff state parent ancestors _).mpr
      ⟨hobligation, hnowitness, hunblocked⟩] at hfalse
    contradiction
  · intro hnone candidate _
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hproperties :=
      (eqUnblockedWitnessCandidateBool_eq_true_iff state parent ancestors candidate).mp htrue
    exact hnone ⟨candidate.2.2, candidate.1, candidate.2.1,
      hproperties.1, hproperties.2.1, hproperties.2.2⟩

noncomputable def eqFreshNodeBool
    (state : EqState Node Concept Role) (target : Node) : Bool := by
  classical
  exact decide (state.Fresh target)

@[simp] theorem eqFreshNodeBool_eq_true_iff
    (state : EqState Node Concept Role) (target : Node) :
    eqFreshNodeBool state target = true ↔ state.Fresh target := by
  simp [eqFreshNodeBool]

noncomputable def selectEqFreshNode
    [Fintype Node] [DecidableEq Node]
    (state : EqState Node Concept Role) : Option Node :=
  firstMatch (eqFreshNodeBool state) Finset.univ.toList

theorem selectEqFreshNode_eq_none_iff
    [Fintype Node] [DecidableEq Node]
    (state : EqState Node Concept Role) :
    selectEqFreshNode state = none ↔ ¬∃ target, state.Fresh target := by
  classical
  rw [selectEqFreshNode, firstMatch_eq_none_iff]
  constructor
  · intro hscan hexists
    rcases hexists with ⟨target, hfresh⟩
    have hfalse := hscan target (by simp)
    rw [(eqFreshNodeBool_eq_true_iff state target).mpr hfresh] at hfalse
    contradiction
  · intro hnone target _
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact hnone ⟨target, (eqFreshNodeBool_eq_true_iff state target).mp htrue⟩

/-- A closed recursive child selected by the exact unblocked-obligation and
fresh-node scans reconstructs the equality-aware witness refutation rule. -/
theorem selectEqWitness_refutes
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (state : EqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node)
    {candidate : WitnessCandidate Node Concept Role}
    (hwitness : selectEqUnblockedUnwitnessed state parent ancestors = some candidate)
    {target : Node} (hfresh : selectEqFreshNode state = some target)
    (child : ClosedEqRefutes Node ontology
      (state.materializeWitness candidate.2.2 target candidate.1 candidate.2.1)) :
    ClosedEqRefutes Node ontology state := by
  classical
  have hcandidate := firstMatch_eq_some_mem
    (by simpa [selectEqUnblockedUnwitnessed] using hwitness)
  have hproperties :=
    (eqUnblockedWitnessCandidateBool_eq_true_iff state parent ancestors candidate).mp
      hcandidate.2
  have htarget := firstMatch_eq_some_mem
    (by simpa [selectEqFreshNode] using hfresh)
  exact .witness state candidate.2.2 target candidate.1 candidate.2.1
    hproperties.1 ((eqFreshNodeBool_eq_true_iff state target).mp htarget.2) child

mutual
  /-- Production-compatible recursive equality refutation check with full
  quotient-closed clause-body evaluation. -/
  def FiniteEqRefutationTree.checkClosed
      (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount) :
      FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount → Bool
    | .clash => certificate.equalityClosureValidB && certificate.closedClashB
    | .branch clause assignment children =>
        certificate.equalityClosureValidB &&
        decide (clause ∈ certificate.base.ontology) &&
        clause.body.all (certificate.quotientClosedHoldsAtomB assignment) &&
        children.checkClosed certificate assignment clause.head
    | .witness source target role filler child =>
        certificate.equalityClosureValidB &&
        decide ((role, filler, source) ∈ certificate.base.obligations) &&
        certificate.freshNodeB target &&
        child.checkClosed (certificate.materializeWitness source target role filler)

  def FiniteEqRefutationChildren.checkClosed
      (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
      (assignment : Fin variableCount → Fin nodeCount) :
      FiniteEqRefutationChildren nodeCount conceptCount roleCount variableCount →
      List (Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) → Bool
    | .nil, heads => heads.isEmpty
    | .cons .., [] => false
    | .cons atom next child rest, head :: heads =>
        decide (atom = head) && certificate.transitionB next assignment atom &&
        child.checkClosed next && rest.checkClosed certificate assignment heads
end

mutual
  /-- The production quotient-closed checker accepts every tree accepted by the
  earlier direct-premise checker. -/
  theorem FiniteEqRefutationTree.check_implies_checkClosed
      (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount) :
      ∀ certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount,
        tree.check certificate = true → tree.checkClosed certificate = true := by
    cases tree with
    | clash =>
        intro certificate hcheck
        simpa [FiniteEqRefutationTree.check, FiniteEqRefutationTree.checkClosed] using hcheck
    | branch clause assignment children =>
        intro certificate hcheck
        simp only [FiniteEqRefutationTree.check, Bool.and_eq_true,
          List.all_eq_true, decide_eq_true_eq] at hcheck
        rcases hcheck with ⟨⟨⟨hvalid, hclause⟩, hbody⟩, hchildren⟩
        simp only [FiniteEqRefutationTree.checkClosed, Bool.and_eq_true,
          List.all_eq_true, decide_eq_true_eq]
        refine ⟨⟨⟨hvalid, hclause⟩, ?_⟩, ?_⟩
        · intro atom hatom
          apply (certificate.quotientClosedHoldsAtomB_eq_true
            hvalid assignment atom).2
          exact certificate.state.holdsAtom_implies_closedHoldsAtom assignment atom
            ((certificate.closedHoldsAtomB_eq_true hvalid assignment atom).1
              (hbody atom hatom))
        · exact children.check_implies_checkClosed certificate assignment clause.head hchildren
    | witness source target role filler child =>
        intro certificate hcheck
        simp only [FiniteEqRefutationTree.check, Bool.and_eq_true,
          decide_eq_true_eq] at hcheck
        rcases hcheck with ⟨⟨⟨hvalid, hobligation⟩, hfresh⟩, hchild⟩
        simp only [FiniteEqRefutationTree.checkClosed, Bool.and_eq_true,
          decide_eq_true_eq]
        exact ⟨⟨⟨hvalid, hobligation⟩, hfresh⟩,
          child.check_implies_checkClosed
            (certificate.materializeWitness source target role filler) hchild⟩

  theorem FiniteEqRefutationChildren.check_implies_checkClosed
      (children : FiniteEqRefutationChildren
        nodeCount conceptCount roleCount variableCount) :
      ∀ (certificate : FiniteEqCertificate
          nodeCount conceptCount roleCount variableCount)
        (assignment : Fin variableCount → Fin nodeCount) heads,
        children.check certificate assignment heads = true →
        children.checkClosed certificate assignment heads = true := by
    cases children with
    | nil =>
        intro certificate assignment heads hcheck
        simpa [FiniteEqRefutationChildren.check,
          FiniteEqRefutationChildren.checkClosed] using hcheck
    | cons recorded next child rest =>
        intro certificate assignment heads hcheck
        cases heads with
        | nil => simp [FiniteEqRefutationChildren.check] at hcheck
        | cons head heads =>
            simp only [FiniteEqRefutationChildren.check, Bool.and_eq_true,
              decide_eq_true_eq] at hcheck
            rcases hcheck with ⟨⟨⟨hrecorded, htransition⟩, hchild⟩, hrest⟩
            simp only [FiniteEqRefutationChildren.checkClosed, Bool.and_eq_true,
              decide_eq_true_eq]
            exact ⟨⟨⟨hrecorded, htransition⟩,
              child.check_implies_checkClosed next hchild⟩,
              rest.check_implies_checkClosed certificate assignment heads hrest⟩

  theorem FiniteEqRefutationTree.checkClosed_sound
      (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount) :
      ∀ certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount,
        tree.checkClosed certificate = true →
        ClosedEqRefutes (Fin nodeCount) certificate.base.ontology certificate.state := by
    cases tree with
    | clash =>
        intro certificate hcheck
        simp only [FiniteEqRefutationTree.checkClosed, Bool.and_eq_true] at hcheck
        exact .clash certificate.state
          (certificate.closedClashB_sound hcheck.1 hcheck.2)
    | branch clause assignment children =>
        intro certificate hcheck
        simp only [FiniteEqRefutationTree.checkClosed, Bool.and_eq_true,
          List.all_eq_true, decide_eq_true_eq] at hcheck
        rcases hcheck with ⟨⟨⟨hvalid, hclause⟩, hbody⟩, hchildren⟩
        apply ClosedEqRefutes.branch certificate.state clause hclause assignment
        · intro atom hatom
          exact (certificate.quotientClosedHoldsAtomB_eq_true
            hvalid assignment atom).mp (hbody atom hatom)
        · intro atom hatom
          exact children.checkClosed_sound certificate assignment clause.head
            hchildren atom hatom
    | witness source target role filler child =>
        intro certificate hcheck
        simp only [FiniteEqRefutationTree.checkClosed, Bool.and_eq_true,
          decide_eq_true_eq] at hcheck
        rcases hcheck with ⟨⟨⟨hvalid, hobligation⟩, hfresh⟩, hchild⟩
        apply ClosedEqRefutes.witness certificate.state source target role filler
          hobligation ((certificate.freshNodeB_eq_true hvalid target).mp hfresh)
        rw [← certificate.state_materializeWitness source target role filler]
        exact child.checkClosed_sound
          (certificate.materializeWitness source target role filler) hchild

  theorem FiniteEqRefutationChildren.checkClosed_sound
      (children : FiniteEqRefutationChildren
        nodeCount conceptCount roleCount variableCount) :
      ∀ (certificate : FiniteEqCertificate
          nodeCount conceptCount roleCount variableCount)
        (assignment : Fin variableCount → Fin nodeCount) (heads)
        (_ : children.checkClosed certificate assignment heads = true)
        (atom), atom ∈ heads →
          ClosedEqRefutes (Fin nodeCount) certificate.base.ontology
            (certificate.state.assertAtom assignment atom) := by
    cases children with
    | nil =>
        intro certificate assignment heads hcheck atom hatom
        simp only [FiniteEqRefutationChildren.checkClosed,
          List.isEmpty_iff] at hcheck
        simp [hcheck] at hatom
    | cons recorded next child rest =>
        intro certificate assignment heads hcheck atom hatom
        cases heads with
        | nil => simp at hatom
        | cons head heads =>
            simp only [FiniteEqRefutationChildren.checkClosed,
              Bool.and_eq_true, decide_eq_true_eq] at hcheck
            rcases hcheck with
              ⟨⟨⟨hrecorded, htransition⟩, hchild⟩, hrest⟩
            subst recorded
            simp only [List.mem_cons] at hatom
            rcases hatom with hatom | hatom
            · subst atom
              rw [← certificate.transitionB_state next assignment head htransition]
              have hbase := certificate.transitionB_base next assignment head htransition
              have hontology : next.base.ontology = certificate.base.ontology := by
                rw [hbase]
                cases head <;> rfl
              simpa only [hontology] using child.checkClosed_sound next hchild
            · exact rest.checkClosed_sound certificate assignment heads hrest atom hatom
end

theorem exists_checkClosed_eq_children
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (heads : List (Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (hencode : ∀ atom, atom ∈ heads →
      let next := (certificate.assertAtom assignment atom).canonicalizeEqualityClosure
      ∃ tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount,
        tree.checkClosed next = true) :
    ∃ children : FiniteEqRefutationChildren
        nodeCount conceptCount roleCount variableCount,
      children.checkClosed certificate assignment heads = true := by
  induction heads with
  | nil => exact ⟨.nil, by simp [FiniteEqRefutationChildren.checkClosed]⟩
  | cons head tail ih =>
      let next := (certificate.assertAtom assignment head).canonicalizeEqualityClosure
      obtain ⟨tree, htree⟩ := hencode head (by simp)
      obtain ⟨rest, hrest⟩ := ih (fun atom hatom => hencode atom (by simp [hatom]))
      exact ⟨.cons head next tree rest, by
        simp [FiniteEqRefutationChildren.checkClosed, next, htree, hrest,
          certificate.transitionB_canonicalized_assertAtom assignment head]⟩

/-- Every finite quotient-closed equality refutation has an accepted production
tree. Canonicalization reconstructs checked representative paths after each
head transition. -/
theorem ClosedEqRefutes.exists_checkClosed_tree
    {ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {state : EqState (Fin nodeCount) (Fin conceptCount) (Fin roleCount)}
    (hrefutes : ClosedEqRefutes (Fin nodeCount) ontology state) :
    ∀ certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount,
      certificate.base.ontology = ontology → certificate.state = state →
      certificate.equalityClosureValidB = true →
      ∃ tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount,
        tree.checkClosed certificate = true := by
  induction hrefutes with
  | clash state hclash =>
      intro certificate hontology hstate hvalid
      rcases hclash with
        ⟨positiveNode, negativeNode, concept, hequiv, hpositive, hnegative⟩
      have hclosed : certificate.closedClashB = true := by
        cases hvalue : certificate.closedClashB with
        | true => rfl
        | false =>
            have hfree := certificate.not_closedClashB_closedClashFree hvalid hvalue
            rw [hstate] at hfree
            exact (hfree positiveNode negativeNode concept hequiv
              ⟨hpositive, hnegative⟩).elim
      exact ⟨.clash, by simp [FiniteEqRefutationTree.checkClosed, hvalid, hclosed]⟩
  | branch state clause hclause assignment hbody children ih =>
      intro certificate hontology hstate hvalid
      have hclause' : clause ∈ certificate.base.ontology := by
        simpa [hontology] using hclause
      have hbody' : ∀ atom ∈ clause.body,
          certificate.quotientClosedHoldsAtomB assignment atom = true := by
        intro atom hatom
        apply (certificate.quotientClosedHoldsAtomB_eq_true hvalid assignment atom).2
        rw [hstate]
        exact hbody atom hatom
      obtain ⟨encodedChildren, hencodedChildren⟩ :=
        exists_checkClosed_eq_children certificate assignment clause.head
          (fun atom hatom => by
            let next := (certificate.assertAtom assignment atom).canonicalizeEqualityClosure
            apply ih atom hatom next
            · cases atom <;>
                simpa [next, FiniteEqCertificate.canonicalizeEqualityClosure,
                  FiniteEqCertificate.assertAtom] using hontology
            · simp only [next, FiniteEqCertificate.canonicalizeEqualityClosure_state,
                certificate.state_assertAtom, hstate]
            · exact (certificate.assertAtom assignment atom).canonicalizeEqualityClosure_valid)
      refine ⟨.branch clause assignment encodedChildren, ?_⟩
      simp only [FiniteEqRefutationTree.checkClosed, Bool.and_eq_true,
        decide_eq_true_eq, List.all_eq_true]
      exact ⟨⟨⟨hvalid, hclause'⟩, hbody'⟩, hencodedChildren⟩
  | witness state source target role filler hobligation hfresh child ih =>
      intro certificate hontology hstate hvalid
      have hobligation' : (role, filler, source) ∈ certificate.base.obligations := by
        change certificate.state.base.obligation role filler source
        rw [hstate]
        exact hobligation
      have hfresh' : certificate.freshNodeB target = true :=
        (certificate.freshNodeB_eq_true hvalid target).2 (by simpa [hstate] using hfresh)
      obtain ⟨encodedChild, hencodedChild⟩ :=
        ih (certificate.materializeWitness source target role filler)
          (by simpa [hontology]) (by rw [certificate.state_materializeWitness, hstate]) hvalid
      refine ⟨.witness source target role filler encodedChild, ?_⟩
      simp [FiniteEqRefutationTree.checkClosed, hvalid, hobligation', hfresh', hencodedChild]

/-- Exact correspondence between the production quotient-closed checker and
its finite semantic refutation relation on canonical certificates. -/
theorem FiniteEqCertificate.closedRefutes_iff_exists_checkClosed_tree
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount) :
    ClosedEqRefutes (Fin nodeCount) certificate.base.ontology certificate.state ↔
      ∃ tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount,
        tree.checkClosed certificate.canonicalizeEqualityClosure = true := by
  constructor
  · intro hrefutes
    exact hrefutes.exists_checkClosed_tree certificate.canonicalizeEqualityClosure rfl rfl
      certificate.canonicalizeEqualityClosure_valid
  · rintro ⟨tree, hcheck⟩
    simpa using tree.checkClosed_sound certificate.canonicalizeEqualityClosure hcheck

theorem FiniteEqRefutationTree.checkClosed_unsatisfiable
    (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hcheck : tree.checkClosed certificate = true) :
    ¬certificate.state.RealizableWith certificate.base.ontology :=
  (tree.checkClosed_sound certificate hcheck).sound

theorem FiniteEqRefutationTree.checkClosed_ontology_unsatisfiable
    [Nonempty (Fin nodeCount)]
    (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hempty : certificate.EmptyRoot)
    (hcheck : tree.checkClosed certificate = true) :
    ¬∃ (Domain : Type) (I : Interp Domain (Fin conceptCount) (Fin roleCount)),
      Nonempty Domain ∧ I.models certificate.base.ontology := by
  rintro ⟨Domain, I, hdomain, hmodels⟩
  apply tree.checkClosed_unsatisfiable certificate hcheck
  let value : Fin nodeCount → Domain := fun _ => Classical.choice hdomain
  refine ⟨Domain, I, value, hmodels, ?_⟩
  rcases hempty with ⟨hlabels, hedges, hobligations⟩
  refine ⟨?_, ?_⟩
  · simp [FiniteEqCertificate.state, FiniteSatCertificate.state, State.RealizedBy,
      hlabels, hedges, hobligations]
  · intro left right _
    rfl

theorem FiniteEqRefutationTree.checkClosed_subsumption
    (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (sub sup : Fin conceptCount)
    (hroot : certificate.SubsumptionRoot root sub sup)
    (hcheck : tree.checkClosed certificate = true) :
    EntailsSub certificate.base.ontology sub sup := by
  intro Domain I hmodels value hsub
  by_contra hsup
  apply tree.checkClosed_unsatisfiable certificate hcheck
  refine ⟨Domain, I, fun _ => value, hmodels, ?_, ?_⟩
  · rcases hroot with ⟨hlabels, hedges, hobligations⟩
    refine ⟨?_, ?_, ?_⟩
    · intro node lit hlabel
      simp only [FiniteEqCertificate.state, FiniteSatCertificate.state, hlabels,
        List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hlabel
      rcases hlabel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa [Interp.satLit, Lit.pos] using hsub
      · simpa [Interp.satLit, Lit.negated] using hsup
    · simp [FiniteEqCertificate.state, FiniteSatCertificate.state, hedges]
    · simp [FiniteEqCertificate.state, FiniteSatCertificate.state, hobligations]
  · intro left right _
    rfl

theorem FiniteEqRefutationTree.checkClosed_unsatisfiable_concept
    (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (concept : Fin conceptCount)
    (hroot : certificate.UnsatisfiableRoot root concept)
    (hcheck : tree.checkClosed certificate = true) :
    UnsatisfiableConcept certificate.base.ontology concept := by
  intro Domain I hmodels value hconcept
  apply tree.checkClosed_unsatisfiable certificate hcheck
  refine ⟨Domain, I, fun _ => value, hmodels, ?_, ?_⟩
  · rcases hroot with ⟨hlabels, hedges, hobligations⟩
    refine ⟨?_, ?_, ?_⟩
    · intro node lit hlabel
      simp only [FiniteEqCertificate.state, FiniteSatCertificate.state, hlabels,
        List.mem_singleton, Prod.mk.injEq] at hlabel
      rcases hlabel with ⟨rfl, rfl⟩
      simpa [Interp.satLit, Lit.pos] using hconcept
    · simp [FiniteEqCertificate.state, FiniteSatCertificate.state, hedges]
    · simp [FiniteEqCertificate.state, FiniteSatCertificate.state, hobligations]
  · intro left right _
    rfl

#print axioms selectEqClash_eq_none_iff
#print axioms ClosedEqRefutes.sound
#print axioms EqRefutes.toClosed
#print axioms selectEqClash_refutes
#print axioms selectEqClash_closedRefutes
#print axioms selectEqClauseGrounding_eq_none_iff
#print axioms selectEqClauseGrounding_closedRefutes
#print axioms selectEqCertificateClauseGrounding_eq_runtime
#print axioms quotientBlockedBool_eq_true_iff
#print axioms selectEqUnblockedUnwitnessed_eq_none_iff
#print axioms selectEqFreshNode_eq_none_iff
#print axioms selectEqWitness_refutes
#print axioms FiniteEqRefutationTree.checkClosed_sound
#print axioms ClosedEqRefutes.exists_checkClosed_tree
#print axioms FiniteEqCertificate.closedRefutes_iff_exists_checkClosed_tree
#print axioms FiniteEqRefutationTree.checkClosed_ontology_unsatisfiable
#print axioms FiniteEqRefutationTree.checkClosed_subsumption
#print axioms FiniteEqRefutationTree.checkClosed_unsatisfiable_concept

end ContextCalculus.Hypertableau
