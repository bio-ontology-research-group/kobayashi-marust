import ContextCalculus.HypertableauAnchoredUnravelling
import ContextCalculus.HypertableauCertificate
import ContextCalculus.HypertableauRegularCertificate
import Mathlib.Data.Fintype.Basic

/-!
# Executable finite premises for anchored HT models

This checker layer derives the finite semantic premises of the anchored
canonical-model theorem from bounded certificate vectors. The later wire layer
only decodes natural-number identifiers into these finite objects.
-/

namespace ContextCalculus.Hypertableau

namespace AnchoredForestDomain

def NominalAnchor
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount))
    (node : Fin nodeCount) : Prop :=
  ∃ name, nominalRoot name = some node

instance nominalAnchorDecidable
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount)) :
    DecidablePred (NominalAnchor nominalRoot) := by
  intro node
  exact Fintype.decidableExistsFintype

def nominalLabelCoherentB
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount)) : Bool :=
  (List.finRange conceptCount).all fun name =>
    match nominalRoot name with
    | none => true
    | some root =>
        (List.finRange nodeCount).all fun node =>
          decide (((node, Lit.pos name) ∈ certificate.labels) ↔ node = root) &&
          decide ((node, Lit.negated name) ∈ certificate.labels → node ≠ root)

theorem nominalLabelCoherentB_sound
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount))
    (hcheck : nominalLabelCoherentB certificate nominalRoot = true) :
    NominalLabelCoherent certificate.state (NominalAnchor nominalRoot) nominalRoot := by
  simp only [nominalLabelCoherentB, List.all_eq_true] at hcheck
  intro name root hroot
  have hname := hcheck name (List.mem_finRange name)
  rw [hroot] at hname
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hname
  refine ⟨⟨name, hroot⟩, ?_, ?_⟩
  · intro node
    exact (hname node (List.mem_finRange node)).1
  · intro node hnegative
    exact (hname node (List.mem_finRange node)).2 hnegative

def clashFreeB
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount) : Bool :=
  certificate.labels.all fun entry =>
    decide ((entry.1, entry.2.complement) ∉ certificate.labels)

theorem clashFreeB_sound
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (hcheck : clashFreeB certificate = true) : certificate.state.ClashFree := by
  simp only [clashFreeB, List.all_eq_true, decide_eq_true_eq] at hcheck
  intro node concept hboth
  have hnot := hcheck (node, Lit.pos concept) hboth.1
  simp only [Lit.complement, Lit.pos, Bool.not_false] at hnot
  exact hnot hboth.2

def redirectWitnessCompleteB
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (redirect : Fin nodeCount → Fin nodeCount) : Bool :=
  certificate.obligations.all fun obligation =>
    (List.finRange nodeCount).any fun target =>
      decide ((obligation.1, redirect obligation.2.2, target) ∈ certificate.edges) &&
      decide ((target, obligation.2.1) ∈ certificate.labels)

theorem redirectWitnessCompleteB_sound
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (redirect : Fin nodeCount → Fin nodeCount)
    (hcheck : redirectWitnessCompleteB certificate redirect = true) :
    RedirectWitnessComplete certificate.state redirect := by
  simp only [redirectWitnessCompleteB, List.all_eq_true] at hcheck
  intro node role filler hobligation
  have hentry : (role, filler, node) ∈ certificate.obligations := hobligation
  have h := hcheck (role, filler, node) hentry
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨target, _, hedge, hlabel⟩
  exact ⟨target, hedge, hlabel⟩

def finitePremisesB
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (redirect : Fin nodeCount → Fin nodeCount)
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount)) : Bool :=
  clashFreeB certificate &&
    nominalLabelCoherentB certificate nominalRoot &&
    redirectWitnessCompleteB certificate redirect

def nominalGuardB
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount))
    (clause : Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))
    (variableNode : Fin variableCount) : Bool :=
  clause.body.any fun atom =>
    match atom with
    | .concept lit node =>
        !lit.neg && decide (node = variableNode) && (nominalRoot lit.concept).isSome
    | _ => false

theorem nominalGuardB_sound
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount))
    (clause : Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))
    (variableNode : Fin variableCount)
    (hcheck : nominalGuardB nominalRoot clause variableNode = true) :
    ∃ name root, nominalRoot name = some root ∧
      Atom.concept (.pos name) variableNode ∈ clause.body := by
  simp only [nominalGuardB, List.any_eq_true] at hcheck
  rcases hcheck with ⟨atom, hatom, hcheck⟩
  cases atom with
  | concept lit node =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨hneg, rfl⟩, hsome⟩
      rcases lit with ⟨name, neg⟩
      cases neg with
      | false =>
          cases hroot : nominalRoot name with
          | none => simp [hroot] at hsome
          | some root => exact ⟨name, root, hroot, hatom⟩
      | true => simp at hneg
  | role => contradiction
  | exists_ => contradiction
  | eq => contradiction

def anchoredHeadLiftableB
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount))
    (clause : Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)) :
    Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount) → Bool
  | .concept .. => true
  | .exists_ .. => true
  | .role .. => false
  | .eq left right =>
      decide (left = right) || nominalGuardB nominalRoot clause left ||
        nominalGuardB nominalRoot clause right

theorem anchoredHeadLiftableB_sound
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount))
    (clause : Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount))
    (hcheck : anchoredHeadLiftableB nominalRoot clause atom = true) :
    AnchoredHeadLiftable nominalRoot clause atom := by
  cases atom with
  | concept => trivial
  | exists_ => trivial
  | role => contradiction
  | eq left right =>
      simp only [anchoredHeadLiftableB, Bool.or_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with (heq | hleft) | hright
      · exact Or.inl heq
      · exact Or.inr (Or.inl
          (nominalGuardB_sound nominalRoot clause left hleft))
      · exact Or.inr (Or.inr
          (nominalGuardB_sound nominalRoot clause right hright))

def AnchoredRegularValid
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount)) : Prop :=
  (∀ rule ∈ certificate.roleClauses,
    rule.Authorized certificate.rules) ∧
  (∀ clause ∈ certificate.residual, clause.GuardedBody) ∧
  (∀ clause ∈ certificate.residual, ∀ atom ∈ clause.head,
    AnchoredHeadLiftable nominalRoot clause atom) ∧
  certificate.state.ClashFree ∧
  certificate.state.WitnessComplete ∧
  (∀ node role filler, certificate.state.obligation role filler node →
    certificate.state.obligation role filler (certificate.redirect node)) ∧
  certificate.CoverClosed ∧
  (∀ clause ∈ certificate.residual,
    certificate.state.CoverDischarges certificate.coverRelation clause)

def anchoredRegularCheck
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount)) : Bool :=
  certificate.roleClauses.all certificate.authorizedB &&
  certificate.residual.all (fun clause => clause.body.all atomGuardedB) &&
  certificate.residual.all (fun clause =>
    clause.head.all (anchoredHeadLiftableB nominalRoot clause)) &&
  certificate.labels.all (fun entry =>
    decide ((entry.1, entry.2.complement) ∉ certificate.labels)) &&
  certificate.obligations.all (fun obligation =>
    (List.finRange nodeCount).any fun witness =>
      decide ((obligation.1, obligation.2.2, witness) ∈ certificate.edges) &&
      decide ((witness, obligation.2.1) ∈ certificate.labels)) &&
  certificate.obligations.all (fun obligation =>
    decide ((obligation.1, obligation.2.1,
      certificate.redirect obligation.2.2) ∈ certificate.obligations)) &&
  certificate.coverClosedB &&
  certificate.residual.all (fun clause =>
    (allAssignments nodeCount variableCount).all fun assignment =>
      !(clause.body.all (certificate.coverHoldsAtomB assignment)) ||
        clause.head.any (certificate.coverHoldsAtomB assignment))

theorem anchoredRegularCheck_sound
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount))
    (hcheck : anchoredRegularCheck certificate nominalRoot = true) :
    AnchoredRegularValid certificate nominalRoot := by
  simp only [anchoredRegularCheck, Bool.and_eq_true, List.all_eq_true] at hcheck
  rcases hcheck with
    ⟨⟨⟨⟨⟨⟨⟨hauthorized, hguarded⟩, hheads⟩, hclash⟩,
      hwitness⟩, hredirect⟩, hcover⟩, hdischarges⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rule hrule
    exact (certificate.authorizedB_eq_true rule).mp (hauthorized rule hrule)
  · intro clause hclause atom hatom
    have h := hguarded clause hclause atom hatom
    cases atom with
    | concept lit node =>
        rcases lit with ⟨concept, neg⟩
        cases neg <;> simp [atomGuardedB, BodyAtom] at h ⊢
    | role => trivial
    | exists_ => simp [atomGuardedB] at h
    | eq => trivial
  · intro clause hclause atom hatom
    exact anchoredHeadLiftableB_sound nominalRoot clause atom
      (hheads clause hclause atom hatom)
  · intro node concept hboth
    have hnot := hclash (node, Lit.pos concept) hboth.1
    simp only [Lit.complement, Lit.pos, Bool.not_false,
      decide_eq_true_eq] at hnot
    exact hnot hboth.2
  · intro node role filler hobligation
    have h := hwitness (role, filler, node) hobligation
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨witness, _, hedge, hlabel⟩
    exact ⟨witness, hedge, hlabel⟩
  · intro node role filler hobligation
    have h := hredirect (role, filler, node) hobligation
    simpa [FiniteRegularCertificate.state] using h
  · exact certificate.coverClosedB_sound hcover
  · intro clause hclause assignment hbody
    have h := hdischarges clause hclause assignment
      (mem_allAssignments nodeCount variableCount assignment)
    have hbodyB :
        clause.body.all (certificate.coverHoldsAtomB assignment) = true := by
      simp only [List.all_eq_true]
      intro atom hatom
      exact (certificate.coverHoldsAtomB_eq_true assignment atom).mpr
        (hbody atom hatom)
    have hheadB :
        clause.head.any (certificate.coverHoldsAtomB assignment) = true := by
      simpa [hbodyB] using h
    rw [List.any_eq_true] at hheadB
    rcases hheadB with ⟨atom, hatom, hholds⟩
    exact ⟨atom, hatom,
      (certificate.coverHoldsAtomB_eq_true assignment atom).mp hholds⟩

theorem finitePremisesB_sound
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (redirect : Fin nodeCount → Fin nodeCount)
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount))
    (hcheck : finitePremisesB certificate redirect nominalRoot = true) :
    certificate.state.ClashFree ∧
      NominalLabelCoherent certificate.state (NominalAnchor nominalRoot) nominalRoot ∧
      RedirectWitnessComplete certificate.state redirect := by
  simp only [finitePremisesB, Bool.and_eq_true] at hcheck
  exact ⟨clashFreeB_sound certificate hcheck.1.1,
    nominalLabelCoherentB_sound certificate nominalRoot hcheck.1.2,
    redirectWitnessCompleteB_sound certificate redirect hcheck.2⟩

/-- The ordinary finite certificate view of a regular certificate. This lets
the nominal checker consume exactly the same labels, edges, and obligations as
the regular saturation checker. -/
def regularSatCertificate
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount) :
    FiniteSatCertificate nodeCount conceptCount roleCount variableCount where
  ontology := certificate.ontology
  labels := certificate.labels
  edges := certificate.edges
  obligations := certificate.obligations

@[simp] theorem regularSatCertificate_state
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount) :
    (regularSatCertificate certificate).state = certificate.state := by
  rfl

/-- Combined executable SAT check for the regular nominal-aware fragment. The
regular checker establishes saturation and RBox closure; the anchored checker
establishes singleton nominal labels and redirected witnesses. -/
def anchoredCheck
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount)) : Bool :=
  anchoredRegularCheck certificate nominalRoot &&
    finitePremisesB (regularSatCertificate certificate) certificate.redirect nominalRoot

theorem anchoredCheck_models
    [NeZero nodeCount]
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount))
    (hcheck : anchoredCheck certificate nominalRoot = true) :
    (interpretation certificate.state certificate.redirect
      (fun _ _ _ _ => True) (NominalAnchor nominalRoot) certificate.rules
      nominalRoot).models certificate.ontology := by
  simp only [anchoredCheck, Bool.and_eq_true] at hcheck
  have hregular := anchoredRegularCheck_sound certificate nominalRoot hcheck.1
  have hanchored := finitePremisesB_sound (regularSatCertificate certificate)
    certificate.redirect nominalRoot hcheck.2
  rw [regularSatCertificate_state] at hanchored
  apply interpretation_models_partition_of_cover_anchored certificate.state
    certificate.redirect (fun _ _ _ _ => True) (NominalAnchor nominalRoot)
    certificate.rules nominalRoot certificate.coverRelation
    certificate.roleClauses certificate.residual
  · exact hregular.1
  · exact hregular.2.1
  · exact hregular.2.2.1
  · exact hanchored.1
  · exact hanchored.2.1
  · exact hanchored.2.2
  · intro _ _ _ _
    trivial
  · exact certificate.coverClosed_covers hregular.2.2.2.2.2.2.1
  · exact hregular.2.2.2.2.2.2.2

private def nominalEqualityCertificate : FiniteRegularCertificate 1 1 1 2 where
  labels := [(0, .pos 0)]
  edges := []
  obligations := []
  redirect := id
  cover := []
  subRoles := []
  inverseRoles := []
  chains := []
  reflexiveRoles := []
  roleClauses := []
  residual := [{
    body := [.concept (.pos 0) 0]
    head := [.eq 0 1]
  }]

private def singletonNominalRoot : Fin 1 → Option (Fin 1) := fun _ => some 0

example : anchoredCheck nominalEqualityCertificate singletonNominalRoot = true := by
  native_decide

private def unguardedEqualityCertificate : FiniteRegularCertificate 1 1 1 2 :=
  { nominalEqualityCertificate with residual := [{ body := [], head := [.eq 0 1] }] }

example : anchoredCheck unguardedEqualityCertificate singletonNominalRoot = false := by
  native_decide

#print axioms nominalLabelCoherentB_sound
#print axioms clashFreeB_sound
#print axioms redirectWitnessCompleteB_sound
#print axioms finitePremisesB_sound
#print axioms anchoredCheck_models

end AnchoredForestDomain

end ContextCalculus.Hypertableau
