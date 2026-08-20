import ContextCalculus.Hypertableau

/-!
# Executable certificates for open hypertableau branches

The certificate stores a finite ontology and a finite terminal completion graph.
`checkSat` decides all semantic endpoint obligations directly:

* every clause body is in the guarded core fragment;
* no node carries complementary concept literals;
* every existential obligation has an edge to a labelled witness;
* every grounding whose body holds has a head atom that holds.

Acceptance constructs a canonical model of the exact encoded ontology. The
grounding enumeration is intentionally simple and may be exponential; later
wire versions can replace it with checked matcher coverage evidence while
retaining the theorem below as their semantic target.
-/

namespace ContextCalculus.Hypertableau

universe u

structure FiniteSatCertificate (nodeCount conceptCount roleCount variableCount : Nat) where
  ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))
  labels : List (Fin nodeCount × Lit (Fin conceptCount))
  edges : List (Fin roleCount × Fin nodeCount × Fin nodeCount)
  obligations : List (Fin roleCount × Lit (Fin conceptCount) × Fin nodeCount)
deriving Repr

def FiniteSatCertificate.state
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount) :
    State (Fin nodeCount) (Fin conceptCount) (Fin roleCount) where
  label node lit := (node, lit) ∈ certificate.labels
  edge role source target := (role, source, target) ∈ certificate.edges
  obligation role filler node := (role, filler, node) ∈ certificate.obligations

def FiniteSatCertificate.Valid
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount) : Prop :=
  (∀ clause ∈ certificate.ontology, clause.GuardedBody) ∧
  certificate.state.ClashFree ∧
  (∀ obligation ∈ certificate.obligations,
    ∃ witness, (obligation.1, obligation.2.2, witness) ∈ certificate.edges ∧
      (witness, obligation.2.1) ∈ certificate.labels) ∧
  certificate.state.SaturatedFor certificate.ontology

def atomGuardedB : Atom V C R → Bool
  | .concept lit _ => !lit.neg
  | .role .. => true
  | .exists_ .. => false
  | .eq .. => true

def FiniteSatCertificate.holdsAtomB
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) : Bool :=
  match atom with
  | .concept lit node => decide ((assignment node, lit) ∈ certificate.labels)
  | .role role source target =>
      decide ((role, assignment source, assignment target) ∈ certificate.edges)
  | .exists_ role filler node =>
      decide ((role, filler, assignment node) ∈ certificate.obligations)
  | .eq left right => decide (assignment left = assignment right)

def allAssignments (nodeCount : Nat) : (variableCount : Nat) →
    List (Fin variableCount → Fin nodeCount)
  | 0 => [Fin.elim0]
  | variableCount + 1 =>
      (List.finRange nodeCount).flatMap fun head =>
        (allAssignments nodeCount variableCount).map fun tail => Fin.cases head tail

theorem mem_allAssignments (nodeCount : Nat) : ∀ (variableCount : Nat)
    (assignment : Fin variableCount → Fin nodeCount),
    assignment ∈ allAssignments nodeCount variableCount := by
  intro variableCount
  induction variableCount with
  | zero =>
      intro assignment
      simp only [allAssignments, List.mem_singleton]
      exact Subsingleton.elim _ _
  | succ variableCount ih =>
      intro assignment
      rw [allAssignments, List.mem_flatMap]
      refine ⟨assignment 0, by simp, ?_⟩
      rw [List.mem_map]
      let tail : Fin variableCount → Fin nodeCount := fun index => assignment index.succ
      refine ⟨tail, ih tail, ?_⟩
      funext index
      refine Fin.cases ?_ (fun predecessor => ?_) index
      · rfl
      · rfl

theorem FiniteSatCertificate.valid_witnessComplete
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.Valid) : certificate.state.WitnessComplete := by
  intro node role filler hobligation
  have hentry : (role, filler, node) ∈ certificate.obligations := hobligation
  rcases hvalid.2.2.1 (role, filler, node) hentry with
    ⟨witness, hedge, hlabel⟩
  exact ⟨witness, hedge, hlabel⟩

theorem FiniteSatCertificate.holdsAtomB_eq_true
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) :
    certificate.holdsAtomB assignment atom = true ↔
      certificate.state.holdsAtom assignment atom := by
  cases atom <;> simp [FiniteSatCertificate.holdsAtomB,
    FiniteSatCertificate.state, State.holdsAtom]

/-- Executable checker for a finite open branch. -/
def FiniteSatCertificate.checkSat
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount) : Bool :=
  certificate.ontology.all (fun clause => clause.body.all atomGuardedB) &&
  certificate.labels.all (fun entry =>
    decide ((entry.1, entry.2.complement) ∉ certificate.labels)) &&
  certificate.obligations.all (fun obligation =>
    (List.finRange nodeCount).any fun witness =>
      decide ((obligation.1, obligation.2.2, witness) ∈ certificate.edges) &&
      decide ((witness, obligation.2.1) ∈ certificate.labels)) &&
  certificate.ontology.all (fun clause =>
    (allAssignments nodeCount variableCount).all fun assignment =>
      !(clause.body.all (certificate.holdsAtomB assignment)) ||
        clause.head.any (certificate.holdsAtomB assignment))

theorem FiniteSatCertificate.checkSat_sound
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount) :
    certificate.checkSat = true → certificate.Valid := by
  intro hcheck
  simp only [FiniteSatCertificate.checkSat, Bool.and_eq_true,
    List.all_eq_true] at hcheck
  rcases hcheck with ⟨⟨⟨hguarded, hclash⟩, hwitness⟩, hsaturated⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro clause hclause atom hatom
    have h := hguarded clause hclause atom hatom
    cases atom with
    | concept lit node =>
        rcases lit with ⟨concept, neg⟩
        cases neg <;> simp [atomGuardedB, BodyAtom] at h ⊢
    | role => trivial
    | exists_ => simp [atomGuardedB] at h
    | eq => trivial
  · intro node concept hboth
    have hpositive : (node, Lit.pos concept) ∈ certificate.labels := hboth.1
    have hnot := hclash (node, Lit.pos concept) hpositive
    simp only [Lit.complement, Lit.pos, Bool.not_false, decide_eq_true_eq] at hnot
    exact hnot hboth.2
  · intro obligation hobligation
    have h := hwitness obligation hobligation
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨witness, hwitnessRange, hedge, hlabel⟩
    exact ⟨witness, hedge, hlabel⟩
  · intro clause hclause assignment hbody
    have hall : assignment ∈ allAssignments nodeCount variableCount := by
      exact mem_allAssignments nodeCount variableCount assignment
    have h := hsaturated clause hclause assignment hall
    have hbodyB : clause.body.all (certificate.holdsAtomB assignment) = true := by
      simp only [List.all_eq_true]
      intro atom hatom
      exact (certificate.holdsAtomB_eq_true assignment atom).2 (hbody atom hatom)
    have hhead : clause.head.any (certificate.holdsAtomB assignment) = true := by
      simpa [hbodyB] using h
    rw [List.any_eq_true] at hhead
    rcases hhead with ⟨atom, hatom, hholds⟩
    exact ⟨atom, hatom,
      (certificate.holdsAtomB_eq_true assignment atom).1 hholds⟩

/-- The finite SAT checker is complete for its stated endpoint invariant. This
direction is needed to prove that a structurally valid blocked fold cannot be
rejected by the executable trust boundary. -/
theorem FiniteSatCertificate.checkSat_complete
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.Valid) :
    certificate.checkSat = true := by
  simp only [FiniteSatCertificate.checkSat, Bool.and_eq_true,
    List.all_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro clause hclause atom hatom
    have hbody := hvalid.1 clause hclause atom hatom
    cases atom with
    | concept lit node =>
        rcases lit with ⟨concept, neg⟩
        cases neg <;> simp_all [atomGuardedB, BodyAtom]
    | role => simp [atomGuardedB]
    | exists_ => contradiction
    | eq => simp [atomGuardedB]
  · rintro ⟨node, literal⟩ hlabel
    simp only [decide_eq_true_eq]
    rcases literal with ⟨concept, neg⟩
    cases neg with
    | false =>
        intro hnegative
        exact hvalid.2.1 node concept ⟨hlabel, hnegative⟩
    | true =>
        intro hpositive
        exact hvalid.2.1 node concept ⟨hpositive, hlabel⟩
  · intro obligation hobligation
    rcases hvalid.2.2.1 obligation hobligation with
      ⟨witness, hedge, hlabel⟩
    rw [List.any_eq_true]
    exact ⟨witness, List.mem_finRange witness, by
      simp [hedge, hlabel]⟩
  · intro clause hclause assignment _
    by_cases hbody : ∀ atom ∈ clause.body,
        certificate.state.holdsAtom assignment atom
    · have hhead := hvalid.2.2.2 clause hclause assignment hbody
      rcases hhead with ⟨atom, hatom, hholds⟩
      have hbodyB : clause.body.all
          (certificate.holdsAtomB assignment) = true := by
        rw [List.all_eq_true]
        intro bodyAtom hbodyAtom
        exact (certificate.holdsAtomB_eq_true assignment bodyAtom).2
          (hbody bodyAtom hbodyAtom)
      have hheadB : clause.head.any
          (certificate.holdsAtomB assignment) = true := by
        rw [List.any_eq_true]
        exact ⟨atom, hatom,
          (certificate.holdsAtomB_eq_true assignment atom).2 hholds⟩
      simp [hbodyB, hheadB]
    · have hbodyB : clause.body.all
          (certificate.holdsAtomB assignment) = false := by
        generalize hall : clause.body.all
          (certificate.holdsAtomB assignment) = value
        cases value with
        | false => rfl
        | true =>
            exfalso
            apply hbody
            intro atom hatom
            exact (certificate.holdsAtomB_eq_true assignment atom).1
              ((List.all_eq_true.mp hall) atom hatom)
      simp [hbodyB]

theorem FiniteSatCertificate.checkSat_eq_true_iff_valid
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount) :
    certificate.checkSat = true ↔ certificate.Valid :=
  ⟨certificate.checkSat_sound, certificate.checkSat_complete⟩

/-- Checker acceptance constructs a model of the exact encoded ontology. -/
theorem FiniteSatCertificate.checkSat_models
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.checkSat = true) :
    certificate.state.canonical.models certificate.ontology := by
  have hvalid := certificate.checkSat_sound hcheck
  exact canonical_models_of_saturated certificate.state certificate.ontology
    hvalid.1 hvalid.2.1 (certificate.valid_witnessComplete hvalid) hvalid.2.2.2

/-- A checked open branch is a concrete satisfiability witness. -/
theorem FiniteSatCertificate.checkSat_satisfiable
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.checkSat = true) :
    ∃ I : Interp (Fin nodeCount) (Fin conceptCount) (Fin roleCount),
      I.models certificate.ontology :=
  ⟨certificate.state.canonical, certificate.checkSat_models hcheck⟩

/-- A checked model carrying `A` and `¬B` at one node refutes `A ⊑ B`. -/
theorem FiniteSatCertificate.checkSat_not_entailsSub
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (sub sup : Fin conceptCount)
    (hsub : (root, .pos sub) ∈ certificate.labels)
    (hnotSup : (root, .negated sup) ∈ certificate.labels)
    (hcheck : certificate.checkSat = true) :
    ¬EntailsSub certificate.ontology sub sup := by
  intro hentails
  have hvalid := certificate.checkSat_sound hcheck
  have hmodels := certificate.checkSat_models hcheck
  have hsubCanonical : certificate.state.canonical.concept sub root := hsub
  have hsupCanonical := hentails _ certificate.state.canonical hmodels root hsubCanonical
  have hneg := certificate.state.canonical_satLit hvalid.2.1 root (.negated sup) hnotSup
  have hnotSupCanonical : ¬certificate.state.canonical.concept sup root := by
    simpa [Interp.satLit, Lit.negated] using hneg
  exact hnotSupCanonical hsupCanonical

/-- A checked model carrying `A` at one node refutes unsatisfiability of `A`. -/
theorem FiniteSatCertificate.checkSat_not_unsatisfiableConcept
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (concept : Fin conceptCount)
    (hconcept : (root, .pos concept) ∈ certificate.labels)
    (hcheck : certificate.checkSat = true) :
    ¬UnsatisfiableConcept certificate.ontology concept := by
  intro hunsatisfiable
  have hmodels := certificate.checkSat_models hcheck
  exact hunsatisfiable _ certificate.state.canonical hmodels root hconcept

namespace CheckerTests

private def reflexiveCertificate : FiniteSatCertificate 1 1 1 1 where
  ontology := [{
    body := [.concept (.pos 0) 0]
    head := [.concept (.pos 0) 0]
  }]
  labels := [(0, .pos 0)]
  edges := []
  obligations := []

example : reflexiveCertificate.checkSat = true := by native_decide

private def clashingCertificate : FiniteSatCertificate 1 1 1 0 where
  ontology := []
  labels := [(0, .pos 0), (0, .negated 0)]
  edges := []
  obligations := []

example : clashingCertificate.checkSat = false := by native_decide

private def missingWitnessCertificate : FiniteSatCertificate 1 1 1 0 where
  ontology := []
  labels := []
  edges := []
  obligations := [(0, .pos 0, 0)]

example : missingWitnessCertificate.checkSat = false := by native_decide

private def undischargedCertificate : FiniteSatCertificate 1 1 1 1 where
  ontology := [{body := [], head := [.concept (.pos 0) 0]}]
  labels := []
  edges := []
  obligations := []

example : undischargedCertificate.checkSat = false := by native_decide

end CheckerTests

#print axioms FiniteSatCertificate.checkSat_sound
#print axioms FiniteSatCertificate.checkSat_complete
#print axioms FiniteSatCertificate.checkSat_eq_true_iff_valid
#print axioms FiniteSatCertificate.checkSat_models
#print axioms FiniteSatCertificate.checkSat_satisfiable
#print axioms FiniteSatCertificate.checkSat_not_entailsSub
#print axioms FiniteSatCertificate.checkSat_not_unsatisfiableConcept

end ContextCalculus.Hypertableau
