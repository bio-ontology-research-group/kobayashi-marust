import ContextCalculus.HypertableauCertificate

/-!
# Executable finite hypertableau refutation certificates

This module checks a finite exhaustive refutation tree.  Each branch records
the matched ontology clause, its grounding, and exactly one child for every
head atom.  The checker rejects equality heads because their implementation
requires a separately certified quotient construction.
-/

namespace ContextCalculus.Hypertableau

def branchableB : Atom V C R → Bool
  | .eq .. => false
  | _ => true

def FiniteSatCertificate.assertAtom
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) :
    FiniteSatCertificate nodeCount conceptCount roleCount variableCount :=
  match atom with
  | .concept lit node =>
      { certificate with labels := (assignment node, lit) :: certificate.labels }
  | .role role source target =>
      { certificate with
        edges := (role, assignment source, assignment target) :: certificate.edges }
  | .exists_ role filler node =>
      { certificate with
        obligations := (role, filler, assignment node) :: certificate.obligations }
  | .eq .. => certificate

theorem FiniteSatCertificate.state_assertAtom
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) :
    (certificate.assertAtom assignment atom).state =
      certificate.state.assertAtom assignment atom := by
  cases atom <;> ext <;>
    simp [FiniteSatCertificate.assertAtom, FiniteSatCertificate.state,
      State.assertAtom, eq_comm, and_assoc, and_left_comm, and_comm, or_comm]

@[simp] theorem FiniteSatCertificate.ontology_assertAtom
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) :
    (certificate.assertAtom assignment atom).ontology = certificate.ontology := by
  cases atom <;> rfl

def FiniteSatCertificate.freshNodeB
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (target : Fin nodeCount) : Bool :=
  (certificate.labels.all fun entry => decide (entry.1 ≠ target)) &&
  (certificate.edges.all fun entry =>
    decide (entry.2.1 ≠ target) && decide (entry.2.2 ≠ target)) &&
  (certificate.obligations.all fun entry => decide (entry.2.2 ≠ target))

def FiniteSatCertificate.materializeWitness
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (source target : Fin nodeCount) (role : Fin roleCount)
    (filler : Lit (Fin conceptCount)) :
    FiniteSatCertificate nodeCount conceptCount roleCount variableCount :=
  { certificate with
    labels := (target, filler) :: certificate.labels
    edges := (role, source, target) :: certificate.edges }

theorem FiniteSatCertificate.freshNodeB_eq_true
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (target : Fin nodeCount) :
    certificate.freshNodeB target = true ↔ certificate.state.Fresh target := by
  simp only [FiniteSatCertificate.freshNodeB, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, FiniteSatCertificate.state, State.Fresh]
  constructor
  · rintro ⟨⟨hlabels, hedges⟩, hobligations⟩
    refine ⟨?_, ?_, ?_⟩
    · intro lit hlabel
      exact (hlabels (target, lit) hlabel).elim rfl
    · intro candidateRole node
      exact ⟨fun hedge => (hedges (candidateRole, target, node) hedge).1 rfl,
        fun hedge => (hedges (candidateRole, node, target) hedge).2 rfl⟩
    · intro candidateRole filler hobligation
      exact (hobligations (candidateRole, filler, target) hobligation).elim rfl
  · rintro ⟨hlabels, hedges, hobligations⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro ⟨node, lit⟩ hentry heq
      have : node = target := by simpa using heq
      subst node
      exact hlabels lit hentry
    · rintro ⟨candidateRole, source, target'⟩ hedge
      exact ⟨fun heq => by
          have : source = target := by simpa using heq
          subst source
          exact (hedges candidateRole target').1 hedge,
        fun heq => by
          have : target' = target := by simpa using heq
          subst target'
          exact (hedges candidateRole source).2 hedge⟩
    · rintro ⟨candidateRole, filler, node⟩ hobligation heq
      have : node = target := by simpa using heq
      subst node
      exact hobligations candidateRole filler hobligation

theorem FiniteSatCertificate.state_materializeWitness
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (source target : Fin nodeCount) (role : Fin roleCount)
    (filler : Lit (Fin conceptCount)) :
    (certificate.materializeWitness source target role filler).state =
      certificate.state.materializeWitness source target role filler := by
  ext <;> simp [FiniteSatCertificate.materializeWitness, FiniteSatCertificate.state,
    State.materializeWitness, eq_comm, or_comm]

@[simp] theorem FiniteSatCertificate.ontology_materializeWitness
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (source target : Fin nodeCount) (role : Fin roleCount)
    (filler : Lit (Fin conceptCount)) :
    (certificate.materializeWitness source target role filler).ontology =
      certificate.ontology := rfl

mutual
  inductive FiniteRefutationTree
      (nodeCount conceptCount roleCount variableCount : Nat) where
    | clash
    | branch
        (clause : Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))
        (assignment : Fin variableCount → Fin nodeCount)
        (children : FiniteRefutationChildren
          nodeCount conceptCount roleCount variableCount)
    | witness
        (source target : Fin nodeCount)
        (role : Fin roleCount)
        (filler : Lit (Fin conceptCount))
        (child : FiniteRefutationTree nodeCount conceptCount roleCount variableCount)

  inductive FiniteRefutationChildren
      (nodeCount conceptCount roleCount variableCount : Nat) where
    | nil
    | cons
        (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount))
        (child : FiniteRefutationTree nodeCount conceptCount roleCount variableCount)
        (rest : FiniteRefutationChildren nodeCount conceptCount roleCount variableCount)
end

mutual
  def FiniteRefutationTree.check
      (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount) :
      FiniteRefutationTree nodeCount conceptCount roleCount variableCount → Bool
    | .clash => certificate.labels.any fun entry =>
        decide ((entry.1, entry.2.complement) ∈ certificate.labels)
    | .branch clause assignment children =>
        decide (clause ∈ certificate.ontology) &&
        clause.body.all (certificate.holdsAtomB assignment) &&
        clause.head.all branchableB &&
        children.check certificate assignment clause.head
    | .witness source target role filler child =>
        decide ((role, filler, source) ∈ certificate.obligations) &&
        certificate.freshNodeB target &&
        child.check (certificate.materializeWitness source target role filler)

  def FiniteRefutationChildren.check
      (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
      (assignment : Fin variableCount → Fin nodeCount) :
      FiniteRefutationChildren nodeCount conceptCount roleCount variableCount →
      List (Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) → Bool
    | .nil, heads => heads.isEmpty
    | .cons .., [] => false
    | .cons atom child rest, head :: heads =>
        decide (atom = head) &&
        child.check (certificate.assertAtom assignment atom) &&
        rest.check certificate assignment heads
end

theorem branchableB_eq_true (atom : Atom V C R) :
    branchableB atom = true ↔ Branchable atom := by
  cases atom <;> simp [branchableB, Branchable]

mutual
  theorem FiniteRefutationTree.check_sound
      (tree : FiniteRefutationTree nodeCount conceptCount roleCount variableCount) :
      ∀ certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount,
        tree.check certificate = true →
        Refutes (Fin nodeCount) certificate.ontology certificate.state := by
    cases tree with
    | clash =>
      intro certificate hcheck
      simp only [FiniteRefutationTree.check, List.any_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨node, lit⟩, hlabel, hcomplement⟩
      apply Refutes.clash
      rcases lit with ⟨concept, neg⟩
      cases neg with
      | false =>
          exact ⟨node, concept, hlabel, by simpa [Lit.complement] using hcomplement⟩
      | true =>
          exact ⟨node, concept, by simpa [Lit.complement] using hcomplement, hlabel⟩
    | branch clause assignment children =>
      intro certificate hcheck
      simp only [FiniteRefutationTree.check, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨⟨hclause, hbody⟩, hbranchable⟩, hchildren⟩
      apply Refutes.branch certificate.state clause hclause assignment
      · intro atom hatom
        exact (certificate.holdsAtomB_eq_true assignment atom).1
          (hbody atom hatom)
      · intro atom hatom
        exact (branchableB_eq_true atom).1 (hbranchable atom hatom)
      · intro atom hatom
        exact children.check_sound certificate assignment clause.head hchildren atom hatom
    | witness source target role filler child =>
      intro certificate hcheck
      simp only [FiniteRefutationTree.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨hobligation, hfresh⟩, hchild⟩
      apply Refutes.witness certificate.state source target role filler hobligation
        ((certificate.freshNodeB_eq_true target).1 hfresh)
      rw [← certificate.state_materializeWitness source target role filler]
      simpa only [FiniteSatCertificate.ontology_materializeWitness] using
        child.check_sound (certificate.materializeWitness source target role filler) hchild

  theorem FiniteRefutationChildren.check_sound
      (children : FiniteRefutationChildren nodeCount conceptCount roleCount variableCount) :
      ∀ (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
        (assignment : Fin variableCount → Fin nodeCount) (heads)
        (_ : children.check certificate assignment heads = true)
        (atom), atom ∈ heads →
          Refutes (Fin nodeCount) certificate.ontology
            (certificate.state.assertAtom assignment atom) := by
    cases children with
    | nil =>
        intro certificate assignment heads hcheck atom hatom
        simp only [FiniteRefutationChildren.check, List.isEmpty_iff] at hcheck
        simp [hcheck] at hatom
    | cons recorded child rest =>
        intro certificate assignment heads hcheck atom hatom
        cases heads with
        | nil => simp at hatom
        | cons head heads =>
            simp only [FiniteRefutationChildren.check, Bool.and_eq_true,
              decide_eq_true_eq] at hcheck
            rcases hcheck with ⟨⟨rfl, hchild⟩, hrest⟩
            simp only [List.mem_cons] at hatom
            rcases hatom with rfl | hatom
            · rw [← certificate.state_assertAtom assignment atom]
              simpa only [FiniteSatCertificate.ontology_assertAtom] using
                child.check_sound (certificate.assertAtom assignment atom) hchild
            · exact rest.check_sound certificate assignment heads hrest atom hatom
end

theorem exists_checked_children
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (heads : List (Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (hencode : ∀ atom, atom ∈ heads →
      ∃ tree : FiniteRefutationTree nodeCount conceptCount roleCount variableCount,
        tree.check (certificate.assertAtom assignment atom) = true) :
    ∃ children : FiniteRefutationChildren
        nodeCount conceptCount roleCount variableCount,
      children.check certificate assignment heads = true := by
  induction heads with
  | nil => exact ⟨.nil, by simp [FiniteRefutationChildren.check]⟩
  | cons head tail ih =>
      obtain ⟨tree, htree⟩ := hencode head (by simp)
      obtain ⟨rest, hrest⟩ := ih (fun atom hatom =>
        hencode atom (by simp [hatom]))
      exact ⟨.cons head tree rest, by
        simp [FiniteRefutationChildren.check, htree, hrest]⟩

/-- Completeness of the executable finite refutation-tree checker relative to
the semantic finite `Refutes` derivation. Every such derivation over the exact
list-backed certificate state can be serialized as a tree accepted by the
Boolean checker. -/
theorem Refutes.exists_checked_tree
    {ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount)}
    (hrefutes : Refutes (Fin nodeCount) ontology state) :
    ∀ certificate : FiniteSatCertificate
        nodeCount conceptCount roleCount variableCount,
      certificate.ontology = ontology → certificate.state = state →
      ∃ tree : FiniteRefutationTree nodeCount conceptCount roleCount variableCount,
        tree.check certificate = true := by
  induction hrefutes with
  | clash state hclash =>
      intro certificate hontology hstate
      rcases hclash with ⟨node, concept, hpositive, hnegative⟩
      have hpositive' : (node, .pos concept) ∈ certificate.labels := by
        change certificate.state.label node (.pos concept)
        rw [hstate]
        exact hpositive
      have hnegative' : (node, .negated concept) ∈ certificate.labels := by
        change certificate.state.label node (.negated concept)
        rw [hstate]
        exact hnegative
      refine ⟨.clash, ?_⟩
      simp only [FiniteRefutationTree.check, List.any_eq_true, decide_eq_true_eq]
      exact ⟨(node, .pos concept), hpositive', by
        simpa [Lit.complement] using hnegative'⟩
  | branch state clause hclause assignment hbody hbranchable children ih =>
      intro certificate hontology hstate
      have hclause' : clause ∈ certificate.ontology := by
        simpa [hontology] using hclause
      have hbody' : ∀ atom ∈ clause.body,
          certificate.holdsAtomB assignment atom = true := by
        intro atom hatom
        apply (certificate.holdsAtomB_eq_true assignment atom).2
        rw [hstate]
        exact hbody atom hatom
      have hbranchable' : ∀ atom ∈ clause.head, branchableB atom = true := by
        intro atom hatom
        exact (branchableB_eq_true atom).2 (hbranchable atom hatom)
      obtain ⟨encodedChildren, hencodedChildren⟩ :=
        exists_checked_children certificate assignment clause.head (fun atom hatom => by
          apply ih atom hatom (certificate.assertAtom assignment atom)
          · simpa [hontology]
          · rw [certificate.state_assertAtom, hstate])
      refine ⟨.branch clause assignment encodedChildren, ?_⟩
      simp only [FiniteRefutationTree.check, Bool.and_eq_true,
        decide_eq_true_eq, List.all_eq_true]
      exact ⟨⟨⟨hclause', hbody'⟩, hbranchable'⟩, hencodedChildren⟩
  | witness state source target role filler hobligation hfresh child ih =>
      intro certificate hontology hstate
      have hobligation' : (role, filler, source) ∈ certificate.obligations := by
        change certificate.state.obligation role filler source
        rw [hstate]
        exact hobligation
      have hfresh' : certificate.freshNodeB target = true :=
        (certificate.freshNodeB_eq_true target).2 (by simpa [hstate] using hfresh)
      obtain ⟨encodedChild, hencodedChild⟩ :=
        ih (certificate.materializeWitness source target role filler)
          (by simpa [hontology]) (by rw [certificate.state_materializeWitness, hstate])
      refine ⟨.witness source target role filler encodedChild, ?_⟩
      simp [FiniteRefutationTree.check, hobligation', hfresh', hencodedChild]

/-- Exactness of the finite refutation certificate format: accepted trees and
semantic finite HT refutations coincide for the certificate's ontology and
list-backed state. -/
theorem FiniteSatCertificate.refutes_iff_exists_checked_tree
    (certificate : FiniteSatCertificate
      nodeCount conceptCount roleCount variableCount) :
    Refutes (Fin nodeCount) certificate.ontology certificate.state ↔
      ∃ tree : FiniteRefutationTree nodeCount conceptCount roleCount variableCount,
        tree.check certificate = true := by
  constructor
  · intro hrefutes
    exact hrefutes.exists_checked_tree certificate rfl rfl
  · rintro ⟨tree, hcheck⟩
    exact tree.check_sound certificate hcheck

theorem FiniteRefutationTree.check_unsatisfiable
    (tree : FiniteRefutationTree nodeCount conceptCount roleCount variableCount)
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (hcheck : tree.check certificate = true) :
    ¬certificate.state.RealizableWith certificate.ontology :=
  (tree.check_sound certificate hcheck).sound

def FiniteSatCertificate.EmptyRoot
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount) : Prop :=
  certificate.labels = [] ∧ certificate.edges = [] ∧ certificate.obligations = []

/-- A checked refutation from an empty root excludes every nonempty-domain
model of the exact encoded ontology. -/
theorem FiniteRefutationTree.check_ontology_unsatisfiable
    [Nonempty (Fin nodeCount)]
    (tree : FiniteRefutationTree nodeCount conceptCount roleCount variableCount)
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (hempty : certificate.EmptyRoot)
    (hcheck : tree.check certificate = true) :
    ¬∃ (Domain : Type) (I : Interp Domain (Fin conceptCount) (Fin roleCount)),
      Nonempty Domain ∧ I.models certificate.ontology := by
  rintro ⟨Domain, I, hdomain, hmodels⟩
  apply tree.check_unsatisfiable certificate hcheck
  let value : Fin nodeCount → Domain := fun _ => Classical.choice hdomain
  refine ⟨Domain, I, value, hmodels, ?_⟩
  rcases hempty with ⟨hlabels, hedges, hobligations⟩
  simp [FiniteSatCertificate.state, hlabels, hedges, hobligations,
    State.RealizedBy]

def FiniteSatCertificate.SubsumptionRoot
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (sub sup : Fin conceptCount) : Prop :=
  certificate.labels = [(root, .pos sub), (root, .negated sup)] ∧
  certificate.edges = [] ∧ certificate.obligations = []

def FiniteSatCertificate.UnsatisfiableRoot
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (concept : Fin conceptCount) : Prop :=
  certificate.labels = [(root, .pos concept)] ∧
  certificate.edges = [] ∧ certificate.obligations = []

/-- Refuting the exact root assumptions `A` and `¬B` certifies `A ⊑ B`. -/
theorem FiniteRefutationTree.check_subsumption
    (tree : FiniteRefutationTree nodeCount conceptCount roleCount variableCount)
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (sub sup : Fin conceptCount)
    (hroot : certificate.SubsumptionRoot root sub sup)
    (hcheck : tree.check certificate = true) :
    EntailsSub certificate.ontology sub sup := by
  intro Domain I hmodels value hsub
  by_contra hsup
  apply tree.check_unsatisfiable certificate hcheck
  refine ⟨Domain, I, fun _ => value, hmodels, ?_⟩
  rcases hroot with ⟨hlabels, hedges, hobligations⟩
  refine ⟨?_, ?_, ?_⟩
  · intro node lit hlabel
    simp only [FiniteSatCertificate.state, hlabels, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] at hlabel
    rcases hlabel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [Interp.satLit, Lit.pos] using hsub
    · simpa [Interp.satLit, Lit.negated] using hsup
  · simp [FiniteSatCertificate.state, hedges]
  · simp [FiniteSatCertificate.state, hobligations]

/-- Refuting the exact root assumption `A` certifies `A ⊑ ⊥`. -/
theorem FiniteRefutationTree.check_unsatisfiable_concept
    (tree : FiniteRefutationTree nodeCount conceptCount roleCount variableCount)
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (concept : Fin conceptCount)
    (hroot : certificate.UnsatisfiableRoot root concept)
    (hcheck : tree.check certificate = true) :
    UnsatisfiableConcept certificate.ontology concept := by
  intro Domain I hmodels value hconcept
  apply tree.check_unsatisfiable certificate hcheck
  refine ⟨Domain, I, fun _ => value, hmodels, ?_⟩
  rcases hroot with ⟨hlabels, hedges, hobligations⟩
  refine ⟨?_, ?_, ?_⟩
  · intro node lit hlabel
    simp only [FiniteSatCertificate.state, hlabels, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] at hlabel
    rcases hlabel with ⟨rfl, rfl⟩
    simpa [Interp.satLit, Lit.pos] using hconcept
  · simp [FiniteSatCertificate.state, hedges]
  · simp [FiniteSatCertificate.state, hobligations]

namespace RefutationCheckerTests

private def emptyHeadClause : Clause (Fin 0) (Fin 1) (Fin 1) :=
  { body := [], head := [] }

private def emptyHeadCertificate : FiniteSatCertificate 1 1 1 0 where
  ontology := [emptyHeadClause]
  labels := []
  edges := []
  obligations := []

private def emptyHeadTree : FiniteRefutationTree 1 1 1 0 :=
  .branch emptyHeadClause Fin.elim0 .nil

example : emptyHeadTree.check emptyHeadCertificate = true := by native_decide

private def binaryClause : Clause (Fin 1) (Fin 2) (Fin 1) :=
  { body := [], head := [.concept (.pos 0) 0, .concept (.pos 1) 0] }

private def binaryCertificate : FiniteSatCertificate 1 2 1 1 where
  ontology := [binaryClause]
  labels := [(0, .negated 0), (0, .negated 1)]
  edges := []
  obligations := []

private def binaryTree : FiniteRefutationTree 1 2 1 1 :=
  .branch binaryClause (fun _ => 0)
    (.cons (.concept (.pos 0) 0) .clash
      (.cons (.concept (.pos 1) 0) .clash .nil))

example : binaryTree.check binaryCertificate = true := by native_decide

private def missingBranchTree : FiniteRefutationTree 1 2 1 1 :=
  .branch binaryClause (fun _ => 0)
    (.cons (.concept (.pos 0) 0) .clash .nil)

example : missingBranchTree.check binaryCertificate = false := by native_decide

private def equalityClause : Clause (Fin 1) (Fin 1) (Fin 1) :=
  { body := [], head := [.eq 0 0] }

private def equalityCertificate : FiniteSatCertificate 1 1 1 1 where
  ontology := [equalityClause]
  labels := []
  edges := []
  obligations := []

private def equalityTree : FiniteRefutationTree 1 1 1 1 :=
  .branch equalityClause (fun _ => 0) (.cons (.eq 0 0) .clash .nil)

example : equalityTree.check equalityCertificate = false := by native_decide

private def witnessOntology :
    List (Clause (Fin 2) (Fin 1) (Fin 1)) := [
  { body := [], head := [.exists_ 0 (.pos 0) 0] },
  { body := [.role 0 0 1, .concept (.pos 0) 1], head := [] }]

private def witnessCertificate : FiniteSatCertificate 2 1 1 2 where
  ontology := witnessOntology
  labels := []
  edges := []
  obligations := []

private def witnessTree : FiniteRefutationTree 2 1 1 2 :=
  .branch witnessOntology[0] (fun _ => 0)
    (.cons (.exists_ 0 (.pos 0) 0)
      (.witness 0 1 0 (.pos 0)
        (.branch witnessOntology[1] (Fin.cases 0 (fun _ => 1)) .nil))
      .nil)

example : witnessTree.check witnessCertificate = true := by native_decide

private def nonfreshWitnessTree : FiniteRefutationTree 2 1 1 2 :=
  .branch witnessOntology[0] (fun _ => 0)
    (.cons (.exists_ 0 (.pos 0) 0)
      (.witness 0 0 0 (.pos 0)
        (.branch witnessOntology[1] (fun _ => 0) .nil))
      .nil)

example : nonfreshWitnessTree.check witnessCertificate = false := by native_decide

end RefutationCheckerTests

#print axioms FiniteRefutationTree.check_sound
#print axioms Refutes.exists_checked_tree
#print axioms FiniteSatCertificate.refutes_iff_exists_checked_tree
#print axioms FiniteRefutationTree.check_unsatisfiable
#print axioms FiniteRefutationTree.check_ontology_unsatisfiable
#print axioms FiniteRefutationTree.check_subsumption
#print axioms FiniteRefutationTree.check_unsatisfiable_concept

end ContextCalculus.Hypertableau
