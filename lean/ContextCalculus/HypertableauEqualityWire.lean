import ContextCalculus.HypertableauEqualityCertificate
import ContextCalculus.HypertableauWire
import Lean

/-!
# Version-2 equality-aware hypertableau certificate wire format

Version 1 remains unchanged and equality-free. Version 2 carries an exact
finite equality state at the root and at every head-branch successor. All
natural-number identifiers are bounds checked before the proved equality-aware
checker sees them.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireEquality where
  left : Nat
  right : Nat
deriving FromJson, ToJson, Repr

structure WireEqState where
  labels : List WireLabel
  edges : List WireEdge
  obligations : List WireObligation
  equalities : List WireEquality
  representatives : List Nat
  representative_paths : List (List Nat)
deriving FromJson, ToJson, Repr

inductive WireEqRefutationTree where
  | clash
  | branch (clause : Nat) (assignment : List Nat)
      (children : List (WireEqState × WireEqRefutationTree))
  | witness (source target role : Nat) (filler : WireLit)
      (child : WireEqRefutationTree)
deriving FromJson, ToJson, Repr

inductive WireEqEvidence where
  | sat
  | unsat (tree : WireEqRefutationTree)
  | subsumption (root sub sup : Nat) (tree : WireEqRefutationTree)
  | unsatisfiable_concept (root concept : Nat) (tree : WireEqRefutationTree)
  | non_subsumption (root sub sup : Nat)
  | satisfiable_concept (root concept : Nat)
deriving FromJson, ToJson, Repr

structure WireEqCertificate where
  version : Nat
  node_count : Nat
  concept_count : Nat
  role_count : Nat
  variable_count : Nat
  ontology : List WireClause
  state : WireEqState
  evidence : WireEqEvidence
deriving FromJson, ToJson, Repr

def decodeNodeVector (kind : String) (nodeCount : Nat) (values : List Nat) :
    Except String (Fin nodeCount → Fin nodeCount) := do
  let decoded ← values.mapM (checkedFin kind nodeCount)
  if h : decoded.length = nodeCount then
    return fun index => decoded.get (h.symm ▸ index)
  else
    throw s!"{kind} has {decoded.length} entries, expected {nodeCount}"

def decodeNodePaths (nodeCount : Nat) (paths : List (List Nat)) :
    Except String (Fin nodeCount → List (Fin nodeCount)) := do
  let decoded ← paths.mapM fun path => path.mapM (checkedFin "path node" nodeCount)
  if h : decoded.length = nodeCount then
    return fun index => decoded.get (h.symm ▸ index)
  else
    throw s!"representative_paths has {decoded.length} entries, expected {nodeCount}"

def WireEqState.decode
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (wire : WireEqState) : Except String
      (FiniteEqCertificate nodeCount conceptCount roleCount variableCount) := do
  let labels ← wire.labels.mapM fun label => do
    return (← checkedFin "node" nodeCount label.node,
      ← label.literal.decode conceptCount)
  let edges ← wire.edges.mapM fun edge => do
    return (← checkedFin "role" roleCount edge.role,
      ← checkedFin "node" nodeCount edge.source,
      ← checkedFin "node" nodeCount edge.target)
  let obligations ← wire.obligations.mapM fun obligation => do
    return (← checkedFin "role" roleCount obligation.role,
      ← obligation.filler.decode conceptCount,
      ← checkedFin "node" nodeCount obligation.node)
  let equalities ← wire.equalities.mapM fun equality => do
    return (← checkedFin "equality node" nodeCount equality.left,
      ← checkedFin "equality node" nodeCount equality.right)
  let representative ← decodeNodeVector "representatives" nodeCount wire.representatives
  let representativePath ← decodeNodePaths nodeCount wire.representative_paths
  return {
    base := { ontology, labels, edges, obligations }
    equalities, representative, representativePath
  }

def buildEqChildren :
    List (Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) →
    List (FiniteEqCertificate nodeCount conceptCount roleCount variableCount ×
      FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount) →
    Except String (FiniteEqRefutationChildren nodeCount conceptCount roleCount variableCount)
  | [], [] => return .nil
  | head :: heads, (state, tree) :: children =>
      return .cons head state tree (← buildEqChildren heads children)
  | _, _ => throw "decoded equality-refutation child count mismatch"

def WireEqRefutationTree.decode
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) :
    WireEqRefutationTree → Except String
      (FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
  | .clash => return .clash
  | .branch clauseIndex assignment children => do
      let clause ← match ontology[clauseIndex]? with
        | some clause => pure clause
        | none => throw s!"clause id {clauseIndex} is outside the ontology"
      let decodedAssignment ← decodeAssignment nodeCount variableCount assignment
      if children.length = clause.head.length then
        let decodedChildren ← children.mapM fun child => do
          let state ← child.1.decode nodeCount conceptCount roleCount variableCount ontology
          let tree ← child.2.decode nodeCount conceptCount roleCount variableCount ontology
          return (state, tree)
        return .branch clause decodedAssignment
          (← buildEqChildren clause.head decodedChildren)
      else
        throw s!"branch has {children.length} children, expected {clause.head.length}"
  | .witness source target role filler child => do
      return .witness
        (← checkedFin "node" nodeCount source)
        (← checkedFin "node" nodeCount target)
        (← checkedFin "role" roleCount role)
        (← filler.decode conceptCount)
        (← child.decode nodeCount conceptCount roleCount variableCount ontology)
termination_by tree => sizeOf tree
decreasing_by
  · simp_wf
    rename_i child hchild
    have hpair := List.sizeOf_lt_of_mem hchild
    have htree : sizeOf child.2 < sizeOf child := by
      rcases child with ⟨state, tree⟩
      simp
      omega
    omega
  · simp_wf
    omega

inductive DecodedEqEvidence (nodeCount conceptCount roleCount variableCount : Nat) where
  | sat (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
  | unsat (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
      (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
  | subsumption
      (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
      (root : Fin nodeCount) (sub sup : Fin conceptCount)
      (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
  | unsatisfiableConcept
      (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
      (root : Fin nodeCount) (concept : Fin conceptCount)
      (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
  | nonSubsumption
      (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
      (root : Fin nodeCount) (sub sup : Fin conceptCount)
  | satisfiableConcept
      (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
      (root : Fin nodeCount) (concept : Fin conceptCount)

structure DecodedEqCertificate where
  nodeCount : Nat
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  evidence : DecodedEqEvidence nodeCount conceptCount roleCount variableCount

def FiniteEqCertificate.checkSubsumptionRoot
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (sub sup : Fin conceptCount) : Bool :=
  certificate.base.checkSubsumptionRoot root sub sup

def FiniteEqCertificate.checkUnsatisfiableRoot
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (concept : Fin conceptCount) : Bool :=
  certificate.base.checkUnsatisfiableRoot root concept

theorem FiniteEqCertificate.checkSubsumptionRoot_sound
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (sub sup : Fin conceptCount)
    (hcheck : certificate.checkSubsumptionRoot root sub sup = true) :
    certificate.SubsumptionRoot root sub sup := by
  simpa [FiniteEqCertificate.checkSubsumptionRoot,
    FiniteEqCertificate.SubsumptionRoot, FiniteSatCertificate.SubsumptionRoot] using
    certificate.base.checkSubsumptionRoot_sound root sub sup hcheck

theorem FiniteEqCertificate.checkUnsatisfiableRoot_sound
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (concept : Fin conceptCount)
    (hcheck : certificate.checkUnsatisfiableRoot root concept = true) :
    certificate.UnsatisfiableRoot root concept := by
  simpa [FiniteEqCertificate.checkUnsatisfiableRoot,
    FiniteEqCertificate.UnsatisfiableRoot, FiniteSatCertificate.UnsatisfiableRoot] using
    certificate.base.checkUnsatisfiableRoot_sound root concept hcheck

def WireEqCertificate.decode (wire : WireEqCertificate) : Except String DecodedEqCertificate := do
  if wire.version != 2 then
    throw s!"unsupported equality hypertableau certificate version {wire.version}"
  let ontology ← wire.ontology.mapM
    (WireClause.decode wire.variable_count wire.concept_count wire.role_count)
  let certificate ← wire.state.decode wire.node_count wire.concept_count
    wire.role_count wire.variable_count ontology
  let evidence ← match wire.evidence with
    | .sat => pure (.sat certificate)
    | .unsat tree => do
        let decodedTree ← WireEqRefutationTree.decode wire.node_count wire.concept_count
          wire.role_count wire.variable_count ontology tree
        pure (.unsat certificate decodedTree)
    | .subsumption root sub sup tree =>
        pure (.subsumption certificate
          (← checkedFin "node" wire.node_count root)
          (← checkedFin "concept" wire.concept_count sub)
          (← checkedFin "concept" wire.concept_count sup)
          (← tree.decode wire.node_count wire.concept_count wire.role_count
            wire.variable_count ontology))
    | .unsatisfiable_concept root concept tree =>
        pure (.unsatisfiableConcept certificate
          (← checkedFin "node" wire.node_count root)
          (← checkedFin "concept" wire.concept_count concept)
          (← tree.decode wire.node_count wire.concept_count wire.role_count
            wire.variable_count ontology))
    | .non_subsumption root sub sup =>
        pure (.nonSubsumption certificate
          (← checkedFin "node" wire.node_count root)
          (← checkedFin "concept" wire.concept_count sub)
          (← checkedFin "concept" wire.concept_count sup))
    | .satisfiable_concept root concept =>
        pure (.satisfiableConcept certificate
          (← checkedFin "node" wire.node_count root)
          (← checkedFin "concept" wire.concept_count concept))
  return {
    nodeCount := wire.node_count
    conceptCount := wire.concept_count
    roleCount := wire.role_count
    variableCount := wire.variable_count
    evidence
  }

def DecodedEqCertificate.check (decoded : DecodedEqCertificate) : Bool :=
  match decoded.evidence with
  | .sat certificate => decide (0 < decoded.nodeCount) && certificate.checkEqSat
  | .unsat certificate tree =>
      decide (0 < decoded.nodeCount) &&
      certificate.base.labels.isEmpty &&
      certificate.base.edges.isEmpty &&
      certificate.base.obligations.isEmpty &&
      tree.check certificate
  | .subsumption certificate root sub sup tree =>
      certificate.checkSubsumptionRoot root sub sup && tree.check certificate
  | .unsatisfiableConcept certificate root concept tree =>
      certificate.checkUnsatisfiableRoot root concept && tree.check certificate
  | .nonSubsumption certificate root sub sup =>
      decide ((root, .pos sub) ∈ certificate.base.labels) &&
      decide ((root, .negated sup) ∈ certificate.base.labels) &&
      certificate.checkEqSat
  | .satisfiableConcept certificate root concept =>
      decide ((root, .pos concept) ∈ certificate.base.labels) &&
      certificate.checkEqSat

def WireEqCertificate.check (wire : WireEqCertificate) : Except String Bool := do
  return (← wire.decode).check

def DecodedEqCertificate.SemanticallyValid (decoded : DecodedEqCertificate) : Prop :=
  match decoded.evidence with
  | .sat certificate =>
      ∃ (Domain : Type) (I : Interp Domain (Fin decoded.conceptCount)
          (Fin decoded.roleCount)),
        Nonempty Domain ∧ I.models certificate.base.ontology
  | .unsat certificate _ =>
      ¬∃ (Domain : Type) (I : Interp Domain (Fin decoded.conceptCount)
          (Fin decoded.roleCount)),
        Nonempty Domain ∧ I.models certificate.base.ontology
  | .subsumption certificate _ sub sup _ =>
      EntailsSub certificate.base.ontology sub sup
  | .unsatisfiableConcept certificate _ concept _ =>
      UnsatisfiableConcept certificate.base.ontology concept
  | .nonSubsumption certificate _ sub sup =>
      ¬EntailsSub certificate.base.ontology sub sup
  | .satisfiableConcept certificate _ concept =>
      ¬UnsatisfiableConcept certificate.base.ontology concept

theorem DecodedEqCertificate.check_sound (decoded : DecodedEqCertificate)
    (hcheck : decoded.check = true) : decoded.SemanticallyValid := by
  cases hevidence : decoded.evidence with
  | sat certificate =>
      simp only [DecodedEqCertificate.check, hevidence, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      simp only [DecodedEqCertificate.SemanticallyValid, hevidence]
      haveI : Nonempty (Fin decoded.nodeCount) := ⟨⟨0, hcheck.1⟩⟩
      refine ⟨certificate.state.QuotientDomain, certificate.state.quotientCanonical,
        ?_, certificate.checkEqSat_models hcheck.2⟩
      exact ⟨Quotient.mk certificate.state.nodeSetoid (Classical.choice inferInstance)⟩
  | unsat certificate tree =>
      simp only [DecodedEqCertificate.check, hevidence, Bool.and_eq_true,
        decide_eq_true_eq, List.isEmpty_iff] at hcheck
      rcases hcheck with ⟨⟨⟨⟨hpositive, hlabels⟩, hedges⟩, hobligations⟩, htree⟩
      haveI : Nonempty (Fin decoded.nodeCount) := ⟨⟨0, hpositive⟩⟩
      simp only [DecodedEqCertificate.SemanticallyValid, hevidence]
      exact tree.check_ontology_unsatisfiable certificate
        ⟨hlabels, hedges, hobligations⟩ htree
  | subsumption certificate root sub sup tree =>
      simp only [DecodedEqCertificate.check, hevidence, Bool.and_eq_true] at hcheck
      simp only [DecodedEqCertificate.SemanticallyValid, hevidence]
      exact tree.check_subsumption certificate root sub sup
        (certificate.checkSubsumptionRoot_sound root sub sup hcheck.1) hcheck.2
  | unsatisfiableConcept certificate root concept tree =>
      simp only [DecodedEqCertificate.check, hevidence, Bool.and_eq_true] at hcheck
      simp only [DecodedEqCertificate.SemanticallyValid, hevidence]
      exact tree.check_unsatisfiable_concept certificate root concept
        (certificate.checkUnsatisfiableRoot_sound root concept hcheck.1) hcheck.2
  | nonSubsumption certificate root sub sup =>
      simp only [DecodedEqCertificate.check, hevidence, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      simp only [DecodedEqCertificate.SemanticallyValid, hevidence]
      exact certificate.checkEqSat_not_entailsSub root sub sup
        hcheck.1.1 hcheck.1.2 hcheck.2
  | satisfiableConcept certificate root concept =>
      simp only [DecodedEqCertificate.check, hevidence, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      simp only [DecodedEqCertificate.SemanticallyValid, hevidence]
      exact certificate.checkEqSat_not_unsatisfiableConcept root concept
        hcheck.1 hcheck.2

namespace EqualityWireTests

private def equalityClause : WireClause :=
  { body := [], head := [.eq 0 2] }

private def rootState : WireEqState where
  labels := []
  edges := []
  obligations := []
  equalities := []
  representatives := [0, 1, 2]
  representative_paths := [[], [], []]

private def childState : WireEqState where
  labels := []
  edges := []
  obligations := []
  equalities := [{ left := 0, right := 2 }]
  representatives := [0, 1, 0]
  representative_paths := [[], [], [0]]

private def contradiction : WireClause :=
  { body := [.eq 0 2], head := [] }

private def accepted : WireEqCertificate where
  version := 2
  node_count := 3
  concept_count := 1
  role_count := 1
  variable_count := 3
  ontology := [equalityClause, contradiction]
  state := rootState
  evidence := .unsat (.branch 0 [0, 1, 2]
    [(childState, .branch 1 [0, 1, 2] [])])

example : accepted.check = .ok true := by native_decide

private def stale : WireEqCertificate :=
  { accepted with evidence := .unsat (.branch 0 [0, 1, 2]
      [(rootState, .branch 1 [0, 1, 2] [])]) }

example : stale.check = .ok false := by native_decide

private def badPath : WireEqCertificate :=
  { accepted with evidence := .unsat (.branch 0 [0, 1, 2]
      [({ childState with representative_paths := [[], [], []] },
        .branch 1 [0, 1, 2] [])]) }

example : badPath.check = .ok false := by native_decide

private def outOfBounds : WireEqCertificate :=
  { accepted with state := { rootState with representatives := [0, 1, 3] } }

example : outOfBounds.check = .error "representatives id 3 is outside [0,3)" := by
  native_decide

private def satDocument : WireEqCertificate where
  version := 2
  node_count := 2
  concept_count := 2
  role_count := 1
  variable_count := 2
  ontology := [
    { body := [.concept { concept := 0, neg := false } 0]
      head := [.concept { concept := 1, neg := false } 0] },
    { body := [], head := [.eq 0 1] }
  ]
  state := {
    labels := [
      { node := 1, literal := { concept := 0, neg := false } },
      { node := 0, literal := { concept := 1, neg := false } }
    ]
    edges := []
    obligations := []
    equalities := [{ left := 0, right := 1 }]
    representatives := [0, 0]
    representative_paths := [[], [0]]
  }
  evidence := .sat

example : satDocument.check = .ok true := by native_decide

private def nonSubsumptionDocument : WireEqCertificate where
  version := 2
  node_count := 2
  concept_count := 2
  role_count := 1
  variable_count := 0
  ontology := []
  state := {
    labels := [
      { node := 1, literal := { concept := 0, neg := false } },
      { node := 1, literal := { concept := 1, neg := true } }
    ]
    edges := []
    obligations := []
    equalities := [{ left := 0, right := 1 }]
    representatives := [0, 0]
    representative_paths := [[], [0]]
  }
  evidence := .non_subsumption 1 0 1

example : nonSubsumptionDocument.check = .ok true := by native_decide

private def badNonSubsumption : WireEqCertificate :=
  { nonSubsumptionDocument with evidence := .non_subsumption 1 1 0 }

example : badNonSubsumption.check = .ok false := by native_decide

private def satisfiableConceptDocument : WireEqCertificate :=
  { nonSubsumptionDocument with evidence := .satisfiable_concept 1 0 }

example : satisfiableConceptDocument.check = .ok true := by native_decide

private def badSatisfiableConcept : WireEqCertificate :=
  { nonSubsumptionDocument with evidence := .satisfiable_concept 1 1 }

example : badSatisfiableConcept.check = .ok false := by native_decide

private def emptyDomainSat : WireEqCertificate where
  version := 2
  node_count := 0
  concept_count := 0
  role_count := 0
  variable_count := 0
  ontology := []
  state := {
    labels := []
    edges := []
    obligations := []
    equalities := []
    representatives := []
    representative_paths := []
  }
  evidence := .sat

example : emptyDomainSat.check = .ok false := by native_decide

end EqualityWireTests

#print axioms DecodedEqCertificate.check_sound

end ContextCalculus.Hypertableau
