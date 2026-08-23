import ContextCalculus.HypertableauRefutationCertificate
import Lean
import Mathlib.Data.List.OfFn

/-!
# JSON wire format for hypertableau certificates

All ids and assignments arrive as untrusted natural numbers.  Decoding checks
every bound before constructing finite semantic objects.  The decoded SAT and
UNSAT payloads are then accepted only by the proved executable checkers.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireLit where
  concept : Nat
  neg : Bool
deriving FromJson, ToJson, Repr, DecidableEq

inductive WireAtom where
  | concept (literal : WireLit) (node : Nat)
  | role (role source target : Nat)
  | exists_ (role : Nat) (filler : WireLit) (node : Nat)
  | eq (left right : Nat)
deriving FromJson, ToJson, Repr, DecidableEq

structure WireClause where
  body : List WireAtom
  head : List WireAtom
deriving FromJson, ToJson, Repr, DecidableEq

structure WireLabel where
  node : Nat
  literal : WireLit
deriving FromJson, ToJson, Repr

structure WireEdge where
  role : Nat
  source : Nat
  target : Nat
deriving FromJson, ToJson, Repr

structure WireObligation where
  role : Nat
  filler : WireLit
  node : Nat
deriving FromJson, ToJson, Repr

inductive WireRefutationTree where
  | clash
  | branch (clause : Nat) (assignment : List Nat)
      (children : List WireRefutationTree)
  | witness (source target role : Nat) (filler : WireLit)
      (child : WireRefutationTree)
deriving FromJson, ToJson, Repr

inductive WireEvidence where
  | sat
  | unsat (tree : WireRefutationTree)
  | subsumption (root sub sup : Nat) (tree : WireRefutationTree)
  | unsatisfiable_concept (root concept : Nat) (tree : WireRefutationTree)
  | non_subsumption (root sub sup : Nat)
  | satisfiable_concept (root concept : Nat)
deriving FromJson, ToJson, Repr

structure WireCertificate where
  version : Nat
  node_count : Nat
  concept_count : Nat
  role_count : Nat
  variable_count : Nat
  ontology : List WireClause
  labels : List WireLabel
  edges : List WireEdge
  obligations : List WireObligation
  evidence : WireEvidence
deriving FromJson, ToJson, Repr

def checkedFin (kind : String) (bound value : Nat) : Except String (Fin bound) :=
  if h : value < bound then .ok ⟨value, h⟩
  else .error s!"{kind} id {value} is outside [0,{bound})"

@[simp] theorem checkedFin_value (kind : String) (value : Fin bound) :
    checkedFin kind bound value.val = .ok value := by
  simp [checkedFin, value.isLt]

theorem finCast_transport_back {left right : Nat} (h : left = right)
    (index : Fin right) : Fin.cast h (h.symm ▸ index) = index := by
  subst right
  rfl

def WireLit.decode (conceptCount : Nat) (literal : WireLit) :
    Except String (Lit (Fin conceptCount)) := do
  return ⟨← checkedFin "concept" conceptCount literal.concept, literal.neg⟩

def WireLit.encode (literal : Lit (Fin conceptCount)) : WireLit where
  concept := literal.concept.val
  neg := literal.neg

@[simp] theorem WireLit.decode_encode (literal : Lit (Fin conceptCount)) :
    (WireLit.encode literal).decode conceptCount = Except.ok literal := by
  rcases literal with ⟨concept, neg⟩
  simp [WireLit.encode, WireLit.decode]

def WireAtom.decode (variableCount conceptCount roleCount : Nat) : WireAtom →
    Except String (Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount))
  | .concept literal node => do
      return .concept (← literal.decode conceptCount)
        (← checkedFin "variable" variableCount node)
  | .role relation source target => do
      return .role (← checkedFin "role" roleCount relation)
        (← checkedFin "variable" variableCount source)
        (← checkedFin "variable" variableCount target)
  | .exists_ relation filler node => do
      return .exists_ (← checkedFin "role" roleCount relation)
        (← filler.decode conceptCount) (← checkedFin "variable" variableCount node)
  | .eq left right => do
      return .eq (← checkedFin "variable" variableCount left)
        (← checkedFin "variable" variableCount right)

def WireAtom.encode :
    Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount) → WireAtom
  | .concept literal node => .concept (WireLit.encode literal) node.val
  | .role relation source target => .role relation.val source.val target.val
  | .exists_ relation filler node =>
      .exists_ relation.val (WireLit.encode filler) node.val
  | .eq left right => .eq left.val right.val

@[simp] theorem WireAtom.decode_encode
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) :
    (WireAtom.encode atom).decode variableCount conceptCount roleCount =
      Except.ok atom := by
  cases atom <;>
    simp only [WireAtom.encode, WireAtom.decode, checkedFin_value,
      WireLit.decode_encode] <;> rfl

@[simp] theorem WireAtom.decode_encode_list
    (atoms : List (Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount))) :
    (atoms.map WireAtom.encode).mapM
        (WireAtom.decode variableCount conceptCount roleCount) =
      Except.ok atoms := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      simp only [List.map_cons, List.mapM_cons, WireAtom.decode_encode, ih]
      rfl

def WireClause.decode (variableCount conceptCount roleCount : Nat)
    (clause : WireClause) : Except String
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)) := do
  return ⟨← clause.body.mapM (WireAtom.decode variableCount conceptCount roleCount),
    ← clause.head.mapM (WireAtom.decode variableCount conceptCount roleCount)⟩

def WireClause.encode
    (clause : Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)) :
    WireClause where
  body := clause.body.map WireAtom.encode
  head := clause.head.map WireAtom.encode

@[simp] theorem WireClause.decode_encode
    (clause : Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)) :
    (WireClause.encode clause).decode variableCount conceptCount roleCount =
      Except.ok clause := by
  rcases clause with ⟨body, head⟩
  simp only [WireClause.encode, WireClause.decode,
    WireAtom.decode_encode_list]
  rfl

@[simp] theorem WireClause.decode_encode_list
    (ontology :
      List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) :
    (ontology.map WireClause.encode).mapM
        (WireClause.decode variableCount conceptCount roleCount) =
      Except.ok ontology := by
  induction ontology with
  | nil => rfl
  | cons clause ontology ih =>
      simp only [List.map_cons, List.mapM_cons, WireClause.decode_encode, ih]
      rfl

def decodeAssignment (nodeCount variableCount : Nat) (values : List Nat) :
    Except String (Fin variableCount → Fin nodeCount) := do
  let decoded ← values.mapM (checkedFin "node" nodeCount)
  if h : decoded.length = variableCount then
    return fun index => decoded.get (h.symm ▸ index)
  else
    throw s!"assignment has {decoded.length} entries, expected {variableCount}"

def encodeAssignment
    (assignment : Fin variableCount → Fin nodeCount) : List Nat :=
  List.ofFn fun index => (assignment index).val

@[simp] theorem checkedFin_value_list (kind : String)
    (values : List (Fin bound)) :
    (values.map Fin.val).mapM (checkedFin kind bound) = Except.ok values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.map_cons, List.mapM_cons, checkedFin_value, ih]
      rfl

@[simp] theorem decodeAssignment_encode
    (assignment : Fin variableCount → Fin nodeCount) :
    decodeAssignment nodeCount variableCount (encodeAssignment assignment) =
      Except.ok assignment := by
  unfold decodeAssignment encodeAssignment
  have hencoded :
      List.ofFn (fun index => (assignment index).val) =
        (List.ofFn assignment).map Fin.val := by
    simpa [Function.comp_def] using
      (List.map_ofFn (f := assignment) (g := Fin.val)).symm
  rw [hencoded]
  rw [checkedFin_value_list]
  change (if h : (List.ofFn assignment).length = variableCount then
      Except.ok (fun index => (List.ofFn assignment).get (h.symm ▸ index))
    else Except.error _) = Except.ok assignment
  split <;> rename_i h
  · congr
    funext index
    rw [List.get_ofFn]
    apply congrArg assignment
    have heq : h = List.length_ofFn (f := assignment) := Subsingleton.elim _ _
    rw [heq]
    exact finCast_transport_back _ _
  · exact (h (by simp)).elim

structure DecodedCertificate where
  nodeCount : Nat
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount

def WireCertificate.decodeBase (wire : WireCertificate) : Except String DecodedCertificate := do
  if wire.version != 1 then
    throw s!"unsupported hypertableau certificate version {wire.version}"
  let ontology ← wire.ontology.mapM
    (WireClause.decode wire.variable_count wire.concept_count wire.role_count)
  let labels ← wire.labels.mapM fun label => do
    return (← checkedFin "node" wire.node_count label.node,
      ← label.literal.decode wire.concept_count)
  let edges ← wire.edges.mapM fun edge => do
    return (← checkedFin "role" wire.role_count edge.role,
      ← checkedFin "node" wire.node_count edge.source,
      ← checkedFin "node" wire.node_count edge.target)
  let obligations ← wire.obligations.mapM fun obligation => do
    return (← checkedFin "role" wire.role_count obligation.role,
      ← obligation.filler.decode wire.concept_count,
      ← checkedFin "node" wire.node_count obligation.node)
  return {
    nodeCount := wire.node_count
    conceptCount := wire.concept_count
    roleCount := wire.role_count
    variableCount := wire.variable_count
    certificate := { ontology, labels, edges, obligations }
  }

def buildChildren :
    List (Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) →
    List (FiniteRefutationTree nodeCount conceptCount roleCount variableCount) →
    Except String
      (FiniteRefutationChildren nodeCount conceptCount roleCount variableCount)
  | [], [] => return .nil
  | head :: heads, tree :: trees =>
      return .cons head tree (← buildChildren heads trees)
  | _, _ => throw "decoded refutation child count mismatch"

def WireRefutationTree.decode
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount) :
    WireRefutationTree → Except String
      (FiniteRefutationTree nodeCount conceptCount roleCount variableCount)
  | .clash => return .clash
  | .branch clauseIndex assignment children => do
      let clause ← match certificate.ontology[clauseIndex]? with
        | some clause => pure clause
        | none => throw s!"clause id {clauseIndex} is outside the ontology"
      let decodedAssignment ← decodeAssignment nodeCount variableCount assignment
      if children.length = clause.head.length then
        let decodedChildren ← children.mapM (WireRefutationTree.decode certificate)
        return .branch clause decodedAssignment
          (← buildChildren clause.head decodedChildren)
      else
        throw s!"branch has {children.length} children, expected {clause.head.length}"
  | .witness source target role filler child => do
      return .witness
        (← checkedFin "node" nodeCount source)
        (← checkedFin "node" nodeCount target)
        (← checkedFin "role" roleCount role)
        (← filler.decode conceptCount)
        (← child.decode certificate)
termination_by tree => sizeOf tree
decreasing_by
  · simp_wf
    rename_i child hchild
    have hsize := List.sizeOf_lt_of_mem hchild
    omega
  · simp_wf
    omega

inductive DecodedEvidence where
  | sat (decoded : DecodedCertificate)
  | unsat (decoded : DecodedCertificate)
      (tree : FiniteRefutationTree decoded.nodeCount decoded.conceptCount
        decoded.roleCount decoded.variableCount)
  | subsumption (decoded : DecodedCertificate)
      (root : Fin decoded.nodeCount) (sub sup : Fin decoded.conceptCount)
      (tree : FiniteRefutationTree decoded.nodeCount decoded.conceptCount
        decoded.roleCount decoded.variableCount)
  | unsatisfiableConcept (decoded : DecodedCertificate)
      (root : Fin decoded.nodeCount) (concept : Fin decoded.conceptCount)
      (tree : FiniteRefutationTree decoded.nodeCount decoded.conceptCount
        decoded.roleCount decoded.variableCount)
  | nonSubsumption (decoded : DecodedCertificate)
      (root : Fin decoded.nodeCount) (sub sup : Fin decoded.conceptCount)
  | satisfiableConcept (decoded : DecodedCertificate)
      (root : Fin decoded.nodeCount) (concept : Fin decoded.conceptCount)

def FiniteSatCertificate.checkSubsumptionRoot
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (sub sup : Fin conceptCount) : Bool :=
  certificate.labels == [(root, .pos sub), (root, .negated sup)] &&
  certificate.edges.isEmpty && certificate.obligations.isEmpty

def FiniteSatCertificate.checkUnsatisfiableRoot
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (concept : Fin conceptCount) : Bool :=
  certificate.labels == [(root, .pos concept)] &&
  certificate.edges.isEmpty && certificate.obligations.isEmpty

theorem FiniteSatCertificate.checkSubsumptionRoot_sound
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (sub sup : Fin conceptCount)
    (hcheck : certificate.checkSubsumptionRoot root sub sup = true) :
    certificate.SubsumptionRoot root sub sup := by
  simp only [FiniteSatCertificate.checkSubsumptionRoot, Bool.and_eq_true,
    beq_iff_eq, List.isEmpty_iff] at hcheck
  exact ⟨hcheck.1.1, hcheck.1.2, hcheck.2⟩

theorem FiniteSatCertificate.checkUnsatisfiableRoot_sound
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (concept : Fin conceptCount)
    (hcheck : certificate.checkUnsatisfiableRoot root concept = true) :
    certificate.UnsatisfiableRoot root concept := by
  simp only [FiniteSatCertificate.checkUnsatisfiableRoot, Bool.and_eq_true,
    beq_iff_eq, List.isEmpty_iff] at hcheck
  exact ⟨hcheck.1.1, hcheck.1.2, hcheck.2⟩

def WireCertificate.decode (wire : WireCertificate) : Except String DecodedEvidence := do
  let decoded ← wire.decodeBase
  match wire.evidence with
  | .sat => return .sat decoded
  | .unsat tree => return .unsat decoded (← tree.decode decoded.certificate)
  | .subsumption root sub sup tree =>
      return .subsumption decoded
        (← checkedFin "node" decoded.nodeCount root)
        (← checkedFin "concept" decoded.conceptCount sub)
        (← checkedFin "concept" decoded.conceptCount sup)
        (← tree.decode decoded.certificate)
  | .unsatisfiable_concept root concept tree =>
      return .unsatisfiableConcept decoded
        (← checkedFin "node" decoded.nodeCount root)
        (← checkedFin "concept" decoded.conceptCount concept)
        (← tree.decode decoded.certificate)
  | .non_subsumption root sub sup =>
      return .nonSubsumption decoded
        (← checkedFin "node" decoded.nodeCount root)
        (← checkedFin "concept" decoded.conceptCount sub)
        (← checkedFin "concept" decoded.conceptCount sup)
  | .satisfiable_concept root concept =>
      return .satisfiableConcept decoded
        (← checkedFin "node" decoded.nodeCount root)
        (← checkedFin "concept" decoded.conceptCount concept)

def DecodedEvidence.check : DecodedEvidence → Bool
  | .sat decoded => decide (0 < decoded.nodeCount) && decoded.certificate.checkSat
  | .unsat decoded tree =>
      decide (0 < decoded.nodeCount) &&
      decoded.certificate.labels.isEmpty &&
      decoded.certificate.edges.isEmpty &&
      decoded.certificate.obligations.isEmpty &&
      tree.check decoded.certificate
  | .subsumption decoded root sub sup tree =>
      decoded.certificate.checkSubsumptionRoot root sub sup &&
      tree.check decoded.certificate
  | .unsatisfiableConcept decoded root concept tree =>
      decoded.certificate.checkUnsatisfiableRoot root concept &&
      tree.check decoded.certificate
  | .nonSubsumption decoded root sub sup =>
      decide ((root, .pos sub) ∈ decoded.certificate.labels) &&
      decide ((root, .negated sup) ∈ decoded.certificate.labels) &&
      decoded.certificate.checkSat
  | .satisfiableConcept decoded root concept =>
      decide ((root, .pos concept) ∈ decoded.certificate.labels) &&
      decoded.certificate.checkSat

def WireCertificate.check (wire : WireCertificate) : Except String Bool := do
  return (← wire.decode).check

theorem DecodedEvidence.sat_sound (decoded : DecodedCertificate)
    (hcheck : (DecodedEvidence.sat decoded).check = true) :
    ∃ (Domain : Type) (I : Interp Domain (Fin decoded.conceptCount)
        (Fin decoded.roleCount)), Nonempty Domain ∧
      I.models decoded.certificate.ontology := by
  simp only [DecodedEvidence.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  letI : Nonempty (Fin decoded.nodeCount) := ⟨⟨0, hcheck.1⟩⟩
  rcases decoded.certificate.checkSat_satisfiable hcheck.2 with ⟨I, hmodels⟩
  exact ⟨Fin decoded.nodeCount, I, inferInstance, hmodels⟩

theorem DecodedEvidence.unsat_sound (decoded : DecodedCertificate)
    (tree : FiniteRefutationTree decoded.nodeCount decoded.conceptCount
      decoded.roleCount decoded.variableCount)
    (hcheck : (DecodedEvidence.unsat decoded tree).check = true) :
    ¬∃ (Domain : Type) (I : Interp Domain (Fin decoded.conceptCount)
        (Fin decoded.roleCount)), Nonempty Domain ∧
      I.models decoded.certificate.ontology := by
  simp only [DecodedEvidence.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨⟨hnode, hlabels⟩, hedges⟩, hobligations⟩,
    hrefutation⟩
  letI : Nonempty (Fin decoded.nodeCount) :=
    ⟨⟨0, hnode⟩⟩
  have hempty : decoded.certificate.EmptyRoot := by
    simp only [List.isEmpty_iff] at hlabels hedges hobligations
    exact ⟨hlabels, hedges, hobligations⟩
  exact tree.check_ontology_unsatisfiable decoded.certificate hempty hrefutation

theorem DecodedEvidence.subsumption_sound (decoded : DecodedCertificate)
    (root : Fin decoded.nodeCount) (sub sup : Fin decoded.conceptCount)
    (tree : FiniteRefutationTree decoded.nodeCount decoded.conceptCount
      decoded.roleCount decoded.variableCount)
    (hcheck : (DecodedEvidence.subsumption decoded root sub sup tree).check = true) :
    EntailsSub decoded.certificate.ontology sub sup := by
  simp only [DecodedEvidence.check, Bool.and_eq_true] at hcheck
  exact tree.check_subsumption decoded.certificate root sub sup
    (decoded.certificate.checkSubsumptionRoot_sound root sub sup hcheck.1) hcheck.2

theorem DecodedEvidence.unsatisfiableConcept_sound (decoded : DecodedCertificate)
    (root : Fin decoded.nodeCount) (concept : Fin decoded.conceptCount)
    (tree : FiniteRefutationTree decoded.nodeCount decoded.conceptCount
      decoded.roleCount decoded.variableCount)
    (hcheck : (DecodedEvidence.unsatisfiableConcept decoded root concept tree).check = true) :
    UnsatisfiableConcept decoded.certificate.ontology concept := by
  simp only [DecodedEvidence.check, Bool.and_eq_true] at hcheck
  exact tree.check_unsatisfiable_concept decoded.certificate root concept
    (decoded.certificate.checkUnsatisfiableRoot_sound root concept hcheck.1) hcheck.2

theorem DecodedEvidence.nonSubsumption_sound (decoded : DecodedCertificate)
    (root : Fin decoded.nodeCount) (sub sup : Fin decoded.conceptCount)
    (hcheck : (DecodedEvidence.nonSubsumption decoded root sub sup).check = true) :
    ¬EntailsSub decoded.certificate.ontology sub sup := by
  simp only [DecodedEvidence.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact decoded.certificate.checkSat_not_entailsSub root sub sup
    hcheck.1.1 hcheck.1.2 hcheck.2

theorem DecodedEvidence.satisfiableConcept_sound (decoded : DecodedCertificate)
    (root : Fin decoded.nodeCount) (concept : Fin decoded.conceptCount)
    (hcheck : (DecodedEvidence.satisfiableConcept decoded root concept).check = true) :
    ¬UnsatisfiableConcept decoded.certificate.ontology concept := by
  simp only [DecodedEvidence.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact decoded.certificate.checkSat_not_unsatisfiableConcept root concept
    hcheck.1 hcheck.2

def DecodedEvidence.SemanticallyValid : DecodedEvidence → Prop
  | .sat decoded =>
      ∃ (Domain : Type) (I : Interp Domain (Fin decoded.conceptCount)
          (Fin decoded.roleCount)),
        Nonempty Domain ∧ I.models decoded.certificate.ontology
  | .unsat decoded _ =>
      ¬∃ (Domain : Type) (I : Interp Domain (Fin decoded.conceptCount)
          (Fin decoded.roleCount)),
        Nonempty Domain ∧ I.models decoded.certificate.ontology
  | .subsumption decoded _ sub sup _ =>
      EntailsSub decoded.certificate.ontology sub sup
  | .unsatisfiableConcept decoded _ concept _ =>
      UnsatisfiableConcept decoded.certificate.ontology concept
  | .nonSubsumption decoded _ sub sup =>
      ¬EntailsSub decoded.certificate.ontology sub sup
  | .satisfiableConcept decoded _ concept =>
      ¬UnsatisfiableConcept decoded.certificate.ontology concept

theorem DecodedEvidence.check_sound (decoded : DecodedEvidence)
    (hcheck : decoded.check = true) : decoded.SemanticallyValid := by
  cases decoded with
  | sat decoded => exact DecodedEvidence.sat_sound decoded hcheck
  | unsat decoded tree => exact DecodedEvidence.unsat_sound decoded tree hcheck
  | subsumption decoded root sub sup tree =>
      exact DecodedEvidence.subsumption_sound decoded root sub sup tree hcheck
  | unsatisfiableConcept decoded root concept tree =>
      exact DecodedEvidence.unsatisfiableConcept_sound decoded root concept tree hcheck
  | nonSubsumption decoded root sub sup =>
      exact DecodedEvidence.nonSubsumption_sound decoded root sub sup hcheck
  | satisfiableConcept decoded root concept =>
      exact DecodedEvidence.satisfiableConcept_sound decoded root concept hcheck

/-- End-to-end fail-closed theorem for the untrusted JSON-shaped wire value.
Successful wire checking necessarily exposes one bounded decoded payload whose
advertised semantics holds. Decode errors and rejected Boolean checks cannot
produce semantic evidence. -/
theorem WireCertificate.check_sound
    (wire : WireCertificate) (hcheck : wire.check = .ok true) :
    ∃ decoded, wire.decode = .ok decoded ∧ decoded.SemanticallyValid := by
  unfold WireCertificate.check at hcheck
  generalize hdecode : wire.decode = result at hcheck
  cases result with
  | error message => simp at hcheck
  | ok decoded =>
      simp at hcheck
      exact ⟨decoded, rfl, decoded.check_sound hcheck⟩

#print axioms WireCertificate.check_sound

namespace WireTests

private def failed : Except String Bool → Bool
  | .error _ => true
  | .ok _ => false

private def satDocument : WireCertificate where
  version := 1
  node_count := 1
  concept_count := 1
  role_count := 1
  variable_count := 0
  ontology := []
  labels := []
  edges := []
  obligations := []
  evidence := .sat

example : satDocument.check = .ok true := by native_decide

private def nonSubsumptionDocument : WireCertificate where
  version := 1
  node_count := 1
  concept_count := 2
  role_count := 1
  variable_count := 0
  ontology := []
  labels := [
    { node := 0, literal := ⟨0, false⟩ },
    { node := 0, literal := ⟨1, true⟩ }]
  edges := []
  obligations := []
  evidence := .non_subsumption 0 0 1

example : nonSubsumptionDocument.check = .ok true := by native_decide

private def wrongNonSubsumptionDocument : WireCertificate :=
  { nonSubsumptionDocument with evidence := .non_subsumption 0 1 0 }

example : wrongNonSubsumptionDocument.check = .ok false := by native_decide

private def satisfiableConceptDocument : WireCertificate where
  version := 1
  node_count := 1
  concept_count := 2
  role_count := 1
  variable_count := 0
  ontology := []
  labels := [{ node := 0, literal := ⟨0, false⟩ }]
  edges := []
  obligations := []
  evidence := .satisfiable_concept 0 0

example : satisfiableConceptDocument.check = .ok true := by native_decide

private def wrongSatisfiableConceptDocument : WireCertificate :=
  { satisfiableConceptDocument with evidence := .satisfiable_concept 0 1 }

example : wrongSatisfiableConceptDocument.check = .ok false := by native_decide

private def contradiction : WireClause := { body := [], head := [] }

private def unsatDocument : WireCertificate where
  version := 1
  node_count := 1
  concept_count := 1
  role_count := 1
  variable_count := 0
  ontology := [contradiction]
  labels := []
  edges := []
  obligations := []
  evidence := .unsat (.branch 0 [] [])

example : unsatDocument.check = .ok true := by native_decide

private def mixedOneNodeUnsatDocument : WireCertificate where
  version := 1
  node_count := 1
  concept_count := 2
  role_count := 1
  variable_count := 1
  ontology := [
    { body := [], head := [.concept ⟨0, false⟩ 0, .concept ⟨1, false⟩ 0] },
    { body := [.concept ⟨0, false⟩ 0], head := [.role 0 0 0] },
    { body := [.role 0 0 0], head := [] },
    { body := [.concept ⟨1, false⟩ 0], head := [.exists_ 0 ⟨0, false⟩ 0] },
    { body := [.exists_ 0 ⟨0, false⟩ 0], head := [] }]
  labels := []
  edges := []
  obligations := []
  evidence := .unsat
    (.branch 0 [0] [
      .branch 1 [0] [.branch 2 [0] []],
      .branch 3 [0] [.branch 4 [0] []]])

example : mixedOneNodeUnsatDocument.check = .ok true := by native_decide

private def witnessUnsatDocument : WireCertificate where
  version := 1
  node_count := 2
  concept_count := 1
  role_count := 1
  variable_count := 2
  ontology := [
    { body := [], head := [.exists_ 0 ⟨0, false⟩ 0] },
    { body := [.role 0 0 1, .concept ⟨0, false⟩ 1], head := [] }]
  labels := []
  edges := []
  obligations := []
  evidence := .unsat
    (.branch 0 [0, 0] [
      .witness 0 1 0 ⟨0, false⟩ (.branch 1 [0, 1] [])])

example : witnessUnsatDocument.check = .ok true := by native_decide

private def subsumptionDocument : WireCertificate where
  version := 1
  node_count := 1
  concept_count := 2
  role_count := 1
  variable_count := 1
  ontology := [
    { body := [.concept ⟨0, false⟩ 0, .concept ⟨1, true⟩ 0], head := [] }]
  labels := [
    { node := 0, literal := ⟨0, false⟩ },
    { node := 0, literal := ⟨1, true⟩ }]
  edges := []
  obligations := []
  evidence := .subsumption 0 0 1 (.branch 0 [0] [])

example : subsumptionDocument.check = .ok true := by native_decide

private def wrongSubsumptionRootDocument : WireCertificate :=
  { subsumptionDocument with evidence := .subsumption 0 1 0 (.branch 0 [0] []) }

example : wrongSubsumptionRootDocument.check = .ok false := by native_decide

private def unsatisfiableConceptDocument : WireCertificate where
  version := 1
  node_count := 1
  concept_count := 2
  role_count := 1
  variable_count := 1
  ontology := [{ body := [.concept ⟨0, false⟩ 0], head := [] }]
  labels := [{ node := 0, literal := ⟨0, false⟩ }]
  edges := []
  obligations := []
  evidence := .unsatisfiable_concept 0 0 (.branch 0 [0] [])

example : unsatisfiableConceptDocument.check = .ok true := by native_decide

private def wrongUnsatisfiableRootDocument : WireCertificate :=
  { unsatisfiableConceptDocument with
    evidence := .unsatisfiable_concept 0 1 (.branch 0 [0] []) }

example : wrongUnsatisfiableRootDocument.check = .ok false := by native_decide

private def nonfreshWitnessDocument : WireCertificate :=
  { witnessUnsatDocument with
    evidence := .unsat
      (.branch 0 [0, 0] [
        .witness 0 0 0 ⟨0, false⟩ (.branch 1 [0, 0] [])]) }

example : nonfreshWitnessDocument.check = .ok false := by native_decide

private def badConceptDocument : WireCertificate :=
  { satDocument with
    variable_count := 1
    ontology := [{ body := [], head := [.concept ⟨1, false⟩ 0] }] }

example : failed badConceptDocument.check = true := by native_decide

private def missingBranchDocument : WireCertificate :=
  { unsatDocument with
    variable_count := 1
    ontology := [{ body := [], head := [.concept ⟨0, false⟩ 0] }]
    evidence := .unsat (.branch 0 [0] []) }

example : failed missingBranchDocument.check = true := by native_decide

private def equalityDocument : WireCertificate :=
  { unsatDocument with
    variable_count := 1
    ontology := [{ body := [], head := [.eq 0 0] }]
    evidence := .unsat (.branch 0 [0] [.clash]) }

example : equalityDocument.check = .ok false := by native_decide

private def badVersionDocument : WireCertificate := { satDocument with version := 2 }

example : failed badVersionDocument.check = true := by native_decide

end WireTests

#print axioms DecodedEvidence.sat_sound
#print axioms checkedFin_value
#print axioms finCast_transport_back
#print axioms checkedFin_value_list
#print axioms decodeAssignment_encode
#print axioms WireLit.decode_encode
#print axioms WireAtom.decode_encode
#print axioms WireAtom.decode_encode_list
#print axioms WireClause.decode_encode
#print axioms WireClause.decode_encode_list
#print axioms DecodedEvidence.unsat_sound
#print axioms DecodedEvidence.subsumption_sound
#print axioms DecodedEvidence.unsatisfiableConcept_sound
#print axioms DecodedEvidence.nonSubsumption_sound
#print axioms DecodedEvidence.satisfiableConcept_sound

end ContextCalculus.Hypertableau
