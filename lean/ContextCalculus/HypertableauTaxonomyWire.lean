import ContextCalculus.HypertableauTaxonomyCertificate
import Lean

/-!
# Executable batch wire format for exact HT taxonomies

One ontology and one named-class vector are shared by every query. Concept
evidence is positional. Subsumption evidence is a square row-major matrix.
Consequently, successful decoding proves that no named concept or ordered pair
was omitted or duplicated.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireQueryPayload where
  node_count : Nat
  labels : List WireLabel
  edges : List WireEdge
  obligations : List WireObligation
  evidence : WireEvidence
deriving FromJson, ToJson, Repr

structure WireTaxonomyCertificate where
  version : Nat
  concept_count : Nat
  role_count : Nat
  variable_count : Nat
  ontology : List WireClause
  named : List Nat
  concepts : List WireQueryPayload
  subsumptions : List (List WireQueryPayload)
deriving FromJson, ToJson, Repr

def WireQueryPayload.decodeCertificate
    (payload : WireQueryPayload)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) :
    Except String { certificate :
      FiniteSatCertificate payload.node_count conceptCount roleCount variableCount //
        certificate.ontology = ontology } := do
  let labels ← payload.labels.mapM fun label => do
    return (← checkedFin "node" payload.node_count label.node,
      ← label.literal.decode conceptCount)
  let edges ← payload.edges.mapM fun edge => do
    return (← checkedFin "role" roleCount edge.role,
      ← checkedFin "node" payload.node_count edge.source,
      ← checkedFin "node" payload.node_count edge.target)
  let obligations ← payload.obligations.mapM fun obligation => do
    return (← checkedFin "role" roleCount obligation.role,
      ← obligation.filler.decode conceptCount,
      ← checkedFin "node" payload.node_count obligation.node)
  return ⟨{ ontology, labels, edges, obligations }, rfl⟩

def WireQueryPayload.decodeConcept
    (payload : WireQueryPayload)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (expected : Fin conceptCount) :
    Except String (FiniteConceptDecision ontology expected) := do
  let decoded ← payload.decodeCertificate ontology
  let certificate := decoded.1
  have sameOntology : certificate.ontology = ontology := decoded.2
  match payload.evidence with
  | .unsatisfiable_concept root concept tree =>
      let root ← checkedFin "node" payload.node_count root
      let concept ← checkedFin "concept" conceptCount concept
      if hconcept : concept = expected then
        let tree ← tree.decode certificate
        if hroot : certificate.checkUnsatisfiableRoot root expected = true then
          if htree : tree.check certificate = true then
            return .unsatisfiable payload.node_count certificate sameOntology root tree
              (certificate.checkUnsatisfiableRoot_sound root expected hroot) htree
          else throw "concept refutation tree was rejected"
        else throw "concept refutation root does not match its matrix cell"
      else throw "concept evidence is in the wrong matrix position"
  | .satisfiable_concept root concept =>
      let root ← checkedFin "node" payload.node_count root
      let concept ← checkedFin "concept" conceptCount concept
      if hconcept : concept = expected then
        if hlabel : (root, .pos expected) ∈ certificate.labels then
          if hmodel : certificate.checkSat = true then
            return .satisfiable payload.node_count certificate sameOntology root hlabel hmodel
          else throw "concept model was rejected"
        else throw "concept model omits its declared root label"
      else throw "concept evidence is in the wrong matrix position"
  | _ => throw "expected concept-status evidence"

def WireQueryPayload.decodeSubsumption
    (payload : WireQueryPayload)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (expectedSub expectedSup : Fin conceptCount) :
    Except String (FiniteSubsumptionDecision ontology expectedSub expectedSup) := do
  let decoded ← payload.decodeCertificate ontology
  let certificate := decoded.1
  have sameOntology : certificate.ontology = ontology := decoded.2
  match payload.evidence with
  | .subsumption root sub sup tree =>
      let root ← checkedFin "node" payload.node_count root
      let sub ← checkedFin "concept" conceptCount sub
      let sup ← checkedFin "concept" conceptCount sup
      if hsub : sub = expectedSub then
        if hsup : sup = expectedSup then
          let tree ← tree.decode certificate
          if hroot : certificate.checkSubsumptionRoot root expectedSub expectedSup = true then
            if htree : tree.check certificate = true then
              return .entailed payload.node_count certificate sameOntology root tree
                (certificate.checkSubsumptionRoot_sound root expectedSub expectedSup hroot) htree
            else throw "subsumption refutation tree was rejected"
          else throw "subsumption refutation root does not match its matrix cell"
        else throw "subsumption evidence has the wrong superclass"
      else throw "subsumption evidence has the wrong subclass"
  | .non_subsumption root sub sup =>
      let root ← checkedFin "node" payload.node_count root
      let sub ← checkedFin "concept" conceptCount sub
      let sup ← checkedFin "concept" conceptCount sup
      if hsub : sub = expectedSub then
        if hsup : sup = expectedSup then
          if hsubLabel : (root, .pos expectedSub) ∈ certificate.labels then
            if hnotSup : (root, .negated expectedSup) ∈ certificate.labels then
              if hmodel : certificate.checkSat = true then
                return .notEntailed payload.node_count certificate sameOntology root
                  hsubLabel hnotSup hmodel
              else throw "subsumption countermodel was rejected"
            else throw "subsumption countermodel omits the negative superclass"
          else throw "subsumption countermodel omits the subclass"
        else throw "non-subsumption evidence has the wrong superclass"
      else throw "non-subsumption evidence has the wrong subclass"
  | _ => throw "expected subsumption evidence"

def decodeConceptEntries
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) :
    (named : List (Fin conceptCount)) → List WireQueryPayload →
      Except String (Σ entries : List (SomeFiniteConceptDecision ontology),
        ∀ concept, concept ∈ named →
          { entry // entry ∈ entries ∧ entry.concept = concept })
  | [], [] => return ⟨[], by
      intro concept hmem
      exact False.elim (by simpa using hmem)⟩
  | concept :: concepts, payload :: payloads => do
      let decision ← payload.decodeConcept ontology concept
      let tail ← decodeConceptEntries ontology concepts payloads
      let head : SomeFiniteConceptDecision ontology := ⟨concept, decision⟩
      return ⟨head :: tail.1, by
        intro candidate hcandidate
        if heq : candidate = concept then
          subst candidate
          exact ⟨head, by simp, rfl⟩
        else
          have htail : candidate ∈ concepts :=
            (List.mem_cons.mp hcandidate).resolve_left heq
          rcases tail.2 candidate htail with ⟨entry, hmem, hentry⟩
          exact ⟨entry, by simp [hmem], hentry⟩⟩
  | _, _ => throw "concept evidence count does not match named classes"

def decodeSubsumptionRow
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (sub : Fin conceptCount) :
    (supers : List (Fin conceptCount)) → List WireQueryPayload →
      Except String (Σ entries : List (SomeFiniteSubsumptionDecision ontology),
        ∀ sup, sup ∈ supers →
          { entry // entry ∈ entries ∧ entry.sub = sub ∧ entry.sup = sup })
  | [], [] => return ⟨[], by
      intro sup hmem
      exact False.elim (by simpa using hmem)⟩
  | sup :: supers, payload :: payloads => do
      let decision ← payload.decodeSubsumption ontology sub sup
      let tail ← decodeSubsumptionRow ontology sub supers payloads
      let head : SomeFiniteSubsumptionDecision ontology := ⟨sub, sup, decision⟩
      return ⟨head :: tail.1, by
        intro candidate hcandidate
        if heq : candidate = sup then
          subst candidate
          exact ⟨head, by simp, rfl, rfl⟩
        else
          have htail : candidate ∈ supers :=
            (List.mem_cons.mp hcandidate).resolve_left heq
          rcases tail.2 candidate htail with ⟨entry, hmem, hsub, hsup⟩
          exact ⟨entry, by simp [hmem], hsub, hsup⟩⟩
  | _, _ => throw "subsumption row width does not match named classes"

def decodeSubsumptionEntries
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (allNamed : List (Fin conceptCount)) :
    (subs : List (Fin conceptCount)) → List (List WireQueryPayload) →
      Except String (Σ entries : List (SomeFiniteSubsumptionDecision ontology),
        ∀ sub, sub ∈ subs → ∀ sup, sup ∈ allNamed →
          { entry // entry ∈ entries ∧ entry.sub = sub ∧ entry.sup = sup })
  | [], [] => return ⟨[], by
      intro sub hmem
      exact False.elim (by simpa using hmem)⟩
  | sub :: subs, row :: rows => do
      let head ← decodeSubsumptionRow ontology sub allNamed row
      let tail ← decodeSubsumptionEntries ontology allNamed subs rows
      return ⟨head.1 ++ tail.1, by
        intro candidate hcandidate sup hsup
        if heq : candidate = sub then
          subst candidate
          rcases head.2 sup hsup with ⟨entry, hmem, hsubEq, hsupEq⟩
          exact ⟨entry, List.mem_append_left _ hmem, hsubEq, hsupEq⟩
        else
          have htail : candidate ∈ subs :=
            (List.mem_cons.mp hcandidate).resolve_left heq
          rcases tail.2 candidate htail sup hsup with
            ⟨entry, hmem, hsubEq, hsupEq⟩
          exact ⟨entry, List.mem_append_right _ hmem, hsubEq, hsupEq⟩⟩
  | _, _ => throw "subsumption row count does not match named classes"

structure DecodedTaxonomyCertificate where
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))
  named : List (Fin conceptCount)
  namedNodup : named.Nodup
  finite : FiniteCoveredTaxonomyCertificate ontology named

def WireTaxonomyCertificate.decode
    (wire : WireTaxonomyCertificate) : Except String DecodedTaxonomyCertificate := do
  if wire.version != 1 then
    throw s!"unsupported hypertableau taxonomy certificate version {wire.version}"
  let ontology ← wire.ontology.mapM
    (WireClause.decode wire.variable_count wire.concept_count wire.role_count)
  let named ← wire.named.mapM (checkedFin "named concept" wire.concept_count)
  if hnodup : named.Nodup then
    let concepts ← decodeConceptEntries ontology named wire.concepts
    let subsumptions ← decodeSubsumptionEntries ontology named named wire.subsumptions
    return {
      conceptCount := wire.concept_count
      roleCount := wire.role_count
      variableCount := wire.variable_count
      ontology
      named
      namedNodup := hnodup
      finite := {
        concepts := concepts.1
        subsumptions := subsumptions.1
        conceptCovered := concepts.2
        subsumptionCovered := subsumptions.2
      }
    }
  else throw "named taxonomy concepts contain duplicates"

def WireTaxonomyCertificate.check (wire : WireTaxonomyCertificate) : Bool :=
  wire.decode.isOk

def DecodedTaxonomyCertificate.semantic
    (decoded : DecodedTaxonomyCertificate) :
    CompleteTaxonomyCertificate decoded.ontology decoded.named :=
  decoded.finite.sound

theorem DecodedTaxonomyCertificate.unsatisfiable_exact
    (decoded : DecodedTaxonomyCertificate)
    (concept : Fin decoded.conceptCount) (hnamed : concept ∈ decoded.named) :
    concept ∈ decoded.semantic.unsatisfiable ↔
      UnsatisfiableConcept decoded.ontology concept :=
  decoded.semantic.unsatisfiable_exact concept hnamed

theorem DecodedTaxonomyCertificate.subsumptions_exact
    (decoded : DecodedTaxonomyCertificate)
    (sub sup : Fin decoded.conceptCount)
    (hsub : sub ∈ decoded.named) (hsup : sup ∈ decoded.named) :
    (sub, sup) ∈ decoded.semantic.subsumptions ↔
      EntailsSub decoded.ontology sub sup :=
  decoded.semantic.subsumptions_exact sub sup hsub hsup

namespace TaxonomyWireTests

private def conceptModel (concept : Nat) : WireQueryPayload where
  node_count := 1
  labels := [{ node := 0, literal := ⟨concept, false⟩ }]
  edges := []
  obligations := []
  evidence := .satisfiable_concept 0 concept

private def reflexiveSubsumption (concept : Nat) : WireQueryPayload where
  node_count := 1
  labels := [
    { node := 0, literal := ⟨concept, false⟩ },
    { node := 0, literal := ⟨concept, true⟩ }]
  edges := []
  obligations := []
  evidence := .subsumption 0 concept concept .clash

private def nonSubsumption (sub sup : Nat) : WireQueryPayload where
  node_count := 1
  labels := [
    { node := 0, literal := ⟨sub, false⟩ },
    { node := 0, literal := ⟨sup, true⟩ }]
  edges := []
  obligations := []
  evidence := .non_subsumption 0 sub sup

private def exactTwoConceptTaxonomy : WireTaxonomyCertificate where
  version := 1
  concept_count := 2
  role_count := 1
  variable_count := 0
  ontology := []
  named := [0, 1]
  concepts := [conceptModel 0, conceptModel 1]
  subsumptions := [
    [reflexiveSubsumption 0, nonSubsumption 0 1],
    [nonSubsumption 1 0, reflexiveSubsumption 1]]

example : exactTwoConceptTaxonomy.check = true := by native_decide

private def missingCell : WireTaxonomyCertificate :=
  { exactTwoConceptTaxonomy with
    subsumptions := [[reflexiveSubsumption 0],
      [nonSubsumption 1 0, reflexiveSubsumption 1]] }

example : missingCell.check = false := by native_decide

private def wrongCell : WireTaxonomyCertificate :=
  { exactTwoConceptTaxonomy with
    subsumptions := [[reflexiveSubsumption 0, nonSubsumption 1 0],
      [nonSubsumption 1 0, reflexiveSubsumption 1]] }

example : wrongCell.check = false := by native_decide

private def duplicateNamed : WireTaxonomyCertificate :=
  { exactTwoConceptTaxonomy with named := [0, 0] }

example : duplicateNamed.check = false := by native_decide

end TaxonomyWireTests

#print axioms DecodedTaxonomyCertificate.unsatisfiable_exact
#print axioms DecodedTaxonomyCertificate.subsumptions_exact

end ContextCalculus.Hypertableau
