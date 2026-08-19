import ContextCalculus.HypertableauTaxonomyWire
import ContextCalculus.HypertableauEqualityWire

/-!
# Mixed equality-free/equality-aware HT taxonomy certificates

Version 1 taxonomy documents remain unchanged. Version 2 shares one decoded
ontology and permits every row-major query cell to carry either the established
equality-free payload or an equality-aware state and evidence object. Both
variants refine to the same semantic decision type before matrix coverage is
assembled.
-/

namespace ContextCalculus.Hypertableau

open Lean

inductive WireMixedQueryPayload where
  | plain (payload : WireQueryPayload)
  | equality (node_count : Nat) (state : WireEqState) (evidence : WireEqEvidence)
deriving FromJson, ToJson, Repr

structure WireMixedTaxonomyCertificate where
  version : Nat
  concept_count : Nat
  role_count : Nat
  variable_count : Nat
  ontology : List WireClause
  named : List Nat
  concepts : List WireMixedQueryPayload
  subsumptions : List (List WireMixedQueryPayload)
deriving FromJson, ToJson, Repr

def WireEqState.decodeForOntology
    (wire : WireEqState) (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) :
    Except String { certificate :
      FiniteEqCertificate nodeCount conceptCount roleCount variableCount //
        certificate.base.ontology = ontology } := do
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
  return ⟨{
    base := { ontology, labels, edges, obligations }
    equalities, representative, representativePath
  }, rfl⟩

def WireMixedQueryPayload.decodeConcept
    (payload : WireMixedQueryPayload)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (expected : Fin conceptCount) : Except String (ConceptDecision ontology expected) := do
  match payload with
  | .plain payload =>
      return (← payload.decodeConcept ontology expected).sound
  | .equality nodeCount state evidence =>
      let decoded ← state.decodeForOntology nodeCount conceptCount roleCount variableCount ontology
      let certificate := decoded.1
      have sameOntology : certificate.base.ontology = ontology := decoded.2
      match evidence with
      | .unsatisfiable_concept root concept tree =>
          let root ← checkedFin "node" nodeCount root
          let concept ← checkedFin "concept" conceptCount concept
          if hconcept : concept = expected then
            let tree ← tree.decode nodeCount conceptCount roleCount variableCount ontology
            if hroot : certificate.checkUnsatisfiableRoot root expected = true then
              if htree : tree.check certificate = true then
                let proof := tree.check_unsatisfiable_concept certificate root expected
                  (certificate.checkUnsatisfiableRoot_sound root expected hroot) htree
                return .unsatisfiable (sameOntology ▸ proof)
              else throw "equality-aware concept refutation tree was rejected"
            else throw "equality-aware concept refutation root does not match its matrix cell"
          else throw "equality-aware concept evidence is in the wrong matrix position"
      | .satisfiable_concept root concept =>
          let root ← checkedFin "node" nodeCount root
          let concept ← checkedFin "concept" conceptCount concept
          if hconcept : concept = expected then
            if hlabel : (root, .pos expected) ∈ certificate.base.labels then
              if hmodel : certificate.checkEqSat = true then
                let proof := certificate.checkEqSat_not_unsatisfiableConcept
                  root expected hlabel hmodel
                return .satisfiable (sameOntology ▸ proof)
              else throw "equality-aware concept model was rejected"
            else throw "equality-aware concept model omits its declared root label"
          else throw "equality-aware concept evidence is in the wrong matrix position"
      | _ => throw "expected equality-aware concept-status evidence"

def WireMixedQueryPayload.decodeSubsumption
    (payload : WireMixedQueryPayload)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (expectedSub expectedSup : Fin conceptCount) :
    Except String (SubsumptionDecision ontology expectedSub expectedSup) := do
  match payload with
  | .plain payload =>
      return (← payload.decodeSubsumption ontology expectedSub expectedSup).sound
  | .equality nodeCount state evidence =>
      let decoded ← state.decodeForOntology nodeCount conceptCount roleCount variableCount ontology
      let certificate := decoded.1
      have sameOntology : certificate.base.ontology = ontology := decoded.2
      match evidence with
      | .subsumption root sub sup tree =>
          let root ← checkedFin "node" nodeCount root
          let sub ← checkedFin "concept" conceptCount sub
          let sup ← checkedFin "concept" conceptCount sup
          if hsub : sub = expectedSub then
            if hsup : sup = expectedSup then
              let tree ← tree.decode nodeCount conceptCount roleCount variableCount ontology
              if hroot : certificate.checkSubsumptionRoot root expectedSub expectedSup = true then
                if htree : tree.check certificate = true then
                  let proof := tree.check_subsumption certificate root expectedSub expectedSup
                    (certificate.checkSubsumptionRoot_sound root expectedSub expectedSup hroot) htree
                  return .entailed (sameOntology ▸ proof)
                else throw "equality-aware subsumption refutation tree was rejected"
              else throw "equality-aware subsumption root does not match its matrix cell"
            else throw "equality-aware subsumption evidence has the wrong superclass"
          else throw "equality-aware subsumption evidence has the wrong subclass"
      | .non_subsumption root sub sup =>
          let root ← checkedFin "node" nodeCount root
          let sub ← checkedFin "concept" conceptCount sub
          let sup ← checkedFin "concept" conceptCount sup
          if hsub : sub = expectedSub then
            if hsup : sup = expectedSup then
              if hsubLabel : (root, .pos expectedSub) ∈ certificate.base.labels then
                if hnotSup : (root, .negated expectedSup) ∈ certificate.base.labels then
                  if hmodel : certificate.checkEqSat = true then
                    let proof := certificate.checkEqSat_not_entailsSub root
                      expectedSub expectedSup hsubLabel hnotSup hmodel
                    return .notEntailed (sameOntology ▸ proof)
                  else throw "equality-aware subsumption countermodel was rejected"
                else throw "equality-aware countermodel omits the negative superclass"
              else throw "equality-aware countermodel omits the subclass"
            else throw "equality-aware non-subsumption evidence has the wrong superclass"
          else throw "equality-aware non-subsumption evidence has the wrong subclass"
      | _ => throw "expected equality-aware subsumption evidence"

def decodeMixedConceptEntries
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) :
    (named : List (Fin conceptCount)) → List WireMixedQueryPayload →
      Except String (Σ entries : List (SomeConceptDecision ontology),
        ∀ concept, concept ∈ named →
          { entry // entry ∈ entries ∧ entry.concept = concept })
  | [], [] => return ⟨[], by
      intro concept hmem
      exact False.elim (by simpa using hmem)⟩
  | concept :: concepts, payload :: payloads => do
      let decision ← payload.decodeConcept ontology concept
      let tail ← decodeMixedConceptEntries ontology concepts payloads
      let head : SomeConceptDecision ontology := ⟨concept, decision⟩
      return ⟨head :: tail.1, by
        intro candidate hcandidate
        if heq : candidate = concept then
          subst candidate
          exact ⟨head, by simp, rfl⟩
        else
          have htail := (List.mem_cons.mp hcandidate).resolve_left heq
          rcases tail.2 candidate htail with ⟨entry, hmem, hentry⟩
          exact ⟨entry, by simp [hmem], hentry⟩⟩
  | _, _ => throw "concept evidence count does not match named classes"

def decodeMixedSubsumptionRow
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (sub : Fin conceptCount) :
    (supers : List (Fin conceptCount)) → List WireMixedQueryPayload →
      Except String (Σ entries : List (SomeSubsumptionDecision ontology),
        ∀ sup, sup ∈ supers →
          { entry // entry ∈ entries ∧ entry.sub = sub ∧ entry.sup = sup })
  | [], [] => return ⟨[], by
      intro sup hmem
      exact False.elim (by simpa using hmem)⟩
  | sup :: supers, payload :: payloads => do
      let decision ← payload.decodeSubsumption ontology sub sup
      let tail ← decodeMixedSubsumptionRow ontology sub supers payloads
      let head : SomeSubsumptionDecision ontology := ⟨sub, sup, decision⟩
      return ⟨head :: tail.1, by
        intro candidate hcandidate
        if heq : candidate = sup then
          subst candidate
          exact ⟨head, by simp, rfl, rfl⟩
        else
          have htail := (List.mem_cons.mp hcandidate).resolve_left heq
          rcases tail.2 candidate htail with ⟨entry, hmem, hsub, hsup⟩
          exact ⟨entry, by simp [hmem], hsub, hsup⟩⟩
  | _, _ => throw "subsumption row width does not match named classes"

def decodeMixedSubsumptionEntries
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (allNamed : List (Fin conceptCount)) :
    (subs : List (Fin conceptCount)) → List (List WireMixedQueryPayload) →
      Except String (Σ entries : List (SomeSubsumptionDecision ontology),
        ∀ sub, sub ∈ subs → ∀ sup, sup ∈ allNamed →
          { entry // entry ∈ entries ∧ entry.sub = sub ∧ entry.sup = sup })
  | [], [] => return ⟨[], by
      intro sub hmem
      exact False.elim (by simpa using hmem)⟩
  | sub :: subs, row :: rows => do
      let head ← decodeMixedSubsumptionRow ontology sub allNamed row
      let tail ← decodeMixedSubsumptionEntries ontology allNamed subs rows
      return ⟨head.1 ++ tail.1, by
        intro candidate hcandidate sup hsup
        if heq : candidate = sub then
          subst candidate
          rcases head.2 sup hsup with ⟨entry, hmem, hsubEq, hsupEq⟩
          exact ⟨entry, List.mem_append_left _ hmem, hsubEq, hsupEq⟩
        else
          have htail := (List.mem_cons.mp hcandidate).resolve_left heq
          rcases tail.2 candidate htail sup hsup with ⟨entry, hmem, hsubEq, hsupEq⟩
          exact ⟨entry, List.mem_append_right _ hmem, hsubEq, hsupEq⟩⟩
  | _, _ => throw "subsumption row count does not match named classes"

structure DecodedMixedTaxonomyCertificate where
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))
  named : List (Fin conceptCount)
  namedNodup : named.Nodup
  covered : CoveredTaxonomyCertificate ontology named

def WireMixedTaxonomyCertificate.decode
    (wire : WireMixedTaxonomyCertificate) : Except String DecodedMixedTaxonomyCertificate := do
  if wire.version != 2 then
    throw s!"unsupported mixed hypertableau taxonomy certificate version {wire.version}"
  let ontology ← wire.ontology.mapM
    (WireClause.decode wire.variable_count wire.concept_count wire.role_count)
  let named ← wire.named.mapM (checkedFin "named concept" wire.concept_count)
  if hnodup : named.Nodup then
    let concepts ← decodeMixedConceptEntries ontology named wire.concepts
    let subsumptions ← decodeMixedSubsumptionEntries ontology named named wire.subsumptions
    return {
      conceptCount := wire.concept_count
      roleCount := wire.role_count
      variableCount := wire.variable_count
      ontology, named, namedNodup := hnodup
      covered := {
        concepts := concepts.1
        subsumptions := subsumptions.1
        conceptCovered := concepts.2
        subsumptionCovered := subsumptions.2
      }
    }
  else throw "named taxonomy concepts contain duplicates"

def WireMixedTaxonomyCertificate.check (wire : WireMixedTaxonomyCertificate) : Bool :=
  wire.decode.isOk

def DecodedMixedTaxonomyCertificate.semantic
    (decoded : DecodedMixedTaxonomyCertificate) :
    CompleteTaxonomyCertificate decoded.ontology decoded.named :=
  decoded.covered.sound

theorem DecodedMixedTaxonomyCertificate.unsatisfiable_exact
    (decoded : DecodedMixedTaxonomyCertificate)
    (concept : Fin decoded.conceptCount) (hnamed : concept ∈ decoded.named) :
    concept ∈ decoded.semantic.unsatisfiable ↔
      UnsatisfiableConcept decoded.ontology concept :=
  decoded.semantic.unsatisfiable_exact concept hnamed

theorem DecodedMixedTaxonomyCertificate.subsumptions_exact
    (decoded : DecodedMixedTaxonomyCertificate)
    (sub sup : Fin decoded.conceptCount)
    (hsub : sub ∈ decoded.named) (hsup : sup ∈ decoded.named) :
    (sub, sup) ∈ decoded.semantic.subsumptions ↔
      EntailsSub decoded.ontology sub sup :=
  decoded.semantic.subsumptions_exact sub sup hsub hsup

namespace MixedTaxonomyWireTests

private def plainConcept (concept : Nat) : WireMixedQueryPayload := .plain {
  node_count := 1
  labels := [{ node := 0, literal := ⟨concept, false⟩ }]
  edges := []
  obligations := []
  evidence := .satisfiable_concept 0 concept
}

private def plainReflexive (concept : Nat) : WireMixedQueryPayload := .plain {
  node_count := 1
  labels := [
    { node := 0, literal := ⟨concept, false⟩ },
    { node := 0, literal := ⟨concept, true⟩ }]
  edges := []
  obligations := []
  evidence := .subsumption 0 concept concept .clash
}

private def quotientState (labels : List WireLabel) : WireEqState where
  labels
  edges := []
  obligations := []
  equalities := [{ left := 0, right := 1 }]
  representatives := [0, 0]
  representative_paths := [[], [0]]

private def eqConcept (concept : Nat) : WireMixedQueryPayload := .equality 2
  (quotientState [{ node := 1, literal := ⟨concept, false⟩ }])
  (.satisfiable_concept 1 concept)

private def eqReflexive (concept : Nat) : WireMixedQueryPayload := .equality 2
  (quotientState [
    { node := 1, literal := ⟨concept, false⟩ },
    { node := 1, literal := ⟨concept, true⟩ }])
  (.subsumption 1 concept concept .clash)

private def eqNonSubsumption (sub sup : Nat) : WireMixedQueryPayload := .equality 2
  (quotientState [
    { node := 1, literal := ⟨sub, false⟩ },
    { node := 1, literal := ⟨sup, true⟩ }])
  (.non_subsumption 1 sub sup)

private def plainNonSubsumption (sub sup : Nat) : WireMixedQueryPayload := .plain {
  node_count := 1
  labels := [
    { node := 0, literal := ⟨sub, false⟩ },
    { node := 0, literal := ⟨sup, true⟩ }]
  edges := []
  obligations := []
  evidence := .non_subsumption 0 sub sup
}

private def accepted : WireMixedTaxonomyCertificate where
  version := 2
  concept_count := 2
  role_count := 1
  variable_count := 0
  ontology := []
  named := [0, 1]
  concepts := [eqConcept 0, plainConcept 1]
  subsumptions := [
    [eqReflexive 0, eqNonSubsumption 0 1],
    [plainNonSubsumption 1 0, plainReflexive 1]]

example : accepted.check = true := by native_decide

private def missingCell : WireMixedTaxonomyCertificate :=
  { accepted with subsumptions := [[eqReflexive 0], accepted.subsumptions[1]!] }

example : missingCell.check = false := by native_decide

private def wrongEqCell : WireMixedTaxonomyCertificate :=
  { accepted with concepts := [eqConcept 1, plainConcept 1] }

example : wrongEqCell.check = false := by native_decide

end MixedTaxonomyWireTests

#print axioms DecodedMixedTaxonomyCertificate.unsatisfiable_exact
#print axioms DecodedMixedTaxonomyCertificate.subsumptions_exact

end ContextCalculus.Hypertableau
