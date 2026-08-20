import ContextCalculus.HypertableauCardinalityWire
import ContextCalculus.HypertableauMixedTaxonomyWire
import ContextCalculus.HypertableauEqualityNormalizationWire
import ContextCalculus.HypertableauNormalizedWire
import ContextCalculus.HypertableauPreprocessingWire

/-!
# Complete cardinality-aware hypertableau taxonomies

Every cell shares one ontology and one list of cardinality definitions.  The
wire contains exactly one concept decision per named concept and one
subsumption decision per ordered named pair.  A cell carries only the varying
equality state, query evidence, and optional refutation trees.
-/

namespace ContextCalculus.Hypertableau

open Lean

inductive CardinalityConceptDecision
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) (concept : Concept) : Type where
  | unsatisfiable
      (proof : UnsatisfiableConceptWithCardinality ontology definitions concept)
  | satisfiable
      (counterexample : ¬UnsatisfiableConceptWithCardinality ontology definitions concept)

inductive CardinalitySubsumptionDecision
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) (sub sup : Concept) : Type where
  | entailed (proof : EntailsSubWithCardinality ontology definitions sub sup)
  | notEntailed (counterexample : ¬EntailsSubWithCardinality ontology definitions sub sup)

structure CompleteCardinalityTaxonomyCertificate
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) (named : List Concept) where
  concept : ∀ candidate, candidate ∈ named →
    CardinalityConceptDecision ontology definitions candidate
  subsumption : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named →
    CardinalitySubsumptionDecision ontology definitions sub sup

structure SomeCardinalityConceptDecision
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) where
  concept : Concept
  decision : CardinalityConceptDecision ontology definitions concept

structure SomeCardinalitySubsumptionDecision
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) where
  sub : Concept
  sup : Concept
  decision : CardinalitySubsumptionDecision ontology definitions sub sup

structure CoveredCardinalityTaxonomyCertificate
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) (named : List Concept) where
  concepts : List (SomeCardinalityConceptDecision ontology definitions)
  subsumptions : List (SomeCardinalitySubsumptionDecision ontology definitions)
  conceptCovered : ∀ concept, concept ∈ named →
    { entry // entry ∈ concepts ∧ entry.concept = concept }
  subsumptionCovered : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named →
    { entry // entry ∈ subsumptions ∧ entry.sub = sub ∧ entry.sup = sup }

def CoveredCardinalityTaxonomyCertificate.sound
    (certificate : CoveredCardinalityTaxonomyCertificate ontology definitions named) :
    CompleteCardinalityTaxonomyCertificate ontology definitions named where
  concept candidate hnamed := by
    rcases certificate.conceptCovered candidate hnamed with ⟨entry, _, heq⟩
    exact heq ▸ entry.decision
  subsumption sub hsub sup hsup := by
    rcases certificate.subsumptionCovered sub hsub sup hsup with
      ⟨entry, _, hsubEq, hsupEq⟩
    exact hsupEq ▸ hsubEq ▸ entry.decision

structure WireCardinalityQueryPayload where
  node_count : Nat
  state : WireEqState
  evidence : WireEqEvidence
  refutation_depth : Nat := 0
  refutation : Option WireCardinalityEqRefutationTree := none
  distinct_refutation_depth : Nat := 0
  distinct_refutation : Option WireDistinctCardinalityRefutationTree := none
deriving FromJson, ToJson, Repr

structure WireCardinalityTaxonomyCertificate where
  version : Nat
  concept_count : Nat
  role_count : Nat
  variable_count : Nat
  ontology : List WireClause
  definitions : List WireCardinalityDef
  named : List Nat
  concepts : List WireCardinalityQueryPayload
  subsumptions : List (List WireCardinalityQueryPayload)
deriving FromJson, ToJson, Repr

def WireCardinalityQueryPayload.document
    (payload : WireCardinalityQueryPayload) (conceptCount roleCount variableCount : Nat)
    (ontology : List WireClause) (definitions : List WireCardinalityDef) :
    WireCardinalityEqCertificate where
  version := 2
  certificate := {
    version := 2
    node_count := payload.node_count
    concept_count := conceptCount
    role_count := roleCount
    variable_count := variableCount
    ontology
    state := payload.state
    evidence := payload.evidence
  }
  definitions := definitions
  refutation_depth := payload.refutation_depth
  refutation := payload.refutation
  distinct_refutation_depth := payload.distinct_refutation_depth
  distinct_refutation := payload.distinct_refutation

structure DecodedCardinalityTaxonomyCertificate where
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))
  definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))
  named : List (Fin conceptCount)
  namedNodup : named.Nodup
  covered : CoveredCardinalityTaxonomyCertificate ontology definitions named

structure DecodedCardinalityQueryPayload
    (conceptCount roleCount variableCount : Nat)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) where
  nodeCount : Nat
  evidence : DecodedEqEvidence nodeCount conceptCount roleCount variableCount
  sameOntology : (DecodedEqCertificate.rootCertificate
    ⟨nodeCount, conceptCount, roleCount, variableCount, evidence⟩).base.ontology = ontology
  refutation : Option (DecodedCardinalityEqRefutation nodeCount conceptCount
    roleCount variableCount)
  distinctRefutation : Option (DecodedDistinctCardinalityRefutation nodeCount
    conceptCount roleCount variableCount)

structure DecodedEqEvidenceFor
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount) where
  evidence : DecodedEqEvidence nodeCount conceptCount roleCount variableCount
  sameCertificate : (DecodedEqCertificate.rootCertificate
    ⟨nodeCount, conceptCount, roleCount, variableCount, evidence⟩) = certificate

def DecodedCardinalityQueryPayload.certificate
    (decoded : DecodedCardinalityQueryPayload conceptCount roleCount variableCount
      ontology definitions) : DecodedCardinalityEqCertificate :=
  ⟨⟨decoded.nodeCount, conceptCount, roleCount, variableCount, decoded.evidence⟩,
    definitions, decoded.refutation, decoded.distinctRefutation⟩

private def WireCardinalityQueryPayload.decode
    (payload : WireCardinalityQueryPayload)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) :
    Except String (DecodedCardinalityQueryPayload conceptCount roleCount variableCount
      ontology definitions) := do
  let decodedState ← payload.state.decodeForOntology payload.node_count conceptCount
    roleCount variableCount ontology
  let certificate := decodedState.1
  have certificateOntology : certificate.base.ontology = ontology := decodedState.2
  let evidenceResult : DecodedEqEvidenceFor certificate ←
    match payload.evidence with
    | .sat => pure (DecodedEqEvidenceFor.mk (.sat certificate) rfl)
    | .unsat tree =>
        pure (DecodedEqEvidenceFor.mk (.unsat certificate
          (← tree.decode payload.node_count conceptCount roleCount variableCount ontology)) rfl)
    | .subsumption root sub sup tree =>
        pure (DecodedEqEvidenceFor.mk (.subsumption certificate
          (← checkedFin "node" payload.node_count root)
          (← checkedFin "concept" conceptCount sub)
          (← checkedFin "concept" conceptCount sup)
          (← tree.decode payload.node_count conceptCount roleCount variableCount ontology)) rfl)
    | .unsatisfiable_concept root concept tree =>
        pure (DecodedEqEvidenceFor.mk (.unsatisfiableConcept certificate
          (← checkedFin "node" payload.node_count root)
          (← checkedFin "concept" conceptCount concept)
          (← tree.decode payload.node_count conceptCount roleCount variableCount ontology)) rfl)
    | .non_subsumption root sub sup =>
        pure (DecodedEqEvidenceFor.mk (.nonSubsumption certificate
          (← checkedFin "node" payload.node_count root)
          (← checkedFin "concept" conceptCount sub)
          (← checkedFin "concept" conceptCount sup)) rfl)
    | .satisfiable_concept root concept =>
        pure (DecodedEqEvidenceFor.mk (.satisfiableConcept certificate
          (← checkedFin "node" payload.node_count root)
          (← checkedFin "concept" conceptCount concept)) rfl)
  let evidence := evidenceResult.evidence
  let refutation : Option (DecodedCardinalityEqRefutation payload.node_count conceptCount
      roleCount variableCount) ← match payload.refutation with
    | none => pure none
    | some tree => do
        let decoded ← tree.decode payload.node_count conceptCount roleCount variableCount
          payload.refutation_depth ontology definitions
        pure (some decoded)
  let distinctRefutation : Option (DecodedDistinctCardinalityRefutation payload.node_count
      conceptCount roleCount variableCount) ← match payload.distinct_refutation with
    | none => pure none
    | some tree => do
        let decoded ← tree.decode payload.node_count conceptCount roleCount variableCount
          payload.distinct_refutation_depth ontology definitions
        pure (some decoded)
  have sameOntology : (DecodedEqCertificate.rootCertificate
      ⟨payload.node_count, conceptCount, roleCount, variableCount, evidence⟩).base.ontology =
      ontology := by
    rw [evidenceResult.sameCertificate]
    exact certificateOntology
  return ⟨payload.node_count, evidence, sameOntology, refutation, distinctRefutation⟩

private def decodeCardinalityConcept
    (payload : WireCardinalityQueryPayload)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (expected : Fin conceptCount) :
    Except String (CardinalityConceptDecision ontology definitions expected) := do
  let decoded ← payload.decode ontology definitions
  let certificate := decoded.certificate
  if hcheck : certificate.check = true then
    match hevidence : decoded.evidence with
    | .unsatisfiableConcept cellCertificate _ concept _ =>
        if hconcept : concept = expected then
          have hsound := certificate.check_sound hcheck
          have hproof : UnsatisfiableConceptWithCardinality ontology definitions concept := by
            dsimp [certificate, DecodedCardinalityQueryPayload.certificate] at hsound
            have htarget : UnsatisfiableConceptWithCardinality
                cellCertificate.base.ontology definitions concept := by
              simpa only [DecodedCardinalityEqCertificate.SemanticallyValid, hevidence]
                using hsound
            have hontology : cellCertificate.base.ontology = ontology := by
              simpa only [DecodedEqCertificate.rootCertificate, hevidence] using
                decoded.sameOntology
            exact hontology ▸ htarget
          return .unsatisfiable (hconcept ▸ hproof)
        else throw "cardinality concept evidence is in the wrong matrix position"
    | .satisfiableConcept cellCertificate _ concept =>
        if hconcept : concept = expected then
          have hsound := certificate.check_sound hcheck
          have hproof : ¬UnsatisfiableConceptWithCardinality ontology definitions concept := by
            dsimp [certificate, DecodedCardinalityQueryPayload.certificate] at hsound
            have htarget : ¬UnsatisfiableConceptWithCardinality
                cellCertificate.base.ontology definitions concept := by
              simpa only [DecodedCardinalityEqCertificate.SemanticallyValid, hevidence]
                using hsound
            have hontology : cellCertificate.base.ontology = ontology := by
              simpa only [DecodedEqCertificate.rootCertificate, hevidence] using
                decoded.sameOntology
            exact hontology ▸ htarget
          return .satisfiable (hconcept ▸ hproof)
        else throw "cardinality concept evidence is in the wrong matrix position"
    | _ => throw "expected cardinality concept-status evidence"
  else throw "cardinality concept evidence was rejected"

private def decodeCardinalitySubsumption
    (payload : WireCardinalityQueryPayload)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (expectedSub expectedSup : Fin conceptCount) :
    Except String (CardinalitySubsumptionDecision ontology definitions expectedSub expectedSup) := do
  let decoded ← payload.decode ontology definitions
  let certificate := decoded.certificate
  if hcheck : certificate.check = true then
    match hevidence : decoded.evidence with
    | .subsumption cellCertificate _ sub sup _ =>
            if hsub : sub = expectedSub then
              if hsup : sup = expectedSup then
                have hsound := certificate.check_sound hcheck
                have hproof : EntailsSubWithCardinality ontology definitions sub sup := by
                  dsimp [certificate, DecodedCardinalityQueryPayload.certificate] at hsound
                  have htarget : EntailsSubWithCardinality
                      cellCertificate.base.ontology definitions sub sup := by
                    simpa only [DecodedCardinalityEqCertificate.SemanticallyValid, hevidence]
                      using hsound
                  have hontology : cellCertificate.base.ontology = ontology := by
                    simpa only [DecodedEqCertificate.rootCertificate, hevidence] using
                      decoded.sameOntology
                  exact hontology ▸ htarget
                return .entailed (hsup ▸ hsub ▸ hproof)
              else throw "cardinality subsumption evidence has the wrong superclass"
            else throw "cardinality subsumption evidence has the wrong subclass"
    | .nonSubsumption cellCertificate _ sub sup =>
            if hsub : sub = expectedSub then
              if hsup : sup = expectedSup then
                have hsound := certificate.check_sound hcheck
                have hproof : ¬EntailsSubWithCardinality ontology definitions sub sup := by
                  dsimp [certificate, DecodedCardinalityQueryPayload.certificate] at hsound
                  have htarget : ¬EntailsSubWithCardinality
                      cellCertificate.base.ontology definitions sub sup := by
                    simpa only [DecodedCardinalityEqCertificate.SemanticallyValid, hevidence]
                      using hsound
                  have hontology : cellCertificate.base.ontology = ontology := by
                    simpa only [DecodedEqCertificate.rootCertificate, hevidence] using
                      decoded.sameOntology
                  exact hontology ▸ htarget
                return .notEntailed (hsup ▸ hsub ▸ hproof)
              else throw "cardinality non-subsumption evidence has the wrong superclass"
            else throw "cardinality non-subsumption evidence has the wrong subclass"
    | _ => throw "expected cardinality subsumption evidence"
  else throw "cardinality subsumption evidence was rejected"

private def decodeCardinalityConceptEntries
    (wireOntology : List WireClause) (wireDefinitions : List WireCardinalityDef)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) :
    (named : List (Fin conceptCount)) → List WireCardinalityQueryPayload →
      Except String (Σ entries : List
        (SomeCardinalityConceptDecision ontology definitions),
        ∀ concept, concept ∈ named →
          { entry // entry ∈ entries ∧ entry.concept = concept })
  | [], [] => return ⟨[], by
      intro concept hmem
      exact False.elim (by simpa using hmem)⟩
  | concept :: concepts, payload :: payloads => do
      let decision ← decodeCardinalityConcept payload ontology definitions concept
      let tail ← decodeCardinalityConceptEntries wireOntology wireDefinitions
        ontology definitions concepts payloads
      let head : SomeCardinalityConceptDecision ontology definitions := ⟨concept, decision⟩
      return ⟨head :: tail.1, by
        intro candidate hcandidate
        if heq : candidate = concept then
          subst candidate
          exact ⟨head, by simp, rfl⟩
        else
          have htail := (List.mem_cons.mp hcandidate).resolve_left heq
          rcases tail.2 candidate htail with ⟨entry, hmem, hentry⟩
          exact ⟨entry, by simp [hmem], hentry⟩⟩
  | _, _ => throw "cardinality concept evidence count does not match named classes"

private def decodeCardinalitySubsumptionRow
    (wireOntology : List WireClause) (wireDefinitions : List WireCardinalityDef)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (sub : Fin conceptCount) :
    (supers : List (Fin conceptCount)) → List WireCardinalityQueryPayload →
      Except String (Σ entries : List
        (SomeCardinalitySubsumptionDecision ontology definitions),
        ∀ sup, sup ∈ supers →
          { entry // entry ∈ entries ∧ entry.sub = sub ∧ entry.sup = sup })
  | [], [] => return ⟨[], by
      intro sup hmem
      exact False.elim (by simpa using hmem)⟩
  | sup :: supers, payload :: payloads => do
      let decision ← decodeCardinalitySubsumption payload ontology definitions sub sup
      let tail ← decodeCardinalitySubsumptionRow wireOntology wireDefinitions
        ontology definitions sub supers payloads
      let head : SomeCardinalitySubsumptionDecision ontology definitions := ⟨sub, sup, decision⟩
      return ⟨head :: tail.1, by
        intro candidate hcandidate
        if heq : candidate = sup then
          subst candidate
          exact ⟨head, by simp, rfl, rfl⟩
        else
          have htail := (List.mem_cons.mp hcandidate).resolve_left heq
          rcases tail.2 candidate htail with ⟨entry, hmem, hsub, hsup⟩
          exact ⟨entry, by simp [hmem], hsub, hsup⟩⟩
  | _, _ => throw "cardinality subsumption row width does not match named classes"

private def decodeCardinalitySubsumptionEntries
    (wireOntology : List WireClause) (wireDefinitions : List WireCardinalityDef)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (allNamed : List (Fin conceptCount)) :
    (subs : List (Fin conceptCount)) → List (List WireCardinalityQueryPayload) →
      Except String (Σ entries : List
        (SomeCardinalitySubsumptionDecision ontology definitions),
        ∀ sub, sub ∈ subs → ∀ sup, sup ∈ allNamed →
          { entry // entry ∈ entries ∧ entry.sub = sub ∧ entry.sup = sup })
  | [], [] => return ⟨[], by
      intro sub hmem
      exact False.elim (by simpa using hmem)⟩
  | sub :: subs, row :: rows => do
      let head ← decodeCardinalitySubsumptionRow wireOntology wireDefinitions
        ontology definitions sub allNamed row
      let tail ← decodeCardinalitySubsumptionEntries wireOntology wireDefinitions
        ontology definitions allNamed subs rows
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
  | _, _ => throw "cardinality subsumption row count does not match named classes"

def WireCardinalityTaxonomyCertificate.decode
    (wire : WireCardinalityTaxonomyCertificate) :
    Except String DecodedCardinalityTaxonomyCertificate := do
  if wire.version != 5 then
    throw s!"unsupported cardinality taxonomy certificate version {wire.version}"
  let ontology ← wire.ontology.mapM
    (WireClause.decode wire.variable_count wire.concept_count wire.role_count)
  let definitions ← wire.definitions.mapM
    (WireCardinalityDef.decode wire.concept_count wire.role_count)
  let named ← wire.named.mapM (checkedFin "named concept" wire.concept_count)
  if hnodup : named.Nodup then
    let concepts ← decodeCardinalityConceptEntries wire.ontology wire.definitions
      ontology definitions named wire.concepts
    let subsumptions ← decodeCardinalitySubsumptionEntries wire.ontology wire.definitions
      ontology definitions named named wire.subsumptions
    return {
      conceptCount := wire.concept_count
      roleCount := wire.role_count
      variableCount := wire.variable_count
      ontology
      definitions
      named
      namedNodup := hnodup
      covered := {
        concepts := concepts.1
        subsumptions := subsumptions.1
        conceptCovered := concepts.2
        subsumptionCovered := subsumptions.2
      }
    }
  else throw "cardinality taxonomy named concepts contain duplicates"

def WireCardinalityTaxonomyCertificate.check
    (wire : WireCardinalityTaxonomyCertificate) : Bool := wire.decode.isOk

def DecodedCardinalityTaxonomyCertificate.semantic
    (decoded : DecodedCardinalityTaxonomyCertificate) :
    CompleteCardinalityTaxonomyCertificate decoded.ontology decoded.definitions decoded.named :=
  decoded.covered.sound

theorem DecodedCardinalityTaxonomyCertificate.check_sound
    (decoded : DecodedCardinalityTaxonomyCertificate) :
    ∃ certificate : CompleteCardinalityTaxonomyCertificate decoded.ontology
      decoded.definitions decoded.named, certificate = decoded.semantic :=
  ⟨decoded.semantic, rfl⟩

def CardinalityConceptDecision.transfer
    (equivalent : ModelEquivalent source target) :
    CardinalityConceptDecision target definitions concept →
      CardinalityConceptDecision source definitions concept
  | .unsatisfiable proof => .unsatisfiable (by
      intro Domain I hsource hdefinitions value hconcept
      exact proof Domain I ((equivalent Domain I).mp hsource)
        hdefinitions value hconcept)
  | .satisfiable counterexample => .satisfiable (by
      intro hsource
      apply counterexample
      intro Domain I htarget hdefinitions value hconcept
      exact hsource Domain I ((equivalent Domain I).mpr htarget)
        hdefinitions value hconcept)

def CardinalitySubsumptionDecision.transfer
    (equivalent : ModelEquivalent source target) :
    CardinalitySubsumptionDecision target definitions sub sup →
      CardinalitySubsumptionDecision source definitions sub sup
  | .entailed proof => .entailed (by
      intro Domain I hsource hdefinitions value hsub
      exact proof Domain I ((equivalent Domain I).mp hsource)
        hdefinitions value hsub)
  | .notEntailed counterexample => .notEntailed (by
      intro hsource
      apply counterexample
      intro Domain I htarget hdefinitions value hsub
      exact hsource Domain I ((equivalent Domain I).mpr htarget)
        hdefinitions value hsub)

def CompleteCardinalityTaxonomyCertificate.transfer
    (equivalent : ModelEquivalent source target)
    (certificate : CompleteCardinalityTaxonomyCertificate target definitions named) :
    CompleteCardinalityTaxonomyCertificate source definitions named where
  concept candidate hnamed :=
    (certificate.concept candidate hnamed).transfer equivalent
  subsumption sub hsub sup hsup :=
    (certificate.subsumption sub hsub sup hsup).transfer equivalent

structure WireNormalizedCardinalityTaxonomyCertificate where
  version : Nat
  normalization : List WireClauseNormalization
  preprocessing : Option WirePreprocessingEvidence := none
  certificate : WireCardinalityTaxonomyCertificate
deriving FromJson, ToJson, Repr

structure DecodedNormalizedCardinalityTaxonomyCertificate where
  target : DecodedCardinalityTaxonomyCertificate
  normalization : DecodedModelNormalization target.ontology

def WireNormalizedCardinalityTaxonomyCertificate.decode
    (wire : WireNormalizedCardinalityTaxonomyCertificate) :
    Except String DecodedNormalizedCardinalityTaxonomyCertificate := do
  if wire.version != 6 && wire.version != 7 then
    throw s!"unsupported normalized cardinality taxonomy version {wire.version}"
  let target ← wire.certificate.decode
  let normalization : DecodedModelNormalization target.ontology ←
    if wire.version = 6 then
      let decoded ← decodeOntologyNormalization target.variableCount
        target.conceptCount target.roleCount wire.normalization target.ontology
      pure ⟨decoded.source, fun _ I => decoded.proof.models_iff I⟩
    else
      match wire.preprocessing with
      | none => throw "version-4 cardinality taxonomy has no preprocessing evidence"
      | some preprocessing =>
          let decoded ← preprocessing.decode target.variableCount target.conceptCount
            target.roleCount wire.normalization target.ontology
          pure ⟨decoded.source, decoded.proof.modelEquivalent⟩
  return ⟨target, normalization⟩

def WireNormalizedCardinalityTaxonomyCertificate.check
    (wire : WireNormalizedCardinalityTaxonomyCertificate) : Bool := wire.decode.isOk

def DecodedNormalizedCardinalityTaxonomyCertificate.semantic
    (decoded : DecodedNormalizedCardinalityTaxonomyCertificate) :
    CompleteCardinalityTaxonomyCertificate decoded.normalization.source
      decoded.target.definitions decoded.target.named :=
  decoded.target.semantic.transfer decoded.normalization.equivalent

theorem DecodedNormalizedCardinalityTaxonomyCertificate.check_sound
    (decoded : DecodedNormalizedCardinalityTaxonomyCertificate) :
    ∃ certificate : CompleteCardinalityTaxonomyCertificate decoded.normalization.source
      decoded.target.definitions decoded.target.named,
      certificate = decoded.semantic := ⟨decoded.semantic, rfl⟩

#print axioms DecodedCardinalityTaxonomyCertificate.check_sound
#print axioms DecodedNormalizedCardinalityTaxonomyCertificate.check_sound

namespace CardinalityTaxonomyWireTests

private def targetClause : WireClause := {
  body := [.concept { concept := 0, neg := false } 0]
  head := [.concept { concept := 0, neg := false } 0]
}

private def modelState : WireEqState where
  labels := [{ node := 0, literal := { concept := 0, neg := false } }]
  edges := []
  obligations := []
  equalities := []
  representatives := [0]
  representative_paths := [[]]

private def clashState : WireEqState := {
  modelState with labels := [
    { node := 0, literal := { concept := 0, neg := false } },
    { node := 0, literal := { concept := 0, neg := true } }]
}

private def conceptPayload : WireCardinalityQueryPayload where
  node_count := 1
  state := modelState
  evidence := .satisfiable_concept 0 0

private def subsumptionPayload : WireCardinalityQueryPayload where
  node_count := 1
  state := clashState
  evidence := .subsumption 0 0 0 .clash
  distinct_refutation := some .clash

private def minimumZero : WireCardinalityDef := {
  marker := 0
  minimum := true
  bound := 0
  role := 0
  filler := 0
}

private def accepted : WireCardinalityTaxonomyCertificate where
  version := 5
  concept_count := 1
  role_count := 1
  variable_count := 2
  ontology := [targetClause]
  definitions := [minimumZero]
  named := [0]
  concepts := [conceptPayload]
  subsumptions := [[subsumptionPayload]]

example : accepted.check = true := by native_decide
example : ({ accepted with concepts := [] }).check = false := by native_decide
example : ({ accepted with subsumptions := [] }).check = false := by native_decide
example : ({ accepted with named := [0, 0] }).check = false := by native_decide
example : ({ accepted with concepts := [
    { conceptPayload with evidence := .satisfiable_concept 0 1 }] }).check = false := by
  native_decide
example : ({ accepted with definitions := [
    { minimumZero with bound := 1 }] }).check = false := by native_decide

private def sourceNormalization : WireClauseNormalization where
  source := {
    body := [
      .concept { concept := 0, neg := false } 0,
      .eq 0 1]
    head := [.concept { concept := 0, neg := false } 0]
  }
  representatives := [0, 0]
  representative_paths := [[0], [1, 0]]

private def normalized : WireNormalizedCardinalityTaxonomyCertificate where
  version := 6
  normalization := [sourceNormalization]
  certificate := accepted

example : normalized.check = true := by native_decide
example : ({ normalized with normalization := [] }).check = false := by native_decide

end CardinalityTaxonomyWireTests

end ContextCalculus.Hypertableau
