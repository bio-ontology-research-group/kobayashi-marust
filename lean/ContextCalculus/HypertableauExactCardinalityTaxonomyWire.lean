import ContextCalculus.HypertableauCardinalityTaxonomyWire
import ContextCalculus.HTDirectCardinalityCommonSourceWire

/-!
# Exact cardinality taxonomy wire

The legacy cardinality taxonomy semantics retained directional definitions but
erased the exact-recognition indices checked in every production cell.  This
module reconstructs each full cell document, checks those indices, and builds
a complete positive/negative taxonomy over directional plus exact semantics.
-/

namespace ContextCalculus.Hypertableau

open Lean
open ContextCalculus.HTDirectCommonSourceWire
open ContextCalculus.HTDirectCardinalityCommonSourceWire

theorem ModelEquivalent.entailsSubWithExactCardinality_iff
    {source target : List (Clause Variable Concept Role)}
    (equivalent : ModelEquivalent source target)
    (definitions exactDefinitions : List (CardinalityDef Concept Role))
    (sub sup : Concept) :
    EntailsSubWithExactCardinality source definitions exactDefinitions sub sup ↔
      EntailsSubWithExactCardinality target definitions exactDefinitions sub sup := by
  constructor
  · intro hsource Domain I htarget hdefinitions hexact value hsub
    exact hsource Domain I ((equivalent Domain I).mpr htarget)
      hdefinitions hexact value hsub
  · intro htarget Domain I hsource hdefinitions hexact value hsub
    exact htarget Domain I ((equivalent Domain I).mp hsource)
      hdefinitions hexact value hsub

theorem ModelEquivalent.unsatisfiableConceptWithExactCardinality_iff
    {source target : List (Clause Variable Concept Role)}
    (equivalent : ModelEquivalent source target)
    (definitions exactDefinitions : List (CardinalityDef Concept Role))
    (concept : Concept) :
    UnsatisfiableConceptWithExactCardinality source definitions exactDefinitions concept ↔
      UnsatisfiableConceptWithExactCardinality target definitions exactDefinitions concept := by
  constructor
  · intro hsource Domain I htarget hdefinitions hexact value hconcept
    exact hsource Domain I ((equivalent Domain I).mpr htarget)
      hdefinitions hexact value hconcept
  · intro htarget Domain I hsource hdefinitions hexact value hconcept
    exact htarget Domain I ((equivalent Domain I).mp hsource)
      hdefinitions hexact value hconcept

def WireCardinalityQueryPayload.exactDocument
    (payload : WireCardinalityQueryPayload)
    (conceptCount roleCount variableCount : Nat)
    (ontology : List WireClause) (definitions : List WireCardinalityDef)
    (exactMaximums exactDefinitions : List Nat) : WireCardinalityEqCertificate := {
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
  definitions
  exact_maximums := exactMaximums
  exact_definitions := exactDefinitions
  refutation_depth := payload.refutation_depth
  refutation := payload.refutation
  distinct_refutation_depth := payload.distinct_refutation_depth
  distinct_refutation := payload.distinct_refutation
}

inductive ExactCardinalityConceptDecision
    (ontology : List (Clause Variable Concept Role))
    (definitions exactDefinitions : List (CardinalityDef Concept Role))
    (concept : Concept) : Type where
  | unsatisfiable
      (proof : UnsatisfiableConceptWithExactCardinality ontology definitions
        exactDefinitions concept)
  | satisfiable
      (counterexample : ¬UnsatisfiableConceptWithExactCardinality ontology definitions
        exactDefinitions concept)

inductive ExactCardinalitySubsumptionDecision
    (ontology : List (Clause Variable Concept Role))
    (definitions exactDefinitions : List (CardinalityDef Concept Role))
    (sub sup : Concept) : Type where
  | entailed
      (proof : EntailsSubWithExactCardinality ontology definitions exactDefinitions sub sup)
  | notEntailed
      (counterexample : ¬EntailsSubWithExactCardinality ontology definitions
        exactDefinitions sub sup)

def ExactCardinalityConceptDecision.answer :
    ExactCardinalityConceptDecision ontology definitions exactDefinitions concept → Bool
  | .unsatisfiable _ => true
  | .satisfiable _ => false

def ExactCardinalitySubsumptionDecision.answer :
    ExactCardinalitySubsumptionDecision ontology definitions exactDefinitions sub sup → Bool
  | .entailed _ => true
  | .notEntailed _ => false

theorem ExactCardinalityConceptDecision.answer_eq_true_iff
    (decision : ExactCardinalityConceptDecision ontology definitions
      exactDefinitions concept) :
    decision.answer = true ↔
      UnsatisfiableConceptWithExactCardinality ontology definitions
        exactDefinitions concept := by
  cases decision <;> simp [ExactCardinalityConceptDecision.answer, *]

theorem ExactCardinalitySubsumptionDecision.answer_eq_true_iff
    (decision : ExactCardinalitySubsumptionDecision ontology definitions
      exactDefinitions sub sup) :
    decision.answer = true ↔
      EntailsSubWithExactCardinality ontology definitions exactDefinitions sub sup := by
  cases decision <;> simp [ExactCardinalitySubsumptionDecision.answer, *]

structure CompleteExactCardinalityTaxonomyCertificate
    (ontology : List (Clause Variable Concept Role))
    (definitions exactDefinitions : List (CardinalityDef Concept Role))
    (named : List Concept) where
  concept : ∀ candidate, candidate ∈ named →
    ExactCardinalityConceptDecision ontology definitions exactDefinitions candidate
  subsumption : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named →
    ExactCardinalitySubsumptionDecision ontology definitions exactDefinitions sub sup

-- Decode the shared exact-definition vectors through the same production
-- decoder used by each cell.  A tiny empty-evidence document is unnecessary:
-- the first checked cell below supplies the canonical decoded vectors, while
-- every other cell is required to equal them.
structure DecodedExactCardinalityCell where
  decoded : DecodedCardinalityEqCertificate
  accepted : decoded.check = true

def WireCardinalityQueryPayload.decodeExactCell
    (payload : WireCardinalityQueryPayload)
    (conceptCount roleCount variableCount : Nat)
    (ontology : List WireClause) (definitions : List WireCardinalityDef)
    (exactMaximums exactDefinitions : List Nat) :
    Except String DecodedExactCardinalityCell := do
  let decoded ← (payload.exactDocument conceptCount roleCount variableCount ontology
    definitions exactMaximums exactDefinitions).decode
  if hcheck : decoded.check = true then return ⟨decoded, hcheck⟩
  else throw "exact cardinality taxonomy cell was rejected"

def DecodedExactCardinalityCell.SubsumptionAt
    (cell : DecodedExactCardinalityCell) (expectedSub expectedSup : Nat) : Prop :=
  match cell.decoded.base.evidence with
  | .subsumption certificate _ sub sup _ =>
      sub.val = expectedSub ∧ sup.val = expectedSup ∧
        EntailsSubWithExactCardinality certificate.base.ontology
          cell.decoded.definitions cell.decoded.exactDefinitions sub sup
  | .nonSubsumption certificate _ sub sup =>
      sub.val = expectedSub ∧ sup.val = expectedSup ∧
        ¬EntailsSubWithExactCardinality certificate.base.ontology
          cell.decoded.definitions cell.decoded.exactDefinitions sub sup
  | _ => False

def DecodedExactCardinalityCell.ConceptAt
    (cell : DecodedExactCardinalityCell) (expected : Nat) : Prop :=
  match cell.decoded.base.evidence with
  | .unsatisfiableConcept certificate _ concept _ =>
      concept.val = expected ∧
        UnsatisfiableConceptWithExactCardinality certificate.base.ontology
          cell.decoded.definitions cell.decoded.exactDefinitions concept
  | .satisfiableConcept certificate _ concept =>
      concept.val = expected ∧
        ¬UnsatisfiableConceptWithExactCardinality certificate.base.ontology
          cell.decoded.definitions cell.decoded.exactDefinitions concept
  | _ => False

/-- Decode one matrix cell without transporting it across artificial `Fin`
count equalities.  Its own decoded finite vocabulary remains authoritative;
the matrix coordinate is checked at the stable natural-number boundary. -/
def decodeExactCardinalitySubsumptionAt
    (payload : WireCardinalityQueryPayload)
    (conceptCount roleCount variableCount : Nat)
    (wireOntology : List WireClause) (wireDefinitions : List WireCardinalityDef)
    (exactMaximums exactDefinitionIndices : List Nat)
    (expectedSub expectedSup : Nat) :
    Except String { cell : DecodedExactCardinalityCell //
      cell.SubsumptionAt expectedSub expectedSup } := do
  let cell ← payload.decodeExactCell conceptCount roleCount variableCount wireOntology
    wireDefinitions exactMaximums exactDefinitionIndices
  match hevidence : cell.decoded.base.evidence with
  | .subsumption _ _ sub sup _ =>
      if hsub : sub.val = expectedSub then
        if hsup : sup.val = expectedSup then
          have hsemantic := cell.decoded.check_exact_sound cell.accepted
          return ⟨cell, by
            simp only [DecodedExactCardinalityCell.SubsumptionAt, hevidence]
            exact ⟨hsub, hsup, by
              simpa only [DecodedCardinalityEqCertificate.ExactSemanticallyValid,
                hevidence] using hsemantic⟩⟩
        else throw "exact cardinality evidence has the wrong superclass"
      else throw "exact cardinality evidence has the wrong subclass"
  | .nonSubsumption _ _ sub sup =>
      if hsub : sub.val = expectedSub then
        if hsup : sup.val = expectedSup then
          have hsemantic := cell.decoded.check_exact_sound cell.accepted
          return ⟨cell, by
            simp only [DecodedExactCardinalityCell.SubsumptionAt, hevidence]
            exact ⟨hsub, hsup, by
              simpa only [DecodedCardinalityEqCertificate.ExactSemanticallyValid,
                hevidence] using hsemantic⟩⟩
        else throw "exact cardinality countermodel has the wrong superclass"
      else throw "exact cardinality countermodel has the wrong subclass"
  | _ => throw "expected exact cardinality subsumption evidence"

def decodeExactCardinalityConceptAt
    (payload : WireCardinalityQueryPayload)
    (conceptCount roleCount variableCount : Nat)
    (wireOntology : List WireClause) (wireDefinitions : List WireCardinalityDef)
    (exactMaximums exactDefinitionIndices : List Nat)
    (expected : Nat) :
    Except String { cell : DecodedExactCardinalityCell // cell.ConceptAt expected } := do
  let cell ← payload.decodeExactCell conceptCount roleCount variableCount wireOntology
    wireDefinitions exactMaximums exactDefinitionIndices
  match hevidence : cell.decoded.base.evidence with
  | .unsatisfiableConcept _ _ concept _ =>
      if hconcept : concept.val = expected then
        have hsemantic := cell.decoded.check_exact_sound cell.accepted
        return ⟨cell, by
          simp only [DecodedExactCardinalityCell.ConceptAt, hevidence]
          exact ⟨hconcept, by
            simpa only [DecodedCardinalityEqCertificate.ExactSemanticallyValid,
              hevidence] using hsemantic⟩⟩
      else throw "exact cardinality concept evidence is in the wrong matrix position"
  | .satisfiableConcept _ _ concept =>
      if hconcept : concept.val = expected then
        have hsemantic := cell.decoded.check_exact_sound cell.accepted
        return ⟨cell, by
          simp only [DecodedExactCardinalityCell.ConceptAt, hevidence]
          exact ⟨hconcept, by
            simpa only [DecodedCardinalityEqCertificate.ExactSemanticallyValid,
              hevidence] using hsemantic⟩⟩
      else throw "exact cardinality concept countermodel is in the wrong matrix position"
  | _ => throw "expected exact cardinality concept-status evidence"

structure ExactCardinalityConceptEntry where
  coordinate : Nat
  cell : DecodedExactCardinalityCell
  valid : cell.ConceptAt coordinate

structure ExactCardinalitySubsumptionEntry where
  sub : Nat
  sup : Nat
  cell : DecodedExactCardinalityCell
  valid : cell.SubsumptionAt sub sup

def DecodedExactCardinalityCell.natOntology (cell : DecodedExactCardinalityCell) :=
  mapOntology cell.decoded.base.rootCertificate.base.ontology

def DecodedExactCardinalityCell.natDefinitions (cell : DecodedExactCardinalityCell) :=
  cell.decoded.definitions.map mapCardinalityDef

def DecodedExactCardinalityCell.natExactDefinitions
    (cell : DecodedExactCardinalityCell) :=
  cell.decoded.exactDefinitions.map mapCardinalityDef

def ExactCardinalitySubsumptionEntry.natDecision
    (entry : ExactCardinalitySubsumptionEntry) :
    ExactCardinalitySubsumptionDecision entry.cell.natOntology
      entry.cell.natDefinitions entry.cell.natExactDefinitions entry.sub entry.sup := by
  cases hevidence : entry.cell.decoded.base.evidence with
  | subsumption certificate root sub sup tree =>
      have hvalid := entry.valid
      simp only [DecodedExactCardinalityCell.SubsumptionAt, hevidence] at hvalid
      rcases hvalid with ⟨hsub, hsup, hproof⟩
      apply ExactCardinalitySubsumptionDecision.entailed
      have hmapped := (entailsWithExact_mapOntology_iff certificate.base.ontology
        entry.cell.decoded.definitions entry.cell.decoded.exactDefinitions sub sup).1 hproof
      simpa [DecodedExactCardinalityCell.natOntology,
        DecodedExactCardinalityCell.natDefinitions,
        DecodedExactCardinalityCell.natExactDefinitions,
        DecodedEqCertificate.rootCertificate, hevidence, hsub, hsup] using hmapped
  | nonSubsumption certificate root sub sup =>
      have hvalid := entry.valid
      simp only [DecodedExactCardinalityCell.SubsumptionAt, hevidence] at hvalid
      rcases hvalid with ⟨hsub, hsup, hproof⟩
      apply ExactCardinalitySubsumptionDecision.notEntailed
      intro hmapped
      apply hproof
      apply (entailsWithExact_mapOntology_iff certificate.base.ontology
        entry.cell.decoded.definitions entry.cell.decoded.exactDefinitions sub sup).2
      simpa [DecodedExactCardinalityCell.natOntology,
        DecodedExactCardinalityCell.natDefinitions,
        DecodedExactCardinalityCell.natExactDefinitions,
        DecodedEqCertificate.rootCertificate, hevidence, hsub, hsup] using hmapped
  | _ =>
      have hvalid := entry.valid
      simp [DecodedExactCardinalityCell.SubsumptionAt, hevidence] at hvalid

def ExactCardinalityConceptEntry.natDecision
    (entry : ExactCardinalityConceptEntry) :
    ExactCardinalityConceptDecision entry.cell.natOntology
      entry.cell.natDefinitions entry.cell.natExactDefinitions entry.coordinate := by
  cases hevidence : entry.cell.decoded.base.evidence with
  | unsatisfiableConcept certificate root concept tree =>
      have hvalid := entry.valid
      simp only [DecodedExactCardinalityCell.ConceptAt, hevidence] at hvalid
      rcases hvalid with ⟨hconcept, hproof⟩
      apply ExactCardinalityConceptDecision.unsatisfiable
      have hmapped := (unsatisfiableWithExact_mapOntology_iff certificate.base.ontology
        entry.cell.decoded.definitions entry.cell.decoded.exactDefinitions concept).1 hproof
      simpa [DecodedExactCardinalityCell.natOntology,
        DecodedExactCardinalityCell.natDefinitions,
        DecodedExactCardinalityCell.natExactDefinitions,
        DecodedEqCertificate.rootCertificate, hevidence, hconcept] using hmapped
  | satisfiableConcept certificate root concept =>
      have hvalid := entry.valid
      simp only [DecodedExactCardinalityCell.ConceptAt, hevidence] at hvalid
      rcases hvalid with ⟨hconcept, hproof⟩
      apply ExactCardinalityConceptDecision.satisfiable
      intro hmapped
      apply hproof
      apply (unsatisfiableWithExact_mapOntology_iff certificate.base.ontology
        entry.cell.decoded.definitions entry.cell.decoded.exactDefinitions concept).2
      simpa [DecodedExactCardinalityCell.natOntology,
        DecodedExactCardinalityCell.natDefinitions,
        DecodedExactCardinalityCell.natExactDefinitions,
        DecodedEqCertificate.rootCertificate, hevidence, hconcept] using hmapped
  | _ =>
      have hvalid := entry.valid
      simp [DecodedExactCardinalityCell.ConceptAt, hevidence] at hvalid

structure CoveredExactCardinalityTaxonomyCertificate (named : List Nat) where
  concepts : List ExactCardinalityConceptEntry
  subsumptions : List ExactCardinalitySubsumptionEntry
  conceptCovered : ∀ concept, concept ∈ named →
    { entry // entry ∈ concepts ∧ entry.coordinate = concept }
  subsumptionCovered : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named →
    { entry // entry ∈ subsumptions ∧ entry.sub = sub ∧ entry.sup = sup }

private def decodeExactCardinalityConceptEntries
    (conceptCount roleCount variableCount : Nat)
    (wireOntology : List WireClause) (wireDefinitions : List WireCardinalityDef)
    (exactMaximums exactDefinitions : List Nat) :
    (named : List Nat) → List WireCardinalityQueryPayload →
      Except String (Σ entries : List ExactCardinalityConceptEntry,
        ∀ concept, concept ∈ named →
          { entry // entry ∈ entries ∧ entry.coordinate = concept })
  | [], [] => return ⟨[], by intro concept hmem; simp at hmem⟩
  | concept :: named, payload :: payloads => do
      let checked ← decodeExactCardinalityConceptAt payload conceptCount roleCount variableCount
        wireOntology wireDefinitions exactMaximums exactDefinitions concept
      let tail ← decodeExactCardinalityConceptEntries conceptCount roleCount variableCount
        wireOntology wireDefinitions exactMaximums exactDefinitions named payloads
      let head : ExactCardinalityConceptEntry := ⟨concept, checked.val, checked.property⟩
      return ⟨head :: tail.1, by
        intro candidate hcandidate
        if heq : candidate = concept then
          subst candidate
          exact ⟨head, by simp, rfl⟩
        else
          have htail := (List.mem_cons.mp hcandidate).resolve_left heq
          rcases tail.2 candidate htail with ⟨entry, hmem, hcoordinate⟩
          exact ⟨entry, by simp [hmem], hcoordinate⟩⟩
  | _, _ => throw "exact cardinality concept evidence count does not match named classes"

private def decodeExactCardinalitySubsumptionRow
    (conceptCount roleCount variableCount : Nat)
    (wireOntology : List WireClause) (wireDefinitions : List WireCardinalityDef)
    (exactMaximums exactDefinitions : List Nat) (sub : Nat) :
    (supers : List Nat) → List WireCardinalityQueryPayload →
      Except String (Σ entries : List ExactCardinalitySubsumptionEntry,
        ∀ sup, sup ∈ supers →
          { entry // entry ∈ entries ∧ entry.sub = sub ∧ entry.sup = sup })
  | [], [] => return ⟨[], by intro sup hmem; simp at hmem⟩
  | sup :: supers, payload :: payloads => do
      let checked ← decodeExactCardinalitySubsumptionAt payload conceptCount roleCount
        variableCount wireOntology wireDefinitions exactMaximums exactDefinitions sub sup
      let tail ← decodeExactCardinalitySubsumptionRow conceptCount roleCount variableCount
        wireOntology wireDefinitions exactMaximums exactDefinitions sub supers payloads
      let head : ExactCardinalitySubsumptionEntry := ⟨sub, sup, checked.val, checked.property⟩
      return ⟨head :: tail.1, by
        intro candidate hcandidate
        if heq : candidate = sup then
          subst candidate
          exact ⟨head, by simp, rfl, rfl⟩
        else
          have htail := (List.mem_cons.mp hcandidate).resolve_left heq
          rcases tail.2 candidate htail with ⟨entry, hmem, hsub, hsup⟩
          exact ⟨entry, by simp [hmem], hsub, hsup⟩⟩
  | _, _ => throw "exact cardinality subsumption row width does not match named classes"

private def decodeExactCardinalitySubsumptionEntries
    (conceptCount roleCount variableCount : Nat)
    (wireOntology : List WireClause) (wireDefinitions : List WireCardinalityDef)
    (exactMaximums exactDefinitions allNamed : List Nat) :
    (subs : List Nat) → List (List WireCardinalityQueryPayload) →
      Except String (Σ entries : List ExactCardinalitySubsumptionEntry,
        ∀ sub, sub ∈ subs → ∀ sup, sup ∈ allNamed →
          { entry // entry ∈ entries ∧ entry.sub = sub ∧ entry.sup = sup })
  | [], [] => return ⟨[], by intro sub hmem; simp at hmem⟩
  | sub :: subs, row :: rows => do
      let head ← decodeExactCardinalitySubsumptionRow conceptCount roleCount variableCount
        wireOntology wireDefinitions exactMaximums exactDefinitions sub allNamed row
      let tail ← decodeExactCardinalitySubsumptionEntries conceptCount roleCount variableCount
        wireOntology wireDefinitions exactMaximums exactDefinitions allNamed subs rows
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
  | _, _ => throw "exact cardinality subsumption row count does not match named classes"

structure DecodedExactCardinalityTaxonomyCertificate where
  baseline : DecodedCardinalityTaxonomyCertificate
  exactDefinitions : List (CardinalityDef (Fin baseline.conceptCount)
    (Fin baseline.roleCount))
  namedNats : List Nat
  covered : CoveredExactCardinalityTaxonomyCertificate namedNats

def WireCardinalityTaxonomyCertificate.decodeExact
    (wire : WireCardinalityTaxonomyCertificate) :
    Except String DecodedExactCardinalityTaxonomyCertificate := do
  /- The baseline decoder validates the version, common ontology and
  directional definitions, finite bounds, duplicate-free names, and complete
  matrix shape.  The second pass strengthens every cell to exact semantics. -/
  let baseline ← wire.decode
  let exactDefinitions ← wire.exact_definitions.mapM fun index =>
    match baseline.definitions[index]? with
    | none => throw s!"exact cardinality definition index {index} is out of range"
    | some definition => pure definition
  let exactMaximums : List { definition : CardinalityDef
      (Fin baseline.conceptCount) (Fin baseline.roleCount) //
      definition.kind = CardinalityKind.maximum } ←
    wire.exact_maximums.mapM fun index =>
    match baseline.definitions[index]? with
    | none => throw s!"exact maximum definition index {index} is out of range"
    | some definition =>
        if hkind : definition.kind = CardinalityKind.maximum then pure ⟨definition, hkind⟩
        else throw s!"exact maximum definition index {index} names a minimum definition"
  let concepts ← decodeExactCardinalityConceptEntries wire.concept_count wire.role_count
    wire.variable_count wire.ontology wire.definitions wire.exact_maximums
    wire.exact_definitions wire.named wire.concepts
  let subsumptions ← decodeExactCardinalitySubsumptionEntries wire.concept_count
    wire.role_count wire.variable_count wire.ontology wire.definitions wire.exact_maximums
    wire.exact_definitions wire.named wire.named wire.subsumptions
  return {
    baseline
    exactDefinitions := exactDefinitions ++ exactMaximums.map (·.1)
    namedNats := wire.named
    covered := {
      concepts := concepts.1
      subsumptions := subsumptions.1
      conceptCovered := concepts.2
      subsumptionCovered := subsumptions.2
    }
  }

#print axioms DecodedCardinalityEqCertificate.check_exact_sound

end ContextCalculus.Hypertableau
