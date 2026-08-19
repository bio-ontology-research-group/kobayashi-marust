import ContextCalculus.HypertableauCardinalityCertificate
import ContextCalculus.HypertableauCardinalityRefutationWire
import Lean

/-!
# Wire certificates for first-class hypertableau cardinality

Positive evidence checks the exact quotient model. Refutational evidence checks
an explicit depth-indexed tree whose maximum nodes close every possible merge.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireCardinalityDef where
  marker : Nat
  minimum : Bool
  bound : Nat
  role : Nat
  filler : Nat
deriving FromJson, ToJson, Repr

def WireCardinalityDef.decode
    (conceptCount roleCount : Nat) (wire : WireCardinalityDef) : Except String
      (CardinalityDef (Fin conceptCount) (Fin roleCount)) := do
  return {
    marker := ← checkedFin "cardinality marker" conceptCount wire.marker
    kind := if wire.minimum then .minimum else .maximum
    bound := wire.bound
    role := ← checkedFin "cardinality role" roleCount wire.role
    filler := ← checkedFin "cardinality filler" conceptCount wire.filler
  }

structure WireCardinalityEqCertificate where
  version : Nat
  certificate : WireEqCertificate
  definitions : List WireCardinalityDef
  refutation_depth : Nat := 0
  refutation : Option WireCardinalityEqRefutationTree := none
deriving FromJson, ToJson, Repr

def DecodedEqCertificate.rootCertificate (decoded : DecodedEqCertificate) :
    FiniteEqCertificate decoded.nodeCount decoded.conceptCount decoded.roleCount
      decoded.variableCount :=
  match decoded.evidence with
  | .sat certificate | .unsat certificate _ | .subsumption certificate .. |
      .unsatisfiableConcept certificate .. | .nonSubsumption certificate .. |
      .satisfiableConcept certificate .. => certificate

structure DecodedCardinalityEqCertificate where
  base : DecodedEqCertificate
  definitions : List
    (CardinalityDef (Fin base.conceptCount) (Fin base.roleCount))
  refutation : Option (DecodedCardinalityEqRefutation base.nodeCount base.conceptCount
    base.roleCount base.variableCount)

def WireCardinalityEqCertificate.decode (wire : WireCardinalityEqCertificate) :
    Except String DecodedCardinalityEqCertificate := do
  if wire.version != 1 && wire.version != 2 then
    throw s!"unsupported cardinality hypertableau certificate version {wire.version}"
  let base ← wire.certificate.decode
  let definitions ← wire.definitions.mapM
    (WireCardinalityDef.decode base.conceptCount base.roleCount)
  let refutation : Option (DecodedCardinalityEqRefutation base.nodeCount
      base.conceptCount base.roleCount base.variableCount) ← match wire.refutation with
    | none => pure none
    | some tree => do
        let certificate := base.rootCertificate
        let decoded ← tree.decode base.nodeCount base.conceptCount base.roleCount
          base.variableCount wire.refutation_depth certificate.base.ontology definitions
        pure (some decoded)
  return ⟨base, definitions, refutation⟩

def DecodedCardinalityEqCertificate.check
    (decoded : DecodedCardinalityEqCertificate) : Bool :=
  match decoded.base.evidence with
  | .sat certificate =>
      decide (0 < decoded.base.nodeCount) &&
        certificate.checkEqSatWithCardinality decoded.definitions
  | .nonSubsumption certificate root sub sup =>
      decide ((root, .pos sub) ∈ certificate.base.labels) &&
      decide ((root, .negated sup) ∈ certificate.base.labels) &&
        certificate.checkEqSatWithCardinality decoded.definitions
  | .satisfiableConcept certificate root concept =>
      decide ((root, .pos concept) ∈ certificate.base.labels) &&
        certificate.checkEqSatWithCardinality decoded.definitions
  | .unsat certificate _ =>
      match decoded.refutation with
      | none => false
      | some refutation =>
          decide (0 < decoded.base.nodeCount) &&
          certificate.base.labels.isEmpty && certificate.base.edges.isEmpty &&
          certificate.base.obligations.isEmpty &&
          refutation.tree.check decoded.definitions certificate
  | .subsumption certificate root sub sup _ =>
      match decoded.refutation with
      | none => false
      | some refutation =>
          certificate.checkSubsumptionRoot root sub sup &&
          refutation.tree.check decoded.definitions certificate
  | .unsatisfiableConcept certificate root concept _ =>
      match decoded.refutation with
      | none => false
      | some refutation =>
          certificate.checkUnsatisfiableRoot root concept &&
          refutation.tree.check decoded.definitions certificate

def WireCardinalityEqCertificate.check (wire : WireCardinalityEqCertificate) :
    Except String Bool := do
  return (← wire.decode).check

def DecodedCardinalityEqCertificate.SemanticallyValid
    (decoded : DecodedCardinalityEqCertificate) : Prop :=
  match decoded.base.evidence with
  | .sat certificate =>
      ∃ (Domain : Type) (I : Interp Domain (Fin decoded.base.conceptCount)
          (Fin decoded.base.roleCount)), Nonempty Domain ∧
        I.models certificate.base.ontology ∧
        I.modelsCardinalityDefs decoded.definitions
  | .nonSubsumption certificate _ sub sup =>
      ¬EntailsSubWithCardinality certificate.base.ontology decoded.definitions sub sup
  | .satisfiableConcept certificate _ concept =>
      ¬UnsatisfiableConceptWithCardinality certificate.base.ontology
        decoded.definitions concept
  | .unsat certificate _ =>
      ¬∃ (Domain : Type) (I : Interp Domain (Fin decoded.base.conceptCount)
          (Fin decoded.base.roleCount)), Nonempty Domain ∧
        I.models certificate.base.ontology ∧ I.modelsCardinalityDefs decoded.definitions
  | .subsumption certificate _ sub sup _ =>
      EntailsSubWithCardinality certificate.base.ontology decoded.definitions sub sup
  | .unsatisfiableConcept certificate _ concept _ =>
      UnsatisfiableConceptWithCardinality certificate.base.ontology
        decoded.definitions concept

theorem DecodedCardinalityEqCertificate.check_sound
    (decoded : DecodedCardinalityEqCertificate)
    (hcheck : decoded.check = true) : decoded.SemanticallyValid := by
  cases hevidence : decoded.base.evidence with
  | sat certificate =>
      simp only [DecodedCardinalityEqCertificate.check, hevidence,
        Bool.and_eq_true, decide_eq_true_eq] at hcheck
      simp only [DecodedCardinalityEqCertificate.SemanticallyValid, hevidence]
      haveI : Nonempty (Fin decoded.base.nodeCount) := ⟨⟨0, hcheck.1⟩⟩
      have hmodels := certificate.checkEqSatWithCardinality_models
        decoded.definitions hcheck.2
      exact ⟨certificate.state.QuotientDomain, certificate.state.quotientCanonical,
        ⟨Quotient.mk certificate.state.nodeSetoid (Classical.choice inferInstance)⟩,
        hmodels⟩
  | nonSubsumption certificate root sub sup =>
      simp only [DecodedCardinalityEqCertificate.check, hevidence,
        Bool.and_eq_true, decide_eq_true_eq] at hcheck
      simp only [DecodedCardinalityEqCertificate.SemanticallyValid, hevidence]
      exact certificate.checkEqSatWithCardinality_not_entailsSub decoded.definitions
        root sub sup hcheck.1.1 hcheck.1.2 hcheck.2
  | satisfiableConcept certificate root concept =>
      simp only [DecodedCardinalityEqCertificate.check, hevidence,
        Bool.and_eq_true, decide_eq_true_eq] at hcheck
      simp only [DecodedCardinalityEqCertificate.SemanticallyValid, hevidence]
      exact certificate.checkEqSatWithCardinality_not_unsatisfiableConcept
        decoded.definitions root concept hcheck.1 hcheck.2
  | unsat certificate tree =>
      cases hrefutation : decoded.refutation with
      | none => simp [DecodedCardinalityEqCertificate.check, hevidence, hrefutation] at hcheck
      | some refutation =>
          simp only [DecodedCardinalityEqCertificate.check, hevidence, hrefutation,
            Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hcheck
          rcases hcheck with
            ⟨⟨⟨⟨hpositive, hlabels⟩, hedges⟩, hobligations⟩, htree⟩
          haveI : Nonempty (Fin decoded.base.nodeCount) := ⟨⟨0, hpositive⟩⟩
          simp only [DecodedCardinalityEqCertificate.SemanticallyValid, hevidence]
          exact refutation.tree.check_ontology_unsatisfiable decoded.definitions certificate
            ⟨hlabels, hedges, hobligations⟩ htree
  | subsumption certificate root sub sup tree =>
      cases hrefutation : decoded.refutation with
      | none => simp [DecodedCardinalityEqCertificate.check, hevidence, hrefutation] at hcheck
      | some refutation =>
          simp only [DecodedCardinalityEqCertificate.check, hevidence, hrefutation,
            Bool.and_eq_true] at hcheck
          simp only [DecodedCardinalityEqCertificate.SemanticallyValid, hevidence]
          exact refutation.tree.check_subsumption decoded.definitions certificate root sub sup
            (certificate.checkSubsumptionRoot_sound root sub sup hcheck.1) hcheck.2
  | unsatisfiableConcept certificate root concept tree =>
      cases hrefutation : decoded.refutation with
      | none => simp [DecodedCardinalityEqCertificate.check, hevidence, hrefutation] at hcheck
      | some refutation =>
          simp only [DecodedCardinalityEqCertificate.check, hevidence, hrefutation,
            Bool.and_eq_true] at hcheck
          simp only [DecodedCardinalityEqCertificate.SemanticallyValid, hevidence]
          exact refutation.tree.check_unsatisfiable_concept decoded.definitions certificate
            root concept (certificate.checkUnsatisfiableRoot_sound root concept hcheck.1) hcheck.2

namespace CardinalityWireTests

private def state : WireEqState where
  labels := [
    { node := 0, literal := { concept := 0, neg := false } },
    { node := 1, literal := { concept := 1, neg := false } },
    { node := 2, literal := { concept := 1, neg := false } }
  ]
  edges := [
    { role := 0, source := 0, target := 1 },
    { role := 0, source := 0, target := 2 }
  ]
  obligations := []
  equalities := []
  representatives := [0, 1, 2]
  representative_paths := [[], [], []]

private def sat : WireEqCertificate where
  version := 2
  node_count := 3
  concept_count := 2
  role_count := 1
  variable_count := 0
  ontology := []
  state := state
  evidence := .sat

private def minimumTwo : WireCardinalityDef :=
  { marker := 0, minimum := true, bound := 2, role := 0, filler := 1 }

private def accepted : WireCardinalityEqCertificate :=
  { version := 1, certificate := sat, definitions := [minimumTwo] }

private def isError {ε α : Type} : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

example : accepted.check = .ok true := by native_decide
example : isError ({ accepted with
    definitions := [{ minimumTwo with marker := 2 }] }).check = true := by
  native_decide
example : ({ accepted with definitions := [{ minimumTwo with bound := 3 }] }).check = .ok false := by
  native_decide

private def maximumZeroClause : WireClause :=
  { body := [.concept { concept := 0, neg := false } 0], head := [.role 0 0 0] }

private def maximumZeroRoot : WireEqState where
  labels := [{ node := 0, literal := { concept := 0, neg := false } }]
  edges := []
  obligations := []
  equalities := []
  representatives := [0]
  representative_paths := [[]]

private def maximumZeroActive : WireEqState :=
  { maximumZeroRoot with edges := [{ role := 0, source := 0, target := 0 }] }

private def maximumZeroBase : WireEqCertificate where
  version := 2
  node_count := 1
  concept_count := 1
  role_count := 1
  variable_count := 1
  ontology := [maximumZeroClause]
  state := maximumZeroRoot
  evidence := .unsatisfiable_concept 0 0 .clash

private def maximumZero : WireCardinalityDef :=
  { marker := 0, minimum := false, bound := 0, role := 0, filler := 0 }

private def maximumZeroRefutation : WireCardinalityEqRefutationTree :=
  .branch 0 [0] [(maximumZeroActive,
    .maximum 0 0 [0] [[(maximumZeroActive, .clash)]])]

private def acceptedMaximumZero : WireCardinalityEqCertificate where
  version := 2
  certificate := maximumZeroBase
  definitions := [maximumZero]
  refutation_depth := 2
  refutation := some maximumZeroRefutation

example : acceptedMaximumZero.check = .ok true := by native_decide

private def missingMaximumChildTree : WireCardinalityEqRefutationTree :=
  .branch 0 [0] [(maximumZeroActive, .maximum 0 0 [0] [])]

private def missingMaximumChild : WireCardinalityEqCertificate :=
  { acceptedMaximumZero with refutation := some missingMaximumChildTree }

example : isError missingMaximumChild.check = true := by native_decide

end CardinalityWireTests

#print axioms DecodedCardinalityEqCertificate.check_sound

end ContextCalculus.Hypertableau
