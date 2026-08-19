import ContextCalculus.HypertableauCardinalityCertificate
import ContextCalculus.HypertableauEqualityWire
import Lean

/-!
# Wire certificates for first-class hypertableau cardinality

This layer currently accepts positive model evidence: SAT, non-subsumption, and
satisfiable-concept certificates. Cardinality-driven refutations need explicit
minimum-witness and maximum-merge proof-tree nodes and remain fail closed.
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
deriving FromJson, ToJson, Repr

structure DecodedCardinalityEqCertificate where
  base : DecodedEqCertificate
  definitions : List
    (CardinalityDef (Fin base.conceptCount) (Fin base.roleCount))

def WireCardinalityEqCertificate.decode (wire : WireCardinalityEqCertificate) :
    Except String DecodedCardinalityEqCertificate := do
  if wire.version != 1 then
    throw s!"unsupported cardinality hypertableau certificate version {wire.version}"
  let base ← wire.certificate.decode
  let definitions ← wire.definitions.mapM
    (WireCardinalityDef.decode base.conceptCount base.roleCount)
  return ⟨base, definitions⟩

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
  | .unsat .. | .subsumption .. | .unsatisfiableConcept .. => false

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
  | .unsat .. | .subsumption .. | .unsatisfiableConcept .. => False

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
  | unsat certificate tree => simp [DecodedCardinalityEqCertificate.check, hevidence] at hcheck
  | subsumption certificate root sub sup tree =>
      simp [DecodedCardinalityEqCertificate.check, hevidence] at hcheck
  | unsatisfiableConcept certificate root concept tree =>
      simp [DecodedCardinalityEqCertificate.check, hevidence] at hcheck

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

end CardinalityWireTests

#print axioms DecodedCardinalityEqCertificate.check_sound

end ContextCalculus.Hypertableau
