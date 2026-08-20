import ContextCalculus.HypertableauCardinalitySearch
import ContextCalculus.HypertableauCardinalityWire

/-!
# Version-2 cardinality document outcome correspondence

The Rust cardinality producer emits global SAT documents without refutations
and global UNSAT documents with exactly one distinct-cardinality refutation.
This module states that shape independently of the untrusted outcome tag and
proves that every accepted document of that shape constructs the corresponding
checked bounded-search outcome.
-/

namespace ContextCalculus.Hypertableau

def DecodedCardinalityEqCertificate.ProductionGlobalShape
    (decoded : DecodedCardinalityEqCertificate) : Prop :=
  match decoded.base.evidence with
  | .sat _ => decoded.refutation = none ∧ decoded.distinctRefutation = none
  | .unsat _ _ => decoded.refutation = none ∧
      ∃ refutation, decoded.distinctRefutation = some refutation
  | _ => False

def DecodedCardinalityEqCertificate.productionGlobalShapeB
    (decoded : DecodedCardinalityEqCertificate) : Bool :=
  match decoded.base.evidence with
  | .sat _ => decoded.refutation.isNone && decoded.distinctRefutation.isNone
  | .unsat _ _ => decoded.refutation.isNone && decoded.distinctRefutation.isSome
  | _ => false

theorem DecodedCardinalityEqCertificate.productionGlobalShapeB_eq_true_iff
    (decoded : DecodedCardinalityEqCertificate) :
    decoded.productionGlobalShapeB = true ↔ decoded.ProductionGlobalShape := by
  cases hevidence : decoded.base.evidence <;>
    simp [DecodedCardinalityEqCertificate.productionGlobalShapeB,
      DecodedCardinalityEqCertificate.ProductionGlobalShape, hevidence,
      Option.isNone_iff_eq_none, Option.isSome_iff_exists]

/-- Executable checker for exactly the global document shape emitted by the
production cardinality decision path. -/
def WireCardinalityEqCertificate.checkProductionGlobal
    (wire : WireCardinalityEqCertificate) : Except String Bool := do
  let decoded ← wire.decode
  return decoded.productionGlobalShapeB && decoded.check

/-- An accepted decoded production-global cardinality document is exactly a
checked SAT or checked closed outcome, never a frontier. -/
theorem DecodedCardinalityEqCertificate.exists_checked_global_outcome
    (decoded : DecodedCardinalityEqCertificate)
    (hshape : decoded.ProductionGlobalShape)
    (hcheck : decoded.check = true) :
    ∃ outcome : CheckedCardinalityDecisionOutcome
        decoded.base.conceptCount decoded.base.roleCount decoded.base.variableCount
        decoded.base.rootCertificate.base.ontology decoded.definitions,
      outcome.Semantics := by
  cases hevidence : decoded.base.evidence with
  | sat certificate =>
      simp only [DecodedCardinalityEqCertificate.ProductionGlobalShape, hevidence] at hshape
      simp only [DecodedCardinalityEqCertificate.check, hevidence, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      let outcome : CheckedCardinalityDecisionOutcome
          decoded.base.conceptCount decoded.base.roleCount decoded.base.variableCount
          certificate.base.ontology decoded.definitions :=
        .sat certificate rfl hcheck.1 hcheck.2
      have hex : ∃ outcome : CheckedCardinalityDecisionOutcome
          decoded.base.conceptCount decoded.base.roleCount decoded.base.variableCount
          certificate.base.ontology decoded.definitions, outcome.Semantics :=
        ⟨outcome, CheckedCardinalityDecisionOutcome.sat_semantics
          certificate rfl hcheck.1 hcheck.2⟩
      have hroot : decoded.base.rootCertificate = certificate := by
        unfold DecodedEqCertificate.rootCertificate
        rw [hevidence]
      rw [hroot]
      exact hex
  | unsat certificate ignoredTree =>
      simp only [DecodedCardinalityEqCertificate.ProductionGlobalShape, hevidence] at hshape
      rcases hshape.2 with ⟨refutation, hrefutation⟩
      simp only [DecodedCardinalityEqCertificate.check, hevidence, hrefutation,
        Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hcheck
      rcases hcheck with
        ⟨⟨⟨⟨hpositive, hlabels⟩, hedges⟩, hobligations⟩, htree⟩
      let root : FiniteDistinctEqCertificate decoded.base.nodeCount
          decoded.base.conceptCount decoded.base.roleCount decoded.base.variableCount :=
        { base := certificate, apart := [] }
      have hempty : certificate.EmptyRoot := ⟨hlabels, hedges, hobligations⟩
      let outcome : CheckedCardinalityDecisionOutcome
          decoded.base.conceptCount decoded.base.roleCount decoded.base.variableCount
          certificate.base.ontology decoded.definitions :=
        .closed root refutation.tree rfl hpositive hempty rfl htree
      have hex : ∃ outcome : CheckedCardinalityDecisionOutcome
          decoded.base.conceptCount decoded.base.roleCount decoded.base.variableCount
          certificate.base.ontology decoded.definitions, outcome.Semantics :=
        ⟨outcome, CheckedCardinalityDecisionOutcome.closed_semantics
          root refutation.tree rfl hpositive hempty rfl htree⟩
      have hroot : decoded.base.rootCertificate = certificate := by
        unfold DecodedEqCertificate.rootCertificate
        rw [hevidence]
      rw [hroot]
      exact hex
  | subsumption certificate root sub sup tree =>
      simp [DecodedCardinalityEqCertificate.ProductionGlobalShape, hevidence] at hshape
  | unsatisfiableConcept certificate root concept tree =>
      simp [DecodedCardinalityEqCertificate.ProductionGlobalShape, hevidence] at hshape
  | nonSubsumption certificate root sub sup =>
      simp [DecodedCardinalityEqCertificate.ProductionGlobalShape, hevidence] at hshape
  | satisfiableConcept certificate root concept =>
      simp [DecodedCardinalityEqCertificate.ProductionGlobalShape, hevidence] at hshape

/-- Direct wire-level form: successful decoding and checker acceptance of the
production global shape yield a semantically conclusive checked outcome. -/
theorem WireCardinalityEqCertificate.exists_checked_global_outcome
    (wire : WireCardinalityEqCertificate)
    (decoded : DecodedCardinalityEqCertificate)
    (hdecode : wire.decode = Except.ok decoded)
    (hshape : decoded.ProductionGlobalShape)
    (hcheck : wire.check = Except.ok true) :
    ∃ outcome : CheckedCardinalityDecisionOutcome
        decoded.base.conceptCount decoded.base.roleCount decoded.base.variableCount
        decoded.base.rootCertificate.base.ontology decoded.definitions,
      outcome.Semantics := by
  have hdecodedCheck : decoded.check = true := by
    unfold WireCardinalityEqCertificate.check at hcheck
    rw [hdecode] at hcheck
    exact Except.ok.inj hcheck
  exact decoded.exists_checked_global_outcome hshape hdecodedCheck

/-- Fully executable trust boundary: no caller-supplied shape proposition is
needed once the production-global checker accepts the wire document. -/
theorem WireCardinalityEqCertificate.checkProductionGlobal_sound
    (wire : WireCardinalityEqCertificate)
    (hcheck : wire.checkProductionGlobal = Except.ok true) :
    ∃ decoded : DecodedCardinalityEqCertificate,
      wire.decode = Except.ok decoded ∧
      ∃ outcome : CheckedCardinalityDecisionOutcome
          decoded.base.conceptCount decoded.base.roleCount decoded.base.variableCount
          decoded.base.rootCertificate.base.ontology decoded.definitions,
        outcome.Semantics := by
  unfold WireCardinalityEqCertificate.checkProductionGlobal at hcheck
  cases hdecode : wire.decode with
  | error message => simp [hdecode] at hcheck
  | ok decoded =>
      simp only [hdecode] at hcheck
      have hand : decoded.productionGlobalShapeB = true ∧ decoded.check = true := by
        simpa only [Bool.and_eq_true] using (Except.ok.inj hcheck)
      have hshape : decoded.ProductionGlobalShape :=
        (decoded.productionGlobalShapeB_eq_true_iff).mp hand.1
      exact ⟨decoded, rfl, decoded.exists_checked_global_outcome hshape hand.2⟩

#print axioms DecodedCardinalityEqCertificate.exists_checked_global_outcome
#print axioms WireCardinalityEqCertificate.exists_checked_global_outcome
#print axioms DecodedCardinalityEqCertificate.productionGlobalShapeB_eq_true_iff
#print axioms WireCardinalityEqCertificate.checkProductionGlobal_sound

end ContextCalculus.Hypertableau
