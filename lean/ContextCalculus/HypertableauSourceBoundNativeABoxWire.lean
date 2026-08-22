import ContextCalculus.HypertableauNativeABoxSourceDecisionWire
import ContextCalculus.HypertableauNativeABoxCardinalitySourceDecisionWire
import ContextCalculus.HypertableauNativeABoxTaxonomySourceWire
import ContextCalculus.HypertableauNativeABoxCardinalityTaxonomySourceWire
import ContextCalculus.HypertableauRootedOrdinaryProductionRunWire
import ContextCalculus.HypertableauRootedCardinalityProductionRunWire
import ContextCalculus.HypertableauNativeABoxTaxonomyRunMatrixWire
import ContextCalculus.HypertableauNativeABoxCardinalityTaxonomyRunMatrixWire

/-!
# Source-bound native-ABox production evidence

These publication documents close the boundary between source projection and
the retained rooted production runs.  A source-semantic decision or complete
taxonomy matrix is accepted only when its internal target evidence is exactly
the terminal evidence reconstructed from those runs.
-/

namespace ContextCalculus.Hypertableau

open Lean

inductive WireNativeABoxSourceDecision where
  | direct (source : WireDirectNativeABoxDecisionCertificate)
  | mixed (source : WireMixedNativeABoxDecisionCertificate)
  | bundle (source : WireBundleNativeABoxDecisionCertificate)
deriving FromJson, ToJson, Repr

def WireNativeABoxSourceDecision.check : WireNativeABoxSourceDecision → Except String Bool
  | .direct source => source.check
  | .mixed source => source.check
  | .bundle source => source.check

def WireNativeABoxSourceDecision.SemanticallyValid : WireNativeABoxSourceDecision → Prop
  | .direct source => ∃ decoded, source.decode = .ok decoded ∧ decoded.SemanticallyValid
  | .mixed source => ∃ decoded, source.decode = .ok decoded ∧ decoded.SemanticallyValid
  | .bundle source => ∃ decoded, source.decode = .ok decoded ∧ decoded.SemanticallyValid

theorem WireNativeABoxSourceDecision.check_semantics
    (source : WireNativeABoxSourceDecision) (hcheck : source.check = .ok true) :
    source.SemanticallyValid := by
  cases source with
  | direct wire =>
      unfold WireNativeABoxSourceDecision.check
        WireDirectNativeABoxDecisionCertificate.check at hcheck
      cases hdecode : wire.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩
  | mixed wire =>
      unfold WireNativeABoxSourceDecision.check
        WireMixedNativeABoxDecisionCertificate.check at hcheck
      cases hdecode : wire.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩
  | bundle wire =>
      unfold WireNativeABoxSourceDecision.check
        WireBundleNativeABoxDecisionCertificate.check at hcheck
      cases hdecode : wire.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩

def WireNativeABoxSourceDecision.target : WireNativeABoxSourceDecision →
    WireNativeABoxDecisionCertificate
  | .direct source => match source.evidence with
      | .sat certificate => { version := source.version, evidence := .sat certificate.certificate }
      | .unsat refutation => { version := source.version, evidence := .unsat refutation.refutation }
  | .mixed source => match source.evidence with
      | .sat certificate => { version := source.version, evidence := .sat certificate.certificate }
      | .unsat refutation => { version := source.version, evidence := .unsat refutation.refutation }
  | .bundle source => match source.evidence with
      | .sat certificate => { version := source.version, evidence := .sat certificate.certificate }
      | .unsat refutation => { version := source.version, evidence := .unsat refutation.refutation }

structure WireSourceBoundNativeABoxGlobal where
  version : Nat
  source : WireNativeABoxSourceDecision
  run : WireRootedOrdinaryProductionRun
deriving FromJson, ToJson, Repr

def WireSourceBoundNativeABoxGlobal.sourceAcceptedB
    (wire : WireSourceBoundNativeABoxGlobal) : Bool :=
  match wire.source.check with
  | .ok true => true
  | _ => false

def WireSourceBoundNativeABoxGlobal.payloadBoundB
    (wire : WireSourceBoundNativeABoxGlobal) : Bool :=
  toJson wire.source.target == toJson wire.run.terminal

def WireSourceBoundNativeABoxGlobal.check
    (wire : WireSourceBoundNativeABoxGlobal) : Bool :=
  wire.version == 1 && wire.sourceAcceptedB && wire.run.check && wire.payloadBoundB

theorem WireSourceBoundNativeABoxGlobal.check_sound
    (wire : WireSourceBoundNativeABoxGlobal) (hcheck : wire.check = true) :
    wire.source.SemanticallyValid ∧ wire.run.check = true ∧
      wire.payloadBoundB = true := by
  have nested : (((wire.version = 1 ∧ wire.sourceAcceptedB = true) ∧
      wire.run.check = true) ∧ wire.payloadBoundB = true) := by
    simpa [WireSourceBoundNativeABoxGlobal.check, Bool.and_eq_true,
      beq_iff_eq] using hcheck
  have hsource : wire.source.check = .ok true := by
    unfold WireSourceBoundNativeABoxGlobal.sourceAcceptedB at nested
    cases h : wire.source.check with
    | error message => simp [h] at nested
    | ok accepted => cases accepted <;> simp [h] at nested ⊢
  exact ⟨wire.source.check_semantics hsource, nested.1.2, nested.2⟩

inductive WireNativeABoxCardinalitySourceDecision where
  | direct (source : WireDirectNativeABoxCardinalityDecisionCertificate)
  | mixed (source : WireMixedNativeABoxCardinalityDecisionCertificate)
  | bundle (source : WireBundleNativeABoxCardinalityDecisionCertificate)
deriving FromJson, ToJson, Repr

def WireNativeABoxCardinalitySourceDecision.check :
    WireNativeABoxCardinalitySourceDecision → Except String Bool
  | .direct source => source.check
  | .mixed source => source.check
  | .bundle source => source.check

def WireNativeABoxCardinalitySourceDecision.SemanticallyValid :
    WireNativeABoxCardinalitySourceDecision → Prop
  | .direct source => ∃ decoded, source.decode = .ok decoded ∧ decoded.SemanticallyValid
  | .mixed source => ∃ decoded, source.decode = .ok decoded ∧ decoded.SemanticallyValid
  | .bundle source => ∃ decoded, source.decode = .ok decoded ∧ decoded.SemanticallyValid

theorem WireNativeABoxCardinalitySourceDecision.check_semantics
    (source : WireNativeABoxCardinalitySourceDecision)
    (hcheck : source.check = .ok true) : source.SemanticallyValid := by
  cases source with
  | direct wire =>
      unfold WireNativeABoxCardinalitySourceDecision.check
        WireDirectNativeABoxCardinalityDecisionCertificate.check at hcheck
      cases hdecode : wire.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩
  | mixed wire =>
      unfold WireNativeABoxCardinalitySourceDecision.check
        WireMixedNativeABoxCardinalityDecisionCertificate.check at hcheck
      cases hdecode : wire.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩
  | bundle wire =>
      unfold WireNativeABoxCardinalitySourceDecision.check
        WireBundleNativeABoxCardinalityDecisionCertificate.check at hcheck
      cases hdecode : wire.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩

def WireNativeABoxCardinalitySourceDecision.target :
    WireNativeABoxCardinalitySourceDecision → WireNativeABoxCardinalityDecisionCertificate
  | .direct source => match source.evidence with
      | .sat certificate => { version := source.version, evidence := .sat certificate.certificate }
      | .unsat refutation => { version := source.version, evidence := .unsat refutation.refutation }
  | .mixed source => match source.evidence with
      | .sat certificate => { version := source.version, evidence := .sat certificate.certificate }
      | .unsat refutation => { version := source.version, evidence := .unsat refutation.refutation }
  | .bundle source => match source.evidence with
      | .sat certificate => { version := source.version, evidence := .sat certificate.certificate }
      | .unsat refutation => { version := source.version, evidence := .unsat refutation.refutation }

structure WireSourceBoundNativeABoxCardinalityGlobal where
  version : Nat
  source : WireNativeABoxCardinalitySourceDecision
  run : WireRootedCardinalityProductionRun
deriving FromJson, ToJson, Repr

def WireSourceBoundNativeABoxCardinalityGlobal.sourceAcceptedB
    (wire : WireSourceBoundNativeABoxCardinalityGlobal) : Bool :=
  match wire.source.check with
  | .ok true => true
  | _ => false

def WireSourceBoundNativeABoxCardinalityGlobal.payloadBoundB
    (wire : WireSourceBoundNativeABoxCardinalityGlobal) : Bool :=
  toJson wire.source.target == toJson wire.run.terminal

def WireSourceBoundNativeABoxCardinalityGlobal.check
    (wire : WireSourceBoundNativeABoxCardinalityGlobal) : Bool :=
  wire.version == 1 && wire.sourceAcceptedB && wire.run.check && wire.payloadBoundB

theorem WireSourceBoundNativeABoxCardinalityGlobal.check_sound
    (wire : WireSourceBoundNativeABoxCardinalityGlobal) (hcheck : wire.check = true) :
    wire.source.SemanticallyValid ∧ wire.run.check = true ∧
      wire.payloadBoundB = true := by
  have nested : (((wire.version = 1 ∧ wire.sourceAcceptedB = true) ∧
      wire.run.check = true) ∧ wire.payloadBoundB = true) := by
    simpa [WireSourceBoundNativeABoxCardinalityGlobal.check, Bool.and_eq_true,
      beq_iff_eq] using hcheck
  have hsource : wire.source.check = .ok true := by
    unfold WireSourceBoundNativeABoxCardinalityGlobal.sourceAcceptedB at nested
    cases h : wire.source.check with
    | error message => simp [h] at nested
    | ok accepted => cases accepted <;> simp [h] at nested ⊢
  exact ⟨wire.source.check_semantics hsource, nested.1.2, nested.2⟩

inductive WireNativeABoxSourceTaxonomy where
  | direct (source : WireDirectNativeABoxTaxonomyMatrix)
  | mixed (source : WireMixedNativeABoxTaxonomyMatrix)
  | bundle (source : WireBundleNativeABoxTaxonomyMatrix)
deriving FromJson, ToJson, Repr

def WireNativeABoxSourceTaxonomy.check : WireNativeABoxSourceTaxonomy → Except String Bool
  | .direct source => source.check
  | .mixed source => source.check
  | .bundle source => source.check

def WireNativeABoxSourceTaxonomy.SemanticallyValid : WireNativeABoxSourceTaxonomy → Prop
  | .direct source => ∃ decoded, source.decode = .ok decoded ∧ decoded.SemanticallyValid
  | .mixed source => ∃ decoded, source.decode = .ok decoded ∧ decoded.SemanticallyValid
  | .bundle source => ∃ decoded, source.decode = .ok decoded ∧ decoded.SemanticallyValid

theorem WireNativeABoxSourceTaxonomy.check_semantics
    (source : WireNativeABoxSourceTaxonomy) (hcheck : source.check = .ok true) :
    source.SemanticallyValid := by
  cases source with
  | direct wire =>
      unfold WireNativeABoxSourceTaxonomy.check
        WireDirectNativeABoxTaxonomyMatrix.check at hcheck
      cases hdecode : wire.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩
  | mixed wire =>
      unfold WireNativeABoxSourceTaxonomy.check
        WireMixedNativeABoxTaxonomyMatrix.check at hcheck
      cases hdecode : wire.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩
  | bundle wire =>
      unfold WireNativeABoxSourceTaxonomy.check
        WireBundleNativeABoxTaxonomyMatrix.check at hcheck
      cases hdecode : wire.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩

def WireNativeABoxSourceTaxonomy.target : WireNativeABoxSourceTaxonomy →
    WireNativeABoxTaxonomyMatrix
  | .direct source => source.matrix
  | .mixed source => source.matrix
  | .bundle source => source.matrix

structure WireSourceBoundNativeABoxTaxonomy where
  version : Nat
  source : WireNativeABoxSourceTaxonomy
  runs : WireNativeABoxTaxonomyRunMatrix
deriving FromJson, ToJson, Repr

def WireSourceBoundNativeABoxTaxonomy.sourceAcceptedB
    (wire : WireSourceBoundNativeABoxTaxonomy) : Bool :=
  match wire.source.check with
  | .ok true => true
  | _ => false

def WireSourceBoundNativeABoxTaxonomy.payloadBoundB
    (wire : WireSourceBoundNativeABoxTaxonomy) : Bool :=
  toJson wire.source.target == toJson wire.runs.terminalMatrix

def WireSourceBoundNativeABoxTaxonomy.check
    (wire : WireSourceBoundNativeABoxTaxonomy) : Bool :=
  wire.version == 1 && wire.sourceAcceptedB && wire.runs.check && wire.payloadBoundB

theorem WireSourceBoundNativeABoxTaxonomy.check_sound
    (wire : WireSourceBoundNativeABoxTaxonomy) (hcheck : wire.check = true) :
    wire.source.SemanticallyValid ∧ wire.runs.check = true ∧
      wire.payloadBoundB = true := by
  have nested : (((wire.version = 1 ∧ wire.sourceAcceptedB = true) ∧
      wire.runs.check = true) ∧ wire.payloadBoundB = true) := by
    simpa [WireSourceBoundNativeABoxTaxonomy.check, Bool.and_eq_true,
      beq_iff_eq] using hcheck
  have hsource : wire.source.check = .ok true := by
    unfold WireSourceBoundNativeABoxTaxonomy.sourceAcceptedB at nested
    cases h : wire.source.check with
    | error message => simp [h] at nested
    | ok accepted => cases accepted <;> simp [h] at nested ⊢
  exact ⟨wire.source.check_semantics hsource, nested.1.2, nested.2⟩

inductive WireNativeABoxCardinalitySourceTaxonomy where
  | direct (source : WireDirectNativeABoxCardinalityTaxonomyMatrix)
  | mixed (source : WireMixedNativeABoxCardinalityTaxonomyMatrix)
  | bundle (source : WireBundleNativeABoxCardinalityTaxonomyMatrix)
deriving FromJson, ToJson, Repr

def WireNativeABoxCardinalitySourceTaxonomy.check :
    WireNativeABoxCardinalitySourceTaxonomy → Except String Bool
  | .direct source => source.check
  | .mixed source => source.check
  | .bundle source => source.check

def WireNativeABoxCardinalitySourceTaxonomy.SemanticallyValid :
    WireNativeABoxCardinalitySourceTaxonomy → Prop
  | .direct source => ∃ decoded, source.decode = .ok decoded ∧ decoded.SemanticallyValid
  | .mixed source => ∃ decoded, source.decode = .ok decoded ∧ decoded.SemanticallyValid
  | .bundle source => ∃ decoded, source.decode = .ok decoded ∧ decoded.SemanticallyValid

theorem WireNativeABoxCardinalitySourceTaxonomy.check_semantics
    (source : WireNativeABoxCardinalitySourceTaxonomy)
    (hcheck : source.check = .ok true) : source.SemanticallyValid := by
  cases source with
  | direct wire =>
      unfold WireNativeABoxCardinalitySourceTaxonomy.check
        WireDirectNativeABoxCardinalityTaxonomyMatrix.check at hcheck
      cases hdecode : wire.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩
  | mixed wire =>
      unfold WireNativeABoxCardinalitySourceTaxonomy.check
        WireMixedNativeABoxCardinalityTaxonomyMatrix.check at hcheck
      cases hdecode : wire.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩
  | bundle wire =>
      unfold WireNativeABoxCardinalitySourceTaxonomy.check
        WireBundleNativeABoxCardinalityTaxonomyMatrix.check at hcheck
      cases hdecode : wire.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩

def WireNativeABoxCardinalitySourceTaxonomy.target :
    WireNativeABoxCardinalitySourceTaxonomy → WireNativeABoxCardinalityTaxonomyMatrix
  | .direct source => source.matrix
  | .mixed source => source.matrix
  | .bundle source => source.matrix

structure WireSourceBoundNativeABoxCardinalityTaxonomy where
  version : Nat
  source : WireNativeABoxCardinalitySourceTaxonomy
  runs : WireNativeABoxCardinalityTaxonomyRunMatrix
deriving FromJson, ToJson, Repr

def WireSourceBoundNativeABoxCardinalityTaxonomy.sourceAcceptedB
    (wire : WireSourceBoundNativeABoxCardinalityTaxonomy) : Bool :=
  match wire.source.check with
  | .ok true => true
  | _ => false

def WireSourceBoundNativeABoxCardinalityTaxonomy.payloadBoundB
    (wire : WireSourceBoundNativeABoxCardinalityTaxonomy) : Bool :=
  toJson wire.source.target == toJson wire.runs.terminalMatrix

def WireSourceBoundNativeABoxCardinalityTaxonomy.check
    (wire : WireSourceBoundNativeABoxCardinalityTaxonomy) : Bool :=
  wire.version == 1 && wire.sourceAcceptedB && wire.runs.check && wire.payloadBoundB

theorem WireSourceBoundNativeABoxCardinalityTaxonomy.check_sound
    (wire : WireSourceBoundNativeABoxCardinalityTaxonomy) (hcheck : wire.check = true) :
    wire.source.SemanticallyValid ∧ wire.runs.check = true ∧
      wire.payloadBoundB = true := by
  have nested : (((wire.version = 1 ∧ wire.sourceAcceptedB = true) ∧
      wire.runs.check = true) ∧ wire.payloadBoundB = true) := by
    simpa [WireSourceBoundNativeABoxCardinalityTaxonomy.check, Bool.and_eq_true,
      beq_iff_eq] using hcheck
  have hsource : wire.source.check = .ok true := by
    unfold WireSourceBoundNativeABoxCardinalityTaxonomy.sourceAcceptedB at nested
    cases h : wire.source.check with
    | error message => simp [h] at nested
    | ok accepted => cases accepted <;> simp [h] at nested ⊢
  exact ⟨wire.source.check_semantics hsource, nested.1.2, nested.2⟩

#print axioms WireSourceBoundNativeABoxGlobal.check_sound
#print axioms WireSourceBoundNativeABoxCardinalityGlobal.check_sound
#print axioms WireSourceBoundNativeABoxTaxonomy.check_sound
#print axioms WireSourceBoundNativeABoxCardinalityTaxonomy.check_sound

end ContextCalculus.Hypertableau
