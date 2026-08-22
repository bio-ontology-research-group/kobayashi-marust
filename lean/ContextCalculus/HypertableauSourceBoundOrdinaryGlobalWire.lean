import ContextCalculus.HypertableauNormalizedWire
import ContextCalculus.HypertableauOrdinaryProductionRunWire
import ContextCalculus.HypertableauOrdinaryUnsatProductionRunWire

/-!
# Source-bound ordinary global production decisions

The source-normalization certificate and complete iterative-deepening run are
accepted as one document.  The normalized payload must be the exact SAT or
UNSAT terminal retained by the run, including regular-decision envelopes.
-/

namespace ContextCalculus.Hypertableau

open Lean

inductive WireOrdinaryGlobalRun where
  | sat (run : WireOrdinaryProductionRun)
  | unsat (run : WireOrdinaryUnsatProductionRun)
deriving FromJson, ToJson, Repr

structure WireSourceBoundOrdinaryGlobal where
  version : Nat
  source : WireNormalizedCertificate
  production : WireOrdinaryGlobalRun
deriving FromJson, ToJson, Repr

def WireOrdinaryGlobalRun.check : WireOrdinaryGlobalRun → Bool
  | .sat run => run.check
  | .unsat run => run.check

private def plainTerminalBoundB
    (certificate : WireCertificate) (run : WireOrdinaryProductionRun) : Bool :=
  match run.finite, run.regular, run.equality with
  | some terminal, none, none => toJson certificate == toJson terminal.finite
  | _, _, _ => false

private def equalityTerminalBoundB
    (certificate : WireEqCertificate) (run : WireOrdinaryProductionRun) : Bool :=
  match run.finite, run.regular, run.equality with
  | none, none, some terminal => toJson certificate == toJson terminal.result
  | _, _, _ => false

private def regularTerminalBoundB
    (certificate : WireRegularDecisionCertificate)
    (run : WireOrdinaryProductionRun) : Bool :=
  match certificate.evidence, run.finite, run.regular, run.equality with
  | .regular_sat source, none, some terminal, none =>
      toJson source == toJson terminal.regular
  | .finite_sat source, some terminal, none, none =>
      toJson source == toJson terminal.finite
  | _, _, _, _ => false

private def plainUnsatBoundB
    (certificate : WireCertificate)
    (run : WireOrdinaryUnsatProductionRun) : Bool :=
  match run.terminal with
  | .ordinary terminal => toJson certificate == toJson terminal
  | .equality _ => false

private def equalityUnsatBoundB
    (certificate : WireEqCertificate)
    (run : WireOrdinaryUnsatProductionRun) : Bool :=
  match run.terminal with
  | .ordinary _ => false
  | .equality terminal => toJson certificate == toJson terminal

private def regularUnsatBoundB
    (certificate : WireRegularDecisionCertificate)
    (run : WireOrdinaryUnsatProductionRun) : Bool :=
  match certificate.evidence, run.terminal with
  | .finite_unsat source, .ordinary terminal =>
      toJson source == toJson terminal
  | _, _ => false

def WireSourceBoundOrdinaryGlobal.payloadBoundB
    (wire : WireSourceBoundOrdinaryGlobal) : Bool :=
  match wire.source.payload, wire.production with
  | .plain certificate, .sat run => plainTerminalBoundB certificate run
  | .equality certificate, .sat run => equalityTerminalBoundB certificate run
  | .regular certificate, .sat run => regularTerminalBoundB certificate run
  | .plain certificate, .unsat run => plainUnsatBoundB certificate run
  | .equality certificate, .unsat run => equalityUnsatBoundB certificate run
  | .regular certificate, .unsat run => regularUnsatBoundB certificate run
  | .cardinality _, _ => false

def WireSourceBoundOrdinaryGlobal.sourceAcceptedB
    (wire : WireSourceBoundOrdinaryGlobal) : Bool :=
  match wire.source.check with
  | .ok true => true
  | _ => false

def WireSourceBoundOrdinaryGlobal.check
    (wire : WireSourceBoundOrdinaryGlobal) : Bool :=
  wire.version == 1 && wire.sourceAcceptedB && wire.production.check &&
    wire.payloadBoundB

theorem WireSourceBoundOrdinaryGlobal.check_sound
    (wire : WireSourceBoundOrdinaryGlobal) (hcheck : wire.check = true) :
    wire.source.check = .ok true ∧ wire.production.check = true ∧
      wire.payloadBoundB = true ∧
      ∃ decoded : DecodedNormalizedCertificate,
        wire.source.decode = .ok decoded ∧ decoded.SemanticallyValid := by
  have nested : (((wire.version = 1 ∧ wire.sourceAcceptedB = true) ∧
      wire.production.check = true) ∧ wire.payloadBoundB = true) := by
    simpa [WireSourceBoundOrdinaryGlobal.check, Bool.and_eq_true,
      beq_iff_eq] using hcheck
  have hsource : wire.source.check = .ok true := by
    unfold WireSourceBoundOrdinaryGlobal.sourceAcceptedB at nested
    cases h : wire.source.check with
    | error message => simp [h] at nested
    | ok accepted => cases accepted <;> simp [h] at nested ⊢
  refine ⟨hsource, nested.1.2, nested.2, ?_⟩
  unfold WireNormalizedCertificate.check at hsource
  cases hdecode : wire.source.decode with
  | error message => simp [hdecode] at hsource
  | ok decoded =>
      refine ⟨decoded, rfl, ?_⟩
      have hdecoded : decoded.check = true := by
        simpa [WireNormalizedCertificate.check, hdecode] using hsource
      exact decoded.check_sound hdecoded

#print axioms WireSourceBoundOrdinaryGlobal.check_sound

end ContextCalculus.Hypertableau
