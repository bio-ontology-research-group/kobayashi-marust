import ContextCalculus.CertifiedRouting
import Lean.Data.Json

/-!
# KM automatic-route decision boundary

This module mirrors the semantic branch order of `engine/src/routing.rs` while
deliberately omitting every measurement-only route.  Expensive numeric profile
predicates are represented by named Boolean decisions here; later executable
profile certificates must justify those decisions from the typed source.

The important distinction is retained in `CoverageBasis`: an atomic specialist
needs a proved source-fragment completeness theorem, a portfolio needs a proved
complete fallback, and a total calculus supplies completeness directly.
-/

namespace ContextCalculus.KMAutomaticRouting

open Lean

inductive SemanticFragment where
  | unsupportedRules
  | rules
  | nativeBridgeABox
  | positiveABox
  | nominal
  | sriqCore
deriving DecidableEq, FromJson, ToJson, Repr

/-- Exactly the routes that the production `select` function may return. -/
inductive Route where
  | certifiedElProduction
  | htRules
  | certifiedNominals
  | elc
  | productionAll
  | productionAll8
  | productionAll1
  | htGeneral
  | certifiedCardNominals
  | certifiedCardProxyABox
  | nominalNiTBox
  | nominals
  | cbPlain16
  | cbPlain8
  | cbPlain1
  | cbAbsorb16
  | cbAbsorb8
  | cbAbsorb1
  | lean
  | seqOn
  | seqOff
deriving DecidableEq, FromJson, ToJson, Repr

def learnedEligible : Route → Bool
  | .elc | .cbPlain16 | .cbPlain8 | .cbPlain1
  | .cbAbsorb16 | .cbAbsorb8 | .cbAbsorb1
  | .lean | .seqOn | .seqOff
  | .productionAll | .productionAll8 | .productionAll1 => true
  | _ => false

/-- Source/profile decisions used by the ordered production selector.  Field
order follows the Rust guards, so later guards cannot shadow earlier semantic
dispatch. -/
structure Decision where
  certifiedElProduction : Bool
  fragment : SemanticFragment
  nominalIndependentLargeEl : Bool := false
  nominalIndependentLarge : Bool := false
  nominalLargeTBoxSmallIdentityABox : Bool := false
  nominalSmallClassIdentityABox : Bool := false
  nominalGroundGeneralHT : Bool := false
  inverseCardinalityRoleSeparable : Bool := false
  cardNumberRoleSeparable : Bool := false
  nominalLargeNoCardinalityABox : Bool := false
  nominalLargePortfolio : Bool := false
  nominalTypedBridgeNonCardinality : Bool := false
  nominalTypedBridge : Bool := false
  nominalNITBox : Bool := false
  sriqEL : Bool := false
  sriqLargeHornFunctionalBridge : Bool := false
  positiveABoxEL : Bool := false
  learned : Route := .productionAll
  oneThreadSmallProduction : Bool := false
deriving FromJson, ToJson, Repr

private def selectNominal (decision : Decision) : Route :=
  if decision.nominalIndependentLargeEl then .elc
  else if decision.nominalIndependentLarge then .productionAll
  else if decision.nominalLargeTBoxSmallIdentityABox then .productionAll
  else if decision.nominalSmallClassIdentityABox then .productionAll
  else if decision.nominalGroundGeneralHT then .htGeneral
  else if decision.inverseCardinalityRoleSeparable then .certifiedCardNominals
  else if decision.cardNumberRoleSeparable then .certifiedCardProxyABox
  else if decision.nominalLargeNoCardinalityABox then .productionAll
  else if decision.nominalLargePortfolio then .certifiedNominals
  else if decision.nominalTypedBridgeNonCardinality then .productionAll
  else if decision.nominalTypedBridge then .certifiedNominals
  else if decision.nominalNITBox then .nominalNiTBox
  else .nominals

private def selectLearned (decision : Decision) : Route :=
  if learnedEligible decision.learned then
    if decision.learned = .productionAll && decision.oneThreadSmallProduction then
      .productionAll1
    else decision.learned
  else .cbPlain16

/-- Pure mirror of the production selector after profile predicates have been
checked.  A stale learned tree fails closed to the total CB calculus. -/
def select (decision : Decision) : Route :=
  if decision.certifiedElProduction then .certifiedElProduction
  else match decision.fragment with
    | .unsupportedRules | .rules => .htRules
    | .nativeBridgeABox => .certifiedNominals
    | .nominal => selectNominal decision
    | .sriqCore =>
        if decision.sriqEL then .elc
        else if decision.sriqLargeHornFunctionalBridge then .productionAll
        else if decision.inverseCardinalityRoleSeparable then .productionAll
        else selectLearned decision
    | .positiveABox =>
        if decision.positiveABoxEL then .elc
        else if decision.inverseCardinalityRoleSeparable then .productionAll
        else selectLearned decision

/-- Executable selector boundary. The version prevents silently reinterpreting
an old decision schema after the Rust or Lean branch order changes. -/
structure WireSelection where
  version : Nat
  decision : Decision
  selected : Route
deriving FromJson, ToJson, Repr

def WireSelection.check (wire : WireSelection) : Bool :=
  wire.version == 1 && decide (wire.selected = select wire.decision)

theorem WireSelection.check_sound (wire : WireSelection)
    (hcheck : wire.check = true) :
    wire.version = 1 ∧ wire.selected = select wire.decision := by
  simpa [WireSelection.check, Bool.and_eq_true, beq_iff_eq] using hcheck

inductive CoverageBasis where
  /-- The worker's checked fragment theorem proves totality on this source. -/
  | certifiedFragment
  /-- At least one exact fallback remains live after every specialist decline. -/
  | certifiedFallback
  /-- The selected CB-family calculus is complete on the routed source language. -/
  | totalCalculus
deriving DecidableEq, Repr

def coverageBasis : Route → CoverageBasis
  | .elc | .htRules | .htGeneral | .certifiedCardNominals
  | .nominalNiTBox => .certifiedFragment
  | .certifiedElProduction | .certifiedNominals | .productionAll
  | .productionAll8 | .productionAll1 | .certifiedCardProxyABox =>
      .certifiedFallback
  | .nominals | .cbPlain16 | .cbPlain8 | .cbPlain1
  | .cbAbsorb16 | .cbAbsorb8 | .cbAbsorb1 | .lean | .seqOn | .seqOff =>
      .totalCalculus

/-- Obligations retained by the concrete route checker.  Source identity is
mandatory for every route.  Absorbed production inputs additionally require a
checked source-to-worker equivalence proof before their CB result can count as
a source-level fallback. -/
structure CoverageObligations where
  basis : CoverageBasis
  sourceExact : Bool
  preprocessingEquivalence : Bool
deriving DecidableEq, Repr

def obligations (route : Route) : CoverageObligations :=
  { basis := coverageBasis route
  , sourceExact := true
  , preprocessingEquivalence := match route with
      | .certifiedElProduction | .productionAll | .productionAll8
      | .productionAll1 | .cbAbsorb16 | .cbAbsorb8 | .cbAbsorb1 => true
      | _ => false }

/-- The concrete completeness obligation produced for every automatic routing
decision.  This theorem does not assume that certificate-or-defer means total:
atomic specialists remain visibly dependent on a fragment proof. -/
theorem selected_route_has_coverage_basis (decision : Decision) :
    ∃ basis, coverageBasis (select decision) = basis := by
  exact ⟨coverageBasis (select decision), rfl⟩

theorem selected_route_requires_exact_source (decision : Decision) :
    (obligations (select decision)).sourceExact = true := by
  rfl

example (decision : Decision) (h : learnedEligible decision.learned = false)
    (hcert : decision.certifiedElProduction = false)
    (hfragment : decision.fragment = .sriqCore)
    (hel : decision.sriqEL = false)
    (hbridge : decision.sriqLargeHornFunctionalBridge = false)
    (hcard : decision.inverseCardinalityRoleSeparable = false) :
    select decision = .cbPlain16 := by
  simp [select, hcert, hfragment, hel, hbridge, hcard, selectLearned, h]

example (decision : Decision)
    (hcert : decision.certifiedElProduction = false)
    (hfragment : decision.fragment = .sriqCore)
    (hel : decision.sriqEL = false)
    (hbridge : decision.sriqLargeHornFunctionalBridge = true) :
    select decision = .productionAll := by
  simp [select, hcert, hfragment, hel, hbridge]

#print axioms selected_route_has_coverage_basis
#print axioms selected_route_requires_exact_source
#print axioms WireSelection.check_sound

end ContextCalculus.KMAutomaticRouting
