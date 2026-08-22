import ContextCalculus.HypertableauDoublingTraceWire
import ContextCalculus.HypertableauMixedTaxonomyWire

/-!
# Complete ontology-only ordinary taxonomy production runs

One artifact binds an equality-free, equality-aware, anchored, or regular
taxonomy terminal to the complete state-bearing frontier history traversed by
the production run that decided the exact query.
-/

namespace ContextCalculus.Hypertableau

open Lean

inductive WireOrdinaryTaxonomyQuery where
  | concept (concept : Nat)
  | subsumption (sub sup : Nat)
deriving FromJson, ToJson, Repr

structure WireOrdinaryTaxonomyProductionRun where
  version : Nat
  start_budget : Nat
  concept_count : Nat
  role_count : Nat
  variable_count : Nat
  ontology : List WireClause
  query : WireOrdinaryTaxonomyQuery
  frontiers : List WireAddressRefinementDocument
  terminal : WireMixedQueryPayload
deriving FromJson, ToJson, Repr

def WireLabel.matchesTaxonomy
    (label : WireLabel) (node conceptId : Nat) (neg : Bool) : Bool :=
  label.node == node && label.literal.concept == conceptId &&
    label.literal.neg == neg

def WireOrdinaryTaxonomyQuery.presentInLabels
    (query : WireOrdinaryTaxonomyQuery) (labels : List WireLabel) : Bool :=
  match query with
  | .concept conceptId => labels.any (·.matchesTaxonomy 0 conceptId false)
  | .subsumption sub sup =>
      labels.any (·.matchesTaxonomy 0 sub false) &&
        labels.any (·.matchesTaxonomy 0 sup true)

def WireOrdinaryTaxonomyQuery.presentInMixed
    (query : WireOrdinaryTaxonomyQuery) : WireMixedQueryPayload → Bool
  | .plain payload => query.presentInLabels payload.labels
  | .equality _ state _ => query.presentInLabels state.labels
  | .anchored certificate _ => query.presentInLabels certificate.equality_state.labels
  | .regular certificate _ => query.presentInLabels certificate.labels

def WireMixedQueryPayload.nodeCount : WireMixedQueryPayload → Nat
  | .plain payload => payload.node_count
  | .equality nodeCount _ _ => nodeCount
  | .anchored certificate _ => certificate.equality_node_count
  | .regular certificate _ => certificate.node_count

def WireOrdinaryTaxonomyProductionRun.trace
    (wire : WireOrdinaryTaxonomyProductionRun) : WireAddressDoublingTrace := {
  version := 1
  start_budget := wire.start_budget
  frontiers := wire.frontiers
}

def WireOrdinaryTaxonomyProductionRun.problemDecodes
    (wire : WireOrdinaryTaxonomyProductionRun) : Bool :=
  match wire.ontology.mapM
      (WireClause.decode wire.variable_count wire.concept_count wire.role_count) with
  | .error _ => false
  | .ok ontology =>
      match wire.query with
      | .concept conceptId =>
          match checkedFin "taxonomy concept" wire.concept_count conceptId with
          | .ok concept => (wire.terminal.decodeConcept ontology concept).isOk
          | .error _ => false
      | .subsumption subId supId =>
          match checkedFin "taxonomy subclass" wire.concept_count subId,
            checkedFin "taxonomy superclass" wire.concept_count supId with
          | .ok sub, .ok sup =>
              (wire.terminal.decodeSubsumption ontology sub sup).isOk
          | _, _ => false

def WireOrdinaryTaxonomyProductionRun.matchesLast
    (wire : WireOrdinaryTaxonomyProductionRun) : Bool :=
  match wire.frontiers.getLast? with
  | none => true
  | some frontier =>
      frontier.state.concept_count == wire.concept_count &&
      frontier.state.role_count == wire.role_count &&
      frontier.state.variable_count == wire.variable_count &&
      wire.query.presentInLabels frontier.state.labels &&
      toJson frontier.state.ontology == toJson wire.ontology

def WireOrdinaryTaxonomyProductionRun.terminalAccepted
    (wire : WireOrdinaryTaxonomyProductionRun) : Bool :=
  wire.problemDecodes &&
    decide (wire.terminal.nodeCount ≤
      8 * 2 ^ (wire.start_budget + wire.frontiers.length)) &&
    wire.query.presentInMixed wire.terminal && wire.matchesLast

def WireOrdinaryTaxonomyProductionRun.check
    (wire : WireOrdinaryTaxonomyProductionRun) : Bool :=
  wire.version == 1 && wire.trace.check && wire.terminalAccepted

structure WireOrdinaryTaxonomyProductionRun.Accepted
    (wire : WireOrdinaryTaxonomyProductionRun) : Prop where
  trace : WireAddressDoublingTrace.ValidFrom wire.start_budget wire.frontiers
  terminal : wire.problemDecodes = true
  withinBudget : wire.terminal.nodeCount ≤
    8 * 2 ^ (wire.start_budget + wire.frontiers.length)
  queryPresent : wire.query.presentInMixed wire.terminal = true
  sameProblem : wire.matchesLast = true

theorem WireOrdinaryTaxonomyProductionRun.check_sound
    (wire : WireOrdinaryTaxonomyProductionRun) (hcheck : wire.check = true) :
    wire.Accepted := by
  simp only [WireOrdinaryTaxonomyProductionRun.check,
    WireOrdinaryTaxonomyProductionRun.terminalAccepted,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨wire.trace.check_sound hcheck.1.2, hcheck.2.1.1.1,
    hcheck.2.1.1.2, hcheck.2.1.2, hcheck.2.2⟩

#print axioms WireOrdinaryTaxonomyProductionRun.check_sound

end ContextCalculus.Hypertableau
