import ContextCalculus.HypertableauCardinalityDoublingTraceWire
import ContextCalculus.HypertableauCardinalityTaxonomyWire

/-!
# Complete ontology-only cardinality taxonomy production runs

This wire binds one semantically checked taxonomy decision to every
state-bearing cardinality frontier traversed by the production run that made
that exact decision. The query is retained explicitly, so a valid terminal for
another matrix cell cannot be substituted after the run has completed.
-/

namespace ContextCalculus.Hypertableau

open Lean

inductive WireCardinalityTaxonomyQuery where
  | concept (concept : Nat)
  | subsumption (sub sup : Nat)
deriving FromJson, ToJson, Repr

def WireEqState.containsTaxonomyLabel
    (state : WireEqState) (node conceptId : Nat) (neg : Bool) : Bool :=
  state.labels.any fun label =>
    label.node == node && label.literal.concept == conceptId &&
      label.literal.neg == neg

structure WireCardinalityTaxonomyProductionRun where
  version : Nat
  start_budget : Nat
  max_width : Nat
  concept_count : Nat
  role_count : Nat
  variable_count : Nat
  ontology : List WireClause
  definitions : List WireCardinalityDef
  query : WireCardinalityTaxonomyQuery
  frontiers : List WireCardinalityAddressRefinementDocument
  terminal : WireCardinalityQueryPayload
deriving FromJson, ToJson, Repr

def WireCardinalityTaxonomyQuery.presentIn
    (query : WireCardinalityTaxonomyQuery) (state : WireEqState) : Bool :=
  match query with
  | .concept conceptId => state.containsTaxonomyLabel 0 conceptId false
  | .subsumption sub sup =>
      state.containsTaxonomyLabel 0 sub false &&
        state.containsTaxonomyLabel 0 sup true

def WireCardinalityTaxonomyProductionRun.trace
    (wire : WireCardinalityTaxonomyProductionRun) : WireCardinalityDoublingTrace := {
  version := 1
  start_budget := wire.start_budget
  max_width := wire.max_width
  frontiers := wire.frontiers
}

def WireCardinalityTaxonomyProductionRun.problemDecodes
    (wire : WireCardinalityTaxonomyProductionRun) : Bool :=
  match wire.ontology.mapM
      (WireClause.decode wire.variable_count wire.concept_count wire.role_count),
    wire.definitions.mapM
      (WireCardinalityDef.decode wire.concept_count wire.role_count) with
  | .ok ontology, .ok definitions =>
      match wire.query with
      | .concept conceptId =>
          match checkedFin "taxonomy concept" wire.concept_count conceptId with
          | .ok concept =>
              (decodeCardinalityConcept wire.terminal ontology definitions concept).isOk
          | .error _ => false
      | .subsumption subId supId =>
          match checkedFin "taxonomy subclass" wire.concept_count subId,
            checkedFin "taxonomy superclass" wire.concept_count supId with
          | .ok sub, .ok sup =>
              (decodeCardinalitySubsumption wire.terminal ontology definitions sub sup).isOk
          | _, _ => false
  | _, _ => false

def WireCardinalityTaxonomyProductionRun.matchesLast
    (wire : WireCardinalityTaxonomyProductionRun) : Bool :=
  match wire.frontiers.getLast? with
  | none => true
  | some frontier =>
      frontier.variable_count == wire.variable_count &&
      frontier.frontier.concept_count == wire.concept_count &&
      frontier.frontier.role_count == wire.role_count &&
      frontier.frontier.definition_count == wire.definitions.length &&
      frontier.frontier.max_width == wire.max_width &&
      wire.query.presentIn frontier.runtime.state.base &&
      toJson frontier.ontology == toJson wire.ontology &&
      toJson frontier.definitions == toJson wire.definitions

def WireCardinalityTaxonomyProductionRun.terminalAccepted
    (wire : WireCardinalityTaxonomyProductionRun) : Bool :=
  wire.problemDecodes &&
    decide (wire.terminal.node_count ≤
      8 * 2 ^ (wire.start_budget + wire.frontiers.length)) &&
    wire.query.presentIn wire.terminal.state && wire.matchesLast

def WireCardinalityTaxonomyProductionRun.check
    (wire : WireCardinalityTaxonomyProductionRun) : Bool :=
  wire.version == 1 && wire.trace.check && wire.terminalAccepted

structure WireCardinalityTaxonomyProductionRun.Accepted
    (wire : WireCardinalityTaxonomyProductionRun) : Prop where
  trace : WireCardinalityDoublingTrace.ValidFrom wire.start_budget
    wire.max_width wire.frontiers
  terminal : wire.problemDecodes = true
  withinBudget : wire.terminal.node_count ≤
    8 * 2 ^ (wire.start_budget + wire.frontiers.length)
  queryPresent : wire.query.presentIn wire.terminal.state = true
  sameProblem : wire.matchesLast = true

theorem WireCardinalityTaxonomyProductionRun.check_sound
    (wire : WireCardinalityTaxonomyProductionRun) (hcheck : wire.check = true) :
    wire.Accepted := by
  simp only [WireCardinalityTaxonomyProductionRun.check,
    WireCardinalityTaxonomyProductionRun.terminalAccepted,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨wire.trace.check_sound hcheck.1.2, hcheck.2.1.1.1,
    hcheck.2.1.1.2, hcheck.2.1.2, hcheck.2.2⟩

#print axioms WireCardinalityTaxonomyProductionRun.check_sound

end ContextCalculus.Hypertableau
