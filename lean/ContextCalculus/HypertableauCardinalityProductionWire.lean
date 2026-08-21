import ContextCalculus.HypertableauCardinalityProductionSearch
import ContextCalculus.HypertableauCardinalityDistinctWire

/-!
# Concrete cardinality production runtime fields

This module checks and decodes the Rust fields that determine logical
cardinality recursion: the distinct equality state, `active_nodes`, and the
branch-local set of expanded `(definition_id, source)` minimum sites.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure FiniteCardinalityRuntimeFields
    (nodeCount conceptCount roleCount variableCount : Nat)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) where
  certificate : FiniteDistinctEqCertificate
    nodeCount conceptCount roleCount variableCount
  activeNodes : Nat
  expandedMinimums : List (IndexedCardinalitySite definitions nodeCount)

def FiniteCardinalityRuntimeFields.check
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions) : Bool :=
  fields.certificate.inactivePrefixFreshB fields.activeNodes &&
    decide fields.expandedMinimums.Nodup &&
    fields.expandedMinimums.all fun site =>
      decide ((definitions.get site.1).kind = .minimum) &&
        decide (site.2.1 < fields.activeNodes)

def FiniteCardinalityRuntimeFields.toConfig
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions)
    (hcheck : fields.check = true) :
    CardinalityRuntimeConfig (Fin conceptCount) (Fin roleCount) definitions nodeCount where
  state := fields.certificate.state
  active := fields.activeNodes
  expanded := fields.expandedMinimums.toFinset
  active_le := by
    simp only [FiniteCardinalityRuntimeFields.check, Bool.and_eq_true] at hcheck
    exact fields.certificate.inactivePrefixFreshB_fit fields.activeNodes hcheck.1.1
  inactive_fresh := by
    simp only [FiniteCardinalityRuntimeFields.check, Bool.and_eq_true] at hcheck
    exact fields.certificate.inactivePrefixFreshB_sound fields.activeNodes hcheck.1.1

@[simp] theorem FiniteCardinalityRuntimeFields.toConfig_state
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions)
    (hcheck : fields.check = true) :
    (fields.toConfig hcheck).state = fields.certificate.state := rfl

@[simp] theorem FiniteCardinalityRuntimeFields.toConfig_active
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions)
    (hcheck : fields.check = true) :
    (fields.toConfig hcheck).active = fields.activeNodes := rfl

@[simp] theorem FiniteCardinalityRuntimeFields.mem_toConfig_expanded
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions)
    (hcheck : fields.check = true)
    (site : IndexedCardinalitySite definitions nodeCount) :
    site ∈ (fields.toConfig hcheck).expanded ↔ site ∈ fields.expandedMinimums := by
  classical
  simp [FiniteCardinalityRuntimeFields.toConfig]

theorem FiniteCardinalityRuntimeFields.expandedMinimums_nodup
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions)
    (hcheck : fields.check = true) : fields.expandedMinimums.Nodup := by
  simp only [FiniteCardinalityRuntimeFields.check, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  exact hcheck.1.2

theorem FiniteCardinalityRuntimeFields.expanded_kind
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions)
    (hcheck : fields.check = true)
    (site : IndexedCardinalitySite definitions nodeCount)
    (hsite : site ∈ fields.expandedMinimums) :
    (definitions.get site.1).kind = .minimum := by
  simp only [FiniteCardinalityRuntimeFields.check, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq] at hcheck
  exact (hcheck.2 site hsite).1

theorem FiniteCardinalityRuntimeFields.expanded_source_lt_active
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions)
    (hcheck : fields.check = true)
    (site : IndexedCardinalitySite definitions nodeCount)
    (hsite : site ∈ fields.expandedMinimums) : site.2.1 < fields.activeNodes := by
  simp only [FiniteCardinalityRuntimeFields.check, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq] at hcheck
  exact (hcheck.2 site hsite).2

structure WireExpandedMinimum where
  definition : Nat
  source : Nat
deriving FromJson, ToJson, Repr

structure WireCardinalityRuntimeFields where
  state : WireDistinctEqState
  active_nodes : Nat
  expanded_minimums : List WireExpandedMinimum
deriving FromJson, ToJson, Repr

def WireCardinalityRuntimeFields.decode
    (wire : WireCardinalityRuntimeFields)
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Except String
      (FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
        definitions) := do
  let certificate ← wire.state.decode nodeCount conceptCount roleCount variableCount ontology
  let expandedMinimums ← wire.expanded_minimums.mapM fun site => do
    return (← checkedFin "expanded minimum definition" definitions.length site.definition,
      ← checkedFin "expanded minimum source" nodeCount site.source)
  return ⟨certificate, wire.active_nodes, expandedMinimums⟩

structure CheckedCardinalityRuntimeFields
    (nodeCount conceptCount roleCount variableCount : Nat)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) where
  fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
    definitions
  valid : fields.check = true

def WireCardinalityRuntimeFields.decodeChecked
    (wire : WireCardinalityRuntimeFields)
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Except String
      (CheckedCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
        definitions) := do
  let fields ← wire.decode nodeCount conceptCount roleCount variableCount ontology definitions
  if hvalid : fields.check = true then
    return ⟨fields, hvalid⟩
  else
    throw "invalid cardinality runtime fields"

theorem CheckedCardinalityRuntimeFields.has_config
    (checked : CheckedCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions) :
    ∃ config : CardinalityRuntimeConfig (Fin conceptCount) (Fin roleCount) definitions nodeCount,
      config = checked.fields.toConfig checked.valid :=
  ⟨_, rfl⟩

#print axioms FiniteCardinalityRuntimeFields.mem_toConfig_expanded
#print axioms FiniteCardinalityRuntimeFields.expandedMinimums_nodup
#print axioms FiniteCardinalityRuntimeFields.expanded_kind
#print axioms FiniteCardinalityRuntimeFields.expanded_source_lt_active
#print axioms CheckedCardinalityRuntimeFields.has_config

end ContextCalculus.Hypertableau
