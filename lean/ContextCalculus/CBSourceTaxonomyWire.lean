import ContextCalculus.CBSourceWire
import ContextCalculus.CBTaxonomyWire

/-!
# Source-bound exact CB taxonomy publication

This is the joint publication boundary for a CB taxonomy.  It accepts the
typed normalized source, its exact verified clause encoding, and a complete
positive-or-countermodel taxonomy matrix only when both documents have the
same symbol bounds and the same decoded clause list.  Consequently every
published bit denotes the semantics of the typed source ontology.
-/

namespace ContextCalculus.CBSourceTaxonomyWire

open Lean ContextCalculus Eqv
open ContextCalculus.CBSourceWire
open ContextCalculus.CBTaxonomyWire
open ContextCalculus.CBRoleChainEncoding

structure WireSourceTaxonomy where
  version : Nat
  source : WireSourceBinding
  taxonomy : WireTaxonomy
deriving FromJson, ToJson

structure DecodedSourceTaxonomy where
  source : DecodedSourceBinding
  taxonomy : DecodedTaxonomy
  same_bounds : taxonomy.bounds = source.bounds
  same_ontology : taxonomy.ontology = source.ontology

def WireSourceTaxonomy.decode (wire : WireSourceTaxonomy) :
    Except String DecodedSourceTaxonomy := do
  if wire.version != 1 then
    throw s!"unsupported source-bound CB taxonomy version {wire.version}"
  let source ← wire.source.decode
  let taxonomy ← wire.taxonomy.decode
  if hbounds : taxonomy.bounds = source.bounds then
    if hontology : taxonomy.ontology = source.ontology then
      return DecodedSourceTaxonomy.mk source taxonomy hbounds hontology
    else throw "CB taxonomy clause list differs from its verified source binding"
  else throw "CB taxonomy symbol bounds differ from its verified source binding"

def WireSourceTaxonomy.check (wire : WireSourceTaxonomy) : Except String Bool := do
  let _ ← wire.decode
  return true

private def DecodedSourceTaxonomy.asSourceConcept
    (decoded : DecodedSourceTaxonomy)
    (concept : Nat) (inBounds : concept < decoded.taxonomy.bounds.concepts) :
    Fin decoded.source.bounds.concepts :=
  ⟨concept, by rw [← decoded.same_bounds]; exact inBounds⟩

def DecodedSourceTaxonomy.SourceEntails
    (decoded : DecodedSourceTaxonomy)
    (cell : DecodedCell decoded.taxonomy.bounds decoded.taxonomy.ontology) : Prop :=
  let sub := decoded.asSourceConcept cell.coreConcept cell.core_in_bounds
  let sup := decoded.asSourceConcept cell.superconcept cell.super_in_bounds
  ∀ (D : Type)
    (interpretation : Eqv.Interp D (Fin decoded.source.bounds.concepts)
      (Fin decoded.source.bounds.roles) (Fin decoded.source.bounds.individuals)),
    CBRoleChainEncoding.models interpretation decoded.source.source → ∀ element,
      interpretation.c sub element → interpretation.c sup element

theorem DecodedSourceTaxonomy.cell_exact
    (decoded : DecodedSourceTaxonomy)
    (cell : DecodedCell decoded.taxonomy.bounds decoded.taxonomy.ontology) :
    cell.answer = true ↔ decoded.SourceEntails cell := by
  let sub := decoded.asSourceConcept cell.coreConcept cell.core_in_bounds
  let sup := decoded.asSourceConcept cell.superconcept cell.super_in_bounds
  have ontology_entails (core superconcept : Nat) :
      Entails decoded.taxonomy.ontology core superconcept ↔
        Entails decoded.source.ontology core superconcept := by
    rw [decoded.same_ontology]
  apply cell.exact.trans
  apply (ontology_entails cell.coreConcept cell.superconcept).trans
  change decoded.source.Entails sub sup ↔ decoded.SourceEntails cell
  exact decoded.source.entails_iff_source sub sup

/-- Every bit in an accepted source-bound taxonomy is exactly the semantic
answer for the corresponding typed normalized source query. -/
theorem DecodedSourceTaxonomy.publishes_source_exactly
    (decoded : DecodedSourceTaxonomy)
    (index : Fin decoded.taxonomy.cells.length) :
    decoded.taxonomy.published.get
      ⟨index, by simp [DecodedTaxonomy.published]⟩ = true ↔
      decoded.SourceEntails (decoded.taxonomy.cells.get index) := by
  have hanswer : decoded.taxonomy.published.get
      ⟨index, by simp [DecodedTaxonomy.published]⟩ =
      (decoded.taxonomy.cells.get index).answer := by
    simp [DecodedTaxonomy.published]
  rw [hanswer]
  exact decoded.cell_exact (decoded.taxonomy.cells.get index)

theorem WireSourceTaxonomy.check_sound (wire : WireSourceTaxonomy)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceTaxonomy,
      wire.decode = .ok decoded ∧
        ∀ index : Fin decoded.taxonomy.cells.length,
          decoded.taxonomy.published.get
            ⟨index, by simp [DecodedTaxonomy.published]⟩ = true ↔
          decoded.SourceEntails (decoded.taxonomy.cells.get index) := by
  cases hdecode : wire.decode with
  | error message => simp [WireSourceTaxonomy.check, hdecode] at hcheck
  | ok decoded => exact ⟨decoded, rfl, decoded.publishes_source_exactly⟩

private def x : CBTermWire.WireTerm := .var 0
private def concept (id : Nat) : CBTermWire.WireLiteral :=
  .predicate (.concept id x)

private def sourceExample : WireSourceBinding where
  version := 1
  concept_count := 1
  role_count := 0
  function_count := 0
  individual_count := 0
  source_clauses := []
  role_chains := []
  ontology := []

private def taxonomyExample : WireTaxonomy where
  version := 2
  concept_count := 1
  role_count := 0
  function_count := 0
  individual_count := 0
  ontology := []
  concept_names := ["A"]
  named_concepts := [0]
  published := [true]
  public_subsumptions := []
  cells := [{
    core_concept := 0
    superconcept := 0
    answer := true
    evidence := .positive [⟨⟨[], [concept 0]⟩, .core⟩]
  }]

private def acceptedExample : WireSourceTaxonomy :=
  { version := 1, source := sourceExample, taxonomy := taxonomyExample }

private def rejected (result : Except String Bool) : Bool :=
  match result with | .error _ => true | .ok _ => false

example : acceptedExample.check = .ok true := by native_decide

example : rejected ({ acceptedExample with taxonomy :=
    { taxonomyExample with ontology := [⟨[], [concept 0]⟩] } }).check = true := by
  native_decide

#print axioms DecodedSourceTaxonomy.cell_exact
#print axioms DecodedSourceTaxonomy.publishes_source_exactly
#print axioms WireSourceTaxonomy.check_sound

end ContextCalculus.CBSourceTaxonomyWire
