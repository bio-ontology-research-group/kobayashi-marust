import ContextCalculus.CBSourceWire
import ContextCalculus.CBStandaloneContextProofWire
import ContextCalculus.CBFiniteModelWire
import ContextCalculus.CBRegularArbitraryChainCountermodelWire
import Mathlib.Data.Finset.Basic

/-!
# Joint source-bound CB taxonomy with shared production proofs

This is the compact production publication boundary. A single chronological
proof DAG establishes all positive clauses, each positive matrix cell cites an
exact node, and every negative cell carries a finite or regular countermodel.
The source binding, proof ontology, matrix coordinates, bits, and public names
are checked together.
-/

namespace ContextCalculus.CBSourceProductionTaxonomyWire

open Lean ContextCalculus CheckerTerm Eqv
open ContextCalculus.CBTermWire ContextCalculus.CBSourceWire
open ContextCalculus.CBStandaloneContextProofWire
open ContextCalculus.CBFiniteModelWire
open ContextCalculus.CBRegularArbitraryChainCountermodelWire
open ContextCalculus.CBRoleChainEncoding

def Entails (ontology : List FCL) (sub sup : Nat) : Prop :=
  ∀ (D : Type) (model : TModel D),
    (∀ clause ∈ ontology, valid model clause) →
    ∀ element, model.conc sub element → model.conc sup element

inductive WireCellEvidence where
  | positiveNode (node : Nat)
  | negative (witness : Nat) (model : WireFiniteModel)
  | regularArbitraryChain (model : WireRegularArbitraryChainCountermodel)
deriving FromJson, ToJson

structure WireCell where
  sub : Nat
  sup : Nat
  answer : Bool
  evidence : WireCellEvidence
deriving FromJson, ToJson

structure WireSubsumption where
  sub : String
  sup : String
deriving DecidableEq, FromJson, ToJson, Repr

structure DecodedCell (source : DecodedSourceBinding)
    (proof : DecodedStandaloneProof source.ontology) where
  sub : Nat
  sub_in_bounds : sub < source.bounds.concepts
  sup : Nat
  sup_in_bounds : sup < source.bounds.concepts
  answer : Bool
  exact : answer = true ↔ Entails source.ontology sub sup

private def queryCore (sub : Nat) : List FPred :=
  [.concept sub (.var 0)]

private def targetClause (sup : Nat) : FCL :=
  ⟨[], [.P (.concept sup (.var 0))]⟩

private def bottomClause : FCL := ⟨[], []⟩

private theorem entails_of_node_target
    (node : DecodedStandaloneNode ontology)
    (sub sup : Nat)
    (hcore : node.core = queryCore sub)
    (htarget : node.clause = targetClause sup) :
    Entails ontology sub sup := by
  intro D model hontology element hsub
  let assignment : Int → D := fun _ => element
  have hquery : ∀ predicate ∈ node.core,
      model.evalL assignment (.P predicate) := by
    rw [hcore]
    intro predicate hpredicate
    simp only [queryCore, List.mem_singleton] at hpredicate
    subst predicate
    exact hsub
  have hvalid := node.contextValid model hontology assignment hquery
  rw [htarget] at hvalid
  have hhead := hvalid (by intro literal hliteral; cases hliteral)
  obtain ⟨literal, hliteral, heval⟩ := hhead
  simp only [targetClause, List.mem_singleton] at hliteral
  subst literal
  exact heval

private theorem entails_of_node_bottom
    (node : DecodedStandaloneNode ontology)
    (sub sup : Nat)
    (hcore : node.core = queryCore sub)
    (hbottom : node.clause = bottomClause) :
    Entails ontology sub sup := by
  intro D model hontology element hsub
  let assignment : Int → D := fun _ => element
  have hquery : ∀ predicate ∈ node.core,
      model.evalL assignment (.P predicate) := by
    rw [hcore]
    intro predicate hpredicate
    simp only [queryCore, List.mem_singleton] at hpredicate
    subst predicate
    exact hsub
  have hvalid := node.contextValid model hontology assignment hquery
  rw [hbottom] at hvalid
  have hfalse := hvalid (by intro literal hliteral; cases hliteral)
  obtain ⟨literal, hliteral, _⟩ := hfalse
  cases hliteral

def WireCell.decode (source : DecodedSourceBinding)
    (proof : DecodedStandaloneProof source.ontology) (wire : WireCell) :
    Except String (DecodedCell source proof) := do
  let sub ← checkId "production taxonomy subclass" source.bounds.concepts wire.sub
  let sup ← checkId "production taxonomy superclass" source.bounds.concepts wire.sup
  if hsub : sub < source.bounds.concepts then
    if hsup : sup < source.bounds.concepts then
      match wire.evidence with
      | .positiveNode index =>
          if wire.answer != true then
            throw "positive production node is paired with a false answer"
          let node ← match proof.nodes[index]? with
            | some node => pure node
            | none => throw "positive production taxonomy node is out of bounds"
          if hcore : node.core = queryCore sub then
            if htarget : node.clause = targetClause sup then
              return {
                sub
                sub_in_bounds := hsub
                sup
                sup_in_bounds := hsup
                answer := true
                exact := ⟨fun _ => entails_of_node_target node sub sup hcore htarget,
                  fun _ => rfl⟩
              }
            else if hbottom : node.clause = bottomClause then
              return {
                sub
                sub_in_bounds := hsub
                sup
                sup_in_bounds := hsup
                answer := true
                exact := ⟨fun _ => entails_of_node_bottom node sub sup hcore hbottom,
                  fun _ => rfl⟩
              }
            else throw "positive production node proves neither target nor contradiction"
          else throw "positive production node uses the wrong query core"
      | .negative witness model =>
          if wire.answer != false then
            throw "negative production evidence is paired with a true answer"
          let countermodel ← (WireCountermodel.mk sub sup witness model).decode
            source.bounds source.ontology
          if hcounterSub : countermodel.coreConcept = sub then
            if hcounterSup : countermodel.superconcept = sup then
              have hnot : ¬ Entails source.ontology sub sup := by
                have hrefute := countermodel.refutes_subsumption
                unfold DecodedCountermodel.Refutes at hrefute
                rw [hcounterSub, hcounterSup] at hrefute
                exact hrefute
              return {
                sub
                sub_in_bounds := hsub
                sup
                sup_in_bounds := hsup
                answer := false
                exact := ⟨by simp, fun h => (hnot h).elim⟩
              }
            else throw "finite countermodel superclass differs after decoding"
          else throw "finite countermodel subclass differs after decoding"
      | .regularArbitraryChain model =>
          if wire.answer != false then
            throw "regular production evidence is paired with a true answer"
          let countermodel ← model.decode source.bounds source.ontology sub sup
          have hnot : ¬ Entails source.ontology sub sup := by
            intro hentails
            rcases countermodel.refutes with
              ⟨D, interpretation, element, hontology, hpositive, hnegative⟩
            exact hnegative (hentails D interpretation hontology element hpositive)
          return {
            sub
            sub_in_bounds := hsub
            sup
            sup_in_bounds := hsup
            answer := false
            exact := ⟨by simp, fun h => (hnot h).elim⟩
          }
    else throw "production taxonomy superclass escaped its checked bound"
  else throw "production taxonomy subclass escaped its checked bound"

def coordinates (named : List Nat) : List (Nat × Nat) :=
  named.flatMap fun sub => named.map fun sup => (sub, sup)

private def conceptName (names : List String) (id : Nat) : String :=
  names[id]?.getD ""

def publicSubsumptions (names : List String)
    (cells : List (DecodedCell source proof)) : List WireSubsumption :=
  cells.filterMap fun cell =>
    if cell.answer && cell.sub != cell.sup then
      some ⟨conceptName names cell.sub, conceptName names cell.sup⟩
    else none

structure WireDocument where
  version : Nat
  source : WireSourceBinding
  proof : WireStandaloneProof
  concept_names : List String
  named_concepts : List Nat
  published : List Bool
  public_subsumptions : List WireSubsumption
  cells : List WireCell
deriving FromJson, ToJson

structure DecodedDocument where
  source : DecodedSourceBinding
  proof : DecodedStandaloneProof source.ontology
  conceptNames : List String
  concept_name_count : conceptNames.length = source.bounds.concepts
  concept_names_nodup : conceptNames.Nodup
  named : List Nat
  publicSubsumptions : List WireSubsumption
  public_subsumptions_nodup : publicSubsumptions.Nodup
  cells : List (DecodedCell source proof)
  published : List Bool
  exact_coordinates : cells.map (fun cell => (cell.sub, cell.sup)) = coordinates named
  exact_bits : cells.map (·.answer) = published
  exact_public : publicSubsumptions.toFinset =
    (CBSourceProductionTaxonomyWire.publicSubsumptions conceptNames cells).toFinset

def WireDocument.decode (wire : WireDocument) : Except String DecodedDocument := do
  if wire.version != 1 then
    throw s!"unsupported source-production taxonomy version {wire.version}"
  let source ← wire.source.decode
  let proof ← wire.proof.decode source.bounds source.ontology
  if hnames : wire.concept_names.length = source.bounds.concepts then
    if hnamesNodup : wire.concept_names.Nodup then
      if _hnamedNodup : wire.named_concepts.Nodup then
        let named ← wire.named_concepts.mapM
          (checkId "source-production named concept" source.bounds.concepts)
        let cells ← wire.cells.mapM (WireCell.decode source proof)
        if hcoordinates : cells.map (fun cell => (cell.sub, cell.sup)) =
            coordinates named then
          if hbits : cells.map (·.answer) = wire.published then
            if hpublicNodup : wire.public_subsumptions.Nodup then
              let expected := publicSubsumptions wire.concept_names cells
              if hpublic : wire.public_subsumptions.toFinset = expected.toFinset then
                return {
                  source
                  proof
                  conceptNames := wire.concept_names
                  concept_name_count := hnames
                  concept_names_nodup := hnamesNodup
                  named
                  publicSubsumptions := wire.public_subsumptions
                  public_subsumptions_nodup := hpublicNodup
                  cells
                  published := wire.published
                  exact_coordinates := hcoordinates
                  exact_bits := hbits
                  exact_public := hpublic
                }
              else throw "source-production public payload differs from checked cells"
            else throw "source-production public payload contains duplicates"
          else throw "source-production publication bits differ from checked cells"
        else throw "source-production cells do not form the complete named matrix"
      else throw "source-production named concept table contains duplicates"
    else throw "source-production concept-name table contains duplicates"
  else throw "source-production concept-name count differs from source bounds"

def WireDocument.check (wire : WireDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

private def DecodedDocument.asSourceConcept (decoded : DecodedDocument)
    (concept : Nat) (hbound : concept < decoded.source.bounds.concepts) :
    Fin decoded.source.bounds.concepts := ⟨concept, hbound⟩

def DecodedDocument.SourceEntails (decoded : DecodedDocument)
    (cell : DecodedCell decoded.source decoded.proof) : Prop :=
  let sub := decoded.asSourceConcept cell.sub cell.sub_in_bounds
  let sup := decoded.asSourceConcept cell.sup cell.sup_in_bounds
  ∀ (D : Type)
    (interpretation : Eqv.Interp D (Fin decoded.source.bounds.concepts)
      (Fin decoded.source.bounds.roles) (Fin decoded.source.bounds.individuals)),
    CBRoleChainEncoding.models interpretation decoded.source.source →
      ∀ element, interpretation.c sub element → interpretation.c sup element

theorem DecodedDocument.cell_source_exact (decoded : DecodedDocument)
    (cell : DecodedCell decoded.source decoded.proof) :
    cell.answer = true ↔ decoded.SourceEntails cell := by
  rw [cell.exact]
  change decoded.source.Entails
      (decoded.asSourceConcept cell.sub cell.sub_in_bounds)
      (decoded.asSourceConcept cell.sup cell.sup_in_bounds) ↔
    decoded.SourceEntails cell
  exact decoded.source.entails_iff_source _ _

theorem DecodedDocument.publishes_source_exactly (decoded : DecodedDocument)
    (index : Fin decoded.cells.length) :
    (decoded.cells.map (·.answer)).get ⟨index, by simp⟩ = true ↔
      decoded.SourceEntails (decoded.cells.get index) := by
  have hanswer : (decoded.cells.map (·.answer)).get ⟨index, by simp⟩ =
      (decoded.cells.get index).answer := by simp
  rw [hanswer]
  exact decoded.cell_source_exact (decoded.cells.get index)

theorem WireDocument.check_sound (wire : WireDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedDocument,
      wire.decode = .ok decoded ∧
      ∀ index : Fin decoded.cells.length,
        (decoded.cells.map (·.answer)).get ⟨index, by simp⟩ = true ↔
          decoded.SourceEntails (decoded.cells.get index) := by
  cases hdecode : wire.decode with
  | error message => simp [WireDocument.check, hdecode] at hcheck
  | ok decoded => exact ⟨decoded, rfl, decoded.publishes_source_exactly⟩

#print axioms DecodedDocument.cell_source_exact
#print axioms DecodedDocument.publishes_source_exactly
#print axioms WireDocument.check_sound

end ContextCalculus.CBSourceProductionTaxonomyWire
