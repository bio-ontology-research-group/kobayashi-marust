import ContextCalculus.CBLiveTaxonomyPublication
import ContextCalculus.CBFiniteModelWire
import ContextCalculus.CBBlockedTaxonomyCountermodelWire
import ContextCalculus.CBRegularALCCountermodelWire
import ContextCalculus.CBRegularRoleCountermodelWire
import ContextCalculus.CBRegularNominalCountermodelWire
import ContextCalculus.CBRegularCardinalityCountermodelWire
import ContextCalculus.CBRegularFreshCardinalityCountermodelWire

/-!
# Exact production-bound CB taxonomy publication

This capstone extends the checked live publication to every materialized query
cell. Positive cells reuse the production insertion proof rather than carrying
a duplicate standalone trace. Reflexive cells are discharged directly;
bottom rows reuse their checked contradiction; and every remaining negative
cell carries a checked countermodel. The row-major coordinate and answer lists
must cover exactly the concepts represented by live query contexts.

Explicit finite tables and query-augmented blocked equality quotients are sound
negative evidence forms. Full SROIQ does not have the finite-model property, so
a regular/infinite blocked model constructor must still be added before this
checker can certify every possible production run.
-/

namespace ContextCalculus.CBLiveExactTaxonomyPublication

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBGlobalClosureWire
open ContextCalculus.CBLiveTaxonomyPublication
open ContextCalculus.CBFiniteModelWire
open ContextCalculus.CBBlockedTaxonomyCountermodelWire
open ContextCalculus.CBRegularALCCountermodelWire
open ContextCalculus.CBRegularRoleCountermodelWire
open ContextCalculus.CBRegularNominalCountermodelWire
open ContextCalculus.CBRegularCardinalityCountermodelWire
open ContextCalculus.CBRegularFreshCardinalityCountermodelWire
open ContextCalculus.CBBlockedCarrierWire
open ContextCalculus.CBBlockedGroundSaturationWire
open ContextCalculus.CBTermWire

inductive WireExactCellEvidence where
  | reflexive
  | positive (live_index : Nat)
  | unsatisfiable (live_index : Nat)
  | negative (witness : Nat) (model : WireFiniteModel)
  | blocked (countermodel : WireBlockedTaxonomyCountermodel)
  | regularALC (countermodel : WireRegularALCCountermodel)
  | regularRole (countermodel : WireRegularRoleCountermodel)
  | regularNominal (countermodel : WireRegularNominalCountermodel)
  | regularCardinality (countermodel : WireRegularCardinalityCountermodel)
  | regularFreshCardinality
      (countermodel : WireRegularFreshCardinalityCountermodel)
  | unresolved
deriving FromJson, ToJson

structure WireExactCell where
  sub : Nat
  sup : Nat
  answer : Bool
  evidence : WireExactCellEvidence
deriving FromJson, ToJson

structure WireLiveExactTaxonomyPublication where
  version : Nat
  live : WireLiveTaxonomyPublication
  named_concepts : List Nat
  published : List Bool
  cells : List WireExactCell
deriving FromJson, ToJson

def liveNamedConcepts (live : DecodedLiveTaxonomyPublication) : List Nat :=
  live.derivation.live.contexts.filterMap fun context =>
    ((rProduction live.derivation.live.global.global.rsucc).contexts.get
      context.contextIndex).queryConcept

def coordinates (named : List Nat) : List (Nat × Nat) :=
  named.flatMap fun sub => named.map fun sup => (sub, sup)

def productionOf (live : DecodedLiveTaxonomyPublication) :=
  rProduction live.derivation.live.global.global.rsucc

def ExactEntails (live : DecodedLiveTaxonomyPublication)
    (sub sup : Nat) : Prop :=
  ∀ (D : Type) (model : TModel D),
    (∀ source ∈ (productionOf live).source.ontology, valid model source) →
    ∀ element, model.conc sub element → model.conc sup element

def SourceExactEntails (live : DecodedLiveTaxonomyPublication)
    (sub sup : Fin (productionOf live).source.bounds.concepts) : Prop :=
  ∀ (D : Type)
    (interpretation : Eqv.Interp D
      (Fin (productionOf live).source.bounds.concepts)
      (Fin (productionOf live).source.bounds.roles)
      (Fin (productionOf live).source.bounds.individuals)),
    CBRoleChainEncoding.models interpretation (productionOf live).source.source →
    ∀ element, interpretation.c sub element → interpretation.c sup element

structure DecodedExactCell (live : DecodedLiveTaxonomyPublication) where
  sub : Nat
  sub_in_bounds : sub < (productionOf live).source.bounds.concepts
  sup : Nat
  sup_in_bounds : sup < (productionOf live).source.bounds.concepts
  answer : Bool
  exact : answer = true ↔ ExactEntails live sub sup

theorem DecodedExactCell.source_exact
    (cell : DecodedExactCell live) :
    cell.answer = true ↔ SourceExactEntails live
      ⟨cell.sub, cell.sub_in_bounds⟩ ⟨cell.sup, cell.sup_in_bounds⟩ := by
  rw [cell.exact]
  let source := (productionOf live).source
  have hsemantic := source.entails_iff_source
    ⟨cell.sub, cell.sub_in_bounds⟩ ⟨cell.sup, cell.sup_in_bounds⟩
  simpa [ExactEntails, SourceExactEntails,
    ContextCalculus.CBSourceWire.DecodedSourceBinding.Entails, productionOf]
    using hsemantic

def WireExactCell.decode (live : DecodedLiveTaxonomyPublication)
    (wire : WireExactCell) : Except String (DecodedExactCell live) := do
  let production := productionOf live
  if hsub : wire.sub < production.source.bounds.concepts then
    if hsup : wire.sup < production.source.bounds.concepts then
      match wire.evidence with
      | .reflexive =>
          if hanswer : wire.answer = true then
            if heq : wire.sub = wire.sup then
              return {
                sub := wire.sub
                sub_in_bounds := hsub
                sup := wire.sup
                sup_in_bounds := hsup
                answer := wire.answer
                exact := by
                  constructor
                  · intro _ D model hontology element hholds
                    simpa [heq] using hholds
                  · intro _
                    exact hanswer
              }
            else throw "reflexive CB taxonomy evidence names different concepts"
          else throw "reflexive CB taxonomy evidence is paired with a false answer"
      | .positive liveIndex =>
          if hanswer : wire.answer = true then
            if hindex : liveIndex < live.publicSubsumptions.length then
              let positive := live.publicSubsumptions.get ⟨liveIndex, hindex⟩
              if hpositiveSub : positive.sub.val = wire.sub then
                if hpositiveSup : positive.sup.val = wire.sup then
                  return {
                    sub := wire.sub
                    sub_in_bounds := hsub
                    sup := wire.sup
                    sup_in_bounds := hsup
                    answer := wire.answer
                    exact := by
                      constructor
                      · intro _ D model hontology element hsubTrue
                        have hresult := positive.entails D model hontology element
                          (hpositiveSub.symm ▸ hsubTrue)
                        exact hpositiveSup ▸ hresult
                      · intro _
                        exact hanswer
                  }
                else throw "live positive CB evidence names a different superclass"
              else throw "live positive CB evidence names a different subclass"
            else throw "live positive CB evidence index is outside the publication"
          else throw "live positive CB evidence is paired with a false answer"
      | .unsatisfiable liveIndex =>
          if hanswer : wire.answer = true then
            if hindex : liveIndex < live.unsatisfiable.length then
              let bottom := live.unsatisfiable.get ⟨liveIndex, hindex⟩
              if hbottomSub : bottom.sub.val = wire.sub then
                return {
                  sub := wire.sub
                  sub_in_bounds := hsub
                  sup := wire.sup
                  sup_in_bounds := hsup
                  answer := wire.answer
                  exact := by
                    constructor
                    · intro _ D model hontology element hsubTrue
                      exact (bottom.refutes D model hontology element
                        (hbottomSub.symm ▸ hsubTrue)).elim
                    · intro _
                      exact hanswer
                }
              else throw "live unsatisfiable CB evidence names a different subclass"
            else throw "live unsatisfiable CB evidence index is outside the publication"
          else throw "live unsatisfiable CB evidence is paired with a false answer"
      | .negative witness model =>
          if hanswer : wire.answer = false then
            let countermodelWire : WireCountermodel := {
              core_concept := wire.sub
              superconcept := wire.sup
              witness
              model
            }
            let countermodel ← countermodelWire.decode
              production.source.bounds production.source.ontology
            if hcore : countermodel.coreConcept = wire.sub then
              if hsuper : countermodel.superconcept = wire.sup then
                have hnot : ¬ExactEntails live wire.sub wire.sup := by
                  intro hentails
                  apply countermodel.refutes_subsumption
                  intro D model hontology element hcoreTrue
                  have hresult := hentails D model hontology element
                    (hcore ▸ hcoreTrue)
                  exact hsuper.symm ▸ hresult
                return {
                  sub := wire.sub
                  sub_in_bounds := hsub
                  sup := wire.sup
                  sup_in_bounds := hsup
                  answer := wire.answer
                  exact := by
                    constructor
                    · intro htrue
                      simp [hanswer] at htrue
                    · intro hentails
                      exact (hnot hentails).elim
                }
              else throw "decoded CB countermodel names a different superclass"
            else throw "decoded CB countermodel names a different subclass"
          else throw "negative CB taxonomy evidence is paired with a true answer"
      | .blocked countermodelWire =>
          if hanswer : wire.answer = false then
            let countermodel ← countermodelWire.decode
              live.derivation.live.global.blocked.carrier wire.sub wire.sup
            if hcounterSub : countermodel.sub.val = wire.sub then
              if hcounterSup : countermodel.sup.val = wire.sup then
                have hnot : ¬ExactEntails live wire.sub wire.sup := by
                  intro hentails
                  obtain ⟨D, interpretation, element, hsource, hcore, hsuper⟩ :=
                    countermodel.refutes
                  let blockedBinding :=
                    (productionRun live.derivation.live.global.blocked.carrier.admissibility).source
                  let model := CBRoleChainEncoding.extendModel
                    (blockedSource live.derivation.live.global.blocked.carrier)
                    interpretation hsource element
                  have hblockedValid : ∀ clause ∈ blockedBinding.ontology,
                      valid model clause := by
                    rw [blockedBinding.exact_encoding]
                    exact CBRoleChainEncoding.models_extend
                      (blockedSource live.derivation.live.global.blocked.carrier)
                      interpretation hsource element
                  have hproductionValid : ∀ clause ∈ production.source.ontology,
                      valid model clause := by
                    change ∀ clause ∈
                      (rProduction live.derivation.live.global.global.rsucc).source.ontology,
                      valid model clause
                    rw [live.derivation.live.global.source_ontology_eq]
                    simpa [blockedBinding] using hblockedValid
                  have hcoreModel : model.conc wire.sub element := by
                    have hcoreModel' : model.conc countermodel.sub.val element := by
                      simpa [model, CBRoleChainEncoding.extendModel] using hcore
                    exact hcounterSub ▸ hcoreModel'
                  have hsuperModel := hentails D model hproductionValid element hcoreModel
                  have hsuperModel' : model.conc countermodel.sup.val element :=
                    hcounterSup.symm ▸ hsuperModel
                  have hsuperInterpretation : interpretation.c countermodel.sup element := by
                    simpa [model, CBRoleChainEncoding.extendModel] using hsuperModel'
                  exact hsuper hsuperInterpretation
                return {
                  sub := wire.sub
                  sub_in_bounds := hsub
                  sup := wire.sup
                  sup_in_bounds := hsup
                  answer := wire.answer
                  exact := by
                    constructor
                    · intro htrue
                      simp [hanswer] at htrue
                    · intro hentails
                      exact (hnot hentails).elim
                }
              else throw "blocked CB countermodel names a different superclass"
            else throw "blocked CB countermodel names a different subclass"
          else throw "blocked CB taxonomy countermodel is paired with a true answer"
      | .regularALC countermodelWire =>
          if hanswer : wire.answer = false then
            let countermodel ← countermodelWire.decode production.source.bounds
              production.source.ontology wire.sub wire.sup
            have hnot : ¬ExactEntails live wire.sub wire.sup := by
              intro hentails
              obtain ⟨D, model, element, hsource, hcore, hsuper⟩ :=
                countermodel.refutes
              exact hsuper (hentails D model hsource element hcore)
            return {
              sub := wire.sub
              sub_in_bounds := hsub
              sup := wire.sup
              sup_in_bounds := hsup
              answer := wire.answer
              exact := by
                constructor
                · intro htrue
                  simp [hanswer] at htrue
                · intro hentails
                  exact (hnot hentails).elim
            }
          else throw "regular ALC CB countermodel is paired with a true answer"
      | .regularRole countermodelWire =>
          if hanswer : wire.answer = false then
            let countermodel ← countermodelWire.decode production.source.bounds
              production.source.ontology wire.sub wire.sup
            have hnot : ¬ExactEntails live wire.sub wire.sup := by
              intro hentails
              obtain ⟨D, model, element, hsource, hcore, hsuper⟩ :=
                countermodel.refutes
              exact hsuper (hentails D model hsource element hcore)
            return {
              sub := wire.sub
              sub_in_bounds := hsub
              sup := wire.sup
              sup_in_bounds := hsup
              answer := wire.answer
              exact := by
                constructor
                · intro htrue
                  simp [hanswer] at htrue
                · intro hentails
                  exact (hnot hentails).elim
            }
          else throw "regular-role CB countermodel is paired with a true answer"
      | .regularNominal countermodelWire =>
          if hanswer : wire.answer = false then
            let countermodel ← countermodelWire.decode production.source.bounds
              production.source.ontology wire.sub wire.sup
            have hnot : ¬ExactEntails live wire.sub wire.sup := by
              intro hentails
              obtain ⟨D, model, element, hsource, hcore, hsuper⟩ :=
                countermodel.refutes
              exact hsuper (hentails D model hsource element hcore)
            return {
              sub := wire.sub
              sub_in_bounds := hsub
              sup := wire.sup
              sup_in_bounds := hsup
              answer := wire.answer
              exact := by
                constructor
                · intro htrue
                  simp [hanswer] at htrue
                · intro hentails
                  exact (hnot hentails).elim
            }
          else throw "regular-nominal CB countermodel is paired with a true answer"
      | .regularCardinality countermodelWire =>
          if hanswer : wire.answer = false then
            let countermodel ← countermodelWire.decode production.source.bounds
              production.source.ontology wire.sub wire.sup
            have hnot : ¬ExactEntails live wire.sub wire.sup := by
              intro hentails
              obtain ⟨D, model, element, hsource, hcore, hsuper⟩ :=
                countermodel.refutes
              exact hsuper (hentails D model hsource element hcore)
            return {
              sub := wire.sub
              sub_in_bounds := hsub
              sup := wire.sup
              sup_in_bounds := hsup
              answer := wire.answer
              exact := by
                constructor
                · intro htrue
                  simp [hanswer] at htrue
                · intro hentails
                  exact (hnot hentails).elim
            }
          else throw "regular-cardinality CB countermodel is paired with a true answer"
      | .regularFreshCardinality countermodelWire =>
          if hanswer : wire.answer = false then
            let countermodel ← countermodelWire.decode production.source.bounds
              production.source.ontology wire.sub wire.sup
            have hnot : ¬ExactEntails live wire.sub wire.sup := by
              intro hentails
              obtain ⟨D, model, element, hsource, hcore, hsuper⟩ :=
                countermodel.refutes
              exact hsuper (hentails D model hsource element hcore)
            return {
              sub := wire.sub
              sub_in_bounds := hsub
              sup := wire.sup
              sup_in_bounds := hsup
              answer := wire.answer
              exact := by
                constructor
                · intro htrue
                  simp [hanswer] at htrue
                · intro hentails
                  exact (hnot hentails).elim
            }
          else
            throw "fresh-cardinality CB countermodel is paired with a true answer"
      | .unresolved =>
          throw "exact CB taxonomy cell has unresolved negative evidence"
    else throw "exact CB taxonomy superclass is outside the source signature"
  else throw "exact CB taxonomy subclass is outside the source signature"

structure DecodedLiveExactTaxonomyPublication where
  live : DecodedLiveTaxonomyPublication
  named : List Nat
  named_nodup : named.Nodup
  named_exact : named.toFinset = (liveNamedConcepts live).toFinset
  cells : List (DecodedExactCell live)
  coordinates_exact : cells.map (fun cell => (cell.sub, cell.sup)) =
    coordinates named
  wirePublished : List Bool
  answers_exact : cells.map (·.answer) = wirePublished

def DecodedLiveExactTaxonomyPublication.published
    (decoded : DecodedLiveExactTaxonomyPublication) : List Bool :=
  decoded.cells.map (·.answer)

def WireLiveExactTaxonomyPublication.decode
    (wire : WireLiveExactTaxonomyPublication) :
    Except String DecodedLiveExactTaxonomyPublication := do
  if wire.version != 1 then
    throw s!"unsupported live exact CB taxonomy-publication version {wire.version}"
  let live ← wire.live.decode
  if hnamedNodup : wire.named_concepts.Nodup then
    if hnamedExact : wire.named_concepts.toFinset =
        (liveNamedConcepts live).toFinset then
      let cells ← wire.cells.mapM (WireExactCell.decode live)
      if hcoordinates : cells.map (fun cell => (cell.sub, cell.sup)) =
          coordinates wire.named_concepts then
        if hanswers : cells.map (·.answer) = wire.published then
          return {
            live
            named := wire.named_concepts
            named_nodup := hnamedNodup
            named_exact := hnamedExact
            cells
            coordinates_exact := hcoordinates
            wirePublished := wire.published
            answers_exact := hanswers
          }
        else throw "exact CB taxonomy publication bits differ from their evidence"
      else throw "exact CB taxonomy cells do not form the complete query matrix"
    else throw "exact CB taxonomy concepts differ from the materialized query contexts"
  else throw "exact CB taxonomy concept list contains duplicates"

def WireLiveExactTaxonomyPublication.check
    (wire : WireLiveExactTaxonomyPublication) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedLiveExactTaxonomyPublication.cell_exact
    (decoded : DecodedLiveExactTaxonomyPublication)
    (index : Fin decoded.cells.length) :
    (decoded.cells.get index).answer = true ↔
      ExactEntails decoded.live (decoded.cells.get index).sub
        (decoded.cells.get index).sup := by
  exact (decoded.cells.get index).exact

theorem DecodedLiveExactTaxonomyPublication.cell_source_exact
    (decoded : DecodedLiveExactTaxonomyPublication)
    (index : Fin decoded.cells.length) :
    (decoded.cells.get index).answer = true ↔
      SourceExactEntails decoded.live
        ⟨(decoded.cells.get index).sub, (decoded.cells.get index).sub_in_bounds⟩
        ⟨(decoded.cells.get index).sup, (decoded.cells.get index).sup_in_bounds⟩ :=
  (decoded.cells.get index).source_exact

theorem WireLiveExactTaxonomyPublication.check_sound
    (wire : WireLiveExactTaxonomyPublication) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedLiveExactTaxonomyPublication,
      wire.decode = .ok decoded ∧
      decoded.named.toFinset = (liveNamedConcepts decoded.live).toFinset ∧
      decoded.cells.map (fun cell => (cell.sub, cell.sup)) =
        coordinates decoded.named ∧
      ∀ index : Fin decoded.cells.length,
        (decoded.cells.get index).answer = true ↔
          ExactEntails decoded.live (decoded.cells.get index).sub
            (decoded.cells.get index).sup := by
  cases hdecode : wire.decode with
  | error message =>
      simp [WireLiveExactTaxonomyPublication.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.named_exact, decoded.coordinates_exact,
        decoded.cell_exact⟩

#print axioms DecodedLiveExactTaxonomyPublication.cell_exact
#print axioms DecodedLiveExactTaxonomyPublication.cell_source_exact
#print axioms WireLiveExactTaxonomyPublication.check_sound

end ContextCalculus.CBLiveExactTaxonomyPublication
