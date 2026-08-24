import ContextCalculus.CBSourceLocalClosure
import ContextCalculus.CBHyperClosure
import ContextCalculus.CBTermDerivationWire

/-!
# Source-bound Hyper closure

This layer reconstructs the finite term and literal universe directly from the
source-bound production snapshot.  It does not accept candidate lists from
Rust.  Lean enumerates all source substitutions and all maximal retained
providers, constructs every Hyper conclusion, and requires a retained
strengthening.
-/

namespace ContextCalculus.CBSourceHyperClosure

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBSourceLiveInsertionDerivation
open ContextCalculus.CBSourceLocalClosure
open ContextCalculus.CBHyperClosure
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBFiniteModel
open ContextCalculus.CBPredEnumeration
open ContextCalculus.CBFiniteTermOrderWire
open ContextCalculus.CBFiniteLiteralOrderWire

def sourceProductionTerms
    (production : DecodedProductionRun) : List FTerm :=
  ((production.source.ontology.flatMap clauseTerms) ++
    (production.contexts.flatMap fun context =>
      context.retained.flatMap clauseTerms) ++
    (List.range production.source.bounds.individuals).map FTerm.const).eraseDups

def sourceProductionLiterals
    (production : DecodedProductionRun) : List FLit :=
  ((production.source.ontology.flatMap clauseLiterals) ++
    (production.contexts.flatMap fun context =>
      context.retained.flatMap clauseLiterals)).eraseDups

structure WireSourceFiniteOrder where
  ordered_terms : List WireTerm
  ordered_literals : List WireLiteral
deriving FromJson, ToJson

structure DecodedSourceFiniteOrder
    (production : DecodedProductionRun) where
  orderedTerms : List FTerm
  orderedLiterals : List FLit
  terms_nodup : orderedTerms.Nodup
  literals_nodup : orderedLiterals.Nodup
  terms_exact : orderedTerms.toFinset =
    (sourceProductionTerms production).toFinset
  literals_exact : orderedLiterals.toFinset =
    (sourceProductionLiterals production).toFinset

def WireSourceFiniteOrder.decode (production : DecodedProductionRun)
    (wire : WireSourceFiniteOrder) :
    Except String (DecodedSourceFiniteOrder production) := do
  let orderedTerms ← wire.ordered_terms.mapM
    (WireTerm.decode production.bounds)
  let orderedLiterals ← wire.ordered_literals.mapM
    (WireLiteral.decode production.bounds)
  if htermsNodup : orderedTerms.Nodup then
    if hliteralsNodup : orderedLiterals.Nodup then
      if htermsExact : orderedTerms.toFinset =
          (sourceProductionTerms production).toFinset then
        if hliteralsExact : orderedLiterals.toFinset =
            (sourceProductionLiterals production).toFinset then
          return {
            orderedTerms
            orderedLiterals
            terms_nodup := htermsNodup
            literals_nodup := hliteralsNodup
            terms_exact := htermsExact
            literals_exact := hliteralsExact
          }
        else throw "source-bound CB literal order omits or invents a literal"
      else throw "source-bound CB term order omits or invents a term"
    else throw "source-bound CB literal order contains a duplicate"
  else throw "source-bound CB term order contains a duplicate"

def DecodedSourceFiniteOrder.rank
    (order : DecodedSourceFiniteOrder production) (literal : FLit) : Nat :=
  order.orderedLiterals.idxOf literal

def DecodedSourceFiniteOrder.maximalHeadIndices
    (order : DecodedSourceFiniteOrder production) (head : List FLit) : List Nat :=
  (List.range head.length).filter fun index =>
    match head[index]? with
    | none => false
    | some literal => head.all fun other => order.rank other ≤ order.rank literal

def maximalProvidersFor
    (order : DecodedSourceFiniteOrder production)
    (retained : List FCL) (literal : FLit) : List ProviderLocation :=
  (List.range retained.length).flatMap fun clauseIndex =>
    match retained[clauseIndex]? with
    | none => []
    | some provider =>
        ((order.maximalHeadIndices provider.head).filter fun headIndex =>
          decide (provider.head[headIndex]? = some literal)).map fun headIndex =>
            (clauseIndex, headIndex)

def providerSelections
    (order : DecodedSourceFiniteOrder production)
    (retained : List FCL) (body : List FLit) :
    List (List ProviderLocation) :=
  cartesianSelections (body.map (maximalProvidersFor order retained))

def hyperCandidates (order : DecodedSourceFiniteOrder production)
    (retained source : List FCL) : List FCL :=
  source.flatMap fun sourceClause =>
    (substitutions order.orderedTerms sourceClause).flatMap fun substitution =>
      let instantiated := substCl substitution sourceClause
      (providerSelections order retained instantiated.body).filterMap fun selection =>
        hyperCandidate? retained sourceClause substitution selection

theorem hyperCandidates_sound {D : Type} (model : TModel D)
    (assignment : Int → D) (order : DecodedSourceFiniteOrder production)
    (retained source : List FCL)
    (hsource : ∀ clause ∈ source, valid model clause)
    (hretained : ∀ clause ∈ retained, HoldsAt model assignment clause) :
    ∀ conclusion ∈ hyperCandidates order retained source,
      HoldsAt model assignment conclusion := by
  intro conclusion hconclusion
  simp only [hyperCandidates, List.mem_flatMap, List.mem_filterMap] at hconclusion
  obtain ⟨sourceClause, hsourceClause, substitution, _hsubstitution,
    selection, _hselection, hcandidate⟩ := hconclusion
  exact hyperCandidate_sound model assignment retained sourceClause substitution
    selection conclusion hcandidate (hsource sourceClause hsourceClause) hretained

def sourceHyperClosedB (order : DecodedSourceFiniteOrder production)
    (context : DecodedProductionContext production.bounds
      production.source.ontology) : Bool :=
  (hyperCandidates order context.retained production.source.ontology).all
    (hasStrengthening context.retained)

theorem sourceHyperClosedB_sound
    (order : DecodedSourceFiniteOrder production)
    (context : DecodedProductionContext production.bounds
      production.source.ontology)
    (hclosed : sourceHyperClosedB order context = true) :
    ∀ candidate ∈ hyperCandidates order context.retained
        production.source.ontology,
      ∃ clause ∈ context.retained, Strengthens clause candidate := by
  intro candidate hcandidate
  have h := List.all_eq_true.mp hclosed candidate hcandidate
  exact (hasStrengthening_eq_true_iff context.retained candidate).mp h

structure WireSourceHyperClosureDocument where
  version : Nat
  local_closure : WireSourceLocalClosureDocument
  order : WireSourceFiniteOrder
deriving FromJson, ToJson

structure DecodedSourceHyperClosureDocument where
  localClosure : DecodedSourceLocalClosureDocument
  order : DecodedSourceFiniteOrder localClosure.live.production
  hyper_closed : ∀ context ∈ localClosure.live.production.contexts,
    sourceHyperClosedB order context = true

def WireSourceHyperClosureDocument.decode
    (wire : WireSourceHyperClosureDocument) :
    Except String DecodedSourceHyperClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported source-bound CB Hyper-closure version {wire.version}"
  let localClosure ← wire.local_closure.decode
  let order ← wire.order.decode localClosure.live.production
  if hclosed : ∀ context ∈ localClosure.live.production.contexts,
      sourceHyperClosedB order context = true then
    return { localClosure, order, hyper_closed := hclosed }
  else throw "source-bound CB terminal state is not Hyper-closed"

def WireSourceHyperClosureDocument.check
    (wire : WireSourceHyperClosureDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedSourceHyperClosureDocument.complete_coverage
    (decoded : DecodedSourceHyperClosureDocument) :
    ∀ context ∈ decoded.localClosure.live.production.contexts,
      ∀ candidate ∈ hyperCandidates decoded.order context.retained
          decoded.localClosure.live.production.source.ontology,
        ∃ clause ∈ context.retained, Strengthens clause candidate := by
  intro context hcontext
  exact sourceHyperClosedB_sound decoded.order context
    (decoded.hyper_closed context hcontext)

theorem WireSourceHyperClosureDocument.check_sound
    (wire : WireSourceHyperClosureDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceHyperClosureDocument,
      wire.decode = .ok decoded ∧
      ∀ context ∈ decoded.localClosure.live.production.contexts,
        ∀ candidate ∈ hyperCandidates decoded.order context.retained
            decoded.localClosure.live.production.source.ontology,
          ∃ clause ∈ context.retained, Strengthens clause candidate := by
  cases hdecode : wire.decode with
  | error message => simp [WireSourceHyperClosureDocument.check, hdecode] at hcheck
  | ok decoded => exact ⟨decoded, rfl, decoded.complete_coverage⟩

#print axioms hyperCandidates_sound
#print axioms sourceHyperClosedB_sound
#print axioms WireSourceHyperClosureDocument.check_sound

end ContextCalculus.CBSourceHyperClosure
