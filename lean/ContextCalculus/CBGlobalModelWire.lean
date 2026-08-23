import ContextCalculus.CBGlobalClosureWire
import ContextCalculus.CBBlockedGroundSaturationWire

/-!
# Globally closed CB run with an independent blocked model certificate

This joins the globally closed production run to the finite blocked grounding.
Both branches must use the same source, terminal contexts, and admissible order.
When the complete finite ground saturation has no empty clause, the accepted
document constructs a model of the exact source ontology.
-/

namespace ContextCalculus.CBGlobalModelWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBGlobalClosureWire
open ContextCalculus.CBBlockedCarrierWire
open ContextCalculus.CBBlockedGroundSaturationWire
open ContextCalculus.CBFiniteOrderAdmissibilityWire
open ContextCalculus.CBRoleChainEncoding
open ContextCalculus.PropRes

structure WireCBGlobalModelDocument where
  version : Nat
  global_closure : WireCBGlobalClosureDocument
  blocked_saturation : WireBlockedGroundSaturationDocument
deriving FromJson, ToJson

structure DecodedCBGlobalModelDocument where
  global : DecodedCBGlobalClosureDocument
  blocked : DecodedBlockedGroundSaturationDocument
  source_bounds_eq : (rProduction global.rsucc).source.bounds =
    (productionRun blocked.carrier.admissibility).source.bounds
  source_ontology_eq : (rProduction global.rsucc).source.ontology =
    (productionRun blocked.carrier.admissibility).source.ontology
  runtime_bounds_eq : (rProduction global.rsucc).bounds =
    (productionRun blocked.carrier.admissibility).bounds
  contexts_eq : contextSnapshot (rProduction global.rsucc).contexts =
    contextSnapshot (productionRun blocked.carrier.admissibility).contexts
  terms_eq : global.order.eqClosure.literalOrder.termOrder.orderedTerms =
    blocked.carrier.admissibility.eqClosure.literalOrder.termOrder.orderedTerms
  literals_eq : global.order.eqClosure.literalOrder.orderedLiterals =
    blocked.carrier.admissibility.eqClosure.literalOrder.orderedLiterals

def WireCBGlobalModelDocument.decode (wire : WireCBGlobalModelDocument) :
    Except String DecodedCBGlobalModelDocument := do
  if wire.version != 1 then
    throw s!"unsupported CB global-model version {wire.version}"
  let global ← wire.global_closure.decode
  let blocked ← wire.blocked_saturation.decode
  if hsourceBounds : (rProduction global.rsucc).source.bounds =
      (productionRun blocked.carrier.admissibility).source.bounds then
    if hsource : (rProduction global.rsucc).source.ontology =
        (productionRun blocked.carrier.admissibility).source.ontology then
      if hruntime : (rProduction global.rsucc).bounds =
          (productionRun blocked.carrier.admissibility).bounds then
        if hcontexts : contextSnapshot (rProduction global.rsucc).contexts =
            contextSnapshot (productionRun blocked.carrier.admissibility).contexts then
          if hterms : global.order.eqClosure.literalOrder.termOrder.orderedTerms =
              blocked.carrier.admissibility.eqClosure.literalOrder.termOrder.orderedTerms then
            if hliterals : global.order.eqClosure.literalOrder.orderedLiterals =
                blocked.carrier.admissibility.eqClosure.literalOrder.orderedLiterals then
              return {
                global := global
                blocked := blocked
                source_bounds_eq := hsourceBounds
                source_ontology_eq := hsource
                runtime_bounds_eq := hruntime
                contexts_eq := hcontexts
                terms_eq := hterms
                literals_eq := hliterals
              }
            else throw "CB blocked model and global closure use different literal orders"
          else throw "CB blocked model and global closure use different term orders"
        else throw "CB blocked model and global closure use different terminal contexts"
      else throw "CB blocked model and global closure use different runtime bounds"
    else throw "CB blocked model and global closure use different source ontologies"
  else throw "CB blocked model and global closure use different source bounds"

def WireCBGlobalModelDocument.check (wire : WireCBGlobalModelDocument) :
    Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedCBGlobalModelDocument.source_model
    (decoded : DecodedCBGlobalModelDocument)
    (hbot : PClause.bot ∉ decoded.blocked.certificate.terminal) :
    ∃ (D : Type) (interpretation : Eqv.Interp D
        (Fin (productionRun decoded.blocked.carrier.admissibility).source.bounds.concepts)
        (Fin (productionRun decoded.blocked.carrier.admissibility).source.bounds.roles)
        (Fin (productionRun decoded.blocked.carrier.admissibility).source.bounds.individuals)),
      CBRoleChainEncoding.models interpretation
        (blockedSource decoded.blocked.carrier) :=
  decoded.blocked.source_model hbot

theorem WireCBGlobalModelDocument.check_sound
    (wire : WireCBGlobalModelDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedCBGlobalModelDocument,
      wire.decode = .ok decoded ∧
      contextSnapshot (rProduction decoded.global.rsucc).contexts =
        contextSnapshot (productionRun decoded.blocked.carrier.admissibility).contexts ∧
      (PClause.bot ∉ decoded.blocked.certificate.terminal →
        ∃ (D : Type) (interpretation : Eqv.Interp D
            (Fin (productionRun decoded.blocked.carrier.admissibility).source.bounds.concepts)
            (Fin (productionRun decoded.blocked.carrier.admissibility).source.bounds.roles)
            (Fin (productionRun decoded.blocked.carrier.admissibility).source.bounds.individuals)),
          CBRoleChainEncoding.models interpretation
            (blockedSource decoded.blocked.carrier)) := by
  cases hdecode : wire.decode with
  | error message => simp [WireCBGlobalModelDocument.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.contexts_eq, decoded.source_model⟩

#print axioms DecodedCBGlobalModelDocument.source_model
#print axioms WireCBGlobalModelDocument.check_sound

end ContextCalculus.CBGlobalModelWire
