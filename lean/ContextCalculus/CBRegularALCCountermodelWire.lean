import ContextCalculus.CBRegularALCCountermodel
import ContextCalculus.CBTermDerivationWire
import ContextCalculus.HypertableauRegularWire

/-! Bounds-checked wire for ALC-shaped CB regular countermodels. -/

namespace ContextCalculus.CBRegularALCCountermodelWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.Ctx
open ContextCalculus.CBALCEncoding
open ContextCalculus.CBRegularALCCountermodel
open ContextCalculus.CBTermWire
open ContextCalculus.Hypertableau

inductive WireALCClause where
  | gci (body head : List Nat)
  | exRight (source role filler : Nat)
  | exLeft (role filler conclusion : Nat)
  | allRight (source role filler : Nat)
deriving FromJson, ToJson

def WireALCClause.decode (conceptCount roleCount : Nat) : WireALCClause →
    Except String (Ctx.Clause (Fin conceptCount) (Fin roleCount))
  | .gci body head => do
      return .gci
        (← body.mapM (checkedFin "ALC body concept" conceptCount))
        (← head.mapM (checkedFin "ALC head concept" conceptCount))
  | .exRight source role filler => do
      return .exRight
        (← checkedFin "ALC existential source" conceptCount source)
        (← checkedFin "ALC existential role" roleCount role)
        (← checkedFin "ALC existential filler" conceptCount filler)
  | .exLeft role filler conclusion => do
      return .exLeft
        (← checkedFin "ALC existential-left role" roleCount role)
        (← checkedFin "ALC existential-left filler" conceptCount filler)
        (← checkedFin "ALC existential-left conclusion" conceptCount conclusion)
  | .allRight source role filler => do
      return .allRight
        (← checkedFin "ALC universal source" conceptCount source)
        (← checkedFin "ALC universal role" roleCount role)
        (← checkedFin "ALC universal filler" conceptCount filler)

structure WireRegularALCCountermodel where
  version : Nat
  ontology : List WireALCClause
  regular : WireRegularCertificate
deriving FromJson, ToJson

private def checkedFinExact (kind : String) (bound value : Nat) :
    Except String { index : Fin bound // index.val = value } :=
  if h : value < bound then .ok ⟨⟨value, h⟩, rfl⟩
  else .error s!"{kind} id {value} is outside [0,{bound})"

structure DecodedRegularALCCountermodel
    (bounds : Bounds) (source : List FCL) (subRaw supRaw : Nat) where
  ontology : Ctx.Ontology (Fin bounds.concepts) (Fin bounds.roles)
  source_exact : CBALCEncoding.encode ontology = source
  regular : DecodedRegularCertificateAt bounds.concepts bounds.roles 2
  regular_ontology_exact : regular.certificate.ontology =
    htOntology (0 : Fin 2) (1 : Fin 2) ontology
  sub : Fin bounds.concepts
  sup : Fin bounds.concepts
  sub_exact : sub.val = subRaw
  sup_exact : sup.val = supRaw
  root_sub : (⟨0, regular.positive⟩, .pos sub) ∈
    regular.certificate.labels
  root_not_sup : (⟨0, regular.positive⟩, .negated sup) ∈
    regular.certificate.labels
  accepted : regular.certificate.check = true

def WireRegularALCCountermodel.decode
    (bounds : Bounds) (source : List FCL) (subRaw supRaw : Nat)
    (wire : WireRegularALCCountermodel) :
    Except String (DecodedRegularALCCountermodel bounds source subRaw supRaw) := do
  if wire.version != 1 then
    throw s!"unsupported regular ALC CB countermodel version {wire.version}"
  let ontology ← wire.ontology.mapM (WireALCClause.decode bounds.concepts bounds.roles)
  if hsource : CBALCEncoding.encode ontology = source then
    let regular ← wire.regular.decodeAt bounds.concepts bounds.roles 2
    if hontology : regular.certificate.ontology =
        htOntology (0 : Fin 2) (1 : Fin 2) ontology then
      let sub ← checkedFinExact "regular ALC subclass" bounds.concepts subRaw
      let sup ← checkedFinExact "regular ALC superclass" bounds.concepts supRaw
      if hsub : (⟨0, regular.positive⟩, .pos sub.val) ∈
          regular.certificate.labels then
        if hsup : (⟨0, regular.positive⟩, .negated sup.val) ∈
            regular.certificate.labels then
          if hcheck : regular.certificate.check = true then
            return {
              ontology
              source_exact := hsource
              regular
              regular_ontology_exact := hontology
              sub := sub.val
              sup := sup.val
              sub_exact := sub.property
              sup_exact := sup.property
              root_sub := hsub
              root_not_sup := hsup
              accepted := hcheck }
          else throw "regular ALC CB countermodel certificate was rejected"
        else throw "regular ALC CB countermodel omits the negative query literal"
      else throw "regular ALC CB countermodel omits the positive query literal"
    else throw "regular HT ontology differs from the exact ALC translation"
  else throw "regular ALC encoding differs from the exact CB source ontology"

theorem DecodedRegularALCCountermodel.refutes
    (decoded : DecodedRegularALCCountermodel bounds source subRaw supRaw) :
    ∃ (D : Type) (model : TModel D) (element : D),
      (∀ clause ∈ source, valid model clause) ∧
      model.conc subRaw element ∧ ¬model.conc supRaw element := by
  letI : NeZero decoded.regular.nodeCount :=
    ⟨Nat.ne_of_gt decoded.regular.positive⟩
  obtain ⟨D, model, element, hsource, hsub, hsup⟩ :=
    checked_regular_countermodel decoded.regular.certificate
      (0 : Fin 2) (1 : Fin 2) (by decide) decoded.ontology decoded.sub decoded.sup
      decoded.regular_ontology_exact
      (by simpa [FiniteRegularCertificate.state] using decoded.root_sub)
      (by simpa [FiniteRegularCertificate.state] using decoded.root_not_sup)
      decoded.accepted
  refine ⟨D, model, element, ?_, ?_, ?_⟩
  · simpa [decoded.source_exact] using hsource
  · exact decoded.sub_exact ▸ hsub
  · exact decoded.sup_exact ▸ hsup

#print axioms DecodedRegularALCCountermodel.refutes

end ContextCalculus.CBRegularALCCountermodelWire
