import ContextCalculus.CBBlockedTaxonomyCountermodel

/-! Bounds-checked wire for query-augmented blocked CB countermodels. -/

namespace ContextCalculus.CBBlockedTaxonomyCountermodelWire

open Lean ContextCalculus PropRes Equiv
open ContextCalculus.CBCert
open ContextCalculus.CBBlockedCarrierWire
open ContextCalculus.CBBlockedGroundSaturationWire
open ContextCalculus.CBBlockedTaxonomyCountermodel

structure WireBlockedTaxonomyCountermodel where
  version : Nat
  witness : Nat
  saturation : CBCert.WireCertificate
deriving FromJson, ToJson

structure DecodedBlockedTaxonomyCountermodel
    (carrier : DecodedBlockedCarrierDocument) (subRaw supRaw : Nat) where
  sub : Fin (productionRun carrier.admissibility).source.bounds.concepts
  sup : Fin (productionRun carrier.admissibility).source.bounds.concepts
  witness : carrier.Carrier
  certificate : CBCert.Certificate (blockedAtomCount carrier)
  premises_exact : certificate.premises.toFinset =
    encodedBlockedQueryGround carrier sub sup witness
  saturation : Saturation
    (encodedBlockedQueryGround carrier sub sup witness) certificate.terminal
  open_terminal : PClause.bot ∉ certificate.terminal

def WireBlockedTaxonomyCountermodel.decode
    (carrier : DecodedBlockedCarrierDocument) (subRaw supRaw : Nat)
    (wire : WireBlockedTaxonomyCountermodel) :
    Except String (DecodedBlockedTaxonomyCountermodel carrier subRaw supRaw) := do
  if wire.version != 1 then
    throw s!"unsupported blocked CB taxonomy-countermodel version {wire.version}"
  let bounds := (productionRun carrier.admissibility).source.bounds
  let sub ← if h : subRaw < bounds.concepts then
      pure (⟨subRaw, h⟩ : Fin bounds.concepts)
    else throw "blocked CB countermodel subclass is outside the source signature"
  let sup ← if h : supRaw < bounds.concepts then
      pure (⟨supRaw, h⟩ : Fin bounds.concepts)
    else throw "blocked CB countermodel superclass is outside the source signature"
  let witness ← if h : wire.witness < carrierSize carrier.admissibility then
      pure ⟨wire.witness, h⟩
    else throw "blocked CB countermodel witness is outside the carrier"
  let expectedAtoms := blockedAtomCount carrier
  if wire.saturation.version != 1 then
    throw s!"unsupported nested CB saturation version {wire.saturation.version}"
  if wire.saturation.atom_count != expectedAtoms then
    throw s!"blocked CB query saturation atom count is {wire.saturation.atom_count}, expected {expectedAtoms}"
  let premises ← wire.saturation.premises.mapM
    (CBCert.WireClause.decode expectedAtoms)
  let trace ← wire.saturation.trace.mapM (CBCert.WireEntry.decode expectedAtoms)
  let certificate : CBCert.Certificate expectedAtoms := { premises, trace }
  if hpremises : certificate.premises.toFinset =
      encodedBlockedQueryGround carrier sub sup witness then
    if hcheck : certificate.check = true then
      let hsaturation := certificate.check_saturation hcheck
      if hopen : PClause.bot ∉ certificate.terminal then
        return {
          sub
          sup
          witness
          certificate
          premises_exact := hpremises
          saturation := hpremises ▸ hsaturation
          open_terminal := hopen }
      else throw "blocked CB query saturation derives the empty clause"
    else throw "blocked CB query saturation certificate was rejected"
  else throw "blocked CB query premises differ from the authoritative augmented grounding"

theorem DecodedBlockedTaxonomyCountermodel.refutes
    (decoded : DecodedBlockedTaxonomyCountermodel carrier subRaw supRaw) :
    ∃ (D : Type) (interpretation : Eqv.Interp D
        (Fin (productionRun carrier.admissibility).source.bounds.concepts)
        (Fin (productionRun carrier.admissibility).source.bounds.roles)
        (Fin (productionRun carrier.admissibility).source.bounds.individuals))
        (element : D),
      CBRoleChainEncoding.models interpretation (blockedSource carrier) ∧
      interpretation.c decoded.sub element ∧
      ¬interpretation.c decoded.sup element :=
  blockedQueryGround_countermodel carrier decoded.sub decoded.sup decoded.witness
    decoded.certificate.terminal decoded.saturation decoded.open_terminal

#print axioms DecodedBlockedTaxonomyCountermodel.refutes

end ContextCalculus.CBBlockedTaxonomyCountermodelWire
