import ContextCalculus.CBFiniteAtomEncoding

/-!
# Executable saturation of the authoritative blocked CB grounding

This layer computes the complete typed ground set from the checked source,
source-name ranks, and existential witness table. It then requires a generic
resolution certificate whose premises equal the canonical finite encoding of
that set exactly. If the checked terminal saturation omits the empty clause,
Lean transports its propositional model through the atom encoding and the
congruence quotient to obtain a model of the original typed source ontology.
-/

namespace ContextCalculus.CBBlockedGroundSaturationWire

open Lean ContextCalculus ContextCalculus.PropRes ContextCalculus.Equiv
open ContextCalculus.CBCert ContextCalculus.CBBlockedCarrierWire
open ContextCalculus.CBFiniteAtomEncoding
open ContextCalculus.CBNamedGroundCompleteness
open ContextCalculus.CBRoleChainEncoding

def blockedSource (carrier : DecodedBlockedCarrierDocument) :=
  (productionRun carrier.admissibility).source.source

def blockedGround (carrier : DecodedBlockedCarrierDocument) :=
  namedGroundSource carrier.name carrier.witness carrier.minimumWitness
    (blockedSource carrier)

def encodedBlockedGround (carrier : DecodedBlockedCarrierDocument) :=
  encodeSet (blockedGround carrier)

def blockedAtomCount (carrier : DecodedBlockedCarrierDocument) : Nat :=
  let bounds := (productionRun carrier.admissibility).source.bounds
  (allAtoms bounds.concepts bounds.roles (carrierSize carrier.admissibility)).length

structure WireBlockedGroundSaturationDocument where
  version : Nat
  carrier : WireBlockedCarrierDocument
  saturation : CBCert.WireCertificate
deriving FromJson, ToJson

structure DecodedBlockedGroundSaturationDocument where
  carrier : DecodedBlockedCarrierDocument
  certificate : CBCert.Certificate (blockedAtomCount carrier)
  premises_exact : certificate.premises.toFinset = encodedBlockedGround carrier
  saturation : Saturation (encodedBlockedGround carrier) certificate.terminal

def WireBlockedGroundSaturationDocument.decode
    (wire : WireBlockedGroundSaturationDocument) :
    Except String DecodedBlockedGroundSaturationDocument := do
  if wire.version != 1 then
    throw s!"unsupported blocked CB ground-saturation version {wire.version}"
  let carrier ← wire.carrier.decode
  let expectedAtoms := blockedAtomCount carrier
  if wire.saturation.version != 1 then
    throw s!"unsupported nested CB saturation version {wire.saturation.version}"
  if wire.saturation.atom_count != expectedAtoms then
    throw s!"blocked CB saturation atom count is {wire.saturation.atom_count}, expected {expectedAtoms}"
  let premises ← wire.saturation.premises.mapM (CBCert.WireClause.decode expectedAtoms)
  let trace ← wire.saturation.trace.mapM (CBCert.WireEntry.decode expectedAtoms)
  let certificate : CBCert.Certificate expectedAtoms := { premises, trace }
  if hpremises : certificate.premises.toFinset = encodedBlockedGround carrier then
    if hcheck : certificate.check = true then
      let hsaturation := certificate.check_saturation hcheck
      return {
        carrier
        certificate
        premises_exact := hpremises
        saturation := hpremises ▸ hsaturation }
    else throw "blocked CB ground saturation certificate was rejected"
  else throw "blocked CB saturation premises differ from the authoritative grounding"

def WireBlockedGroundSaturationDocument.check
    (wire : WireBlockedGroundSaturationDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedBlockedGroundSaturationDocument.source_model_nonempty
    (decoded : DecodedBlockedGroundSaturationDocument)
    (hbot : PClause.bot ∉ decoded.certificate.terminal) :
    ∃ (D : Type) (interpretation : Eqv.Interp D
        (Fin (productionRun decoded.carrier.admissibility).source.bounds.concepts)
        (Fin (productionRun decoded.carrier.admissibility).source.bounds.roles)
        (Fin (productionRun decoded.carrier.admissibility).source.bounds.individuals)),
      Nonempty D ∧
      CBRoleChainEncoding.models interpretation (blockedSource decoded.carrier) := by
  have hencodedSat : ¬ PropRes.Unsat (encodedBlockedGround decoded.carrier) := by
    intro hunsat
    exact hbot ((saturation_refutes_iff_unsat decoded.saturation).mpr hunsat)
  have hexists : ∃ valuation : Fin (blockedAtomCount decoded.carrier) → Prop,
      ∀ clause ∈ encodedBlockedGround decoded.carrier, clause.sat valuation := by
    by_contra hnone
    exact hencodedSat hnone
  obtain ⟨valuation, hvaluation⟩ := hexists
  have hgroundModels : ∀ clause ∈ blockedGround decoded.carrier,
      clause.sat (fun atom => valuation (atomIndex atom)) :=
    (models_encodeSet_iff valuation (blockedGround decoded.carrier)).mp hvaluation
  have hnotDerivable : ¬ PropRes.Derivable (blockedGround decoded.carrier)
      PClause.bot := by
    intro hderivable
    have hfalse := PropRes.derivable_sound
      (fun atom => valuation (atomIndex atom))
      (blockedGround decoded.carrier) hgroundModels hderivable
    exact PClause.not_sat_bot _ hfalse
  letI : Nonempty decoded.carrier.Carrier :=
    ⟨⟨0, decoded.carrier.carrier_nonempty⟩⟩
  exact source_complete_ground_named_nonempty decoded.carrier.name
    decoded.carrier.witness decoded.carrier.minimumWitness
    (blockedSource decoded.carrier) hnotDerivable

theorem DecodedBlockedGroundSaturationDocument.source_model
    (decoded : DecodedBlockedGroundSaturationDocument)
    (hbot : PClause.bot ∉ decoded.certificate.terminal) :
    ∃ (D : Type) (interpretation : Eqv.Interp D
        (Fin (productionRun decoded.carrier.admissibility).source.bounds.concepts)
        (Fin (productionRun decoded.carrier.admissibility).source.bounds.roles)
        (Fin (productionRun decoded.carrier.admissibility).source.bounds.individuals)),
      CBRoleChainEncoding.models interpretation (blockedSource decoded.carrier) := by
  obtain ⟨D, interpretation, _, hmodels⟩ := decoded.source_model_nonempty hbot
  exact ⟨D, interpretation, hmodels⟩

theorem WireBlockedGroundSaturationDocument.check_sound
    (wire : WireBlockedGroundSaturationDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedBlockedGroundSaturationDocument,
      wire.decode = .ok decoded ∧
      decoded.certificate.premises.toFinset = encodedBlockedGround decoded.carrier ∧
      Saturation (encodedBlockedGround decoded.carrier)
        decoded.certificate.terminal ∧
      (PClause.bot ∉ decoded.certificate.terminal →
        ∃ (D : Type) (interpretation : Eqv.Interp D
            (Fin (productionRun decoded.carrier.admissibility).source.bounds.concepts)
            (Fin (productionRun decoded.carrier.admissibility).source.bounds.roles)
            (Fin (productionRun decoded.carrier.admissibility).source.bounds.individuals)),
          CBRoleChainEncoding.models interpretation
            (blockedSource decoded.carrier)) := by
  cases hdecode : wire.decode with
  | error message =>
      simp [WireBlockedGroundSaturationDocument.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.premises_exact, decoded.saturation,
        decoded.source_model⟩

#print axioms DecodedBlockedGroundSaturationDocument.source_model
#print axioms DecodedBlockedGroundSaturationDocument.source_model_nonempty
#print axioms WireBlockedGroundSaturationDocument.check_sound

end ContextCalculus.CBBlockedGroundSaturationWire
