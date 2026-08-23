import ContextCalculus.CBNamedGroundCompleteness

/-!
# Proof-carrying finite blocked carrier for production CB

This layer turns the checked production term permutation into the finite carrier
used by the complete ground model theorem. Every declared source individual is
mapped to the rank of its exact constant term. A wire-supplied row-major table
chooses one bounded carrier witness for every concept/role/concept/carrier
coordinate, making the existential witness function total and explicit.
-/

namespace ContextCalculus.CBBlockedCarrierWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBFiniteTermOrderWire
open ContextCalculus.CBFiniteOrderAdmissibilityWire

def productionRun (admissible : DecodedFiniteOrderAdmissibilityDocument) :=
  admissible.eqClosure.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production

def carrierSize (admissible : DecodedFiniteOrderAdmissibilityDocument) : Nat :=
  admissible.eqClosure.literalOrder.termOrder.orderedTerms.length

def witnessTableSize (admissible : DecodedFiniteOrderAdmissibilityDocument) : Nat :=
  let bounds := (productionRun admissible).source.bounds
  bounds.concepts * bounds.roles * bounds.concepts * carrierSize admissible

structure WireBlockedCarrierDocument where
  version : Nat
  admissibility : WireFiniteOrderAdmissibilityDocument
  witnesses : List Nat
deriving FromJson, ToJson

structure DecodedBlockedCarrierDocument where
  admissibility : DecodedFiniteOrderAdmissibilityDocument
  carrier_nonempty : 0 < carrierSize admissibility
  witnesses : List (Fin (carrierSize admissibility))
  witnesses_length : witnesses.length = witnessTableSize admissibility

def WireBlockedCarrierDocument.decode (wire : WireBlockedCarrierDocument) :
    Except String DecodedBlockedCarrierDocument := do
  if wire.version != 1 then
    throw s!"unsupported blocked CB carrier version {wire.version}"
  let admissibility ← wire.admissibility.decode
  if hnonempty : 0 < carrierSize admissibility then
    let witnesses ← wire.witnesses.mapM fun witness =>
      if hwitness : witness < carrierSize admissibility then
        return (⟨witness, hwitness⟩ : Fin (carrierSize admissibility))
      else throw "blocked CB witness is outside the finite carrier"
    if hlength : witnesses.length = witnessTableSize admissibility then
      return {
        admissibility := admissibility
        carrier_nonempty := hnonempty
        witnesses := witnesses
        witnesses_length := hlength }
    else throw s!"blocked CB witness table has {witnesses.length} entries, expected {witnessTableSize admissibility}"
  else throw "blocked CB carrier must be nonempty"

def WireBlockedCarrierDocument.check (wire : WireBlockedCarrierDocument) :
    Except String Bool := do
  let _ ← wire.decode
  return true

abbrev DecodedBlockedCarrierDocument.Carrier
    (decoded : DecodedBlockedCarrierDocument) := Fin (carrierSize decoded.admissibility)

def DecodedBlockedCarrierDocument.name
    (decoded : DecodedBlockedCarrierDocument)
    (individual : Fin (productionRun decoded.admissibility).source.bounds.individuals) :
    decoded.Carrier := by
  let order := decoded.admissibility.eqClosure.literalOrder.termOrder
  refine ⟨order.rank (.const individual.val), ?_⟩
  apply List.idxOf_lt_length_iff.mpr
  apply (order.mem_ordered_iff (.const individual.val)).mpr
  exact sourceIndividual_mem_productionTerms order.factorClosure individual

def witnessIndex (conceptCount roleCount carrierCount : Nat)
    (source : Fin conceptCount) (role : Fin roleCount)
    (filler : Fin conceptCount) (carrier : Fin carrierCount) : Nat :=
  (((source.val * roleCount + role.val) * conceptCount + filler.val) *
    carrierCount + carrier.val)

theorem witnessIndex_lt (conceptCount roleCount carrierCount : Nat)
    (source : Fin conceptCount) (role : Fin roleCount)
    (filler : Fin conceptCount) (carrier : Fin carrierCount) :
    witnessIndex conceptCount roleCount carrierCount source role filler carrier <
      conceptCount * roleCount * conceptCount * carrierCount := by
  unfold witnessIndex
  have hrolePositive : 0 < roleCount := Nat.zero_lt_of_lt role.isLt
  have hconceptPositive : 0 < conceptCount := Nat.zero_lt_of_lt source.isLt
  have hcarrierPositive : 0 < carrierCount := Nat.zero_lt_of_lt carrier.isLt
  have hfirst : source.val * roleCount + role.val < conceptCount * roleCount := by
    calc
      source.val * roleCount + role.val < source.val * roleCount + roleCount :=
        Nat.add_lt_add_left role.isLt _
      _ = (source.val + 1) * roleCount := by simp [Nat.add_mul]
      _ ≤ conceptCount * roleCount :=
        Nat.mul_le_mul_right roleCount (Nat.succ_le_iff.mpr source.isLt)
  have hsecond :
      (source.val * roleCount + role.val) * conceptCount + filler.val <
        (conceptCount * roleCount) * conceptCount := by
    calc
      _ < (source.val * roleCount + role.val) * conceptCount + conceptCount :=
        Nat.add_lt_add_left filler.isLt _
      _ = (source.val * roleCount + role.val + 1) * conceptCount := by
        simp [Nat.add_mul]
      _ ≤ (conceptCount * roleCount) * conceptCount :=
        Nat.mul_le_mul_right conceptCount (Nat.succ_le_iff.mpr hfirst)
  calc
    _ < ((source.val * roleCount + role.val) * conceptCount + filler.val) *
        carrierCount + carrierCount := Nat.add_lt_add_left carrier.isLt _
    _ = ((source.val * roleCount + role.val) * conceptCount + filler.val + 1) *
        carrierCount := by simp [Nat.add_mul]
    _ ≤ ((conceptCount * roleCount) * conceptCount) * carrierCount :=
      Nat.mul_le_mul_right carrierCount (Nat.succ_le_iff.mpr hsecond)
    _ = conceptCount * roleCount * conceptCount * carrierCount := rfl

def DecodedBlockedCarrierDocument.witness
    (decoded : DecodedBlockedCarrierDocument)
    (source : Fin (productionRun decoded.admissibility).source.bounds.concepts)
    (role : Fin (productionRun decoded.admissibility).source.bounds.roles)
    (filler : Fin (productionRun decoded.admissibility).source.bounds.concepts)
    (carrier : decoded.Carrier) : decoded.Carrier :=
  let bounds := (productionRun decoded.admissibility).source.bounds
  decoded.witnesses.getD
    (witnessIndex bounds.concepts bounds.roles (carrierSize decoded.admissibility)
      source role filler carrier)
    ⟨0, decoded.carrier_nonempty⟩

theorem DecodedBlockedCarrierDocument.witness_eq_get
    (decoded : DecodedBlockedCarrierDocument)
    (source : Fin (productionRun decoded.admissibility).source.bounds.concepts)
    (role : Fin (productionRun decoded.admissibility).source.bounds.roles)
    (filler : Fin (productionRun decoded.admissibility).source.bounds.concepts)
    (carrier : decoded.Carrier) :
    decoded.witness source role filler carrier = decoded.witnesses.get
      ⟨witnessIndex (productionRun decoded.admissibility).source.bounds.concepts
        (productionRun decoded.admissibility).source.bounds.roles
        (carrierSize decoded.admissibility) source role filler carrier, by
        rw [decoded.witnesses_length]
        exact witnessIndex_lt _ _ _ source role filler carrier⟩ := by
  have hindex : witnessIndex
      (productionRun decoded.admissibility).source.bounds.concepts
      (productionRun decoded.admissibility).source.bounds.roles
      (carrierSize decoded.admissibility) source role filler carrier <
      decoded.witnesses.length := by
    rw [decoded.witnesses_length]
    exact witnessIndex_lt _ _ _ source role filler carrier
  unfold DecodedBlockedCarrierDocument.witness
  simp only [List.getD, List.getElem?_eq_getElem hindex, Option.getD_some]
  rfl

theorem DecodedBlockedCarrierDocument.name_term
    (decoded : DecodedBlockedCarrierDocument)
    (individual : Fin (productionRun decoded.admissibility).source.bounds.individuals) :
    decoded.admissibility.eqClosure.literalOrder.termOrder.orderedTerms.get
      (decoded.name individual) = .const individual.val := by
  let order := decoded.admissibility.eqClosure.literalOrder.termOrder
  have hmem : FTerm.const individual.val ∈ order.orderedTerms :=
    (order.mem_ordered_iff (.const individual.val)).mpr
      (sourceIndividual_mem_productionTerms order.factorClosure individual)
  have hbound : order.rank (.const individual.val) < order.orderedTerms.length :=
    List.idxOf_lt_length_iff.mpr hmem
  change order.orderedTerms[order.rank (.const individual.val)]'hbound =
    .const individual.val
  exact List.getElem_idxOf hbound

theorem WireBlockedCarrierDocument.check_sound
    (wire : WireBlockedCarrierDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedBlockedCarrierDocument,
      wire.decode = .ok decoded ∧
      0 < carrierSize decoded.admissibility ∧
      decoded.witnesses.length = witnessTableSize decoded.admissibility ∧
      ∀ individual,
        decoded.admissibility.eqClosure.literalOrder.termOrder.orderedTerms.get
          (decoded.name individual) = .const individual.val := by
  cases hdecode : wire.decode with
  | error message => simp [WireBlockedCarrierDocument.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.carrier_nonempty, decoded.witnesses_length,
        decoded.name_term⟩

#print axioms DecodedBlockedCarrierDocument.name_term
#print axioms WireBlockedCarrierDocument.check_sound

end ContextCalculus.CBBlockedCarrierWire
