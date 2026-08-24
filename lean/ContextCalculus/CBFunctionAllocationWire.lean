import ContextCalculus.CBFunctionRenaming
import ContextCalculus.CBTermDerivationWire
import Mathlib.Data.List.Nodup

/-!
# Executable CB Skolem-function allocation

The frontend records one entry for every canonical source-clause index.  An
existential-right index maps to its bounded production function id.  Every
other index uses the canonical sentinel `productionCount + index`; these
indices never occur as functions in the encoded ontology.  The checker proves
the complete table duplicate-free and each entry either bounded or its exact
sentinel.  The same sentinel formula extends the table above `canonicalCount`,
giving a total injective renaming without requiring a fictitious production
function for every non-existential source clause.
-/

namespace ContextCalculus.CBFunctionAllocationWire

open Lean ContextCalculus CheckerTerm
open ContextCalculus.CBTermWire
open ContextCalculus.CBFunctionRenaming

structure WireFunctionAllocation where
  version : Nat
  canonical_count : Nat
  production_count : Nat
  allocation : List Nat
deriving FromJson, ToJson, Repr

structure DecodedFunctionAllocation where
  canonicalCount : Nat
  productionCount : Nat
  allocation : List Nat
  allocation_count : allocation.length = canonicalCount
  allocation_shape : ∀ index : Fin allocation.length,
    allocation.get index < productionCount ∨
      allocation.get index = productionCount + index.val
  allocation_nodup : allocation.Nodup

def WireFunctionAllocation.decode (wire : WireFunctionAllocation) :
    Except String DecodedFunctionAllocation := do
  if wire.version != 1 then
    throw s!"unsupported CB function-allocation version {wire.version}"
  if hcount : wire.allocation.length = wire.canonical_count then
    if hshape : ∀ index : Fin wire.allocation.length,
        wire.allocation.get index < wire.production_count ∨
          wire.allocation.get index = wire.production_count + index.val then
      if hnodup : wire.allocation.Nodup then
      return {
        canonicalCount := wire.canonical_count
        productionCount := wire.production_count
        allocation := wire.allocation
        allocation_count := hcount
        allocation_shape := hshape
        allocation_nodup := hnodup
      }
      else throw "CB function allocation reuses a production Skolem id"
    else throw "CB function allocation entry is neither bounded nor its canonical sentinel"
  else throw "CB function allocation does not cover every canonical Skolem id"

def WireFunctionAllocation.check (wire : WireFunctionAllocation) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedFunctionAllocation.rename (decoded : DecodedFunctionAllocation)
    (source : Nat) : Nat :=
  if hsource : source < decoded.canonicalCount then
    decoded.allocation.get ⟨source, by simpa [decoded.allocation_count]⟩
  else decoded.productionCount + source

theorem DecodedFunctionAllocation.rename_bounded_or_sentinel
    (decoded : DecodedFunctionAllocation) (source : Nat)
    (hsource : source < decoded.canonicalCount) :
    decoded.rename source < decoded.productionCount ∨
      decoded.rename source = decoded.productionCount + source := by
  rw [DecodedFunctionAllocation.rename, dif_pos hsource]
  simpa only using decoded.allocation_shape
    ⟨source, by simpa [decoded.allocation_count]⟩

theorem DecodedFunctionAllocation.rename_injective
    (decoded : DecodedFunctionAllocation) : Function.Injective decoded.rename := by
  intro left right heq
  by_cases hleft : left < decoded.canonicalCount
  · by_cases hright : right < decoded.canonicalCount
    · simp only [DecodedFunctionAllocation.rename, dif_pos hleft,
        dif_pos hright] at heq
      have hindex := decoded.allocation_nodup.get_inj_iff.mp heq
      exact congrArg Fin.val hindex
    · rcases decoded.rename_bounded_or_sentinel left hleft with hbounded | hsentinel
      · rw [DecodedFunctionAllocation.rename, dif_pos hleft] at hbounded
        rw [DecodedFunctionAllocation.rename, dif_pos hleft,
          DecodedFunctionAllocation.rename, dif_neg hright] at heq
        omega
      · rw [DecodedFunctionAllocation.rename, dif_pos hleft] at hsentinel
        rw [DecodedFunctionAllocation.rename, dif_pos hleft,
          DecodedFunctionAllocation.rename, dif_neg hright] at heq
        omega
  · by_cases hright : right < decoded.canonicalCount
    · rcases decoded.rename_bounded_or_sentinel right hright with hbounded | hsentinel
      · rw [DecodedFunctionAllocation.rename, dif_pos hright] at hbounded
        rw [DecodedFunctionAllocation.rename, dif_neg hleft,
          DecodedFunctionAllocation.rename, dif_pos hright] at heq
        omega
      · rw [DecodedFunctionAllocation.rename, dif_pos hright] at hsentinel
        rw [DecodedFunctionAllocation.rename, dif_neg hleft,
          DecodedFunctionAllocation.rename, dif_pos hright] at heq
        omega
    · simp only [DecodedFunctionAllocation.rename, dif_neg hleft,
        dif_neg hright] at heq
      omega

theorem WireFunctionAllocation.check_sound
    (wire : WireFunctionAllocation) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedFunctionAllocation,
      wire.decode = .ok decoded ∧
      Function.Injective decoded.rename ∧
      ∀ source < decoded.canonicalCount,
        decoded.rename source < decoded.productionCount ∨
          decoded.rename source = decoded.productionCount + source := by
  cases hdecode : wire.decode with
  | error message => simp_all [WireFunctionAllocation.check]
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.rename_injective,
        decoded.rename_bounded_or_sentinel⟩

#print axioms DecodedFunctionAllocation.rename_injective
#print axioms WireFunctionAllocation.check_sound

end ContextCalculus.CBFunctionAllocationWire
