import ContextCalculus.CBFunctionRenaming
import ContextCalculus.CBTermDerivationWire
import Mathlib.Data.List.Nodup

/-!
# Executable CB Skolem-function allocation

The frontend records one production function id for every canonical source
Skolem id.  The checker requires a complete, bounded, duplicate-free table.
Its total extension maps all irrelevant ids above the production namespace;
Lean proves that extension injective, so `CBFunctionRenaming` transports the
complete taxonomy semantics to the production numbering.
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
  allocation : List (Fin productionCount)
  allocation_count : allocation.length = canonicalCount
  allocation_nodup : allocation.Nodup

def WireFunctionAllocation.decode (wire : WireFunctionAllocation) :
    Except String DecodedFunctionAllocation := do
  if wire.version != 1 then
    throw s!"unsupported CB function-allocation version {wire.version}"
  if hcount : wire.allocation.length = wire.canonical_count then
    if hbound : ∀ value ∈ wire.allocation, value < wire.production_count then
      let allocation : List (Fin wire.production_count) :=
        wire.allocation.attach.map fun value =>
          ⟨value.1, hbound value.1 value.2⟩
      if hnodup : allocation.Nodup then
      return {
        canonicalCount := wire.canonical_count
        productionCount := wire.production_count
        allocation
        allocation_count := by simp [allocation, hcount]
        allocation_nodup := hnodup
      }
      else throw "CB function allocation reuses a production Skolem id"
    else throw "CB function allocation contains an out-of-range production id"
  else throw "CB function allocation does not cover every canonical Skolem id"

def WireFunctionAllocation.check (wire : WireFunctionAllocation) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedFunctionAllocation.rename (decoded : DecodedFunctionAllocation)
    (source : Nat) : Nat :=
  if hsource : source < decoded.canonicalCount then
    (decoded.allocation.get ⟨source, by simpa [decoded.allocation_count]⟩).val
  else decoded.productionCount + source

theorem DecodedFunctionAllocation.rename_bounded
    (decoded : DecodedFunctionAllocation) (source : Nat)
    (hsource : source < decoded.canonicalCount) :
    decoded.rename source < decoded.productionCount := by
  rw [DecodedFunctionAllocation.rename, dif_pos hsource]
  exact (decoded.allocation.get _).isLt

theorem DecodedFunctionAllocation.rename_injective
    (decoded : DecodedFunctionAllocation) : Function.Injective decoded.rename := by
  intro left right heq
  by_cases hleft : left < decoded.canonicalCount
  · by_cases hright : right < decoded.canonicalCount
    · simp only [DecodedFunctionAllocation.rename, dif_pos hleft,
        dif_pos hright] at heq
      have hfin :
          decoded.allocation.get ⟨left, by simpa [decoded.allocation_count]⟩ =
            decoded.allocation.get ⟨right, by simpa [decoded.allocation_count]⟩ := by
        apply Fin.ext
        exact heq
      have hindex := decoded.allocation_nodup.get_inj_iff.mp hfin
      exact congrArg Fin.val hindex
    · have hbounded := decoded.rename_bounded left hleft
      simp only [DecodedFunctionAllocation.rename, dif_pos hleft,
        dif_neg hright] at heq hbounded
      omega
  · by_cases hright : right < decoded.canonicalCount
    · have hbounded := decoded.rename_bounded right hright
      simp only [DecodedFunctionAllocation.rename, dif_neg hleft,
        dif_pos hright] at heq hbounded
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
        decoded.rename source < decoded.productionCount := by
  cases hdecode : wire.decode with
  | error message => simp_all [WireFunctionAllocation.check]
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.rename_injective,
        decoded.rename_bounded⟩

#print axioms DecodedFunctionAllocation.rename_injective
#print axioms WireFunctionAllocation.check_sound

end ContextCalculus.CBFunctionAllocationWire
