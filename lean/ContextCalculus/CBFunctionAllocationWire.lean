import ContextCalculus.CBFunctionRenaming
import ContextCalculus.CBTermDerivationWire
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sigma

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

structure WireFunctionAssignment where
  source : Nat
  target : Nat
deriving FromJson, ToJson, Repr

structure WireFunctionAllocation where
  version : Nat
  canonical_count : Nat
  production_count : Nat
  allocation : List Nat
  sparse_allocation : List WireFunctionAssignment := []
deriving FromJson, ToJson, Repr

structure DenseFunctionAllocation where
  canonicalCount : Nat
  productionCount : Nat
  allocation : List Nat
  allocation_count : allocation.length = canonicalCount
  allocation_shape : ∀ index : Fin allocation.length,
    allocation.get index < productionCount ∨
      allocation.get index = productionCount + index.val
  allocation_nodup : allocation.Nodup

abbrev SparseEntry := Sigma fun _ : Nat => Nat

structure SparseFunctionAllocation where
  canonicalCount : Nat
  productionCount : Nat
  entries : List SparseEntry
  entries_nodup_keys : entries.NodupKeys
  targets_nodup : (entries.map Sigma.snd).Nodup
  targets_bounded : ∀ entry ∈ entries, entry.snd < productionCount

inductive DecodedFunctionAllocation where
  | dense (allocation : DenseFunctionAllocation)
  | sparse (allocation : SparseFunctionAllocation)

def WireFunctionAllocation.decode (wire : WireFunctionAllocation) :
    Except String DecodedFunctionAllocation := do
  if wire.version = 1 then
    if !wire.sparse_allocation.isEmpty then
      throw "dense CB function allocation carries sparse entries"
    if hcount : wire.allocation.length = wire.canonical_count then
      if hshape : ∀ index : Fin wire.allocation.length,
          wire.allocation.get index < wire.production_count ∨
            wire.allocation.get index = wire.production_count + index.val then
        if hnodup : wire.allocation.Nodup then
          return .dense {
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
  else if wire.version = 2 then
    if !wire.allocation.isEmpty then
      throw "sparse CB function allocation carries dense entries"
    let entries : List SparseEntry := wire.sparse_allocation.map fun entry =>
      ⟨entry.source, entry.target⟩
    if hkeys' : entries.keys.Nodup then
      have hkeys : entries.NodupKeys := hkeys'
      if htargets : (entries.map Sigma.snd).Nodup then
        if hbounded : ∀ entry ∈ entries, entry.snd < wire.production_count then
          return .sparse {
            canonicalCount := wire.canonical_count
            productionCount := wire.production_count
            entries
            entries_nodup_keys := hkeys
            targets_nodup := htargets
            targets_bounded := hbounded
          }
        else throw "sparse CB function allocation target is outside function_count"
      else throw "sparse CB function allocation reuses a production Skolem id"
    else throw "sparse CB function allocation repeats a canonical Skolem id"
  else throw s!"unsupported CB function-allocation version {wire.version}"

def WireFunctionAllocation.check (wire : WireFunctionAllocation) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedFunctionAllocation.canonicalCount : DecodedFunctionAllocation → Nat
  | .dense allocation => allocation.canonicalCount
  | .sparse allocation => allocation.canonicalCount

def DecodedFunctionAllocation.productionCount : DecodedFunctionAllocation → Nat
  | .dense allocation => allocation.productionCount
  | .sparse allocation => allocation.productionCount

def DenseFunctionAllocation.rename (decoded : DenseFunctionAllocation)
    (source : Nat) : Nat :=
  if hsource : source < decoded.canonicalCount then
    decoded.allocation.get ⟨source, by simpa [decoded.allocation_count]⟩
  else decoded.productionCount + source

def SparseFunctionAllocation.rename (decoded : SparseFunctionAllocation)
    (source : Nat) : Nat :=
  (decoded.entries.dlookup source).getD (decoded.productionCount + source)

def DecodedFunctionAllocation.rename : DecodedFunctionAllocation → Nat → Nat
  | .dense allocation => allocation.rename
  | .sparse allocation => allocation.rename

theorem DenseFunctionAllocation.rename_bounded_or_sentinel
    (decoded : DenseFunctionAllocation) (source : Nat)
    (hsource : source < decoded.canonicalCount) :
    decoded.rename source < decoded.productionCount ∨
      decoded.rename source = decoded.productionCount + source := by
  rw [DenseFunctionAllocation.rename, dif_pos hsource]
  simpa only using decoded.allocation_shape
    ⟨source, by simpa [decoded.allocation_count]⟩

theorem DenseFunctionAllocation.rename_injective
    (decoded : DenseFunctionAllocation) : Function.Injective decoded.rename := by
  intro left right heq
  by_cases hleft : left < decoded.canonicalCount
  · by_cases hright : right < decoded.canonicalCount
    · simp only [DenseFunctionAllocation.rename, dif_pos hleft, dif_pos hright] at heq
      have hindex := decoded.allocation_nodup.get_inj_iff.mp heq
      exact congrArg Fin.val hindex
    · rcases decoded.rename_bounded_or_sentinel left hleft with hbounded | hsentinel
      · rw [DenseFunctionAllocation.rename, dif_pos hleft] at hbounded
        rw [DenseFunctionAllocation.rename, dif_pos hleft,
          DenseFunctionAllocation.rename, dif_neg hright] at heq
        omega
      · rw [DenseFunctionAllocation.rename, dif_pos hleft] at hsentinel
        rw [DenseFunctionAllocation.rename, dif_pos hleft,
          DenseFunctionAllocation.rename, dif_neg hright] at heq
        omega
  · by_cases hright : right < decoded.canonicalCount
    · rcases decoded.rename_bounded_or_sentinel right hright with hbounded | hsentinel
      · rw [DenseFunctionAllocation.rename, dif_pos hright] at hbounded
        rw [DenseFunctionAllocation.rename, dif_neg hleft,
          DenseFunctionAllocation.rename, dif_pos hright] at heq
        omega
      · rw [DenseFunctionAllocation.rename, dif_pos hright] at hsentinel
        rw [DenseFunctionAllocation.rename, dif_neg hleft,
          DenseFunctionAllocation.rename, dif_pos hright] at heq
        omega
    · simp only [DenseFunctionAllocation.rename, dif_neg hleft, dif_neg hright] at heq
      omega

theorem SparseFunctionAllocation.rename_injective
    (decoded : SparseFunctionAllocation) : Function.Injective decoded.rename := by
  intro left right hequal
  cases hleft : decoded.entries.dlookup left with
  | none =>
      cases hright : decoded.entries.dlookup right with
      | none =>
          simp only [SparseFunctionAllocation.rename, hleft, hright,
            Option.getD_none] at hequal
          omega
      | some rightTarget =>
          have hentry : Sigma.mk right rightTarget ∈ decoded.entries :=
            (List.mem_dlookup_iff decoded.entries_nodup_keys).mp (by simp [hright])
          have hbounded := decoded.targets_bounded _ hentry
          change rightTarget < decoded.productionCount at hbounded
          simp only [SparseFunctionAllocation.rename, hleft, hright,
            Option.getD_none, Option.getD_some] at hequal
          omega
  | some leftTarget =>
      have hleftEntry : Sigma.mk left leftTarget ∈ decoded.entries :=
        (List.mem_dlookup_iff decoded.entries_nodup_keys).mp (by simp [hleft])
      cases hright : decoded.entries.dlookup right with
      | none =>
          have hbounded := decoded.targets_bounded _ hleftEntry
          change leftTarget < decoded.productionCount at hbounded
          simp only [SparseFunctionAllocation.rename, hleft, hright,
            Option.getD_none, Option.getD_some] at hequal
          omega
      | some rightTarget =>
          have hrightEntry : Sigma.mk right rightTarget ∈ decoded.entries :=
            (List.mem_dlookup_iff decoded.entries_nodup_keys).mp (by simp [hright])
          simp only [SparseFunctionAllocation.rename, hleft, hright,
            Option.getD_some] at hequal
          have hsame := List.inj_on_of_nodup_map decoded.targets_nodup
            hleftEntry hrightEntry hequal
          exact congrArg Sigma.fst hsame

theorem DecodedFunctionAllocation.rename_injective
    (decoded : DecodedFunctionAllocation) : Function.Injective decoded.rename := by
  cases decoded with
  | dense allocation => exact allocation.rename_injective
  | sparse allocation => exact allocation.rename_injective

theorem DecodedFunctionAllocation.rename_bounded_or_sentinel
    (decoded : DecodedFunctionAllocation) (source : Nat)
    (hsource : source < decoded.canonicalCount) :
    decoded.rename source < decoded.productionCount ∨
      decoded.rename source = decoded.productionCount + source := by
  cases decoded with
  | dense allocation => exact allocation.rename_bounded_or_sentinel source hsource
  | sparse allocation =>
      cases hlookup : allocation.entries.dlookup source with
      | none =>
          right
          change allocation.rename source = allocation.productionCount + source
          simp [SparseFunctionAllocation.rename, hlookup]
      | some target =>
          left
          change allocation.rename source < allocation.productionCount
          rw [SparseFunctionAllocation.rename, hlookup]
          simpa only [Option.getD_some] using allocation.targets_bounded
            (Sigma.mk source target)
            ((List.mem_dlookup_iff allocation.entries_nodup_keys).mp (by simp [hlookup]))

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
