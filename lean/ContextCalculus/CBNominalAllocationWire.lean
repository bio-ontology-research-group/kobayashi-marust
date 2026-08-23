import ContextCalculus.CBProductionTraceWire

/-!
# Executable allocation evidence for production CB Nom firings

Nom is not an ordinary local derivation step.  Its soundness theorem chooses
interpretations for fresh individual constants, and a complete run may make
many such choices.  This wire checks the operational side condition required
by `Nominals.nom_family_sound`: every exact grounded Hyper firing owns one
stable, nonempty, consecutive block, and all blocks are globally fresh and
disjoint.  It also checks exact budget accounting and rejects truncated runs.

The semantic connection from each firing key to its covering premise remains a
separate certificate layer.  Keeping allocation evidence separate prevents a
Nom conclusion from being incorrectly justified as ordinary resolution.
-/

namespace ContextCalculus.CBNominalAllocationWire

open Lean ContextCalculus.CBTermWire ContextCalculus.CBSourceWire

structure WireNominalFiringKey where
  context : Nat
  source_body : List WirePredicate
  source_head : List WireLiteral
  side_body : List WirePredicate
  side_head : List WireLiteral
  selected : List (Nat × WirePredicate)
  substitution : List WireSubstitutionEntry
deriving DecidableEq, FromJson, ToJson

structure WireNominalBlock where
  key : WireNominalFiringKey
  first : Nat
  width : Nat
deriving DecidableEq, FromJson, ToJson

structure WireNominalAllocation where
  version : Nat
  source : WireSourceBinding
  individual_count : Nat
  budget : Nat
  allocated : Nat
  truncated : Bool
  blocks : List WireNominalBlock
deriving FromJson, ToJson

structure NominalFiringKey where
  context : Nat
  sourceBody : List CheckerTerm.FPred
  sourceHead : List CheckerTerm.FLit
  sideBody : List CheckerTerm.FPred
  sideHead : List CheckerTerm.FLit
  selected : List (Nat × CheckerTerm.FPred)
  substitution : List (Int × CheckerTerm.FTerm)

structure NominalBlock where
  wireKey : WireNominalFiringKey
  key : NominalFiringKey
  first : Nat
  width : Nat

private def decodeSelected (bounds : Bounds)
    (entry : Nat × WirePredicate) :
    Except String (Nat × CheckerTerm.FPred) := do
  let predicate ← entry.2.decode bounds
  return (entry.1, predicate)

def WireNominalFiringKey.decode (bounds : Bounds)
    (wire : WireNominalFiringKey) : Except String NominalFiringKey := do
  let variableIds := wire.substitution.map WireSubstitutionEntry.variableId
  if !wire.selected.isEmpty then
    if variableIds.Nodup then
      return {
        context := wire.context
        sourceBody := ← wire.source_body.mapM (WirePredicate.decode bounds)
        sourceHead := ← wire.source_head.mapM (WireLiteral.decode bounds)
        sideBody := ← wire.side_body.mapM (WirePredicate.decode bounds)
        sideHead := ← wire.side_head.mapM (WireLiteral.decode bounds)
        selected := ← wire.selected.mapM (decodeSelected bounds)
        substitution := ← wire.substitution.mapM
          (WireSubstitutionEntry.decode bounds)
      }
    else throw "Nom firing substitution contains a duplicate variable"
  else throw "Nom firing must select at least one matched predicate"

def WireNominalBlock.decode (bounds : Bounds)
    (wire : WireNominalBlock) : Except String NominalBlock := do
  let key ← wire.key.decode bounds
  return { wireKey := wire.key, key, first := wire.first, width := wire.width }

def blockIds (block : NominalBlock) : List Nat :=
  (List.range block.width).map (block.first + ·)

def allBlockIds (blocks : List NominalBlock) : List Nat :=
  blocks.flatMap blockIds

def sequentialFrom : Nat → List NominalBlock → Bool
  | _, [] => true
  | cursor, block :: rest =>
      decide (block.first = cursor) &&
        sequentialFrom (cursor + block.width) rest

structure DecodedNominalAllocation where
  source : DecodedSourceBinding
  individualCount : Nat
  source_count_le : source.bounds.individuals ≤ individualCount
  budget : Nat
  allocated : Nat
  blocks : List NominalBlock
  keys_nodup : (blocks.map (·.wireKey)).Nodup
  widths_positive : ∀ block ∈ blocks, 0 < block.width
  sequential : sequentialFrom source.bounds.individuals blocks = true
  ids_nodup : (allBlockIds blocks).Nodup
  ids_fresh : ∀ id ∈ allBlockIds blocks,
    source.bounds.individuals ≤ id ∧ id < individualCount
  allocated_eq : allocated = (blocks.map (·.width)).sum
  allocated_le_budget : allocated ≤ budget

def WireNominalAllocation.decode (wire : WireNominalAllocation) :
    Except String DecodedNominalAllocation := do
  if wire.version != 1 then
    throw s!"unsupported CB Nom-allocation version {wire.version}"
  if wire.truncated then
    throw "CB Nom allocation was truncated"
  let source ← wire.source.decode
  if hcount : source.bounds.individuals ≤ wire.individual_count then
    let bounds := { source.bounds with individuals := wire.individual_count }
    let blocks ← wire.blocks.mapM (WireNominalBlock.decode bounds)
    if blocks.isEmpty then
      throw "CB Nom allocation must contain at least one firing"
    if hkeys : (blocks.map (·.wireKey)).Nodup then
      if hwidths : ∀ block ∈ blocks, 0 < block.width then
        if hsequential : sequentialFrom source.bounds.individuals blocks = true then
          if hids : (allBlockIds blocks).Nodup then
            if hfresh : ∀ id ∈ allBlockIds blocks,
                source.bounds.individuals ≤ id ∧ id < wire.individual_count then
              if hallocated : wire.allocated = (blocks.map (·.width)).sum then
                if hbudget : wire.allocated ≤ wire.budget then
                  return {
                    source
                    individualCount := wire.individual_count
                    source_count_le := hcount
                    budget := wire.budget
                    allocated := wire.allocated
                    blocks
                    keys_nodup := hkeys
                    widths_positive := hwidths
                    sequential := hsequential
                    ids_nodup := hids
                    ids_fresh := hfresh
                    allocated_eq := hallocated
                    allocated_le_budget := hbudget
                  }
                else throw "CB Nom allocation exceeds its declared budget"
              else throw "CB Nom allocated count differs from the block widths"
            else throw "CB Nom block contains a non-fresh or out-of-range individual"
          else throw "CB Nom blocks overlap"
        else throw "CB Nom blocks are not one consecutive allocation sequence"
      else throw "CB Nom block has zero width"
    else throw "CB Nom firing key occurs more than once"
  else throw "CB Nom individual table is smaller than the source individual table"

def WireNominalAllocation.check (wire : WireNominalAllocation) :
    Except String Bool := do
  let _ ← wire.decode
  return true

theorem WireNominalAllocation.check_sound (wire : WireNominalAllocation)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedNominalAllocation,
      wire.decode = .ok decoded ∧
      (decoded.blocks.map (·.wireKey)).Nodup ∧
      (allBlockIds decoded.blocks).Nodup ∧
      (∀ id ∈ allBlockIds decoded.blocks,
        decoded.source.bounds.individuals ≤ id ∧
          id < decoded.individualCount) ∧
      decoded.allocated = (decoded.blocks.map (·.width)).sum ∧
      decoded.allocated ≤ decoded.budget := by
  cases hdecode : wire.decode with
  | error message => simp [WireNominalAllocation.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.keys_nodup, decoded.ids_nodup,
        decoded.ids_fresh, decoded.allocated_eq, decoded.allocated_le_budget⟩

private def conceptAt (concept individual : Nat) : WirePredicate :=
  .concept concept (.constant individual)

private def exampleKey (context : Nat) : WireNominalFiringKey where
  context
  source_body := [.role 0 (.constant 0) (.var (-1))]
  source_head := [.equality (.var (-1)) (.var (-1))]
  side_body := [.concept 0 (.var (-1))]
  side_head := []
  selected := [(0, conceptAt 0 0)]
  substitution := [{ variableId := 0, term := .constant 0 }]

private def exampleSource : WireSourceBinding where
  version := 1
  concept_count := 1
  role_count := 1
  function_count := 0
  individual_count := 1
  source_clauses := []
  role_chains := []
  ontology := []

private def acceptedExample : WireNominalAllocation where
  version := 1
  source := exampleSource
  individual_count := 4
  budget := 3
  allocated := 3
  truncated := false
  blocks :=
    [{ key := exampleKey 0, first := 1, width := 2 },
     { key := exampleKey 1, first := 3, width := 1 }]

example : acceptedExample.check = .ok true := by native_decide

private def overlappingExample : WireNominalAllocation :=
  { acceptedExample with
    blocks :=
      [{ key := exampleKey 0, first := 1, width := 2 },
       { key := exampleKey 1, first := 2, width := 1 }] }

private def rejected (result : Except String Bool) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

example : rejected overlappingExample.check = true := by native_decide

private def replayedKeyExample : WireNominalAllocation :=
  { acceptedExample with
    blocks :=
      [{ key := exampleKey 0, first := 1, width := 2 },
       { key := exampleKey 0, first := 3, width := 1 }] }

example : rejected replayedKeyExample.check = true := by native_decide

private def truncatedExample : WireNominalAllocation :=
  { acceptedExample with truncated := true }

example : rejected truncatedExample.check = true := by native_decide

#print axioms WireNominalAllocation.check_sound

end ContextCalculus.CBNominalAllocationWire
