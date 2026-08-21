import ContextCalculus.HypertableauCardinalityProjection
import ContextCalculus.HypertableauDirectProjectionWire

/-!
# Checked cardinality projection metadata

This wire checks the production `CardDefJson` fields used by KM's source-to-HT
conversion. Exactness is not trusted as a free Boolean: every exact definition
must belong to a checked complementary maximum/minimum pair, and every member
of such a pair must be marked exact. Definitions are required to be distinct so
index-level provenance cannot be transferred to an unrelated duplicate.

The source-clause shape checker is composed in the next projection layer. This
module establishes the finite semantic contract for all cardinality definitions
at once.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireProjectionCardinalityDef where
  marker : Nat
  min : Bool
  n : Nat
  role : Nat
  filler : Nat
  exact : Bool := false
deriving FromJson, ToJson, Repr

def WireProjectionCardinalityDef.decode
    (conceptCount roleCount : Nat) (wire : WireProjectionCardinalityDef) :
    Except String (CardinalityDef (Fin conceptCount) (Fin roleCount)) := do
  return {
    marker := ← checkedFin "cardinality marker" conceptCount wire.marker
    kind := if wire.min then .minimum else .maximum
    bound := wire.n
    role := ← checkedFin "cardinality role" roleCount wire.role
    filler := ← checkedFin "cardinality filler" conceptCount wire.filler
  }

structure WireComplementaryCardinalityPair where
  maximum : Nat
  minimum : Nat
deriving FromJson, ToJson, Repr

structure IndexedComplementaryCardinalityPair
    (definitions : List (CardinalityDef Concept Role)) where
  maximum : Fin definitions.length
  minimum : Fin definitions.length
  complementary : ComplementaryCardinalityPair
    (definitions.get maximum) (definitions.get minimum)

def IndexedComplementaryCardinalityPair.toPair
    {Concept Role : Type}
    {definitions : List (CardinalityDef Concept Role)}
    (pair : IndexedComplementaryCardinalityPair definitions) :
    PairedCardinality Concept Role := {
  maximum := definitions.get pair.maximum
  minimum := definitions.get pair.minimum
  complementary := pair.complementary
}

def WireComplementaryCardinalityPair.decode
    {Concept Role : Type}
    [DecidableEq Concept] [DecidableEq Role]
    (definitions : List (CardinalityDef Concept Role))
    (wire : WireComplementaryCardinalityPair) : Except String
      (IndexedComplementaryCardinalityPair definitions) := do
  let maximum ← checkedFin "exact maximum definition" definitions.length wire.maximum
  let minimum ← checkedFin "exact minimum definition" definitions.length wire.minimum
  let maximumDefinition := definitions.get maximum
  let minimumDefinition := definitions.get minimum
  if hmaximum : maximumDefinition.kind = .maximum then
    if hminimum : minimumDefinition.kind = .minimum then
      if hbound : minimumDefinition.bound = maximumDefinition.bound + 1 then
        if hrole : minimumDefinition.role = maximumDefinition.role then
          if hfiller : minimumDefinition.filler = maximumDefinition.filler then
            return ⟨maximum, minimum, hmaximum, hminimum, hbound, hrole, hfiller⟩
          else
            throw "claimed exact cardinality pair has different fillers"
        else
          throw "claimed exact cardinality pair has different roles"
      else
        throw "claimed exact cardinality pair has non-complementary bounds"
    else
      throw "claimed exact minimum definition is not a minimum"
  else
    throw "claimed exact maximum definition is not a maximum"

def exactPairIndices
    (pairs : List (IndexedComplementaryCardinalityPair definitions)) : List Nat :=
  pairs.flatMap fun pair => [pair.maximum.val, pair.minimum.val]

structure WireCardinalityProjection where
  concept_count : Nat
  role_count : Nat
  definitions : List WireProjectionCardinalityDef
  exact_pairs : List WireComplementaryCardinalityPair
deriving FromJson, ToJson, Repr

structure DecodedCardinalityProjection where
  conceptCount : Nat
  roleCount : Nat
  definitions : List
    (CardinalityDef (Fin conceptCount) (Fin roleCount))
  wires : List WireProjectionCardinalityDef
  wireLength : wires.length = definitions.length
  uniqueDefinitions : definitions.Nodup
  pairs : List (IndexedComplementaryCardinalityPair definitions)
  uniquePairIndices : (exactPairIndices pairs).Nodup
  exactFlags : ∀ index : Fin definitions.length,
    (wires.get (wireLength.symm ▸ index)).exact =
      decide (index.val ∈ exactPairIndices pairs)

def WireCardinalityProjection.decode (wire : WireCardinalityProjection) :
    Except String DecodedCardinalityProjection := do
  let definitions ← wire.definitions.mapM
    (WireProjectionCardinalityDef.decode wire.concept_count wire.role_count)
  if hlength : wire.definitions.length = definitions.length then
    if hdefinitions : definitions.Nodup then
      let pairs ← wire.exact_pairs.mapM
        (WireComplementaryCardinalityPair.decode definitions)
      if hpairs : (exactPairIndices pairs).Nodup then
        if hflags : ∀ index : Fin definitions.length,
            (wire.definitions.get (hlength.symm ▸ index)).exact =
              decide (index.val ∈ exactPairIndices pairs) then
          return {
            conceptCount := wire.concept_count
            roleCount := wire.role_count
            definitions
            wires := wire.definitions
            wireLength := hlength
            uniqueDefinitions := hdefinitions
            pairs
            uniquePairIndices := hpairs
            exactFlags := hflags
          }
        else
          throw "cardinality exact flags differ from checked complementary-pair provenance"
      else
        throw "an exact cardinality definition occurs in more than one complementary pair"
    else
      throw "cardinality projection contains duplicate definitions"
  else
    throw "internal cardinality-definition decode length mismatch"

def WireCardinalityProjection.check (wire : WireCardinalityProjection) :
    Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedCardinalityProjection.semanticPairs
    (decoded : DecodedCardinalityProjection) :
    List (PairedCardinality (Fin decoded.conceptCount) (Fin decoded.roleCount)) :=
  decoded.pairs.map IndexedComplementaryCardinalityPair.toPair

theorem DecodedCardinalityProjection.semanticPairs_mem
    (decoded : DecodedCardinalityProjection)
    (pair : PairedCardinality (Fin decoded.conceptCount) (Fin decoded.roleCount))
    (hpair : pair ∈ decoded.semanticPairs) :
    pair.maximum ∈ decoded.definitions ∧ pair.minimum ∈ decoded.definitions := by
  simp only [DecodedCardinalityProjection.semanticPairs, List.mem_map] at hpair
  rcases hpair with
    ⟨indexed, _, rfl⟩
  exact ⟨List.get_mem decoded.definitions indexed.maximum,
    List.get_mem decoded.definitions indexed.minimum⟩

theorem DecodedCardinalityProjection.models_source_iff_target
    (decoded : DecodedCardinalityProjection)
    (I : Interp Domain (Fin decoded.conceptCount) (Fin decoded.roleCount)) :
    I.modelsProjectedCardinalityDefs decoded.definitions decoded.semanticPairs ↔
      I.modelsProjectedCardinalityTargets decoded.definitions decoded.semanticPairs := by
  exact modelsProjectedCardinalityDefs_iff_targets I decoded.definitions
    decoded.semanticPairs (fun pair hpair => decoded.semanticPairs_mem pair hpair)

theorem WireCardinalityProjection.check_sound
    (wire : WireCardinalityProjection)
    (decoded : DecodedCardinalityProjection)
    (_hdecode : wire.decode = .ok decoded)
    (_hcheck : wire.check = .ok true)
    (I : Interp Domain (Fin decoded.conceptCount) (Fin decoded.roleCount)) :
    I.modelsProjectedCardinalityDefs decoded.definitions decoded.semanticPairs ↔
      I.modelsProjectedCardinalityTargets decoded.definitions decoded.semanticPairs :=
  decoded.models_source_iff_target I

private def acceptedCardinalityProjection : WireCardinalityProjection where
  concept_count := 4
  role_count := 1
  definitions := [
    ⟨0, false, 1, 0, 2, true⟩,
    ⟨1, true, 2, 0, 2, true⟩,
    ⟨3, true, 3, 0, 2, false⟩
  ]
  exact_pairs := [⟨0, 1⟩]

private def projectionRejected (result : Except String Bool) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

example : acceptedCardinalityProjection.check = .ok true := by native_decide

example : projectionRejected ({ acceptedCardinalityProjection with
    definitions := acceptedCardinalityProjection.definitions.set 2
      ⟨3, true, 3, 0, 2, true⟩ }).check = true := by native_decide

example : projectionRejected ({ acceptedCardinalityProjection with
    definitions := acceptedCardinalityProjection.definitions.set 1
      ⟨1, true, 2, 0, 3, true⟩ }).check = true := by native_decide

#print axioms DecodedCardinalityProjection.models_source_iff_target
#print axioms WireCardinalityProjection.check_sound

end ContextCalculus.Hypertableau
