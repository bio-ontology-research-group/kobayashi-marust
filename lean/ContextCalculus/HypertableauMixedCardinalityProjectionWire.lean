import ContextCalculus.HypertableauMixedProjectionWire
import ContextCalculus.HypertableauCardinalityProjectionWire

/-!
# Checked mixed Skolem-pair and cardinality projection

Both transformations retain the same finite concept and role signature.  The
joint wire reuses the complete mixed decoder, checks cardinality provenance,
and composes both semantic equivalences in one interpretation.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireMixedCardinalityProjection where
  mixed : WireMixedProjection
  definitions : List WireProjectionCardinalityDef
  exact_pairs : List WireComplementaryCardinalityPair
deriving FromJson, ToJson, Repr

structure DecodedMixedCardinalityProjection where
  mixed : DecodedMixedProjection
  definitions : List
    (CardinalityDef (Fin mixed.concepts.length) (Fin mixed.roles.length))
  definitionWires : List WireProjectionCardinalityDef
  wireLength : definitionWires.length = definitions.length
  uniqueDefinitions : definitions.Nodup
  pairs : List (IndexedComplementaryCardinalityPair definitions)
  uniquePairIndices : (exactPairIndices pairs).Nodup
  exactFlags : ∀ index : Fin definitions.length,
    (definitionWires.get (wireLength.symm ▸ index)).exact =
      decide (index.val ∈ exactPairIndices pairs)

def WireMixedCardinalityProjection.decode
    (wire : WireMixedCardinalityProjection) :
    Except String DecodedMixedCardinalityProjection := do
  let mixed ← wire.mixed.decode
  let definitions ← wire.definitions.mapM
    (WireProjectionCardinalityDef.decode mixed.concepts.length mixed.roles.length)
  if hlength : wire.definitions.length = definitions.length then
    if hdefinitions : definitions.Nodup then
      let pairs ← wire.exact_pairs.mapM
        (WireComplementaryCardinalityPair.decode definitions)
      if hpairs : (exactPairIndices pairs).Nodup then
        if hflags : ∀ index : Fin definitions.length,
            (wire.definitions.get (hlength.symm ▸ index)).exact =
              decide (index.val ∈ exactPairIndices pairs) then
          return {
            mixed
            definitions
            definitionWires := wire.definitions
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

def WireMixedCardinalityProjection.check
    (wire : WireMixedCardinalityProjection) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedMixedCardinalityProjection.semanticPairs
    (decoded : DecodedMixedCardinalityProjection) :
    List (PairedCardinality (Fin decoded.mixed.concepts.length)
      (Fin decoded.mixed.roles.length)) :=
  decoded.pairs.map IndexedComplementaryCardinalityPair.toPair

theorem DecodedMixedCardinalityProjection.semanticPairs_mem
    (decoded : DecodedMixedCardinalityProjection)
    (pair : PairedCardinality (Fin decoded.mixed.concepts.length)
      (Fin decoded.mixed.roles.length))
    (hpair : pair ∈ decoded.semanticPairs) :
    pair.maximum ∈ decoded.definitions ∧ pair.minimum ∈ decoded.definitions := by
  simp only [DecodedMixedCardinalityProjection.semanticPairs, List.mem_map] at hpair
  rcases hpair with ⟨indexed, _, rfl⟩
  exact ⟨List.get_mem decoded.definitions indexed.maximum,
    List.get_mem decoded.definitions indexed.minimum⟩

theorem DecodedMixedCardinalityProjection.models_source_iff_target
    (decoded : DecodedMixedCardinalityProjection)
    (I : Interp Domain (Fin decoded.mixed.concepts.length)
      (Fin decoded.mixed.roles.length))
    (base : SkolemInterp Domain (Fin decoded.mixed.functions.length)) :
    (∃ functions : SkolemInterp Domain (Fin decoded.mixed.functions.length),
      I.models decoded.mixed.direct ∧
        ModelsSkolemPairs I functions decoded.mixed.pairs ∧
        I.modelsProjectedCardinalityDefs
          decoded.definitions decoded.semanticPairs) ↔
    (I.models decoded.mixed.target ∧
      I.modelsPairedCardinalityTargets
        decoded.definitions decoded.semanticPairs) := by
  have hmixed := decoded.mixed.models_source_iff_target I base
  have hcardinality := modelsProjectedCardinalityDefs_iff_pairedTargets
    I decoded.definitions decoded.semanticPairs
    (fun pair hpair => decoded.semanticPairs_mem pair hpair)
  constructor
  · rintro ⟨functions, hdirect, hpairs, hcardinalitySource⟩
    exact ⟨hmixed.1 ⟨functions, hdirect, hpairs⟩,
      hcardinality.1 hcardinalitySource⟩
  · rintro ⟨htarget, hcardinalityTarget⟩
    rcases hmixed.2 htarget with ⟨functions, hdirect, hpairs⟩
    exact ⟨functions, hdirect, hpairs, hcardinality.2 hcardinalityTarget⟩

theorem WireMixedCardinalityProjection.check_sound
    (wire : WireMixedCardinalityProjection)
    (decoded : DecodedMixedCardinalityProjection)
    (_hdecode : wire.decode = .ok decoded)
    (_hcheck : wire.check = .ok true)
    (I : Interp Domain (Fin decoded.mixed.concepts.length)
      (Fin decoded.mixed.roles.length))
    (base : SkolemInterp Domain (Fin decoded.mixed.functions.length)) :
    (∃ functions : SkolemInterp Domain (Fin decoded.mixed.functions.length),
      I.models decoded.mixed.direct ∧
        ModelsSkolemPairs I functions decoded.mixed.pairs ∧
        I.modelsProjectedCardinalityDefs
          decoded.definitions decoded.semanticPairs) ↔
    (I.models decoded.mixed.target ∧
      I.modelsPairedCardinalityTargets
        decoded.definitions decoded.semanticPairs) :=
  decoded.models_source_iff_target I base

#print axioms DecodedMixedCardinalityProjection.models_source_iff_target
#print axioms WireMixedCardinalityProjection.check_sound

end ContextCalculus.Hypertableau
