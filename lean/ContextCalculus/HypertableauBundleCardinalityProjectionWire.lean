import ContextCalculus.HypertableauBundleProjectionWire
import ContextCalculus.HypertableauBundleCardinalityProjection
import ContextCalculus.HypertableauCardinalityProjectionWire

/-!
# Checked bundle, RBox, and cardinality projection wire

The bundle decoder remains the sole authority for direct clauses, bundles,
domain consequences, and target clauses.  This wrapper adds cardinality
families over the bundle source signature and composes both checks into the
joint semantic theorem.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireBundleCardinalityProjection where
  bundle : WireBundleProjection
  definitions : List WireProjectionCardinalityDef
  exact_pairs : List WireComplementaryCardinalityPair
deriving FromJson, ToJson, Repr

structure DecodedBundleCardinalityProjection where
  bundle : DecodedBundleProjection
  definitions : List
    (CardinalityDef (Fin bundle.sourceConcepts.length) (Fin bundle.roles.length))
  definitionWires : List WireProjectionCardinalityDef
  wireLength : definitionWires.length = definitions.length
  uniqueDefinitions : definitions.Nodup
  pairs : List (IndexedComplementaryCardinalityPair definitions)
  uniquePairIndices : (exactPairIndices pairs).Nodup
  exactFlags : ∀ index : Fin definitions.length,
    (definitionWires.get (wireLength.symm ▸ index)).exact =
      decide (index.val ∈ exactPairIndices pairs)

def WireBundleCardinalityProjection.decode
    (wire : WireBundleCardinalityProjection) :
    Except String DecodedBundleCardinalityProjection := do
  let bundle ← wire.bundle.decode
  let definitions ← wire.definitions.mapM
    (WireProjectionCardinalityDef.decode
      bundle.sourceConcepts.length bundle.roles.length)
  if hlength : wire.definitions.length = definitions.length then
    if hdefinitions : definitions.Nodup then
      let pairs ← wire.exact_pairs.mapM
        (WireComplementaryCardinalityPair.decode definitions)
      if hpairs : (exactPairIndices pairs).Nodup then
        if hflags : ∀ index : Fin definitions.length,
            (wire.definitions.get (hlength.symm ▸ index)).exact =
              decide (index.val ∈ exactPairIndices pairs) then
          return {
            bundle
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

def WireBundleCardinalityProjection.check
    (wire : WireBundleCardinalityProjection) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedBundleCardinalityProjection.semanticPairs
    (decoded : DecodedBundleCardinalityProjection) :
    List (PairedCardinality (Fin decoded.bundle.sourceConcepts.length)
      (Fin decoded.bundle.roles.length)) :=
  decoded.pairs.map IndexedComplementaryCardinalityPair.toPair

theorem DecodedBundleCardinalityProjection.semanticPairs_mem
    (decoded : DecodedBundleCardinalityProjection)
    (pair : PairedCardinality (Fin decoded.bundle.sourceConcepts.length)
      (Fin decoded.bundle.roles.length))
    (hpair : pair ∈ decoded.semanticPairs) :
    pair.maximum ∈ decoded.definitions ∧ pair.minimum ∈ decoded.definitions := by
  simp only [DecodedBundleCardinalityProjection.semanticPairs, List.mem_map] at hpair
  rcases hpair with ⟨indexed, _, rfl⟩
  exact ⟨List.get_mem decoded.definitions indexed.maximum,
    List.get_mem decoded.definitions indexed.minimum⟩

theorem DecodedBundleCardinalityProjection.models_source_iff_target
    (decoded : DecodedBundleCardinalityProjection)
    (base : SkolemInterp Domain (Fin decoded.bundle.functions.length)) :
    (∃ I : Interp Domain (Fin decoded.bundle.sourceConcepts.length)
        (Fin decoded.bundle.roles.length),
      ∃ functions : SkolemInterp Domain (Fin decoded.bundle.functions.length),
        I.models decoded.bundle.direct ∧
          ModelsBundles I functions (decodedBundleSpecs decoded.bundle.bundles) ∧
          I.modelsProjectedCardinalityDefs
            decoded.definitions decoded.semanticPairs) ↔
    (∃ J : Interp Domain (Fin decoded.bundle.concepts.length)
        (Fin decoded.bundle.roles.length),
      J.models decoded.bundle.target ∧
        J.modelsPairedCardinalityTargets
          ((decoded.definitions.map (renameCardinalityDef Sum.inr)).map
            (renameCardinalityDef
              (bundleConceptEmbedding decoded.bundle.sourceTargets
                decoded.bundle.bundles)))
          ((decoded.semanticPairs.map (renamePairedCardinality Sum.inr)).map
            (renamePairedCardinality
              (bundleConceptEmbedding decoded.bundle.sourceTargets
                decoded.bundle.bundles)))) := by
  have hpositive : 0 < decoded.bundle.bundles.length :=
    List.length_pos_of_ne_nil decoded.bundle.nonemptyBundles
  letI : Nonempty (Sum (Fin decoded.bundle.bundles.length)
      (Fin decoded.bundle.sourceConcepts.length)) := ⟨.inl ⟨0, hpositive⟩⟩
  obtain ⟨inverse, hleft⟩ := decoded.bundle.embeddingInjective.hasLeftInverse
  rw [indexedBundleDomainCardinalityProjection_renamed_sat_iff base
    decoded.bundle.direct (decodedBundleSpecs decoded.bundle.bundles)
    decoded.bundle.uniqueFunctions decoded.bundle.domainExtras
    decoded.bundle.rboxSource decoded.bundle.rboxTarget decoded.bundle.rboxDistinct
    decoded.bundle.pathPremises decoded.bundle.domainPremises decoded.definitions
    decoded.semanticPairs
    (fun pair hpair => decoded.semanticPairs_mem pair hpair)
    (bundleConceptEmbedding decoded.bundle.sourceTargets decoded.bundle.bundles)
    inverse hleft]
  constructor
  · rintro ⟨J, hmodels, hcardinality⟩
    exact ⟨J, (models_iff_of_toFinset_eq J _ _
      decoded.bundle.exactProjection).1 hmodels, hcardinality⟩
  · rintro ⟨J, hmodels, hcardinality⟩
    exact ⟨J, (models_iff_of_toFinset_eq J _ _
      decoded.bundle.exactProjection).2 hmodels, hcardinality⟩

theorem WireBundleCardinalityProjection.check_sound
    (wire : WireBundleCardinalityProjection)
    (decoded : DecodedBundleCardinalityProjection)
    (_hdecode : wire.decode = .ok decoded)
    (_hcheck : wire.check = .ok true)
    (base : SkolemInterp Domain (Fin decoded.bundle.functions.length)) :
    (∃ I : Interp Domain (Fin decoded.bundle.sourceConcepts.length)
        (Fin decoded.bundle.roles.length),
      ∃ functions : SkolemInterp Domain (Fin decoded.bundle.functions.length),
        I.models decoded.bundle.direct ∧
          ModelsBundles I functions (decodedBundleSpecs decoded.bundle.bundles) ∧
          I.modelsProjectedCardinalityDefs
            decoded.definitions decoded.semanticPairs) ↔
    (∃ J : Interp Domain (Fin decoded.bundle.concepts.length)
        (Fin decoded.bundle.roles.length),
      J.models decoded.bundle.target ∧
        J.modelsPairedCardinalityTargets
          ((decoded.definitions.map (renameCardinalityDef Sum.inr)).map
            (renameCardinalityDef
              (bundleConceptEmbedding decoded.bundle.sourceTargets
                decoded.bundle.bundles)))
          ((decoded.semanticPairs.map (renamePairedCardinality Sum.inr)).map
            (renamePairedCardinality
              (bundleConceptEmbedding decoded.bundle.sourceTargets
                decoded.bundle.bundles)))) :=
  decoded.models_source_iff_target base

#print axioms DecodedBundleCardinalityProjection.models_source_iff_target
#print axioms WireBundleCardinalityProjection.check_sound

end ContextCalculus.Hypertableau
