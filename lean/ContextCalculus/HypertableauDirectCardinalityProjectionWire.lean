import ContextCalculus.HypertableauCardinalityProjectionWire
import ContextCalculus.HypertableauMixedProjectionWire

/-!
# Combined direct and cardinality source projection

This is the production boundary for ontologies whose non-cardinality residual
is projected directly. One decoder fixes a single concept, role, and variable
signature for the residual source, exact HT target, first-class cardinality
definitions, and exact complementary pairs. Acceptance therefore proves the
conjunction of both source components equivalent to the conjunction consumed
by the hypertableau.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireDirectCardinalityProjection where
  variable_count : Nat
  concepts : List String
  roles : List String
  source : List WireDirectSourceClause
  target : List WireClause
  definitions : List WireProjectionCardinalityDef
  exact_pairs : List WireComplementaryCardinalityPair
deriving FromJson, ToJson, Repr

structure DecodedDirectCardinalityProjection where
  variableCount : Nat
  concepts : List String
  roles : List String
  source : List
    (Clause (Fin variableCount) (Fin concepts.length) (Fin roles.length))
  target : List
    (Clause (Fin variableCount) (Fin concepts.length) (Fin roles.length))
  exactProjection : source.toFinset = target.toFinset
  definitions : List
    (CardinalityDef (Fin concepts.length) (Fin roles.length))
  definitionWires : List WireProjectionCardinalityDef
  wireLength : definitionWires.length = definitions.length
  uniqueDefinitions : definitions.Nodup
  pairs : List (IndexedComplementaryCardinalityPair definitions)
  uniquePairIndices : (exactPairIndices pairs).Nodup
  exactFlags : ∀ index : Fin definitions.length,
    (definitionWires.get (wireLength.symm ▸ index)).exact =
      decide (index.val ∈ exactPairIndices pairs)

def WireDirectCardinalityProjection.decode
    (wire : WireDirectCardinalityProjection) :
    Except String DecodedDirectCardinalityProjection := do
  if _hconcepts : wire.concepts.Nodup then
    if _hroles : wire.roles.Nodup then
      let source ← wire.source.mapM
        (WireDirectSourceClause.decode wire.variable_count wire.concepts wire.roles)
      let target ← wire.target.mapM
        (WireClause.decode wire.variable_count wire.concepts.length wire.roles.length)
      if hprojection : source.toFinset = target.toFinset then
        let definitions ← wire.definitions.mapM
          (WireProjectionCardinalityDef.decode wire.concepts.length wire.roles.length)
        if hlength : wire.definitions.length = definitions.length then
          if hdefinitions : definitions.Nodup then
            let pairs ← wire.exact_pairs.mapM
              (WireComplementaryCardinalityPair.decode definitions)
            if hpairs : (exactPairIndices pairs).Nodup then
              if hflags : ∀ index : Fin definitions.length,
                  (wire.definitions.get (hlength.symm ▸ index)).exact =
                    decide (index.val ∈ exactPairIndices pairs) then
                return {
                  variableCount := wire.variable_count
                  concepts := wire.concepts
                  roles := wire.roles
                  source
                  target
                  exactProjection := hprojection
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
      else
        throw "direct residual conversion differs from the claimed HT ontology"
    else
      throw "HT role-name table contains duplicates"
  else
    throw "HT concept-name table contains duplicates"

def WireDirectCardinalityProjection.check
    (wire : WireDirectCardinalityProjection) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedDirectCardinalityProjection.semanticPairs
    (decoded : DecodedDirectCardinalityProjection) :
    List (PairedCardinality (Fin decoded.concepts.length) (Fin decoded.roles.length)) :=
  decoded.pairs.map IndexedComplementaryCardinalityPair.toPair

theorem DecodedDirectCardinalityProjection.semanticPairs_mem
    (decoded : DecodedDirectCardinalityProjection)
    (pair : PairedCardinality (Fin decoded.concepts.length) (Fin decoded.roles.length))
    (hpair : pair ∈ decoded.semanticPairs) :
    pair.maximum ∈ decoded.definitions ∧ pair.minimum ∈ decoded.definitions := by
  simp only [DecodedDirectCardinalityProjection.semanticPairs, List.mem_map] at hpair
  rcases hpair with ⟨indexed, _, rfl⟩
  exact ⟨List.get_mem decoded.definitions indexed.maximum,
    List.get_mem decoded.definitions indexed.minimum⟩

theorem DecodedDirectCardinalityProjection.models_source_iff_target
    (decoded : DecodedDirectCardinalityProjection)
    (I : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length)) :
    (I.models decoded.source ∧
      I.modelsProjectedCardinalityDefs decoded.definitions decoded.semanticPairs) ↔
    (I.models decoded.target ∧
      I.modelsProjectedCardinalityTargets decoded.definitions decoded.semanticPairs) := by
  have hdirect : I.models decoded.source ↔ I.models decoded.target := by
    exact models_iff_of_toFinset_eq I decoded.source decoded.target
      decoded.exactProjection
  constructor
  · rintro ⟨hsource, hcardinality⟩
    constructor
    · exact hdirect.1 hsource
    · exact (modelsProjectedCardinalityDefs_iff_targets I decoded.definitions
        decoded.semanticPairs
        (fun pair hpair => decoded.semanticPairs_mem pair hpair)).1 hcardinality
  · rintro ⟨htarget, hcardinality⟩
    constructor
    · exact hdirect.2 htarget
    · exact (modelsProjectedCardinalityDefs_iff_targets I decoded.definitions
        decoded.semanticPairs
        (fun pair hpair => decoded.semanticPairs_mem pair hpair)).2 hcardinality

theorem WireDirectCardinalityProjection.check_sound
    (wire : WireDirectCardinalityProjection)
    (decoded : DecodedDirectCardinalityProjection)
    (_hdecode : wire.decode = .ok decoded)
    (_hcheck : wire.check = .ok true)
    (I : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length)) :
    (I.models decoded.source ∧
      I.modelsProjectedCardinalityDefs decoded.definitions decoded.semanticPairs) ↔
    (I.models decoded.target ∧
      I.modelsProjectedCardinalityTargets decoded.definitions decoded.semanticPairs) :=
  decoded.models_source_iff_target I

private def combinedExample : WireDirectCardinalityProjection where
  variable_count := 1
  concepts := ["Qmax", "Qmin", "C", "A", "B"]
  roles := ["r"]
  source := [{
    variableNames := ["x"]
    body := [.con "A" "x" false]
    head := [.con "B" "x" false]
  }]
  target := [{
    body := [.concept ⟨3, false⟩ 0]
    head := [.concept ⟨4, false⟩ 0]
  }]
  definitions := [
    ⟨0, false, 1, 0, 2, true⟩,
    ⟨1, true, 2, 0, 2, true⟩
  ]
  exact_pairs := [⟨0, 1⟩]

private def combinedRejected (result : Except String Bool) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

example : combinedExample.check = .ok true := by native_decide

example : combinedRejected ({ combinedExample with target := [] }).check = true := by
  native_decide

example : combinedRejected ({ combinedExample with
    definitions := combinedExample.definitions.set 1
      ⟨1, true, 2, 0, 2, false⟩ }).check = true := by
  native_decide

#print axioms DecodedDirectCardinalityProjection.models_source_iff_target
#print axioms WireDirectCardinalityProjection.check_sound

end ContextCalculus.Hypertableau
