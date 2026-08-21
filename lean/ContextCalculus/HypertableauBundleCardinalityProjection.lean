import ContextCalculus.HypertableauSkolemBundleListProjection
import ContextCalculus.HypertableauCardinalityRenaming
import ContextCalculus.HypertableauBundleDomainProjection

/-!
# Joint Skolem-bundle and cardinality projection

The production projection performs both transformations in one ontology.  This
module composes their semantic contracts over one shared interpretation.  In
particular, the source side contains the actual frontend cardinality families,
not an already interpreted cardinality assumption.
-/

namespace ContextCalculus.Hypertableau

theorem indexedBundleCardinalityProjection_sat_iff
    [DecidableEq Function]
    (base : SkolemInterp Domain Function)
    (direct : List (Clause Variable Concept Role))
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (hunique : (skolemPairFunctions (indexedBundlePairs specs)).Nodup)
    (definitions : List (CardinalityDef Concept Role))
    (pairs : List (PairedCardinality Concept Role))
    (hpairs : ∀ pair ∈ pairs,
      pair.maximum ∈ definitions ∧ pair.minimum ∈ definitions) :
    (∃ I : Interp Domain Concept Role,
      ∃ functions : SkolemInterp Domain Function,
        I.models direct ∧
          ModelsBundles I functions specs ∧
          I.modelsProjectedCardinalityDefs definitions pairs) ↔
    (∃ J : Interp Domain (Sum (Fin n) Concept) Role,
      J.models (indexedBundleOntology direct specs) ∧
        J.modelsPairedCardinalityTargets
          (definitions.map (renameCardinalityDef Sum.inr))
          (pairs.map (renamePairedCardinality Sum.inr))) := by
  constructor
  · rintro ⟨I, functions, hdirect, hbundles, hcardinality⟩
    let J := indexedBundleExtension I specs
    refine ⟨J,
      indexedBundleProjection_sound I functions direct specs hdirect hbundles, ?_⟩
    apply (modelsPairedCardinalityTargets_rename_pullback_iff
      Sum.inr J definitions pairs).2
    simpa [J, pullbackConcepts, indexedBundleExtension] using
      (modelsProjectedCardinalityDefs_iff_pairedTargets
        I definitions pairs hpairs).1 hcardinality
  · rintro ⟨J, htarget, hcardinality⟩
    rcases indexedBundleProjection_complete J base direct specs hunique htarget with
      ⟨functions, hdirect, hbundles⟩
    refine ⟨indexedRestrict J, functions, hdirect, hbundles, ?_⟩
    apply (modelsProjectedCardinalityDefs_iff_pairedTargets
      (indexedRestrict J) definitions pairs hpairs).2
    simpa [pullbackConcepts, indexedRestrict] using
      (modelsPairedCardinalityTargets_rename_pullback_iff
        Sum.inr J definitions pairs).1 hcardinality

theorem indexedBundleDomainCardinalityProjection_sat_iff
    [DecidableEq Variable] [DecidableEq Function]
    (base : SkolemInterp Domain Function)
    (direct : List (Clause Variable Concept Role))
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (hunique : (skolemPairFunctions (indexedBundlePairs specs)).Nodup)
    (domains : List (IndexedBundleDomainSpec Concept Role n))
    (source target : Variable) (hne : source ≠ target)
    (hpaths : ∀ spec ∈ domains, ∀ clause ∈
      roleInclusionPathClauses (Concept := Concept)
        (specs spec.bundle).role spec.path source target,
      clause ∈ direct)
    (hdomains : ∀ spec ∈ domains,
      roleDomainClause (spec.superRole specs) spec.domain source target ∈ direct)
    (definitions : List (CardinalityDef Concept Role))
    (pairs : List (PairedCardinality Concept Role))
    (hpairs : ∀ pair ∈ pairs,
      pair.maximum ∈ definitions ∧ pair.minimum ∈ definitions) :
    (∃ I : Interp Domain Concept Role,
      ∃ functions : SkolemInterp Domain Function,
        I.models direct ∧
          ModelsBundles I functions specs ∧
          I.modelsProjectedCardinalityDefs definitions pairs) ↔
    (∃ J : Interp Domain (Sum (Fin n) Concept) Role,
      J.models (indexedBundleOntology direct specs ++
          indexedBundleDomainOntology specs domains) ∧
        J.modelsPairedCardinalityTargets
          (definitions.map (renameCardinalityDef Sum.inr))
          (pairs.map (renamePairedCardinality Sum.inr))) := by
  rw [indexedBundleCardinalityProjection_sat_iff base direct specs hunique
    definitions pairs hpairs]
  constructor
  · rintro ⟨J, hcore, hcardinality⟩
    exact ⟨J, (add_indexedBundleDomainOntology_of_direct_iff J direct specs
      domains source target hne hpaths hdomains).2 hcore, hcardinality⟩
  · rintro ⟨J, htarget, hcardinality⟩
    exact ⟨J, (add_indexedBundleDomainOntology_of_direct_iff J direct specs
      domains source target hne hpaths hdomains).1 htarget, hcardinality⟩

theorem indexedBundleDomainCardinalityProjection_renamed_sat_iff
    [DecidableEq Variable] [DecidableEq Function]
    (base : SkolemInterp Domain Function)
    (direct : List (Clause Variable Concept Role))
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (hunique : (skolemPairFunctions (indexedBundlePairs specs)).Nodup)
    (domains : List (IndexedBundleDomainSpec Concept Role n))
    (source target : Variable) (hne : source ≠ target)
    (hpaths : ∀ spec ∈ domains, ∀ clause ∈
      roleInclusionPathClauses (Concept := Concept)
        (specs spec.bundle).role spec.path source target,
      clause ∈ direct)
    (hdomains : ∀ spec ∈ domains,
      roleDomainClause (spec.superRole specs) spec.domain source target ∈ direct)
    (definitions : List (CardinalityDef Concept Role))
    (pairs : List (PairedCardinality Concept Role))
    (hpairs : ∀ pair ∈ pairs,
      pair.maximum ∈ definitions ∧ pair.minimum ∈ definitions)
    (embedding : Sum (Fin n) Concept → TargetConcept)
    (inverse : TargetConcept → Sum (Fin n) Concept)
    (hleft : ∀ concept, inverse (embedding concept) = concept) :
    (∃ I : Interp Domain Concept Role,
      ∃ functions : SkolemInterp Domain Function,
        I.models direct ∧
          ModelsBundles I functions specs ∧
          I.modelsProjectedCardinalityDefs definitions pairs) ↔
    (∃ J : Interp Domain TargetConcept Role,
      J.models (renameOntology embedding
        (indexedBundleOntology direct specs ++
          indexedBundleDomainOntology specs domains)) ∧
        J.modelsPairedCardinalityTargets
          ((definitions.map (renameCardinalityDef Sum.inr)).map
            (renameCardinalityDef embedding))
          ((pairs.map (renamePairedCardinality Sum.inr)).map
            (renamePairedCardinality embedding))) := by
  rw [indexedBundleDomainCardinalityProjection_sat_iff base direct specs hunique
    domains source target hne hpaths hdomains definitions pairs hpairs]
  exact renameOntology_pairedCardinality_sat_iff_of_leftInverse
    embedding inverse hleft
    (indexedBundleOntology direct specs ++ indexedBundleDomainOntology specs domains)
    (definitions.map (renameCardinalityDef Sum.inr))
    (pairs.map (renamePairedCardinality Sum.inr))

#print axioms indexedBundleCardinalityProjection_sat_iff
#print axioms indexedBundleDomainCardinalityProjection_sat_iff
#print axioms indexedBundleDomainCardinalityProjection_renamed_sat_iff

end ContextCalculus.Hypertableau
