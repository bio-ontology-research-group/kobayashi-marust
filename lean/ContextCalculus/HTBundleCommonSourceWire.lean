import ContextCalculus.HTMixedCommonSourceWire
import ContextCalculus.HTSkolemBundleCheckerTermEmbedding
import ContextCalculus.HypertableauBundleProjectionWire

/-!
# Executable bundle HT adapter to the common routing source

The checked bundle projection introduces target-only definers.  This adapter
reconstructs the original shared-function role and filler clauses in the
proper-term source and proves taxonomy equivalence specifically at the checked
images of source concepts.
-/

namespace ContextCalculus.HTBundleCommonSourceWire

open ContextCalculus
open ContextCalculus.Hypertableau
open ContextCalculus.HTDirectCommonSourceWire
open ContextCalculus.HTMixedCommonSourceWire
open ContextCalculus.HTSkolemBundleCheckerTermEmbedding
open Lean

def mapBundle
    (bundle : BundleSpec (Fin nvars) (Fin concepts) (Fin roles) (Fin functions)) :
    BundleSpec Nat Nat Nat Nat where
  body := bundle.body.map mapAtom
  source := bundle.source.val
  function := bundle.function.val
  role := bundle.role.val
  fillers := bundle.fillers.map fun filler => ⟨filler.concept.val, filler.neg⟩

def bundleNoExistentials
    (bundle : BundleSpec Variable Concept Role Function) : Bool :=
  bundle.body.all noExistential

theorem direct_mapBundle
    (bundle : BundleSpec (Fin nvars) (Fin concepts) (Fin roles) (Fin functions))
    (hcheck : bundleNoExistentials bundle = true) :
    HTSkolemBundleCheckerTermEmbedding.Direct (mapBundle bundle) := by
  intro atom hatom
  rcases List.mem_map.mp hatom with ⟨source, hsource, rfl⟩
  have hall := List.all_eq_true.mp hcheck source hsource
  cases source <;> simp_all [bundleNoExistentials, noExistential,
    HTCheckerTermEmbedding.directAtom, mapAtom]

theorem models_mapBundle_nat_iff [Nonempty Domain]
    (interpretation : Interp Domain (Fin concepts) (Fin roles))
    (functions : SkolemInterp Domain (Fin functionCount))
    (bundle : BundleSpec (Fin nvars) (Fin concepts) (Fin roles)
      (Fin functionCount)) :
    ModelsSkolemBundle (natInterp interpretation) (natFunctions functions)
      (mapBundle bundle).body (mapBundle bundle).source
      (mapBundle bundle).function (mapBundle bundle).role
      (mapBundle bundle).fillers ↔
    ModelsSkolemBundle interpretation functions bundle.body bundle.source
      bundle.function bundle.role bundle.fillers := by
  constructor
  · rintro ⟨hrole, hfillers⟩
    constructor
    · intro assignment hbody
      let extension : Nat → Domain := fun index =>
        if h : index < nvars then assignment ⟨index, h⟩ else Classical.choice inferInstance
      have hresult := hrole extension
        ((holdsBody_map_nat interpretation assignment bundle.body).2 hbody)
      simpa [mapBundle, extension, natInterp] using hresult
    · intro filler hfiller assignment hbody
      have hmappedFiller :
          (⟨filler.concept.val, filler.neg⟩ : Hypertableau.Lit Nat) ∈
            (mapBundle bundle).fillers :=
        List.mem_map.mpr ⟨filler, hfiller, rfl⟩
      let extension : Nat → Domain := fun index =>
        if h : index < nvars then assignment ⟨index, h⟩ else Classical.choice inferInstance
      have hresult := hfillers ⟨filler.concept.val, filler.neg⟩ hmappedFiller extension
        ((holdsBody_map_nat interpretation assignment bundle.body).2 hbody)
      simpa [mapBundle, extension, natInterp, Interp.satLit] using hresult
  · rintro ⟨hrole, hfillers⟩
    constructor
    · intro assignment hbody
      let restricted : Fin nvars → Domain := fun index => assignment index.val
      have hsourceBody : HoldsBody interpretation restricted bundle.body := by
        apply (holdsBody_map_nat interpretation restricted bundle.body).1
        intro atom hatom
        rcases List.mem_map.mp hatom with ⟨source, hsource, rfl⟩
        apply (satAtom_map_assignment_congr interpretation assignment
          (fun index => if h : index < nvars then restricted ⟨index, h⟩
            else Classical.choice inferInstance)
          (by intro index; simp [restricted]) source).1
        exact hbody (mapAtom source) (List.mem_map.mpr ⟨source, hsource, rfl⟩)
      have hresult := hrole restricted hsourceBody
      simpa [mapBundle, restricted, natInterp] using hresult
    · intro filler hfiller assignment hbody
      rcases List.mem_map.mp hfiller with ⟨sourceFiller, hsourceFiller, rfl⟩
      let restricted : Fin nvars → Domain := fun index => assignment index.val
      have hsourceBody : HoldsBody interpretation restricted bundle.body := by
        apply (holdsBody_map_nat interpretation restricted bundle.body).1
        intro atom hatom
        rcases List.mem_map.mp hatom with ⟨source, hsource, rfl⟩
        apply (satAtom_map_assignment_congr interpretation assignment
          (fun index => if h : index < nvars then restricted ⟨index, h⟩
            else Classical.choice inferInstance)
          (by intro index; simp [restricted]) source).1
        exact hbody (mapAtom source) (List.mem_map.mpr ⟨source, hsource, rfl⟩)
      have hresult := hfillers sourceFiller hsourceFiller restricted hsourceBody
      simpa [mapBundle, restricted, natInterp, Interp.satLit] using hresult

theorem models_mapBundle_fin_iff [Nonempty Domain]
    (interpretation : Interp Domain Nat Nat) (functions : SkolemInterp Domain Nat)
    (bundle : BundleSpec (Fin nvars) (Fin concepts) (Fin roles)
      (Fin functionCount)) :
    ModelsSkolemBundle (finInterp interpretation) (finFunctions functions)
      bundle.body bundle.source bundle.function bundle.role bundle.fillers ↔
    ModelsSkolemBundle interpretation functions
      (mapBundle bundle).body (mapBundle bundle).source
      (mapBundle bundle).function (mapBundle bundle).role
      (mapBundle bundle).fillers := by
  constructor
  · rintro ⟨hrole, hfillers⟩
    constructor
    · intro assignment hbody
      let restricted : Fin nvars → Domain := fun index => assignment index.val
      have hsourceBody := (holdsBody_map_fin interpretation assignment bundle.body).2 hbody
      have hresult := hrole restricted hsourceBody
      simpa [mapBundle, restricted, finInterp, finFunctions] using hresult
    · intro filler hfiller assignment hbody
      rcases List.mem_map.mp hfiller with ⟨sourceFiller, hsourceFiller, rfl⟩
      let restricted : Fin nvars → Domain := fun index => assignment index.val
      have hsourceBody := (holdsBody_map_fin interpretation assignment bundle.body).2 hbody
      have hresult := hfillers sourceFiller hsourceFiller restricted hsourceBody
      simpa [mapBundle, restricted, finInterp, finFunctions, Interp.satLit] using hresult
  · rintro ⟨hrole, hfillers⟩
    constructor
    · intro assignment hbody
      let extension : Nat → Domain := fun index =>
        if h : index < nvars then assignment ⟨index, h⟩ else Classical.choice inferInstance
      have hmappedBody : HoldsBody interpretation extension (bundle.body.map mapAtom) :=
        (holdsBody_map_fin interpretation extension bundle.body).1 (by
          simpa [extension] using hbody)
      have hresult := hrole extension hmappedBody
      simpa [mapBundle, extension, finInterp, finFunctions] using hresult
    · intro filler hfiller assignment hbody
      let extension : Nat → Domain := fun index =>
        if h : index < nvars then assignment ⟨index, h⟩ else Classical.choice inferInstance
      have hmappedBody : HoldsBody interpretation extension (bundle.body.map mapAtom) :=
        (holdsBody_map_fin interpretation extension bundle.body).1 (by
          simpa [extension] using hbody)
      have hmappedFiller :
          (⟨filler.concept.val, filler.neg⟩ : Hypertableau.Lit Nat) ∈
            (mapBundle bundle).fillers := List.mem_map.mpr ⟨filler, hfiller, rfl⟩
      have hresult := hfillers ⟨filler.concept.val, filler.neg⟩ hmappedFiller
        extension hmappedBody
      simpa [mapBundle, extension, finInterp, finFunctions, Interp.satLit] using hresult

structure WireBundleCommonSource where
  version : Nat
  projection : WireBundleProjection
deriving FromJson, ToJson, Repr

structure DecodedBundleCommonSource where
  projection : DecodedBundleProjection
  directClauses : ∀ clause ∈ projection.direct, clauseNoExistentials clause = true
  bundleBodies : ∀ bundle ∈ projection.bundles,
    bundleNoExistentials bundle.spec = true

def WireBundleCommonSource.decode (wire : WireBundleCommonSource) :
    Except String DecodedBundleCommonSource := do
  if wire.version != 1 then
    throw s!"unsupported bundle common-source version {wire.version}"
  let projection ← wire.projection.decode
  if hdirect : ∀ clause ∈ projection.direct, clauseNoExistentials clause = true then
    if hbundles : ∀ bundle ∈ projection.bundles,
        bundleNoExistentials bundle.spec = true then
      return { projection, directClauses := hdirect, bundleBodies := hbundles }
    else throw "bundle common-source body contains an existential atom"
  else throw "bundle common-source direct residual contains an existential atom"

def WireBundleCommonSource.check (wire : WireBundleCommonSource) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedBundleCommonSource.commonDirect (decoded : DecodedBundleCommonSource) :=
  mapOntology decoded.projection.direct

def DecodedBundleCommonSource.commonBundles (decoded : DecodedBundleCommonSource) :=
  decoded.projection.bundles.map fun bundle => mapBundle bundle.spec

theorem DecodedBundleCommonSource.directBundles
    (decoded : DecodedBundleCommonSource) :
    DirectBundles decoded.commonDirect decoded.commonBundles := by
  constructor
  · intro clause hclause
    rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
    exact direct_mapClause source (decoded.directClauses source hsource)
  · intro bundle hbundle
    rcases List.mem_map.mp hbundle with ⟨source, hsource, rfl⟩
    exact direct_mapBundle source.spec (decoded.bundleBodies source hsource)

def DecodedBundleCommonSource.CommonEntails (decoded : DecodedBundleCommonSource)
    (sub sup : Fin decoded.projection.sourceConcepts.length) : Prop :=
  CommonEntailsSub decoded.commonDirect decoded.commonBundles sub.val sup.val

def FiniteSourceEntails (decoded : DecodedBundleCommonSource)
    (sub sup : Fin decoded.projection.sourceConcepts.length) : Prop :=
  ∀ (Domain : Type)
    (interpretation : Interp Domain (Fin decoded.projection.sourceConcepts.length)
      (Fin decoded.projection.roles.length))
    (functions : SkolemInterp Domain (Fin decoded.projection.functions.length)),
    interpretation.models decoded.projection.direct →
      ModelsBundles interpretation functions
        (decodedBundleSpecs decoded.projection.bundles) →
      ∀ value, interpretation.concept sub value → interpretation.concept sup value

theorem DecodedBundleCommonSource.entails_source_iff
    (decoded : DecodedBundleCommonSource)
    (sub sup : Fin decoded.projection.sourceConcepts.length) :
    decoded.CommonEntails sub sup ↔ FiniteSourceEntails decoded sub sup := by
  change HTSkolemBundleCheckerTermEmbedding.CommonEntailsSub
      decoded.commonDirect decoded.commonBundles sub.val sup.val ↔
    FiniteSourceEntails decoded sub sup
  rw [entailsSub_bundles_encode_iff decoded.commonDirect decoded.commonBundles
    decoded.directBundles sub.val sup.val]
  constructor
  · intro hnat Domain interpretation functions hdirect hbundles value hsub
    letI : Nonempty Domain := ⟨value⟩
    have hbundleList : ModelsBundleList (natInterp interpretation)
        (natFunctions functions) decoded.commonBundles := by
      intro bundle hbundle
      rcases List.mem_map.mp hbundle with ⟨source, hsource, rfl⟩
      rcases List.get_of_mem hsource with ⟨index, hindex⟩
      have hsourceModels := hbundles index
      simp only [decodedBundleSpecs] at hsourceModels
      rw [hindex] at hsourceModels
      exact (models_mapBundle_nat_iff interpretation functions source.spec).2
        hsourceModels
    have hresult := hnat Domain (natInterp interpretation) (natFunctions functions)
      (by
        intro clause hclause
        rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
        exact (modelsClause_map_natInterp interpretation source).2
          (hdirect source hsource)) hbundleList value (by simpa using hsub)
    simpa using hresult
  · intro hfin Domain interpretation functions hdirect hbundles value hsub
    letI : Nonempty Domain := ⟨value⟩
    have hfiniteBundles : ModelsBundles (finInterp interpretation)
        (finFunctions functions) (decodedBundleSpecs decoded.projection.bundles) := by
      intro index
      have hmapped : mapBundle (decoded.projection.bundles.get index).spec ∈
          decoded.commonBundles := List.mem_map.mpr
            ⟨decoded.projection.bundles.get index, List.get_mem _ _, rfl⟩
      exact (models_mapBundle_fin_iff interpretation functions
        (decoded.projection.bundles.get index).spec).2
          (hbundles _ hmapped)
    have hresult := hfin Domain (finInterp interpretation) (finFunctions functions)
      (by
        intro clause hclause
        exact (modelsClause_map_finInterp interpretation clause).2
          (hdirect (mapClause clause) (List.mem_map.mpr ⟨clause, hclause, rfl⟩)))
      hfiniteBundles value (by simpa [finInterp] using hsub)
    simpa [finInterp] using hresult

theorem DecodedBundleCommonSource.finiteSource_entails_iff_target
    (decoded : DecodedBundleCommonSource)
    (sub sup : Fin decoded.projection.sourceConcepts.length) :
    FiniteSourceEntails decoded sub sup ↔
      EntailsSub decoded.projection.target
        (decoded.projection.sourceTargets sub)
        (decoded.projection.sourceTargets sup) := by
  constructor
  · intro hsource Domain J htarget value hsub
    let embedding := bundleConceptEmbedding decoded.projection.sourceTargets
      decoded.projection.bundles
    let combined := indexedBundleOntology decoded.projection.direct
        (decodedBundleSpecs decoded.projection.bundles) ++
      indexedBundleDomainOntology (decodedBundleSpecs decoded.projection.bundles)
        decoded.projection.domainExtras
    have hrenamed : J.models (renameOntology embedding combined) :=
      (models_iff_of_toFinset_eq J _ _ decoded.projection.exactProjection).2 htarget
    let K := pullbackConcepts embedding J
    have hcombined : K.models combined :=
      (models_rename_pullback_iff embedding J combined).1 hrenamed
    have hcore : K.models (indexedBundleOntology decoded.projection.direct
        (decodedBundleSpecs decoded.projection.bundles)) := by
      intro clause hclause
      exact hcombined clause (List.mem_append_left _ hclause)
    let base : SkolemInterp Domain (Fin decoded.projection.functions.length) :=
      ⟨fun _ _ => value⟩
    rcases indexedBundleProjection_complete K base decoded.projection.direct
        (decodedBundleSpecs decoded.projection.bundles)
        decoded.projection.uniqueFunctions hcore with
      ⟨functions, hdirect, hbundles⟩
    have hresult := hsource Domain (indexedRestrict K) functions hdirect hbundles value
      (by simpa [K, embedding, pullbackConcepts, indexedRestrict] using hsub)
    simpa [K, embedding, pullbackConcepts, indexedRestrict] using hresult
  · intro htarget Domain I functions hdirect hbundles value hsub
    have hpositive : 0 < decoded.projection.bundles.length :=
      List.length_pos_of_ne_nil decoded.projection.nonemptyBundles
    letI : Nonempty
        (Sum (Fin decoded.projection.bundles.length)
          (Fin decoded.projection.sourceConcepts.length)) :=
      ⟨.inl ⟨0, hpositive⟩⟩
    obtain ⟨inverse, hleft⟩ := decoded.projection.embeddingInjective.hasLeftInverse
    let extended := indexedBundleExtension I
      (decodedBundleSpecs decoded.projection.bundles)
    have hcore : extended.models (indexedBundleOntology decoded.projection.direct
        (decodedBundleSpecs decoded.projection.bundles)) :=
      indexedBundleProjection_sound I functions decoded.projection.direct
        (decodedBundleSpecs decoded.projection.bundles) hdirect hbundles
    have hdomains : extended.models
        (indexedBundleOntology decoded.projection.direct
          (decodedBundleSpecs decoded.projection.bundles) ++
        indexedBundleDomainOntology (decodedBundleSpecs decoded.projection.bundles)
          decoded.projection.domainExtras) :=
      (add_indexedBundleDomainOntology_of_direct_iff extended decoded.projection.direct
        (decodedBundleSpecs decoded.projection.bundles) decoded.projection.domainExtras
        decoded.projection.rboxSource decoded.projection.rboxTarget
        decoded.projection.rboxDistinct decoded.projection.pathPremises
        decoded.projection.domainPremises).2 hcore
    let embedding := bundleConceptEmbedding decoded.projection.sourceTargets
      decoded.projection.bundles
    let J := pushforwardConcepts inverse extended
    have hrenamed : J.models (renameOntology embedding
        (indexedBundleOntology decoded.projection.direct
          (decodedBundleSpecs decoded.projection.bundles) ++
        indexedBundleDomainOntology (decodedBundleSpecs decoded.projection.bundles)
          decoded.projection.domainExtras)) :=
      (models_rename_pushforward_iff embedding inverse hleft extended _).2 hdomains
    have hmodels : J.models decoded.projection.target :=
      (models_iff_of_toFinset_eq J _ _ decoded.projection.exactProjection).1 hrenamed
    have hsubJ : J.concept (decoded.projection.sourceTargets sub) value := by
      have hinverse : inverse (decoded.projection.sourceTargets sub) = .inr sub := by
        simpa [embedding] using hleft (.inr sub)
      simpa [J, pushforwardConcepts, hinverse, extended, indexedBundleExtension] using hsub
    have hsupJ := htarget Domain J hmodels value hsubJ
    have hinverse : inverse (decoded.projection.sourceTargets sup) = .inr sup := by
      simpa [embedding] using hleft (.inr sup)
    simpa [J, pushforwardConcepts, hinverse, extended, indexedBundleExtension] using hsupJ

theorem DecodedBundleCommonSource.entails_target_iff
    (decoded : DecodedBundleCommonSource)
    (sub sup : Fin decoded.projection.sourceConcepts.length) :
    decoded.CommonEntails sub sup ↔
      EntailsSub decoded.projection.target
        (decoded.projection.sourceTargets sub)
        (decoded.projection.sourceTargets sup) :=
  (decoded.entails_source_iff sub sup).trans
    (decoded.finiteSource_entails_iff_target sub sup)

theorem WireBundleCommonSource.check_sound (wire : WireBundleCommonSource)
    (decoded : DecodedBundleCommonSource) (_hdecode : wire.decode = .ok decoded)
    (_hcheck : wire.check = .ok true)
    (sub sup : Fin decoded.projection.sourceConcepts.length) :
    decoded.CommonEntails sub sup ↔
      EntailsSub decoded.projection.target
        (decoded.projection.sourceTargets sub)
        (decoded.projection.sourceTargets sup) :=
  decoded.entails_target_iff sub sup

#print axioms DecodedBundleCommonSource.entails_target_iff
#print axioms WireBundleCommonSource.check_sound

end ContextCalculus.HTBundleCommonSourceWire
