import ContextCalculus.HypertableauDomainProjection
import ContextCalculus.HypertableauSkolemBundleListProjection

/-!
# Domain consequences for a finite Skolem-bundle projection

This module composes the finite bundle projection with the domain clauses that
the production adapter emits beside projected existential clauses.  The extra
clauses are admitted only when their role inclusion and role-domain premises
hold in the same interpretation.
-/

namespace ContextCalculus.Hypertableau

structure IndexedBundleDomainSpec (Concept Role : Type*) (n : Nat) where
  bundle : Fin n
  path : List Role
  domain : Lit Concept

def IndexedBundleDomainSpec.superRole
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (spec : IndexedBundleDomainSpec Concept Role n) : Role :=
  roleInclusionPathTarget (specs spec.bundle).role spec.path

def indexedBundleDomainClause
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (spec : IndexedBundleDomainSpec Concept Role n) :
    Clause Variable (Sum (Fin n) Concept) Role :=
  domainConsequenceClause
    ((specs spec.bundle).body.map indexedLiftAtom)
    (specs spec.bundle).source
    (indexedLiftLit spec.domain)

def indexedBundleDomainOntology
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (domains : List (IndexedBundleDomainSpec Concept Role n)) :
    List (Clause Variable (Sum (Fin n) Concept) Role) :=
  domains.map (indexedBundleDomainClause specs)

theorem indexedBundleOntology_models_direct
    (J : Interp Domain (Sum (Fin n) Concept) Role)
    (direct : List (Clause Variable Concept Role))
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (hcore : J.models (indexedBundleOntology direct specs)) :
    (indexedRestrict J).models direct := by
  apply (indexed_models_lift_iff J direct).1
  intro clause hclause
  apply hcore clause
  exact List.mem_append_left _ (List.mem_append_left _ hclause)

theorem indexedBundle_roleIncluded_of_direct [DecidableEq Variable]
    (J : Interp Domain (Sum (Fin n) Concept) Role)
    (direct : List (Clause Variable Concept Role))
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (hcore : J.models (indexedBundleOntology direct specs))
    (start : Role) (steps : List Role) (source target : Variable)
    (hne : source ≠ target)
    (hpremises : ∀ clause ∈
      roleInclusionPathClauses (Concept := Concept) start steps source target,
      clause ∈ direct) :
    RoleIncluded J start (roleInclusionPathTarget start steps) := by
  have hsource := indexedBundleOntology_models_direct J direct specs hcore
  have hpath : (indexedRestrict J).models
      (roleInclusionPathClauses (Concept := Concept) start steps source target) := by
    intro clause hclause
    exact hsource clause (hpremises clause hclause)
  have hincluded := models_roleInclusionPathClauses_implies
    (indexedRestrict J) start steps source target hne hpath
  exact hincluded

theorem indexedBundle_roleDomain_of_direct [DecidableEq Variable]
    (J : Interp Domain (Sum (Fin n) Concept) Role)
    (direct : List (Clause Variable Concept Role))
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (hcore : J.models (indexedBundleOntology direct specs))
    (role : Role) (domain : Lit Concept) (source target : Variable)
    (hne : source ≠ target)
    (hpremise : roleDomainClause role domain source target ∈ direct) :
    RoleDomain J role (indexedLiftLit domain) := by
  have hsource := indexedBundleOntology_models_direct J direct specs hcore
  have hsourceDomain : RoleDomain (indexedRestrict J) role domain :=
    (models_roleDomainClause_iff (indexedRestrict J) role domain source target hne).1
      (hsource _ hpremise)
  intro left right hedge
  exact (indexed_satLit_lift_iff J domain left).2
    (hsourceDomain left right hedge)

theorem indexedBundleDomainClause_sound
    (J : Interp Domain (Sum (Fin n) Concept) Role)
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (spec : IndexedBundleDomainSpec Concept Role n)
    (hexist : J.modelsClause
      (SkolemPairSpec.target (indexedBundlePair specs spec.bundle)))
    (hincluded : RoleIncluded J (specs spec.bundle).role (spec.superRole specs))
    (hdomain : RoleDomain J (spec.superRole specs) (indexedLiftLit spec.domain)) :
    J.modelsClause (indexedBundleDomainClause specs spec) := by
  exact domainConsequence_sound J
    ((specs spec.bundle).body.map indexedLiftAtom)
    (specs spec.bundle).source
    (specs spec.bundle).role (spec.superRole specs)
    (.pos (.inl spec.bundle)) (indexedLiftLit spec.domain)
    hexist hincluded hdomain

theorem indexedBundleDomainOntology_sound
    (J : Interp Domain (Sum (Fin n) Concept) Role)
    (direct : List (Clause Variable Concept Role))
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (domains : List (IndexedBundleDomainSpec Concept Role n))
    (hcore : J.models (indexedBundleOntology direct specs))
    (hincluded : ∀ spec ∈ domains,
      RoleIncluded J (specs spec.bundle).role (spec.superRole specs))
    (hdomain : ∀ spec ∈ domains,
      RoleDomain J (spec.superRole specs) (indexedLiftLit spec.domain)) :
    J.models (indexedBundleDomainOntology specs domains) := by
  intro clause hclause
  rcases List.mem_map.mp hclause with ⟨spec, hspec, rfl⟩
  apply indexedBundleDomainClause_sound J specs spec
  · apply hcore
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨indexedBundlePair specs spec.bundle,
      List.mem_ofFn.mpr ⟨spec.bundle, rfl⟩, rfl⟩
  · exact hincluded spec hspec
  · exact hdomain spec hspec

theorem add_indexedBundleDomainOntology_iff
    (J : Interp Domain (Sum (Fin n) Concept) Role)
    (direct : List (Clause Variable Concept Role))
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (domains : List (IndexedBundleDomainSpec Concept Role n))
    (hincluded : ∀ spec ∈ domains,
      RoleIncluded J (specs spec.bundle).role (spec.superRole specs))
    (hdomain : ∀ spec ∈ domains,
      RoleDomain J (spec.superRole specs) (indexedLiftLit spec.domain)) :
    J.models (indexedBundleOntology direct specs ++
        indexedBundleDomainOntology specs domains) ↔
      J.models (indexedBundleOntology direct specs) := by
  constructor
  · intro hmodels clause hclause
    exact hmodels clause (List.mem_append_left _ hclause)
  · intro hcore clause hclause
    rcases List.mem_append.mp hclause with hclause | hclause
    · exact hcore clause hclause
    · exact indexedBundleDomainOntology_sound J direct specs domains hcore
        hincluded hdomain clause hclause

theorem add_indexedBundleDomainOntology_of_direct_iff [DecidableEq Variable]
    (J : Interp Domain (Sum (Fin n) Concept) Role)
    (direct : List (Clause Variable Concept Role))
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (domains : List (IndexedBundleDomainSpec Concept Role n))
    (source target : Variable) (hne : source ≠ target)
    (hpaths : ∀ spec ∈ domains, ∀ clause ∈
      roleInclusionPathClauses (Concept := Concept)
        (specs spec.bundle).role spec.path source target,
      clause ∈ direct)
    (hdomains : ∀ spec ∈ domains,
      roleDomainClause (spec.superRole specs) spec.domain source target ∈ direct) :
    J.models (indexedBundleOntology direct specs ++
        indexedBundleDomainOntology specs domains) ↔
      J.models (indexedBundleOntology direct specs) := by
  constructor
  · intro hmodels clause hclause
    exact hmodels clause (List.mem_append_left _ hclause)
  · intro hcore
    apply (add_indexedBundleDomainOntology_iff J direct specs domains
      (fun spec hspec => indexedBundle_roleIncluded_of_direct J direct specs hcore
        (specs spec.bundle).role spec.path source target hne
        (hpaths spec hspec))
      (fun spec hspec => indexedBundle_roleDomain_of_direct J direct specs hcore
        (spec.superRole specs) spec.domain source target hne
        (hdomains spec hspec))).2
    exact hcore

theorem indexedBundleDomainProjection_renamed_sat_iff
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
    (embedding : Sum (Fin n) Concept → TargetConcept)
    (inverse : TargetConcept → Sum (Fin n) Concept)
    (hleft : ∀ concept, inverse (embedding concept) = concept) :
    (∃ I : Interp Domain Concept Role, ∃ functions : SkolemInterp Domain Function,
      I.models direct ∧ ModelsBundles I functions specs) ↔
    (∃ J : Interp Domain TargetConcept Role,
      J.models (renameOntology embedding
        (indexedBundleOntology direct specs ++
          indexedBundleDomainOntology specs domains))) := by
  rw [indexedBundleProjection_sat_iff base direct specs hunique]
  have hdomainsIff :
      (∃ J : Interp Domain (Sum (Fin n) Concept) Role,
        J.models (indexedBundleOntology direct specs)) ↔
      (∃ J : Interp Domain (Sum (Fin n) Concept) Role,
        J.models (indexedBundleOntology direct specs ++
          indexedBundleDomainOntology specs domains)) := by
    constructor
    · rintro ⟨J, hcore⟩
      exact ⟨J, (add_indexedBundleDomainOntology_of_direct_iff J direct specs
        domains source target hne hpaths hdomains).2 hcore⟩
    · rintro ⟨J, hmodels⟩
      exact ⟨J, (add_indexedBundleDomainOntology_of_direct_iff J direct specs
        domains source target hne hpaths hdomains).1 hmodels⟩
  rw [hdomainsIff]
  exact renameOntology_sat_iff_of_leftInverse embedding inverse hleft _

#print axioms indexedBundleDomainClause_sound
#print axioms indexedBundleDomainOntology_sound
#print axioms add_indexedBundleDomainOntology_iff
#print axioms add_indexedBundleDomainOntology_of_direct_iff
#print axioms indexedBundleDomainProjection_renamed_sat_iff

end ContextCalculus.Hypertableau
