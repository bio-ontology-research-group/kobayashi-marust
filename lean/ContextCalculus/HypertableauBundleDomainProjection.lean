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
  superRole : Role
  domain : Lit Concept

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

theorem indexedBundleDomainClause_sound
    (J : Interp Domain (Sum (Fin n) Concept) Role)
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (spec : IndexedBundleDomainSpec Concept Role n)
    (hexist : J.modelsClause
      (SkolemPairSpec.target (indexedBundlePair specs spec.bundle)))
    (hincluded : RoleIncluded J (specs spec.bundle).role spec.superRole)
    (hdomain : RoleDomain J spec.superRole (indexedLiftLit spec.domain)) :
    J.modelsClause (indexedBundleDomainClause specs spec) := by
  exact domainConsequence_sound J
    ((specs spec.bundle).body.map indexedLiftAtom)
    (specs spec.bundle).source
    (specs spec.bundle).role spec.superRole
    (.pos (.inl spec.bundle)) (indexedLiftLit spec.domain)
    hexist hincluded hdomain

theorem indexedBundleDomainOntology_sound
    (J : Interp Domain (Sum (Fin n) Concept) Role)
    (direct : List (Clause Variable Concept Role))
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (domains : List (IndexedBundleDomainSpec Concept Role n))
    (hcore : J.models (indexedBundleOntology direct specs))
    (hincluded : ∀ spec ∈ domains,
      RoleIncluded J (specs spec.bundle).role spec.superRole)
    (hdomain : ∀ spec ∈ domains,
      RoleDomain J spec.superRole (indexedLiftLit spec.domain)) :
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
      RoleIncluded J (specs spec.bundle).role spec.superRole)
    (hdomain : ∀ spec ∈ domains,
      RoleDomain J spec.superRole (indexedLiftLit spec.domain)) :
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

#print axioms indexedBundleDomainClause_sound
#print axioms indexedBundleDomainOntology_sound
#print axioms add_indexedBundleDomainOntology_iff

end ContextCalculus.Hypertableau
