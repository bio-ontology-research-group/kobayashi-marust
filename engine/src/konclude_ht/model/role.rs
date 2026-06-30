//! Port of Konclude `Reasoner/Ontology/CRole` (`CRole.{h,cpp}`).
//!
//! Faithful, function-by-function translation. Konclude's `CRole` is a static
//! ontology-model object describing one role (object or data property): its
//! inverse, its super/equivalent/disjoint/indirect-super hierarchy links, its
//! domain/range concept lists, the boolean role characteristics
//! (transitive/functional/.../reflexive), the simple-vs-complex flag, and the
//! role-chain sharing linkers.
//!
//! LGPL: this is a derivative translation of LGPLv3 Konclude source — keep the
//! whole `konclude_ht/` module self-contained and LGPL-headed (see PORT.md).
//!
//! KONCLUDE-PORT-NOTE[ownership]: every `CXxx*` back-pointer becomes a typed
//! arena id (see `model/substrate.rs`), and every intrusive `CSortedNegLinker`
//! / `CXLinker` chain becomes a `Vec` of entries. The neg-bit lists
//! (`CSortedNegLinker<CRole*>` / `CSortedNegLinker<CConcept*>`) map to
//! `Vec<NegLink<RoleId>>` / `Vec<NegLink<ConceptId>>`. This is the single
//! global ownership decision; per-site notes below point here.

#![allow(dead_code)]

use super::concept::Concept;
use super::stubs::{NameId, RoleChainId, RoleDataId, Terminology, TerminologyId};
use super::substrate::{Arena, Cint64, Id, NegLink};
use super::{ConceptId, RoleId};

/// KONCLUDE-PORT-NOTE[ownership]: `insertSortedNextSorted` keeps a
/// `CSortedNegLinker<T*>` chain sorted ascending by the data pointer
/// (`next->getData() > data`). The arena id is the port's pointer, so this
/// inserts `link` into `list` at the first position whose `target.raw` exceeds
/// `link.target.raw`, preserving that ascending order.
fn insert_sorted_neg<T>(list: &mut Vec<NegLink<Id<T>>>, link: NegLink<Id<T>>) {
    let mut pos = list.len();
    for (i, e) in list.iter().enumerate() {
        if e.target.raw > link.target.raw {
            pos = i;
            break;
        }
    }
    list.insert(pos, link);
}

/// Port of `CRole` (extends `CTagItem` + `CNamedItem`).
pub struct Role {
    // --- inherited from CTagItem ---
    /// Port of `CTagItem::mTag` (the role tag).
    pub tag: Cint64,
    // --- inherited from CNamedItem ---
    // KONCLUDE-PORT-NOTE[ownership]: `CNamedItem::mNameLinker`
    // (`CLinker<CName*>*`) → `Vec<NameId>`.
    /// Port of `CNamedItem::mNameLinker`.
    pub name_linker: Vec<NameId>,

    // --- CRole's own fields ---
    // KONCLUDE-PORT-NOTE[ownership]: `mRoleData` (`CRoleData*`) → `RoleDataId`.
    /// Port of `CRole::mRoleData`.
    pub role_data: RoleDataId,
    // KONCLUDE-PORT-NOTE[ownership]: `tax` (`CTerminology*`) → `TerminologyId`.
    /// Port of `CRole::tax`.
    pub tax: TerminologyId,

    /// Port of `CRole::mTransetive`.
    pub transetive: bool,
    /// Port of `CRole::mFunctional`.
    pub functional: bool,
    /// Port of `CRole::mInvFunctional`.
    pub inv_functional: bool,
    /// Port of `CRole::mAsymmetric`.
    pub asymmetric: bool,
    /// Port of `CRole::mSymmetric`.
    pub symmetric: bool,
    /// Port of `CRole::mReflexive`.
    pub reflexive: bool,
    /// Port of `CRole::mIrreflexive`.
    pub irreflexive: bool,
    /// Port of `CRole::mComplexity`.
    pub complexity: bool,
    /// Port of `CRole::mDataRole`.
    pub data_role: bool,

    // KONCLUDE-PORT-NOTE[ownership]: `mInverseRole` (`CRole*`) → `RoleId`.
    /// Port of `CRole::mInverseRole`.
    pub inverse_role: RoleId,

    // KONCLUDE-PORT-NOTE[ownership]: range/domain concept linkers
    // (`CSortedNegLinker<CConcept*>*`) → `Vec<NegLink<ConceptId>>`.
    /// Port of `CRole::rangeLinker`.
    pub range_linker: Vec<NegLink<ConceptId>>,
    /// Port of `CRole::domainLinker`.
    pub domain_linker: Vec<NegLink<ConceptId>>,

    // KONCLUDE-PORT-NOTE[ownership]: role hierarchy linkers
    // (`CSortedNegLinker<CRole*>*`) → `Vec<NegLink<RoleId>>`.
    /// Port of `CRole::mInverseEquivalentRoles`.
    pub inverse_equivalent_roles: Vec<NegLink<RoleId>>,
    /// Port of `CRole::mDisjointRoles`.
    pub disjoint_roles: Vec<NegLink<RoleId>>,
    /// Port of `CRole::superRoles`.
    pub super_roles: Vec<NegLink<RoleId>>,
    /// Port of `CRole::indirectSuperRoles`.
    pub indirect_super_roles: Vec<NegLink<RoleId>>,

    // KONCLUDE-PORT-NOTE[ownership]: role-chain sharing linkers
    // (`CXLinker<CRoleChain*>*`) → `Vec<RoleChainId>`.
    /// Port of `CRole::mRoleChainSuperSharingLinker`.
    pub role_chain_super_sharing_linker: Vec<RoleChainId>,
    /// Port of `CRole::mRoleChainSubSharingLinker`.
    pub role_chain_sub_sharing_linker: Vec<RoleChainId>,
}

impl Default for Role {
    fn default() -> Self {
        Role {
            tag: 0,
            name_linker: Vec::new(),
            role_data: RoleDataId::NONE,
            tax: TerminologyId::NONE,
            transetive: false,
            functional: false,
            inv_functional: false,
            asymmetric: false,
            symmetric: false,
            reflexive: false,
            irreflexive: false,
            complexity: false,
            data_role: false,
            inverse_role: RoleId::NONE,
            range_linker: Vec::new(),
            domain_linker: Vec::new(),
            inverse_equivalent_roles: Vec::new(),
            disjoint_roles: Vec::new(),
            super_roles: Vec::new(),
            indirect_super_roles: Vec::new(),
            role_chain_super_sharing_linker: Vec::new(),
            role_chain_sub_sharing_linker: Vec::new(),
        }
    }
}

impl Role {
    // ===================== construction / init =====================

    /// Port of `CRole::CRole`.
    pub fn new() -> Role {
        let mut r = Role::default();
        r.init_role();
        r
    }

    /// Port of `CRole::initRole`.
    pub fn init_role(&mut self) -> &mut Self {
        self.super_roles = Vec::new();
        self.indirect_super_roles = Vec::new();
        self.complexity = false;
        self.functional = false;
        self.inv_functional = false;
        self.transetive = false;
        self.asymmetric = false;
        self.symmetric = false;
        self.reflexive = false;
        self.irreflexive = false;
        self.data_role = false;
        self.range_linker = Vec::new();
        self.domain_linker = Vec::new();
        self.tax = TerminologyId::NONE;
        self.inverse_equivalent_roles = Vec::new();
        self.disjoint_roles = Vec::new();
        self.role_chain_sub_sharing_linker = Vec::new();
        self.role_chain_super_sharing_linker = Vec::new();
        self.inverse_role = RoleId::NONE;
        self.role_data = RoleDataId::NONE;
        self
    }

    /// Port of `CRole::init(qint64 roleTag)` (deprecated overload).
    pub fn init_with_tag(&mut self, role_tag: Cint64) -> &mut Self {
        self.init_role();
        self.tag = role_tag;
        self
    }

    /// Port of `CRole::init(CRole *role)` (deprecated overload).
    pub fn init_from_role(&mut self, role: &Role) -> &mut Self {
        self.name_linker = role.get_property_name_linker().to_vec();
        self.tag = role.tag;
        self.data_role = role.data_role;
        self.super_roles = Vec::new();
        self.indirect_super_roles = Vec::new();
        self.range_linker = Vec::new();
        self.domain_linker = Vec::new();
        self.tax = TerminologyId::NONE;
        self.inverse_equivalent_roles = Vec::new();
        self.disjoint_roles = Vec::new();
        self.inverse_role = RoleId::NONE;
        self.complexity = role.complexity;
        self.functional = role.functional;
        self.inv_functional = role.inv_functional;
        self.transetive = role.transetive;
        self.asymmetric = role.asymmetric;
        self.symmetric = role.symmetric;
        self.reflexive = role.reflexive;
        self.irreflexive = role.irreflexive;
        self.role_chain_sub_sharing_linker = role.role_chain_sub_sharing_linker.clone();
        self.role_chain_super_sharing_linker = role.role_chain_super_sharing_linker.clone();
        self
    }

    /// Port of `CRole::initRoleCopy`.
    ///
    /// KONCLUDE-PORT-NOTE[memory-pool]: the `CMemoryAllocationManager* memMan`
    /// argument drives Konclude's per-task bump allocation of fresh
    /// `CSortedNegLinker` nodes; the port allocates `NegLink` entries via the
    /// owning `Vec` and so drops `memMan`. The per-list copy loops are kept
    /// verbatim (each source linker is re-added through `add_*_linker`).
    pub fn init_role_copy(&mut self, role: &Role) -> &mut Self {
        self.name_linker = role.get_property_name_linker().to_vec();
        self.tag = role.tag;
        self.data_role = role.data_role;
        self.super_roles = Vec::new();
        self.indirect_super_roles = Vec::new();
        self.range_linker = Vec::new();
        self.domain_linker = Vec::new();
        self.tax = TerminologyId::NONE;
        self.inverse_equivalent_roles = Vec::new();
        self.disjoint_roles = Vec::new();
        self.complexity = role.complexity;
        self.functional = role.functional;
        self.inv_functional = role.inv_functional;
        self.transetive = role.transetive;
        self.asymmetric = role.asymmetric;
        self.symmetric = role.symmetric;
        self.reflexive = role.reflexive;
        self.irreflexive = role.irreflexive;
        self.role_chain_sub_sharing_linker = role.role_chain_sub_sharing_linker.clone();
        self.role_chain_super_sharing_linker = role.role_chain_super_sharing_linker.clone();
        self.inverse_role = role.inverse_role;

        for super_role_it in role.super_roles.iter() {
            let super_role = super_role_it.target;
            let negated = super_role_it.negated;
            let super_role_linker = NegLink { target: super_role, negated };
            self.add_super_role_linker(super_role_linker);
        }

        for inverse_roles_it in role.get_inverse_role_list().iter() {
            let inv_role_linker = NegLink {
                target: inverse_roles_it.target,
                negated: inverse_roles_it.negated,
            };
            self.add_inverse_role_linker(inv_role_linker);
        }

        for disjoint_roles_it in role.get_disjoint_role_list().iter() {
            let dis_role_linker = NegLink {
                target: disjoint_roles_it.target,
                negated: disjoint_roles_it.negated,
            };
            self.add_disjoint_role_linker(dis_role_linker);
        }

        for range_linker_it in role.get_range_concept_list().iter() {
            let range_con_linker = NegLink {
                target: range_linker_it.target,
                negated: range_linker_it.negated,
            };
            self.add_range_concept_linker(range_con_linker);
        }

        for domain_linker_it in role.get_domain_concept_list().iter() {
            let domain_con_linker = NegLink {
                target: domain_linker_it.target,
                negated: domain_linker_it.negated,
            };
            self.add_domain_concept_linker(domain_con_linker);
        }

        self
    }

    // ===================== data / object role =====================

    /// Port of `CRole::isDataRole`.
    pub fn is_data_role(&self) -> bool {
        self.data_role
    }

    /// Port of `CRole::isObjectRole`.
    pub fn is_object_role(&self) -> bool {
        !self.is_data_role()
    }

    /// Port of `CRole::setDataRole`.
    pub fn set_data_role(&mut self, data_role: bool) -> &mut Self {
        self.data_role = data_role;
        self
    }

    /// Port of `CRole::setObjectRole`.
    pub fn set_object_role(&mut self, object_role: bool) -> &mut Self {
        self.set_data_role(!object_role);
        self
    }

    // ===================== inverse role (single) =====================

    /// Port of `CRole::getInverseRole`.
    pub fn get_inverse_role(&self) -> RoleId {
        self.inverse_role
    }

    /// Port of `CRole::setInverseRole`.
    pub fn set_inverse_role(&mut self, inverse_role: RoleId) -> &mut Self {
        self.inverse_role = inverse_role;
        self
    }

    /// Port of `CRole::hasInverseRoles`.
    pub fn has_inverse_roles(&self) -> bool {
        if self.inverse_role.is_some() {
            return true;
        }
        for inverse_equivalent_roles_it in self.inverse_equivalent_roles.iter() {
            if inverse_equivalent_roles_it.negated {
                return true;
            }
        }
        false
    }

    // ===================== inverse / equivalent role list =====================

    /// Port of `CRole::addInverseRoleLinker`.
    pub fn add_inverse_role_linker(&mut self, inverse_role: NegLink<RoleId>) -> &mut Self {
        insert_sorted_neg(&mut self.inverse_equivalent_roles, inverse_role);
        self
    }

    /// Port of `CRole::getInverseRoleList`.
    pub fn get_inverse_role_list(&self) -> &[NegLink<RoleId>] {
        &self.inverse_equivalent_roles
    }

    /// Port of `CRole::setInverseEquivalentRoleList`.
    pub fn set_inverse_equivalent_role_list(
        &mut self,
        inv_eq_role_list: Vec<NegLink<RoleId>>,
    ) -> &mut Self {
        self.inverse_equivalent_roles = inv_eq_role_list;
        self
    }

    /// Port of `CRole::getInverseEquivalentRoleList`.
    pub fn get_inverse_equivalent_role_list(&self) -> &[NegLink<RoleId>] {
        &self.inverse_equivalent_roles
    }

    /// Port of `CRole::hasEquivalentRoles`.
    pub fn has_equivalent_roles(&self) -> bool {
        for inverse_equivalent_roles_it in self.inverse_equivalent_roles.iter() {
            if !inverse_equivalent_roles_it.negated {
                return true;
            }
        }
        false
    }

    /// Port of `CRole::addEquivalentRoleLinker`.
    pub fn add_equivalent_role_linker(&mut self, equivalent_role: NegLink<RoleId>) -> &mut Self {
        insert_sorted_neg(&mut self.inverse_equivalent_roles, equivalent_role);
        self
    }

    /// Port of `CRole::hasEquivalentRole`.
    pub fn has_equivalent_role(&self, role: RoleId) -> bool {
        for inverse_equivalent_roles_it in self.inverse_equivalent_roles.iter() {
            if !inverse_equivalent_roles_it.negated && inverse_equivalent_roles_it.target == role {
                return true;
            }
        }
        false
    }

    /// Port of `CRole::hasInverseRole`.
    pub fn has_inverse_role(&self, role: RoleId) -> bool {
        if self.inverse_role == role {
            return true;
        }
        for inverse_equivalent_roles_it in self.inverse_equivalent_roles.iter() {
            if inverse_equivalent_roles_it.negated && inverse_equivalent_roles_it.target == role {
                return true;
            }
        }
        false
    }

    /// Port of `CRole::getEquivalentRoleList`.
    pub fn get_equivalent_role_list(&self) -> &[NegLink<RoleId>] {
        &self.inverse_equivalent_roles
    }

    // ===================== disjoint roles =====================

    /// Port of `CRole::hasDisjointRole`.
    pub fn has_disjoint_role(&self, role: RoleId) -> bool {
        for disjoint_roles_it in self.disjoint_roles.iter() {
            if disjoint_roles_it.target == role {
                return true;
            }
        }
        false
    }

    /// Port of `CRole::setDisjointRoleList`.
    pub fn set_disjoint_role_list(&mut self, dis_role_list: Vec<NegLink<RoleId>>) -> &mut Self {
        self.disjoint_roles = dis_role_list;
        self
    }

    /// Port of `CRole::hasDisjointRoles`.
    pub fn has_disjoint_roles(&self) -> bool {
        !self.disjoint_roles.is_empty()
    }

    /// Port of `CRole::addDisjointRoleLinker`.
    pub fn add_disjoint_role_linker(&mut self, disjoint_role: NegLink<RoleId>) -> &mut Self {
        insert_sorted_neg(&mut self.disjoint_roles, disjoint_role);
        self
    }

    /// Port of `CRole::getDisjointRoleList`.
    pub fn get_disjoint_role_list(&self) -> &[NegLink<RoleId>] {
        &self.disjoint_roles
    }

    // ===================== tag / terminology =====================

    /// Port of `CRole::setRoleTag`.
    pub fn set_role_tag(&mut self, role_tag: Cint64) -> &mut Self {
        self.tag = role_tag;
        self
    }

    /// Port of `CRole::getRoleTag`.
    pub fn get_role_tag(&self) -> Cint64 {
        self.tag
    }

    /// Port of `CRole::setTerminology`.
    pub fn set_terminology(&mut self, ontology: TerminologyId) -> &mut Self {
        self.tax = ontology;
        self
    }

    /// Port of `CRole::getTerminology`.
    pub fn get_terminology(&self) -> TerminologyId {
        self.tax
    }

    /// Port of `CRole::getTerminologyTag`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ derefs `tax->getTerminologyID()`;
    /// the port takes the terminology arena to dereference the `TerminologyId`.
    pub fn get_terminology_tag(&self, terms: &Arena<Terminology>) -> Cint64 {
        if self.tax.is_some() {
            terms.get(self.tax).get_terminology_id()
        } else {
            0
        }
    }

    // ===================== role complexity =====================

    /// Port of `CRole::setRoleComplexity`.
    pub fn set_role_complexity(&mut self, complex_role: bool) -> &mut Self {
        self.complexity = complex_role;
        self
    }

    /// Port of `CRole::isComplexRole`.
    pub fn is_complex_role(&self) -> bool {
        self.complexity
    }

    /// Port of `CRole::isSimpleRole`.
    pub fn is_simple_role(&self) -> bool {
        !self.complexity
    }

    /// Port of `CRole::getRoleComplexity`.
    pub fn get_role_complexity(&self) -> bool {
        self.complexity
    }

    // ===================== boolean role characteristics =====================

    /// Port of `CRole::setFunctional`.
    pub fn set_functional(&mut self, functional: bool) -> &mut Self {
        self.functional = functional;
        self
    }

    /// Port of `CRole::isFunctional`.
    pub fn is_functional(&self) -> bool {
        self.functional
    }

    /// Port of `CRole::getFunctional`.
    pub fn get_functional(&self) -> bool {
        self.functional
    }

    /// Port of `CRole::setInverseFunctional`.
    pub fn set_inverse_functional(&mut self, inv_functional: bool) -> &mut Self {
        self.inv_functional = inv_functional;
        self
    }

    /// Port of `CRole::isInverseFunctional`.
    pub fn is_inverse_functional(&self) -> bool {
        self.inv_functional
    }

    /// Port of `CRole::getInverseFunctional`.
    pub fn get_inverse_functional(&self) -> bool {
        self.inv_functional
    }

    /// Port of `CRole::setTransitive`.
    pub fn set_transitive(&mut self, transetive: bool) -> &mut Self {
        self.transetive = transetive;
        self
    }

    /// Port of `CRole::isTransitive`.
    pub fn is_transitive(&self) -> bool {
        self.transetive
    }

    /// Port of `CRole::getTransitive`.
    pub fn get_transitive(&self) -> bool {
        self.is_transitive()
    }

    /// Port of `CRole::setAsymmetric`.
    pub fn set_asymmetric(&mut self, asymmetric: bool) -> &mut Self {
        self.asymmetric = asymmetric;
        self
    }

    /// Port of `CRole::isAsymmetric`.
    pub fn is_asymmetric(&self) -> bool {
        self.asymmetric
    }

    /// Port of `CRole::getAsymmetric`.
    pub fn get_asymmetric(&self) -> bool {
        self.asymmetric
    }

    /// Port of `CRole::setSymmetric`.
    pub fn set_symmetric(&mut self, symmetric: bool) -> &mut Self {
        self.symmetric = symmetric;
        self
    }

    /// Port of `CRole::isSymmetric`.
    pub fn is_symmetric(&self) -> bool {
        self.symmetric
    }

    /// Port of `CRole::getSymmetric`.
    pub fn get_symmetric(&self) -> bool {
        self.symmetric
    }

    /// Port of `CRole::setReflexive`.
    pub fn set_reflexive(&mut self, reflexive: bool) -> &mut Self {
        self.reflexive = reflexive;
        self
    }

    /// Port of `CRole::isReflexive`.
    pub fn is_reflexive(&self) -> bool {
        self.reflexive
    }

    /// Port of `CRole::getReflexive`.
    pub fn get_reflexive(&self) -> bool {
        self.reflexive
    }

    /// Port of `CRole::setIrreflexive`.
    pub fn set_irreflexive(&mut self, irreflexive: bool) -> &mut Self {
        self.irreflexive = irreflexive;
        self
    }

    /// Port of `CRole::isIrreflexive`.
    pub fn is_irreflexive(&self) -> bool {
        self.irreflexive
    }

    /// Port of `CRole::getIrreflexive`.
    pub fn get_irreflexive(&self) -> bool {
        self.irreflexive
    }

    // ===================== role data =====================

    /// Port of `CRole::hasRoleData`.
    pub fn has_role_data(&self) -> bool {
        self.role_data.is_some()
    }

    /// Port of `CRole::getRoleData`.
    pub fn get_role_data(&self) -> RoleDataId {
        self.role_data
    }

    /// Port of `CRole::setRoleData`.
    pub fn set_role_data(&mut self, role_data: RoleDataId) -> &mut Self {
        self.role_data = role_data;
        self
    }

    // ===================== domain / range =====================

    /// Port of `CRole::getRangeConceptList`.
    pub fn get_range_concept_list(&self) -> &[NegLink<ConceptId>] {
        &self.range_linker
    }

    /// Port of `CRole::getRelativeRangeConceptList`.
    pub fn get_relative_range_concept_list(&self, role_inversed: bool) -> &[NegLink<ConceptId>] {
        if role_inversed {
            &self.domain_linker
        } else {
            &self.range_linker
        }
    }

    /// Port of `CRole::getDomainRangeConceptList`.
    pub fn get_domain_range_concept_list(&self, role_inversed: bool) -> &[NegLink<ConceptId>] {
        if role_inversed {
            &self.range_linker
        } else {
            &self.domain_linker
        }
    }

    /// Port of `CRole::hasRangeConceptTag`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ derefs `getData()->getConceptTag()`;
    /// the port takes the concept arena to dereference each `ConceptId`. The
    /// sorted early-exit (`rangeConTag > rangeConceptTag → false`) is preserved.
    pub fn has_range_concept_tag(
        &self,
        range_concept_tag: Cint64,
        concepts: &Arena<Concept>,
    ) -> bool {
        for range_con_it in self.range_linker.iter() {
            let range_con_tag = concepts.get(range_con_it.target).get_concept_tag();
            if range_con_tag == range_concept_tag {
                return true;
            } else if range_con_tag > range_concept_tag {
                return false;
            }
        }
        false
    }

    /// Port of `CRole::hasRangeConcept`.
    pub fn has_range_concept(&self, concept: ConceptId) -> bool {
        for range_con_it in self.range_linker.iter() {
            let range_concept = range_con_it.target;
            if range_concept == concept {
                return true;
            }
        }
        false
    }

    /// Port of `CRole::hasDomainConcept`.
    pub fn has_domain_concept(&self, concept: ConceptId) -> bool {
        for domain_con_it in self.domain_linker.iter() {
            let domain_concept = domain_con_it.target;
            if domain_concept == concept {
                return true;
            }
        }
        false
    }

    /// Port of `CRole::hasDomainConceptTag`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: concept arena needed to deref the tag;
    /// sorted early-exit preserved.
    pub fn has_domain_concept_tag(
        &self,
        domain_concept_tag: Cint64,
        concepts: &Arena<Concept>,
    ) -> bool {
        for domain_con_it in self.domain_linker.iter() {
            let domain_con_tag = concepts.get(domain_con_it.target).get_concept_tag();
            if domain_con_tag == domain_concept_tag {
                return true;
            } else if domain_con_tag > domain_concept_tag {
                return false;
            }
        }
        false
    }

    /// Port of `CRole::hasDomainOrRangeConceptTag`.
    pub fn has_domain_or_range_concept_tag(
        &self,
        concept_tag: Cint64,
        concepts: &Arena<Concept>,
    ) -> bool {
        self.has_range_concept_tag(concept_tag, concepts)
            || self.has_domain_concept_tag(concept_tag, concepts)
    }

    /// Port of `CRole::setRangeConceptList`.
    pub fn set_range_concept_list(
        &mut self,
        range_concept_list: Vec<NegLink<ConceptId>>,
    ) -> &mut Self {
        self.range_linker = range_concept_list;
        self
    }

    /// Port of `CRole::addRangeConceptLinker`.
    pub fn add_range_concept_linker(
        &mut self,
        range_concept_linker: NegLink<ConceptId>,
    ) -> &mut Self {
        insert_sorted_neg(&mut self.range_linker, range_concept_linker);
        self
    }

    /// Port of `CRole::getDomainConceptList`.
    pub fn get_domain_concept_list(&self) -> &[NegLink<ConceptId>] {
        &self.domain_linker
    }

    /// Port of `CRole::setDomainConceptList`.
    pub fn set_domain_concept_list(
        &mut self,
        domain_concept_list: Vec<NegLink<ConceptId>>,
    ) -> &mut Self {
        self.domain_linker = domain_concept_list;
        self
    }

    /// Port of `CRole::addDomainConceptLinker`.
    pub fn add_domain_concept_linker(
        &mut self,
        domain_concept_linker: NegLink<ConceptId>,
    ) -> &mut Self {
        insert_sorted_neg(&mut self.domain_linker, domain_concept_linker);
        self
    }

    // ===================== super roles =====================

    /// Port of `CRole::setSuperRoleList`.
    pub fn set_super_role_list(&mut self, super_role_list: Vec<NegLink<RoleId>>) -> &mut Self {
        self.super_roles = super_role_list;
        self
    }

    /// Port of `CRole::addSuperRoleLinker`.
    pub fn add_super_role_linker(&mut self, super_role_linker: NegLink<RoleId>) -> &mut Self {
        insert_sorted_neg(&mut self.super_roles, super_role_linker);
        self
    }

    /// Port of `CRole::getSuperRoleList`.
    pub fn get_super_role_list(&self) -> &[NegLink<RoleId>] {
        &self.super_roles
    }

    /// Port of `CRole::hasSuperRole`.
    pub fn has_super_role(&self, role: RoleId) -> bool {
        for super_role_it in self.super_roles.iter() {
            let super_role = super_role_it.target;
            if super_role == role {
                return true;
            }
        }
        false
    }

    /// Port of `CRole::hasSuperRoleTag(qint64 tag)`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: role arena needed to deref each super
    /// role's tag (`superRole->getRoleTag()`); sorted early-exit preserved.
    pub fn has_super_role_tag(&self, tag: Cint64, roles: &Arena<Role>) -> bool {
        for super_role_it in self.super_roles.iter() {
            let super_role = super_role_it.target;
            let super_role_tag = roles.get(super_role).get_role_tag();
            if tag == super_role_tag {
                return true;
            } else if super_role_tag > tag {
                return false;
            }
        }
        false
    }

    /// Port of `CRole::hasSuperRoleTag(qint64 tag, bool negated)`.
    pub fn has_super_role_tag_neg(&self, tag: Cint64, negated: bool, roles: &Arena<Role>) -> bool {
        for super_role_it in self.super_roles.iter() {
            let super_role = super_role_it.target;
            let super_role_tag = roles.get(super_role).get_role_tag();
            if tag == super_role_tag && super_role_it.negated == negated {
                return true;
            } else if super_role_tag > tag {
                return false;
            }
        }
        false
    }

    // ===================== indirect super roles =====================

    /// Port of `CRole::setIndirectSuperRoleLinker`.
    pub fn set_indirect_super_role_linker(
        &mut self,
        sub_role_list: Vec<NegLink<RoleId>>,
    ) -> &mut Self {
        self.indirect_super_roles = sub_role_list;
        self
    }

    /// Port of `CRole::addIndirectSuperRoleLinker`.
    pub fn add_indirect_super_role_linker(
        &mut self,
        sub_role_linker: NegLink<RoleId>,
    ) -> &mut Self {
        insert_sorted_neg(&mut self.indirect_super_roles, sub_role_linker);
        self
    }

    /// Port of `CRole::getIndirectSuperRoleList`.
    pub fn get_indirect_super_role_list(&self) -> &[NegLink<RoleId>] {
        &self.indirect_super_roles
    }

    /// Port of `CRole::hasIndirectSuperRole`.
    pub fn has_indirect_super_role(&self, role: RoleId) -> bool {
        for super_role_it in self.indirect_super_roles.iter() {
            let super_role = super_role_it.target;
            if super_role == role {
                return true;
            }
        }
        false
    }

    /// Port of `CRole::hasIndirectSuperRoleTag(qint64 tag)`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: role arena needed to deref the tag; sorted
    /// early-exit preserved.
    pub fn has_indirect_super_role_tag(&self, tag: Cint64, roles: &Arena<Role>) -> bool {
        for super_role_it in self.indirect_super_roles.iter() {
            let super_role = super_role_it.target;
            let super_role_tag = roles.get(super_role).get_role_tag();
            if tag == super_role_tag {
                return true;
            } else if super_role_tag > tag {
                return false;
            }
        }
        false
    }

    /// Port of `CRole::hasIndirectSuperRoleTag(qint64 tag, bool negated)`.
    pub fn has_indirect_super_role_tag_neg(
        &self,
        tag: Cint64,
        negated: bool,
        roles: &Arena<Role>,
    ) -> bool {
        for super_role_it in self.indirect_super_roles.iter() {
            let super_role = super_role_it.target;
            let super_role_tag = roles.get(super_role).get_role_tag();
            if tag == super_role_tag && super_role_it.negated == negated {
                return true;
            } else if super_role_tag > tag {
                return false;
            }
        }
        false
    }

    // ===================== operators =====================

    /// Port of `CRole::operator<=`.
    ///
    /// KONCLUDE-PORT-NOTE[overload]: C++ `operator<=`; ported as a named method
    /// taking the terminology arena (needed by `get_terminology_tag`).
    pub fn le(&self, role: &Role, terms: &Arena<Terminology>) -> bool {
        if self.tag < role.tag {
            true
        } else if self.tag > role.tag {
            false
        } else {
            self.get_terminology_tag(terms) <= role.get_terminology_tag(terms)
        }
    }

    /// Port of `CRole::operator==`.
    ///
    /// KONCLUDE-PORT-NOTE[overload]: C++ `operator==`; `tax == role.tax` becomes
    /// `TerminologyId` equality.
    pub fn eq_role(&self, role: &Role) -> bool {
        self.tag == role.tag && self.tax == role.tax
    }

    // ===================== property name (inherited CNamedItem) =====================

    /// Port of `CRole::hasPropertyName` (delegates to `CNamedItem::hasName`).
    pub fn has_property_name(&self) -> bool {
        self.has_name()
    }

    /// Port of `CRole::setPropertyNameLinker` (delegates to `setNameLinker`).
    pub fn set_property_name_linker(&mut self, property_name_linker: Vec<NameId>) -> &mut Self {
        self.set_name_linker(property_name_linker);
        self
    }

    /// Port of `CRole::addPropertyNameLinker` (delegates to `addNameLinker`).
    pub fn add_property_name_linker(&mut self, property_name_linker: NameId) -> &mut Self {
        self.add_name_linker(property_name_linker);
        self
    }

    /// Port of `CRole::getPropertyNameLinker` (delegates to `getNameLinker`).
    pub fn get_property_name_linker(&self) -> &[NameId] {
        self.get_name_linker()
    }

    // KONCLUDE-PORT-NOTE[api]: `CNamedItem::{hasName,setNameLinker,addNameLinker,
    // getNameLinker}` are inherited base-class methods; modelled inline here over
    // `name_linker` until `CNamedItem` lands as its own unit.

    /// Port of `CNamedItem::hasName`.
    pub fn has_name(&self) -> bool {
        !self.name_linker.is_empty()
    }

    /// Port of `CNamedItem::setNameLinker`.
    pub fn set_name_linker(&mut self, name_linker: Vec<NameId>) -> &mut Self {
        self.name_linker = name_linker;
        self
    }

    /// Port of `CNamedItem::addNameLinker`.
    pub fn add_name_linker(&mut self, name_linker: NameId) -> &mut Self {
        self.name_linker.push(name_linker);
        self
    }

    /// Port of `CNamedItem::getNameLinker`.
    pub fn get_name_linker(&self) -> &[NameId] {
        &self.name_linker
    }

    // ===================== role-chain sub sharing =====================

    /// Port of `CRole::hasRoleChainSubSharing`.
    pub fn has_role_chain_sub_sharing(&self) -> bool {
        !self.role_chain_sub_sharing_linker.is_empty()
    }

    /// Port of `CRole::addRoleChainSubSharingLinker`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: C++ `roleChainLinker->append(existing)`
    /// makes the new linker the head (new entries go to the front); the port
    /// inserts at index 0 of the `Vec`.
    pub fn add_role_chain_sub_sharing_linker(
        &mut self,
        role_chain_linker: RoleChainId,
    ) -> &mut Self {
        if role_chain_linker.is_some() {
            if self.role_chain_sub_sharing_linker.is_empty() {
                self.role_chain_sub_sharing_linker.push(role_chain_linker);
            } else {
                self.role_chain_sub_sharing_linker.insert(0, role_chain_linker);
            }
        }
        self
    }

    /// Port of `CRole::getRoleChainSubSharingLinker`.
    pub fn get_role_chain_sub_sharing_linker(&self) -> &[RoleChainId] {
        &self.role_chain_sub_sharing_linker
    }

    /// Port of `CRole::hasRoleChainSubSharingLinker(CRoleChain*)`.
    pub fn has_role_chain_sub_sharing_linker(&self, role_chain: RoleChainId) -> bool {
        for role_chain_it in self.role_chain_sub_sharing_linker.iter() {
            if *role_chain_it == role_chain {
                return true;
            }
        }
        false
    }

    // ===================== role-chain super sharing =====================

    /// Port of `CRole::hasRoleChainSuperSharing`.
    pub fn has_role_chain_super_sharing(&self) -> bool {
        !self.role_chain_super_sharing_linker.is_empty()
    }

    /// Port of `CRole::addRoleChainSuperSharingLinker`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: as `add_role_chain_sub_sharing_linker`,
    /// new entries go to the front (C++ append-as-head).
    pub fn add_role_chain_super_sharing_linker(
        &mut self,
        role_chain_linker: RoleChainId,
    ) -> &mut Self {
        if role_chain_linker.is_some() {
            if self.role_chain_super_sharing_linker.is_empty() {
                self.role_chain_super_sharing_linker.push(role_chain_linker);
            } else {
                self.role_chain_super_sharing_linker.insert(0, role_chain_linker);
            }
        }
        self
    }

    /// Port of `CRole::getRoleChainSuperSharingLinker`.
    pub fn get_role_chain_super_sharing_linker(&self) -> &[RoleChainId] {
        &self.role_chain_super_sharing_linker
    }

    /// Port of `CRole::hasRoleChainSuperSharingLinker(CRoleChain*)`.
    pub fn has_role_chain_super_sharing_linker(&self, role_chain: RoleChainId) -> bool {
        for role_chain_it in self.role_chain_super_sharing_linker.iter() {
            if *role_chain_it == role_chain {
                return true;
            }
        }
        false
    }
}
