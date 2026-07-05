//! Port of `Reasoner/Preprocess/CRoleChainAutomataTransformationPreProcess.{h,cpp}`.
//!
//! Rewrites every `∀R.C` / `∃R.C` (and the IMPL/BRANCH/PBIND/VARBIND/VARPBACK
//! `∀` variants) whose role is COMPLEX (transitive / chain-entailed) into a
//! role automaton: a `CCAQCHOOCE` trigger, a fresh begin/end `CCAQAND` state
//! pair, and `CCAQALL` transition concepts whose operand is the next state.
//! The already-ported automat choose/AND rules (`completion/u05.rs`) consume
//! this encoding, so complex roles never reach the tableau's plain ∀-rule.
//!
//! KONCLUDE-PORT-NOTE[api]: the C++ member vectors (`mRoleVec`, `mConVec`,
//! memory manager) collapse into the `&mut OntologyArenas` passed to
//! `preprocess`; `QHash::insertMulti` maps to `HashMap<K, Vec<V>>` with the
//! Konclude iteration order preserved where the algorithm depends on it
//! (grouping in `createRecursiveTraversalData`). Statistics counters are kept
//! 1:1. The expression-mapping bookkeeping for freshly created inverse roles
//! (`mRoleObjPropTermHash` etc., parser-layer back-references) has no
//! counterpart in the port and is dropped; the reasoning-relevant super-role
//! linker wiring is ported exactly.

#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use super::super::model::ontology::OntologyArenas;
use super::super::model::op;
use super::super::model::role_chain::RoleChain;
use super::super::model::substrate::Cint64;
use super::super::model::{ConceptId, IndividualId, RoleChainId, RoleId};

/// Port of `TRANSLATIONTYPE`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TranslationType {
    /// `TTNORMAL`
    Normal,
    /// `TTIMPL`
    Impl,
    /// `TTBRANCH`
    Branch,
    /// `TTPROPBIND`
    PropBind,
    /// `TTBACKPROP`
    BackProp,
    /// `TTVARBIND`
    VarBind,
}

/// Port of `CRoleSubRoleChainData` — one `chain ⊑ role` record as seen from an
/// (indirect) super role: `mRole` is the chain's direct super role, `mInverse`
/// the negation flag of the super-role linker it was reached through.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RoleSubRoleChainData {
    /// `mRole`
    pub role: RoleId,
    /// `mRoleChain`
    pub role_chain: RoleChainId,
    /// `mInverse`
    pub inverse: bool,
}

/// Port of `CRoleSubRoleChainDataItem` (the domain/range-propagation worklist
/// entry: initial entries allow the propagated-concept shortcut, re-enqueued
/// entries do not).
#[derive(Clone, Copy, Debug)]
pub struct RoleSubRoleChainDataItem {
    /// `mChainData`
    pub chain_data: RoleSubRoleChainData,
    /// `mNegated`
    pub negated: bool,
    /// `mAllowPropagated`
    pub allow_propagated: bool,
}

impl RoleSubRoleChainDataItem {
    /// Port of `CRoleSubRoleChainDataItem(CRoleSubRoleChainData&)`.
    pub fn new(chain_data: RoleSubRoleChainData) -> Self {
        RoleSubRoleChainDataItem {
            chain_data,
            negated: false,
            allow_propagated: true,
        }
    }
    /// Port of `CRoleSubRoleChainDataItem(CRoleSubRoleChainData&, bool)`.
    pub fn new_negated(chain_data: RoleSubRoleChainData, negated: bool) -> Self {
        RoleSubRoleChainDataItem {
            chain_data,
            negated,
            allow_propagated: false,
        }
    }
}

/// Port of `CRecTravSubRoleChainDataItem` — per-role automaton-generation data:
/// the chains unfolded inline (`mDirectSubRoleChainDataList`) and the critical
/// sub roles that get their own recursive begin/end state pair
/// (`mRecTraversalSubRoleList`, `(role, inversed)`).
#[derive(Clone, Debug)]
pub struct RecTravSubRoleChainDataItem {
    /// `mRole` (`RoleId::NONE` when default-constructed).
    pub role: RoleId,
    /// `mDirectSubRoleChainDataList`
    pub direct_sub_role_chain_data_list: Vec<RoleSubRoleChainData>,
    /// `mRecTraversalSubRoleList` (`QList<TRoleNegationPair>`)
    pub rec_traversal_sub_role_list: Vec<(RoleId, bool)>,
}

impl Default for RecTravSubRoleChainDataItem {
    /// Port of the default constructor (`mRole = nullptr`).
    fn default() -> Self {
        RecTravSubRoleChainDataItem {
            role: RoleId::NONE,
            direct_sub_role_chain_data_list: Vec::new(),
            rec_traversal_sub_role_list: Vec::new(),
        }
    }
}

/// Port of `CRoleChainAutomataTransformationPreProcess`.
pub struct RoleChainAutomataTransformationPreProcess {
    /// `mConfSaveTransitiveTransitions` (constructor default `true`).
    pub conf_save_transitive_transitions: bool,
    /// `mNextConceptTag` (`CTBox::getNextConceptID`).
    next_concept_tag: Cint64,
    /// `mRoleRecTravSubRoleChainDataHash`.
    role_rec_trav_sub_role_chain_data_hash: HashMap<RoleId, RecTravSubRoleChainDataItem>,
    /// `mRoleSubRoleChainDataHash` (`QHash::insertMulti` → `Vec` per key).
    role_sub_role_chain_data_hash: HashMap<RoleId, Vec<RoleSubRoleChainData>>,
    /// `mInverseUpdateRoleChainSet`.
    inverse_update_role_chain_set: HashSet<RoleChainId>,
    /// `mLastConceptForallId` (incremental `continuePreprocessing` cursor).
    last_concept_forall_id: Cint64,
    /// `mLastConceptValueId`.
    last_concept_value_id: Cint64,

    /// `mStatAutomateStateConceptCount`.
    pub stat_automate_state_concept_count: Cint64,
    /// `mStatAutomateTransitionConceptCount`.
    pub stat_automate_transition_concept_count: Cint64,
    /// `mStatAutomateTransformedConceptCount`.
    pub stat_automate_transformed_concept_count: Cint64,
    /// `mStatAutomateTransitiveSavedCount`.
    pub stat_automate_transitive_saved_count: Cint64,
    /// `mStatRangePropagationCount`.
    pub stat_range_propagation_count: Cint64,
    /// `mStatDomainPropagationCount`.
    pub stat_domain_propagation_count: Cint64,
    /// `mStatCreatedRangePropagationCount`.
    pub stat_created_range_propagation_count: Cint64,
    /// `mStatCreatedDomainPropagationCount`.
    pub stat_created_domain_propagation_count: Cint64,
    /// `mStatPropagationAlreadyInDomainRangeCount`.
    pub stat_propagation_already_in_domain_range_count: Cint64,
    /// `mStatPropagatedAlreadyInDomainRangeCount`.
    pub stat_propagated_already_in_domain_range_count: Cint64,
}

impl RoleChainAutomataTransformationPreProcess {
    /// Port of the constructor.
    pub fn new() -> Self {
        RoleChainAutomataTransformationPreProcess {
            conf_save_transitive_transitions: true,
            next_concept_tag: 0,
            role_rec_trav_sub_role_chain_data_hash: HashMap::new(),
            role_sub_role_chain_data_hash: HashMap::new(),
            inverse_update_role_chain_set: HashSet::new(),
            last_concept_forall_id: 0,
            last_concept_value_id: 0,
            stat_automate_state_concept_count: 0,
            stat_automate_transition_concept_count: 0,
            stat_automate_transformed_concept_count: 0,
            stat_automate_transitive_saved_count: 0,
            stat_range_propagation_count: 0,
            stat_domain_propagation_count: 0,
            stat_created_range_propagation_count: 0,
            stat_created_domain_propagation_count: 0,
            stat_propagation_already_in_domain_range_count: 0,
            stat_propagated_already_in_domain_range_count: 0,
        }
    }

    // ---------------------------------------------------------------------
    // inverse-role helpers
    // ---------------------------------------------------------------------

    /// Port of `hasInverseRole`.
    pub fn has_inverse_role(
        &self,
        arenas: &OntologyArenas,
        role: RoleId,
        search_inverse_equivalent: bool,
    ) -> bool {
        self.get_inverse_role(arenas, role, search_inverse_equivalent)
            .is_some()
    }

    /// Port of `getInverseRole` (default `searchInverseEquivalent = true` at
    /// the call sites that omit it).
    ///
    /// Lookup order is exact: the `mInverseRole` field; else a NEGATED entry in
    /// the inverse-equivalent list; else a NEGATED entry in the super-role list
    /// (with, when `search_inverse_equivalent`, the reciprocity check that the
    /// candidate's own super list points back at `role`).
    pub fn get_inverse_role(
        &self,
        arenas: &OntologyArenas,
        role: RoleId,
        search_inverse_equivalent: bool,
    ) -> Option<RoleId> {
        let r = arenas.role(role);
        let inverse = r.get_inverse_role();
        if inverse != RoleId::NONE {
            return Some(inverse);
        }
        for link in r.get_inverse_equivalent_role_list() {
            if link.negated {
                return Some(link.target);
            }
        }
        for link in &r.super_roles {
            if link.negated {
                let super_role = link.target;
                if !search_inverse_equivalent {
                    return Some(super_role);
                }
                for back in &arenas.role(super_role).super_roles {
                    if arenas.role(back.target).get_role_tag()
                        == arenas.role(role).get_role_tag()
                    {
                        return Some(super_role);
                    }
                }
            }
        }
        None
    }

    /// Port of `hasSuperRole(role, testingSuperRole, testInversed, superRoleInversedRequired)`.
    pub fn has_super_role(
        &self,
        arenas: &OntologyArenas,
        role: RoleId,
        testing_super_role: RoleId,
        test_inversed: bool,
        super_role_inversed_required: bool,
    ) -> bool {
        for link in &arenas.role(role).indirect_super_roles {
            if link.target == testing_super_role {
                if test_inversed {
                    if link.negated == super_role_inversed_required {
                        return true;
                    }
                } else {
                    return true;
                }
            }
        }
        false
    }

    /// Port of `hasSuperRole(role, testingSuperRole, superRoleInversedRequired)`.
    pub fn has_super_role3(
        &self,
        arenas: &OntologyArenas,
        role: RoleId,
        testing_super_role: RoleId,
        super_role_inversed_required: bool,
    ) -> bool {
        self.has_super_role(
            arenas,
            role,
            testing_super_role,
            true,
            super_role_inversed_required,
        )
    }

    /// Port of `hasInversedOrNonInversedSuperRole`.
    pub fn has_inversed_or_non_inversed_super_role(
        &self,
        arenas: &OntologyArenas,
        role: RoleId,
        testing_super_role: RoleId,
    ) -> bool {
        self.has_super_role(arenas, role, testing_super_role, false, false)
    }

    /// Port of `hasInversedSuperRole`.
    pub fn has_inversed_super_role(
        &self,
        arenas: &OntologyArenas,
        role: RoleId,
        testing_super_role: RoleId,
    ) -> bool {
        self.has_super_role(arenas, role, testing_super_role, true, true)
    }

    /// Port of `hasNonInversedSuperRole`.
    pub fn has_non_inversed_super_role(
        &self,
        arenas: &OntologyArenas,
        role: RoleId,
        testing_super_role: RoleId,
    ) -> bool {
        self.has_super_role(arenas, role, testing_super_role, true, false)
    }

    // ---------------------------------------------------------------------
    // chain collection (steps 1 + 3)
    // ---------------------------------------------------------------------

    /// Port of `collectSubRoleChains`: for every COMPLEX role and every chain
    /// it super-shares, record the chain under each of the role's indirect
    /// super roles (the linker's negation flag = the `inverse` mark); chains
    /// without an inverse role list yet are queued for
    /// `createInverseRoleChainLinkers`.
    pub fn collect_sub_role_chains(&mut self, arenas: &OntologyArenas) {
        let item_counts = arenas.role_count();
        for i in 0..item_counts {
            let role_id = RoleId::new(i);
            let role = arenas.role(role_id);
            if !role.is_complex_role() {
                continue;
            }
            let chains: Vec<RoleChainId> = role.role_chain_super_sharing_linker.clone();
            for role_chain in chains {
                if !arenas
                    .role_chain(role_chain)
                    .has_inverse_role_chain_linker()
                {
                    self.inverse_update_role_chain_set.insert(role_chain);
                }
                for super_link in &arenas.role(role_id).indirect_super_roles {
                    let super_role = super_link.target;
                    let super_role_neg = super_link.negated;
                    self.role_sub_role_chain_data_hash
                        .entry(super_role)
                        .or_default()
                        .push(RoleSubRoleChainData {
                            role: role_id,
                            role_chain,
                            inverse: super_role_neg,
                        });
                }
            }
        }
    }

    /// Port of `createInverseRoleChainLinkers`: the inverse list is the
    /// REVERSED role list (forward walk + prepend).
    pub fn create_inverse_role_chain_linkers(&mut self, arenas: &mut OntologyArenas) {
        // deterministic order (QSet iteration order is arbitrary; the result
        // is order-independent, so sort for reproducible builds).
        let mut chains: Vec<RoleChainId> =
            self.inverse_update_role_chain_set.iter().copied().collect();
        chains.sort_by_key(|c| c.index());
        for role_chain in chains {
            if arenas
                .role_chain(role_chain)
                .has_inverse_role_chain_linker()
            {
                continue;
            }
            let roles: Vec<RoleId> = arenas
                .role_chain(role_chain)
                .get_role_chain_linker()
                .to_vec();
            for chained_role in roles {
                arenas
                    .role_chain_mut(role_chain)
                    .prepend_inverse_role_chain_linker(chained_role);
            }
        }
    }

    // ---------------------------------------------------------------------
    // hasValue rewrite (step 4)
    // ---------------------------------------------------------------------

    /// Port of `createNominalConcept`: the individual's cached nominal concept,
    /// creating a fresh `CCNOMINAL` (and back-linking it) on first use.
    pub fn create_nominal_concept(
        &mut self,
        arenas: &mut OntologyArenas,
        individual: IndividualId,
    ) -> ConceptId {
        let existing = arenas.individual(individual).get_individual_nominal_concept();
        if existing != ConceptId::NONE {
            return existing;
        }
        let con_tag = self.next_concept_tag;
        self.next_concept_tag += 1;
        let mut concept = super::super::model::concept::Concept::new();
        concept.set_concept_tag(con_tag);
        concept.set_operator_code(op::CCNOMINAL);
        concept.set_nominal_individual(individual);
        let concept_id = arenas.alloc_concept(concept);
        arenas
            .individual_mut(individual)
            .set_individual_nominal_concept(concept_id);
        concept_id
    }

    /// Port of `transformVALUERestrictions`: `CCVALUE` (hasValue) on a COMPLEX
    /// role becomes `CCSOME` over the individual's nominal concept, so the ∀/∃
    /// automaton transformation below covers it. Incremental via
    /// `mLastConceptValueId`.
    pub fn transform_value_restrictions(&mut self, arenas: &mut OntologyArenas) {
        let con_count = arenas.concept_count();
        for i in self.last_concept_value_id..con_count {
            let concept_id = ConceptId::new(i);
            let (is_value, role_id, nom_individual) = {
                let concept = arenas.concept(concept_id);
                (
                    concept.get_operator_code() == op::CCVALUE,
                    concept.get_role(),
                    concept.get_nominal_individual(),
                )
            };
            if !is_value {
                continue;
            }
            if !arenas.role(role_id).is_complex_role() {
                continue;
            }
            let nom_concept = if nom_individual != IndividualId::NONE {
                let existing = arenas
                    .individual(nom_individual)
                    .get_individual_nominal_concept();
                if existing != ConceptId::NONE {
                    existing
                } else {
                    self.create_nominal_concept(arenas, nom_individual)
                }
            } else {
                continue;
            };
            let concept = arenas.concept_mut(concept_id);
            concept.set_operator_code(op::CCSOME);
            concept.set_nominal_individual(IndividualId::NONE);
            concept.set_operand_list(vec![super::super::model::substrate::NegLink {
                target: nom_concept,
                negated: false,
            }]);
            concept.set_operand_count(1);
        }
        self.last_concept_value_id = con_count;
    }

    // ---------------------------------------------------------------------
    // automaton building blocks (used by convertAutomatConcept; slice 3)
    // ---------------------------------------------------------------------

    /// Port of `createStateConcept` (`CC*AQAND` by translation type).
    pub fn create_state_concept(
        &mut self,
        arenas: &mut OntologyArenas,
        trans_type: TranslationType,
    ) -> ConceptId {
        let op_code = match trans_type {
            TranslationType::Normal => op::CCAQAND,
            TranslationType::Impl => op::CCIMPLAQAND,
            TranslationType::Branch => op::CCBRANCHAQAND,
            TranslationType::PropBind => op::CCPBINDAQAND,
            TranslationType::BackProp => op::CCVARPBACKAQAND,
            TranslationType::VarBind => op::CCVARBINDAQAND,
        };
        let con_tag = self.next_concept_tag;
        self.next_concept_tag += 1;
        let mut concept = super::super::model::concept::Concept::new();
        concept.set_concept_tag(con_tag);
        concept.set_operator_code(op_code);
        let id = arenas.alloc_concept(concept);
        self.stat_automate_state_concept_count += 1;
        id
    }

    /// Port of `createTransitionConcept` (`CC*AQALL` carrying the role).
    pub fn create_transition_concept(
        &mut self,
        arenas: &mut OntologyArenas,
        role: RoleId,
        trans_type: TranslationType,
    ) -> ConceptId {
        let op_code = match trans_type {
            TranslationType::Normal => op::CCAQALL,
            TranslationType::Impl => op::CCIMPLAQALL,
            TranslationType::Branch => op::CCBRANCHAQALL,
            TranslationType::PropBind => op::CCPBINDAQALL,
            TranslationType::BackProp => op::CCVARPBACKAQALL,
            TranslationType::VarBind => op::CCVARBINDAQALL,
        };
        let con_tag = self.next_concept_tag;
        self.next_concept_tag += 1;
        let mut concept = super::super::model::concept::Concept::new();
        concept.set_concept_tag(con_tag);
        concept.set_role(role);
        concept.set_operator_code(op_code);
        let id = arenas.alloc_concept(concept);
        self.stat_automate_transition_concept_count += 1;
        id
    }

    /// Port of `createAutomatGeneratingConcept`: fresh `CCAQSOME` on the role
    /// whose operands are the original operands, each negation XORed with
    /// `negate`.
    pub fn create_automat_generating_concept(
        &mut self,
        arenas: &mut OntologyArenas,
        op_linker: &[(ConceptId, bool)],
        negate: bool,
        role: RoleId,
    ) -> ConceptId {
        let con_tag = self.next_concept_tag;
        self.next_concept_tag += 1;
        let mut concept = super::super::model::concept::Concept::new();
        concept.set_concept_tag(con_tag);
        concept.set_operator_code(op::CCAQSOME);
        concept.set_role(role);
        let id = arenas.alloc_concept(concept);
        for &(op_concept, op_negation) in op_linker {
            self.append_transition_operand(arenas, id, op_concept, op_negation ^ negate);
        }
        id
    }

    /// Port of `createTransitionOperandConceptLinker` +
    /// `appendTransitionOperandConceptLinker` (linker allocation collapses into
    /// the `add_operand_linker` push).
    pub fn append_transition_operand(
        &mut self,
        arenas: &mut OntologyArenas,
        concept: ConceptId,
        operand: ConceptId,
        negation: bool,
    ) {
        let c = arenas.concept_mut(concept);
        c.add_operand_linker(operand, negation);
        c.inc_operand_count(1);
    }

    /// Attach the arenas' next concept tag before any pass (`preprocess` reads
    /// `tbox->getNextConceptID()`; here the arena length is the next tag).
    pub fn begin(&mut self, arenas: &OntologyArenas) {
        self.next_concept_tag = arenas.concept_count();
    }

    // ---------------------------------------------------------------------
    // chain relevance / recursive-traversal analysis (step 6)
    // ---------------------------------------------------------------------

    /// Port of `isChainLinkerImplicit`: element-wise, every role of the
    /// testing chain must have the corresponding role of `chain_linker` as an
    /// (indirect) super role with the required inversion; both chains must
    /// have equal length.
    pub fn is_chain_linker_implicit(
        &self,
        arenas: &OntologyArenas,
        testing_implicit_chain_linker: &[RoleId],
        chain_linker: &[RoleId],
        inversed_testing: bool,
    ) -> bool {
        if testing_implicit_chain_linker.len() != chain_linker.len() {
            return false;
        }
        for (&testing_chain_role, &chain_role) in
            testing_implicit_chain_linker.iter().zip(chain_linker.iter())
        {
            if !self.has_super_role3(arenas, testing_chain_role, chain_role, inversed_testing) {
                return false;
            }
        }
        true
    }

    /// Port of `isTransitiveChainData`: every chain element IS the chain's
    /// super role and the chain has exactly 2 elements (`R ∘ R ⊑ R`).
    pub fn is_transitive_chain_data(
        &self,
        arenas: &OntologyArenas,
        chain_data: &RoleSubRoleChainData,
    ) -> bool {
        let chain_super_role = chain_data.role;
        let mut trans_chained_role_count = 0;
        for &chained_role in arenas
            .role_chain(chain_data.role_chain)
            .get_role_chain_linker()
        {
            if chained_role != chain_super_role {
                return false;
            }
            trans_chained_role_count += 1;
        }
        trans_chained_role_count == 2
    }

    /// Port of `isChainDataImplicit`: `testing` is implicit when its super
    /// role is (inversed or not, per the combined inversion flag) below
    /// `chain_data`'s super role and its chain is element-wise below
    /// `chain_data`'s (inverse-)chain.
    pub fn is_chain_data_implicit(
        &self,
        arenas: &OntologyArenas,
        testing_implicit_chain_data: &RoleSubRoleChainData,
        chain_data: &RoleSubRoleChainData,
    ) -> bool {
        let testing_chain_super_role = testing_implicit_chain_data.role;
        let chain_super_role = chain_data.role;
        let inversed_testing = chain_data.inverse ^ testing_implicit_chain_data.inverse;
        if !self.has_inversed_or_non_inversed_super_role(
            arenas,
            testing_chain_super_role,
            chain_super_role,
        ) {
            return false;
        }
        if !inversed_testing
            && self.has_non_inversed_super_role(arenas, testing_chain_super_role, chain_super_role)
        {
            let testing_chain = arenas
                .role_chain(testing_implicit_chain_data.role_chain)
                .get_role_chain_linker();
            let chain = arenas
                .role_chain(chain_data.role_chain)
                .get_role_chain_linker();
            if self.is_chain_linker_implicit(arenas, testing_chain, chain, false) {
                return true;
            }
        }
        if inversed_testing
            && self.has_inversed_super_role(arenas, testing_chain_super_role, chain_super_role)
        {
            let testing_chain = arenas
                .role_chain(testing_implicit_chain_data.role_chain)
                .get_role_chain_linker();
            let inv_chain = arenas
                .role_chain(chain_data.role_chain)
                .get_inverse_role_chain_linker();
            if self.is_chain_linker_implicit(arenas, testing_chain, inv_chain, true) {
                return true;
            }
        }
        false
    }

    /// Port of `getRelevantChainDataList`: drop every chain that is implicit
    /// in a LATER list entry or in an already-kept one.
    pub fn get_relevant_chain_data_list(
        &self,
        arenas: &OntologyArenas,
        _role: RoleId,
        role_sub_chain_data_list: &[RoleSubRoleChainData],
    ) -> Vec<RoleSubRoleChainData> {
        let mut relevant: Vec<RoleSubRoleChainData> = Vec::new();
        for (i, chain_data) in role_sub_chain_data_list.iter().enumerate() {
            let mut has_implicit = false;
            for chain_data2 in role_sub_chain_data_list.iter().skip(i + 1) {
                if self.is_chain_data_implicit(arenas, chain_data, chain_data2) {
                    has_implicit = true;
                    break;
                }
            }
            if !has_implicit {
                for chain_data2 in &relevant {
                    if self.is_chain_data_implicit(arenas, chain_data, chain_data2) {
                        has_implicit = true;
                        break;
                    }
                }
            }
            if !has_implicit {
                relevant.push(*chain_data);
            }
        }
        relevant
    }

    /// Port of `isChainDataRecursiveTraversalCritical`: the chain's super role
    /// is a DIFFERENT role that is not above `role`, and the chain starts or
    /// ends with that super role (so inlining it would loop).
    pub fn is_chain_data_recursive_traversal_critical(
        &self,
        arenas: &OntologyArenas,
        role: RoleId,
        chain_data: &RoleSubRoleChainData,
    ) -> bool {
        let chain_super_role = chain_data.role;
        if chain_super_role == role {
            return false;
        }
        if self.has_inversed_or_non_inversed_super_role(arenas, role, chain_super_role) {
            return false;
        }
        let chain = arenas
            .role_chain(chain_data.role_chain)
            .get_role_chain_linker();
        if let (Some(&first), Some(&last)) = (chain.first(), chain.last()) {
            if first == chain_super_role || last == chain_super_role {
                return true;
            }
        }
        false
    }

    /// Port of `collectRecursiveTraversalCriticalRoles`.
    pub fn collect_recursive_traversal_critical_roles(
        &self,
        arenas: &OntologyArenas,
        role: RoleId,
        chain_data: &RoleSubRoleChainData,
        critical_role_negation_hash: &mut HashMap<RoleId, bool>,
    ) -> bool {
        if self.is_chain_data_recursive_traversal_critical(arenas, role, chain_data) {
            critical_role_negation_hash.insert(chain_data.role, chain_data.inverse);
            return true;
        }
        false
    }

    /// Port of `getRelevantRecursiveTraversalCriticalRoles`: keep only the
    /// most general critical roles (those with no critical strict super role).
    pub fn get_relevant_recursive_traversal_critical_roles(
        &self,
        arenas: &OntologyArenas,
        critical_role_negation_hash: &HashMap<RoleId, bool>,
    ) -> HashMap<RoleId, bool> {
        // deterministic iteration (QHash order is arbitrary; result depends
        // only on the SET of survivors, but sort for reproducible builds).
        let mut entries: Vec<(RoleId, bool)> = critical_role_negation_hash
            .iter()
            .map(|(k, v)| (*k, *v))
            .collect();
        entries.sort_by_key(|(r, _)| r.index());
        let mut critical_general: HashMap<RoleId, bool> = HashMap::new();
        for (i, &(role, role_inversed)) in entries.iter().enumerate() {
            let mut has_critical_super_role = false;
            for &(role2, _) in entries.iter().skip(i + 1) {
                if role != role2
                    && self.has_inversed_or_non_inversed_super_role(arenas, role, role2)
                {
                    has_critical_super_role = true;
                    break;
                }
            }
            if !has_critical_super_role {
                for (&role2, _) in critical_general.iter() {
                    if role != role2
                        && self.has_inversed_or_non_inversed_super_role(arenas, role, role2)
                    {
                        has_critical_super_role = true;
                        break;
                    }
                }
            }
            if !has_critical_super_role {
                critical_general.insert(role, role_inversed);
            }
        }
        critical_general
    }

    /// Port of `requiresRecursiveTraversalForRole`: the chain's super role has
    /// an (indirect) super role in the critical set.
    pub fn requires_recursive_traversal_for_role(
        &self,
        arenas: &OntologyArenas,
        _role: RoleId,
        chain_data: &RoleSubRoleChainData,
        critical_role_negation_hash: &HashMap<RoleId, bool>,
    ) -> bool {
        let chain_super_role = chain_data.role;
        for link in &arenas.role(chain_super_role).indirect_super_roles {
            if critical_role_negation_hash.contains_key(&link.target) {
                return true;
            }
        }
        false
    }

    /// Port of `addRecursiveTraversalData`.
    pub fn add_recursive_traversal_data(
        &mut self,
        arenas: &OntologyArenas,
        role: RoleId,
        role_sub_chain_data_list: &[RoleSubRoleChainData],
    ) {
        let relevant = self.get_relevant_chain_data_list(arenas, role, role_sub_chain_data_list);
        let mut item = RecTravSubRoleChainDataItem {
            role,
            ..Default::default()
        };
        let mut critical_role_negation_hash: HashMap<RoleId, bool> = HashMap::new();
        let mut critical = false;
        for chain_data in &relevant {
            critical |= self.collect_recursive_traversal_critical_roles(
                arenas,
                role,
                chain_data,
                &mut critical_role_negation_hash,
            );
        }
        if !critical {
            item.direct_sub_role_chain_data_list = relevant;
        } else {
            let relevant_critical = self
                .get_relevant_recursive_traversal_critical_roles(
                    arenas,
                    &critical_role_negation_hash,
                );
            for chain_data in &relevant {
                if !self.requires_recursive_traversal_for_role(
                    arenas,
                    role,
                    chain_data,
                    &relevant_critical,
                ) {
                    item.direct_sub_role_chain_data_list.push(*chain_data);
                }
            }
            // deterministic order for the recursion list too.
            let mut crit_entries: Vec<(RoleId, bool)> = relevant_critical
                .iter()
                .map(|(k, v)| (*k, *v))
                .collect();
            crit_entries.sort_by_key(|(r, _)| r.index());
            for (crit_role, inversed) in crit_entries {
                let outer = arenas.role(item.role);
                if outer.is_symmetric() && outer.get_inverse_role() == item.role {
                    item.rec_traversal_sub_role_list.push((crit_role, !inversed));
                }
                item.rec_traversal_sub_role_list.push((crit_role, inversed));
            }
        }
        self.role_rec_trav_sub_role_chain_data_hash.insert(role, item);
    }

    /// Port of `createRecursiveTraversalData`: group the multi-hash per role
    /// and analyse each group.
    pub fn create_recursive_traversal_data(&mut self, arenas: &OntologyArenas) {
        // Konclude walks the QHash grouped by key (same-key values adjacent,
        // most-recent-first). The per-key grouping is what matters; iterate
        // keys deterministically and hand each full group over.
        let mut keys: Vec<RoleId> = self.role_sub_role_chain_data_hash.keys().copied().collect();
        keys.sort_by_key(|r| r.index());
        for role in keys {
            // QHash multi-values iterate most-recently-inserted first; our Vec
            // holds insertion order, so reverse for the exact Konclude order
            // (mutually-implicit chain pairs keep the same survivor).
            let mut list = self.role_sub_role_chain_data_hash[&role].clone();
            list.reverse();
            self.add_recursive_traversal_data(arenas, role, &list);
        }
    }
}

impl Default for RoleChainAutomataTransformationPreProcess {
    fn default() -> Self {
        RoleChainAutomataTransformationPreProcess::new()
    }
}
