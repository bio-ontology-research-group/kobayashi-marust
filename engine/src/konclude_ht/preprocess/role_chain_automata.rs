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
                    if arenas.role(back.target).get_role_tag() == arenas.role(role).get_role_tag() {
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
        let existing = arenas
            .individual(individual)
            .get_individual_nominal_concept();
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

    /// Attach the arenas' next concept tag before any pass. Konclude reads
    /// `tbox->getNextConceptID()`, which is one past the largest allocated
    /// concept tag, not the number of arena entries. The two differ for the
    /// bridge's reserved TOP/named tag ranges.
    pub fn begin(&mut self, arenas: &OntologyArenas) {
        self.next_concept_tag = (0..arenas.concept_count())
            .map(|i| arenas.concept(ConceptId::new(i)).get_concept_tag())
            .max()
            .unwrap_or(-1)
            + 1;
        if std::env::var_os("KM_HT_STATS").is_some() {
            eprintln!(
                "role-automata begin concepts={} next-tag={}",
                arenas.concept_count(),
                self.next_concept_tag
            );
        }
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
        for (&testing_chain_role, &chain_role) in testing_implicit_chain_linker
            .iter()
            .zip(chain_linker.iter())
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
            let relevant_critical = self.get_relevant_recursive_traversal_critical_roles(
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
            let mut crit_entries: Vec<(RoleId, bool)> =
                relevant_critical.iter().map(|(k, v)| (*k, *v)).collect();
            crit_entries.sort_by_key(|(r, _)| r.index());
            for (crit_role, inversed) in crit_entries {
                let outer = arenas.role(item.role);
                if outer.is_symmetric() && outer.get_inverse_role() == item.role {
                    item.rec_traversal_sub_role_list
                        .push((crit_role, !inversed));
                }
                item.rec_traversal_sub_role_list.push((crit_role, inversed));
            }
        }
        self.role_rec_trav_sub_role_chain_data_hash
            .insert(role, item);
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

    // ---------------------------------------------------------------------
    // the automaton transformation (steps 7 + 8 + 9)
    // ---------------------------------------------------------------------

    /// Port of `transformFORALLPropagations`: every `∀`/`∃`-family concept on a
    /// COMPLEX role becomes an automaton. Incremental via
    /// `mLastConceptForallId` (`continuePreprocessing` re-enters here).
    pub fn transform_forall_propagations(&mut self, arenas: &mut OntologyArenas) {
        let con_count = arenas.concept_count();
        for i in self.last_concept_forall_id..con_count {
            let concept_id = ConceptId::new(i);
            let (op_code, role_id) = {
                let concept = arenas.concept(concept_id);
                (concept.get_operator_code(), concept.get_role())
            };
            let is_forall_family = op_code == op::CCALL
                || op_code == op::CCSOME
                || op_code == op::CCIMPLALL
                || op_code == op::CCBRANCHALL
                || op_code == op::CCVARBINDALL
                || op_code == op::CCPBINDALL
                || op_code == op::CCVARPBACKALL;
            if !is_forall_family || role_id == RoleId::NONE {
                continue;
            }
            if !arenas.role(role_id).is_complex_role() {
                continue;
            }
            self.stat_automate_transformed_concept_count += 1;
            self.convert_automat_concept(arenas, concept_id);
        }
        self.last_concept_forall_id = con_count;
    }

    /// Port of `convertAutomatConcept` — the heart of the transformation.
    ///
    /// `∀R.C` (`CCALL`, and the IMPL/BRANCH/…∀ variants) with complex `R`
    /// becomes:
    ///   - TTNORMAL: the concept itself turns into `CCAQCHOOCE` whose operands
    ///     are a fresh `CCAQSOME` generating concept (negated per the ∃/∀
    ///     duality) and the automaton's begin state;
    ///   - non-normal variants: the concept itself BECOMES the begin state
    ///     (`CC*AQAND`, role cleared).
    /// The begin state fires a `CC*AQALL` transition on `R` into the end state
    /// (which carries the original filler operands), and
    /// `generateRoleChainAutomatConcept` glues in one sub-automaton per
    /// relevant sub-role chain — transitive chains become loops between the
    /// states, which is exactly what lets a single concept chase `R`-paths of
    /// unbounded length.
    pub fn convert_automat_concept(&mut self, arenas: &mut OntologyArenas, concept_id: ConceptId) {
        let (op_con_linker, role): (Vec<(ConceptId, bool)>, RoleId) = {
            let concept = arenas.concept(concept_id);
            (
                concept
                    .get_operand_list()
                    .iter()
                    .map(|l| (l.target, l.negated))
                    .collect(),
                concept.get_role(),
            )
        };
        let op_code = arenas.concept(concept_id).get_operator_code();
        let exist_negation = op_code == op::CCSOME;

        let trans_type = if op_code == op::CCIMPLALL {
            TranslationType::Impl
        } else if op_code == op::CCBRANCHALL {
            TranslationType::Branch
        } else if op_code == op::CCPBINDALL {
            TranslationType::PropBind
        } else if op_code == op::CCVARPBACKALL {
            TranslationType::BackProp
        } else if op_code == op::CCVARBINDALL {
            TranslationType::VarBind
        } else {
            TranslationType::Normal
        };

        let mut generating_concept = ConceptId::NONE;
        let begin_state;

        if trans_type == TranslationType::Normal {
            arenas
                .concept_mut(concept_id)
                .set_operator_code(op::CCAQCHOOCE);
            generating_concept = self.create_automat_generating_concept(
                arenas,
                &op_con_linker,
                !exist_negation,
                role,
            );
            begin_state = self.create_state_concept(arenas, trans_type);
        } else {
            // the ∀ concept itself becomes the begin state.
            begin_state = concept_id;
            let aqand_code = match trans_type {
                TranslationType::Impl => op::CCIMPLAQAND,
                TranslationType::Branch => op::CCBRANCHAQAND,
                TranslationType::PropBind => op::CCPBINDAQAND,
                TranslationType::BackProp => op::CCVARPBACKAQAND,
                TranslationType::VarBind => op::CCVARBINDAQAND,
                TranslationType::Normal => op::CCAQAND,
            };
            let c = arenas.concept_mut(concept_id);
            c.set_operator_code(aqand_code);
            c.set_role(RoleId::NONE);
        }
        {
            let c = arenas.concept_mut(concept_id);
            c.set_operand_list(Vec::new());
            c.set_operand_count(0);
        }

        let prop_con = self.create_transition_concept(arenas, role, trans_type);
        let end_state = self.create_state_concept(arenas, trans_type);

        for &(op_concept, op_neg) in &op_con_linker {
            self.append_transition_operand(arenas, end_state, op_concept, op_neg ^ exist_negation);
        }

        if trans_type == TranslationType::Normal {
            self.append_transition_operand(arenas, concept_id, generating_concept, !exist_negation);
            self.append_transition_operand(arenas, concept_id, begin_state, exist_negation);
        }

        self.append_transition_operand(arenas, begin_state, prop_con, false);
        self.append_transition_operand(arenas, prop_con, end_state, false);

        if arenas.role(role).get_role_tag() == 1 {
            // the TOP/universal role: everything reachable — a plain self-loop.
            self.append_transition_operand(arenas, end_state, begin_state, false);
        } else {
            let rec_trav_item = self
                .role_rec_trav_sub_role_chain_data_hash
                .get(&role)
                .cloned()
                .unwrap_or_default();
            let mut loc_unfold: HashSet<RoleId> = HashSet::new();
            self.generate_role_chain_automat_concept_rec(
                arenas,
                role,
                &rec_trav_item,
                &mut loc_unfold,
                begin_state,
                end_state,
                trans_type,
            );
        }
    }

    /// Port of `generateRoleChainAutomatConcept(lastRole, recTravItem, …)` —
    /// unfold the direct chains, then give each recursive-traversal critical
    /// sub role its own begin/end state pair and recurse into ITS automaton.
    #[allow(clippy::too_many_arguments)]
    pub fn generate_role_chain_automat_concept_rec(
        &mut self,
        arenas: &mut OntologyArenas,
        last_role: RoleId,
        rec_trav_item: &RecTravSubRoleChainDataItem,
        already_unfold_role_set: &mut HashSet<RoleId>,
        begin_concept: ConceptId,
        end_concept: ConceptId,
        trans_type: TranslationType,
    ) -> bool {
        self.generate_role_chain_automat_concept_list(
            arenas,
            last_role,
            &rec_trav_item.direct_sub_role_chain_data_list,
            already_unfold_role_set,
            begin_concept,
            end_concept,
            trans_type,
        );

        for &(rec_trav_sub_role0, inversed) in &rec_trav_item.rec_traversal_sub_role_list {
            if already_unfold_role_set.contains(&rec_trav_sub_role0) {
                continue;
            }
            let rec_trav_sub_role = if inversed {
                match self.get_inverse_role(arenas, rec_trav_sub_role0, true) {
                    Some(r) => r,
                    // createMissingInverseChainedRoles guarantees existence in
                    // Konclude; degrade gracefully if the RBox lacks it.
                    None => continue,
                }
            } else {
                rec_trav_sub_role0
            };

            let mut loc_unfold: HashSet<RoleId> = already_unfold_role_set.clone();
            loc_unfold.insert(rec_trav_sub_role);
            for link in &arenas.role(rec_trav_sub_role).indirect_super_roles {
                loc_unfold.insert(link.target);
            }

            let rec_begin = self.create_state_concept(arenas, trans_type);
            let rec_end = self.create_state_concept(arenas, trans_type);
            self.append_transition_operand(arenas, begin_concept, rec_begin, false);
            self.append_transition_operand(arenas, rec_end, end_concept, false);
            let rec_prop = self.create_transition_concept(arenas, rec_trav_sub_role, trans_type);
            self.append_transition_operand(arenas, rec_begin, rec_prop, false);
            self.append_transition_operand(arenas, rec_prop, rec_end, false);
            let next_item = self
                .role_rec_trav_sub_role_chain_data_hash
                .get(&rec_trav_sub_role)
                .cloned()
                .unwrap_or_default();
            self.generate_role_chain_automat_concept_rec(
                arenas,
                rec_trav_sub_role,
                &next_item,
                &mut loc_unfold,
                rec_begin,
                rec_end,
                trans_type,
            );
        }
        true
    }

    /// Port of `generateRoleChainAutomatConcept(lastRole, subRoleChainDataList, …)`.
    #[allow(clippy::too_many_arguments)]
    pub fn generate_role_chain_automat_concept_list(
        &mut self,
        arenas: &mut OntologyArenas,
        last_role: RoleId,
        sub_role_chain_data_list: &[RoleSubRoleChainData],
        already_unfold_role_set: &mut HashSet<RoleId>,
        begin_concept: ConceptId,
        end_concept: ConceptId,
        trans_type: TranslationType,
    ) -> bool {
        for chain_data in sub_role_chain_data_list {
            let mut loc_unfold: HashSet<RoleId> = already_unfold_role_set.clone();
            loc_unfold.insert(last_role);
            for link in &arenas.role(chain_data.role).indirect_super_roles {
                loc_unfold.insert(link.target);
            }
            self.generate_role_chain_automat_concept_chain(
                arenas,
                last_role,
                chain_data.role,
                chain_data.role_chain,
                chain_data.inverse,
                &mut loc_unfold,
                begin_concept,
                end_concept,
                trans_type,
            );
        }
        true
    }

    /// Port of `generateRoleChainAutomatConcept(lastRole, superRole, chain, …)`
    /// — one chain `S1 ∘ … ∘ Sn ⊑ superRole` glued between `begin_concept` and
    /// `end_concept`. A chain that STARTS with its own super role loops through
    /// the end state (`transStart`), one that ENDS with it loops through the
    /// begin state (`transEnd`); the pure transitive chain `R ∘ R ⊑ R` reduces
    /// to the ε-transition `end → begin`.
    #[allow(clippy::too_many_arguments)]
    pub fn generate_role_chain_automat_concept_chain(
        &mut self,
        arenas: &mut OntologyArenas,
        last_role: RoleId,
        super_role: RoleId,
        descending_role_chain: RoleChainId,
        negated_chain: bool,
        already_unfold_role_set: &mut HashSet<RoleId>,
        begin_concept: ConceptId,
        end_concept: ConceptId,
        trans_type: TranslationType,
    ) -> bool {
        let use_inverse_roles = negated_chain;
        let chained_roles: Vec<RoleId> = if !negated_chain {
            arenas
                .role_chain(descending_role_chain)
                .get_role_chain_linker()
                .to_vec()
        } else {
            arenas
                .role_chain(descending_role_chain)
                .get_inverse_role_chain_linker()
                .to_vec()
        };

        let mut connect_begin_con = ConceptId::NONE;
        let mut connect_end_con = ConceptId::NONE;
        let mut first_concept = ConceptId::NONE;
        let mut trans_start = false;
        let mut trans_end = false;

        let test_role = if use_inverse_roles && last_role != super_role {
            self.get_inverse_role(arenas, super_role, true)
                .unwrap_or(super_role)
        } else {
            super_role
        };

        let n = chained_roles.len();
        for (idx, &chained_role) in chained_roles.iter().enumerate() {
            let sub_role = if use_inverse_roles {
                match self.get_inverse_role(arenas, chained_role, true) {
                    Some(r) => r,
                    None => continue,
                }
            } else {
                chained_role
            };
            let is_last = idx + 1 == n;

            if first_concept == ConceptId::NONE && sub_role == test_role && !trans_start {
                trans_start = true;
            } else if is_last && sub_role == test_role {
                trans_end = true;
            } else if !already_unfold_role_set.contains(&sub_role) {
                let sub_begin = self.create_state_concept(arenas, trans_type);
                let prop_con = self.create_transition_concept(arenas, sub_role, trans_type);
                let sub_end = self.create_state_concept(arenas, trans_type);
                if connect_begin_con == ConceptId::NONE {
                    connect_begin_con = sub_begin;
                }
                if connect_end_con != ConceptId::NONE {
                    self.append_transition_operand(arenas, connect_end_con, sub_begin, false);
                }
                connect_end_con = sub_end;
                if first_concept == ConceptId::NONE {
                    first_concept = prop_con;
                }
                self.append_transition_operand(arenas, sub_begin, prop_con, false);
                self.append_transition_operand(arenas, prop_con, sub_end, false);

                let next_item = self
                    .role_rec_trav_sub_role_chain_data_hash
                    .get(&sub_role)
                    .cloned()
                    .unwrap_or_default();
                self.generate_role_chain_automat_concept_rec(
                    arenas,
                    sub_role,
                    &next_item,
                    already_unfold_role_set,
                    sub_begin,
                    sub_end,
                    trans_type,
                );
            } else {
                // Konclude: "error, not allowed construct" (a chain element
                // already being unfolded above) — silently skipped there too.
            }
        }

        if trans_start && !trans_end {
            self.append_transition_operand(arenas, end_concept, connect_begin_con, false);
            self.append_transition_operand(arenas, connect_end_con, end_concept, false);
        } else if trans_end && !trans_start {
            self.append_transition_operand(arenas, connect_end_con, begin_concept, false);
            self.append_transition_operand(arenas, begin_concept, connect_begin_con, false);
        } else if trans_start && trans_end && first_concept == ConceptId::NONE {
            // pure transitivity `R ∘ R ⊑ R`: the ε-loop end → begin.
            self.append_transition_operand(arenas, end_concept, begin_concept, false);
        } else if !trans_start && !trans_end {
            if connect_begin_con != ConceptId::NONE && connect_end_con != ConceptId::NONE {
                self.append_transition_operand(arenas, begin_concept, connect_begin_con, false);
                self.append_transition_operand(arenas, connect_end_con, end_concept, false);
            }
        } else {
            // error, not allowed construct (transStart && transEnd with inner
            // concepts) — Konclude falls through silently.
        }
        true
    }

    // ---------------------------------------------------------------------
    // missing inverse roles (step 2)
    // ---------------------------------------------------------------------

    /// Port of `createMissingInverseChainedRoles`: every role that the
    /// chain/domain machinery will need inverted gets a synthesized inverse
    /// role wired through NEGATED super-role linkers (Konclude models
    /// inversion that way; `getInverseRole` finds it via the reciprocity
    /// check). Re-collects the chains afterwards when anything was created.
    pub fn create_missing_inverse_chained_roles(&mut self, arenas: &mut OntologyArenas) {
        // collect direct and indirect sub roles (super-tag → (sub-tag, neg)).
        let item_counts = arenas.role_count();
        let mut indirect_sub: HashMap<Cint64, Vec<(Cint64, bool)>> = HashMap::new();
        let mut direct_sub: HashMap<Cint64, Vec<(Cint64, bool)>> = HashMap::new();
        for i in 0..item_counts {
            let role_id = RoleId::new(i);
            let role = arenas.role(role_id);
            let role_tag = role.get_role_tag();
            for link in &role.indirect_super_roles {
                indirect_sub
                    .entry(arenas.role(link.target).get_role_tag())
                    .or_default()
                    .push((role_tag, link.negated));
            }
            for link in &arenas.role(role_id).super_roles {
                direct_sub
                    .entry(arenas.role(link.target).get_role_tag())
                    .or_default()
                    .push((role_tag, link.negated));
            }
        }

        // roles that need an inverse.
        let mut needs_inverse: HashSet<RoleId> = HashSet::new();
        for i in 0..item_counts {
            let role_id = RoleId::new(i);
            if !arenas.role(role_id).is_complex_role() {
                continue;
            }
            if !arenas.role(role_id).get_domain_concept_list().is_empty() {
                needs_inverse.insert(role_id);
            }
            let has_dom_range = !arenas.role(role_id).get_domain_concept_list().is_empty()
                || !arenas.role(role_id).get_range_concept_list().is_empty();
            if self.has_inverse_role(arenas, role_id, true) || has_dom_range {
                // BFS over the chain graph: every chain super role and every
                // chained sub role will be traversed inverted.
                let mut search_list: Vec<RoleId> = vec![role_id];
                let mut search_set: HashSet<RoleId> = HashSet::new();
                search_set.insert(role_id);
                while let Some(search_role) = search_list.pop() {
                    let datas: Vec<RoleSubRoleChainData> = self
                        .role_sub_role_chain_data_hash
                        .get(&search_role)
                        .cloned()
                        .unwrap_or_default();
                    for data in datas {
                        needs_inverse.insert(data.role);
                        let chained: Vec<RoleId> = arenas
                            .role_chain(data.role_chain)
                            .get_role_chain_linker()
                            .to_vec();
                        for sub_role in chained {
                            needs_inverse.insert(sub_role);
                            if search_set.insert(sub_role) {
                                search_list.push(sub_role);
                            }
                        }
                    }
                }
            }
        }

        let mut updated_inverse_roles = false;
        let mut needs: Vec<RoleId> = needs_inverse.into_iter().collect();
        needs.sort_by_key(|r| r.index());
        for role_id in needs {
            if self.has_inverse_role(arenas, role_id, true) {
                continue;
            }
            updated_inverse_roles = true;
            let role_tag = arenas.role(role_id).get_role_tag();
            let complexity = arenas.role(role_id).get_role_complexity();

            let mut inverse = super::super::model::role::Role::new();
            let inverse_role_tag = arenas.role_count();
            inverse.set_role_tag(inverse_role_tag);
            inverse.set_role_complexity(complexity);
            let inverse_id = arenas.alloc_role(inverse);

            // the defining pair of NEGATED super-role linkers.
            arenas
                .role_mut(inverse_id)
                .super_roles
                .push(super::super::model::substrate::NegLink {
                    target: role_id,
                    negated: true,
                });
            arenas
                .role_mut(role_id)
                .super_roles
                .push(super::super::model::substrate::NegLink {
                    target: inverse_id,
                    negated: true,
                });

            // every direct sub role of `role` gets the new inverse as an
            // INVERTED super role (and dito the indirect ones).
            for &(sub_tag, neg) in direct_sub
                .get(&role_tag)
                .map(|v| v.as_slice())
                .unwrap_or(&[])
            {
                let sub_id = RoleId::new(sub_tag);
                arenas
                    .role_mut(sub_id)
                    .super_roles
                    .push(super::super::model::substrate::NegLink {
                        target: inverse_id,
                        negated: !neg,
                    });
            }
            for &(sub_tag, neg) in indirect_sub
                .get(&role_tag)
                .map(|v| v.as_slice())
                .unwrap_or(&[])
            {
                let sub_id = RoleId::new(sub_tag);
                arenas.role_mut(sub_id).indirect_super_roles.push(
                    super::super::model::substrate::NegLink {
                        target: inverse_id,
                        negated: !neg,
                    },
                );
            }

            // copy `role`'s (indirect) super lists onto the inverse, inverted,
            // and register the inverse as their sub role in the tag hashes.
            let indirect_of_role: Vec<(RoleId, bool)> = arenas
                .role(role_id)
                .indirect_super_roles
                .iter()
                .map(|l| (l.target, l.negated))
                .collect();
            for (super_role, neg) in indirect_of_role {
                arenas.role_mut(inverse_id).indirect_super_roles.push(
                    super::super::model::substrate::NegLink {
                        target: super_role,
                        negated: !neg,
                    },
                );
                indirect_sub
                    .entry(arenas.role(super_role).get_role_tag())
                    .or_default()
                    .push((inverse_role_tag, !neg));
            }
            let supers_of_role: Vec<(RoleId, bool)> = arenas
                .role(role_id)
                .super_roles
                .iter()
                .map(|l| (l.target, l.negated))
                .collect();
            for (super_role, neg) in supers_of_role {
                arenas.role_mut(inverse_id).super_roles.push(
                    super::super::model::substrate::NegLink {
                        target: super_role,
                        negated: !neg,
                    },
                );
                direct_sub
                    .entry(arenas.role(super_role).get_role_tag())
                    .or_default()
                    .push((inverse_role_tag, !neg));
            }
        }

        if updated_inverse_roles {
            self.role_sub_role_chain_data_hash.clear();
            self.collect_sub_role_chains(arenas);
        }
    }

    // ---------------------------------------------------------------------
    // domain / range propagation down chains (step 5)
    // ---------------------------------------------------------------------

    /// Port of `hasPropagatedConcept`: the concept already sits directly in
    /// the relevant domain/range list of some (indirect) super role.
    pub fn has_propagated_concept(
        &mut self,
        arenas: &OntologyArenas,
        negated: bool,
        concept: ConceptId,
        role_list: &[(RoleId, bool)],
        inverse_dom_range: bool,
    ) -> bool {
        for &(super_role, super_neg) in role_list {
            let switch_domain_range = inverse_dom_range ^ super_neg;
            for link in arenas
                .role(super_role)
                .get_domain_range_concept_list(!switch_domain_range)
            {
                if link.target == concept && link.negated == negated {
                    self.stat_propagated_already_in_domain_range_count += 1;
                    return true;
                }
            }
        }
        false
    }

    /// Port of `hasPropagationConcept`: some (indirect) super role already
    /// carries a `∀role.concept`-shaped propagation in the relevant
    /// domain/range list.
    ///
    /// KONCLUDE-PORT-NOTE[fidelity]: the operand test keeps the C++ operator
    /// precedence exactly as written — `opNeg ^ conNeg == negated` parses as
    /// `opNeg ^ (conNeg == negated)` (== binds tighter than ^). Both helpers
    /// only dedup already-present propagations, so this affects redundancy,
    /// never soundness.
    pub fn has_propagation_concept(
        &mut self,
        arenas: &OntologyArenas,
        negated: bool,
        concept: ConceptId,
        role: RoleId,
        role_list: &[(RoleId, bool)],
        inverse_dom_range: bool,
    ) -> bool {
        for &(super_role, super_neg) in role_list {
            let switch_domain_range = inverse_dom_range ^ super_neg;
            for link in arenas
                .role(super_role)
                .get_domain_range_concept_list(switch_domain_range)
            {
                let con = link.target;
                let con_neg = link.negated;
                if arenas.concept(con).get_role() != role {
                    continue;
                }
                let con_code = arenas.concept(con).get_operator_code();
                let all_shaped =
                    (con_code == op::CCALL || con_code == op::CCAQALL || con_code == op::CCIMPLALL)
                        && !con_neg
                        || con_neg && con_code == op::CCSOME;
                if !all_shaped {
                    continue;
                }
                for op_link in arenas.concept(con).get_operand_list() {
                    if op_link.target == concept && (op_link.negated ^ (con_neg == negated)) {
                        self.stat_propagation_already_in_domain_range_count += 1;
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Port of `createDomainRangePropagations`: push each complex role's
    /// domain down to the LAST role of every entailing chain (as a range
    /// `∀inv(R).dom` propagation) and its range down to the FIRST role (as a
    /// domain `∀R.range` propagation), transitively through re-enqueued
    /// chains.
    pub fn create_domain_range_propagations(&mut self, arenas: &mut OntologyArenas) {
        let mut dom_range_prop_concept_set: HashSet<ConceptId> = HashSet::new();
        let item_counts = arenas.role_count();
        for i in 0..item_counts {
            let role_id = RoleId::new(i);
            if !arenas.role(role_id).is_complex_role() {
                continue;
            }
            let mut inverse_role: Option<RoleId> = None;

            // --- domain concepts → range propagations on chain-last roles ---
            let domain_list: Vec<(ConceptId, bool)> = arenas
                .role(role_id)
                .get_domain_concept_list()
                .iter()
                .map(|l| (l.target, l.negated))
                .collect();
            for (dom_con, dom_con_neg) in domain_list {
                if !dom_con_neg && dom_range_prop_concept_set.contains(&dom_con) {
                    continue;
                }
                self.stat_range_propagation_count += 1;
                if inverse_role.is_none() {
                    inverse_role = self.get_inverse_role(arenas, role_id, true);
                }
                let Some(inv_role) = inverse_role else {
                    continue; // guaranteed by createMissingInverseChainedRoles
                };
                let mut worklist: Vec<RoleSubRoleChainDataItem> = self
                    .role_sub_role_chain_data_hash
                    .get(&role_id)
                    .map(|v| {
                        v.iter()
                            .map(|d| RoleSubRoleChainDataItem::new(*d))
                            .collect()
                    })
                    .unwrap_or_default();
                let mut prop_concept = ConceptId::NONE;

                while let Some(item) = (!worklist.is_empty()).then(|| worklist.remove(0)) {
                    let data = item.chain_data;
                    let inversed_to_original = item.negated ^ data.inverse;
                    let chain = arenas.role_chain(data.role_chain);
                    let (first_sub, last_sub) = if inversed_to_original {
                        let inv = chain.get_inverse_role_chain_linker();
                        let (Some(&f), Some(&l)) = (inv.first(), inv.last()) else {
                            continue;
                        };
                        let (Some(fi), Some(li)) = (
                            self.get_inverse_role(arenas, f, true),
                            self.get_inverse_role(arenas, l, true),
                        ) else {
                            continue;
                        };
                        (fi, li)
                    } else {
                        let fwd = chain.get_role_chain_linker();
                        let (Some(&f), Some(&l)) = (fwd.first(), fwd.last()) else {
                            continue;
                        };
                        (f, l)
                    };

                    let last_supers: Vec<(RoleId, bool)> = arenas
                        .role(last_sub)
                        .indirect_super_roles
                        .iter()
                        .map(|l| (l.target, l.negated))
                        .collect();
                    let first_supers: Vec<(RoleId, bool)> = arenas
                        .role(first_sub)
                        .indirect_super_roles
                        .iter()
                        .map(|l| (l.target, l.negated))
                        .collect();
                    if self.has_propagation_concept(
                        arenas,
                        dom_con_neg,
                        dom_con,
                        inv_role,
                        &last_supers,
                        true,
                    ) || (item.allow_propagated
                        && self.has_propagated_concept(
                            arenas,
                            dom_con_neg,
                            dom_con,
                            &first_supers,
                            true,
                        ))
                    {
                        continue;
                    }
                    if prop_concept == ConceptId::NONE {
                        prop_concept = self.create_transition_concept(
                            arenas,
                            inv_role,
                            TranslationType::Normal,
                        );
                        arenas
                            .concept_mut(prop_concept)
                            .set_operator_code(op::CCALL);
                        self.append_transition_operand(arenas, prop_concept, dom_con, dom_con_neg);
                    }
                    dom_range_prop_concept_set.insert(prop_concept);
                    arenas.role_mut(last_sub).add_range_concept_linker(
                        super::super::model::substrate::NegLink {
                            target: prop_concept,
                            negated: false,
                        },
                    );
                    self.stat_created_domain_propagation_count += 1;
                    if let Some(datas) = self.role_sub_role_chain_data_hash.get(&last_sub) {
                        for d in datas.clone() {
                            worklist.push(RoleSubRoleChainDataItem::new_negated(d, false));
                        }
                    }
                }
            }

            // --- range concepts → domain propagations on chain-first roles ---
            let range_list: Vec<(ConceptId, bool)> = arenas
                .role(role_id)
                .get_range_concept_list()
                .iter()
                .map(|l| (l.target, l.negated))
                .collect();
            for (range_con, range_con_neg) in range_list {
                if !range_con_neg && dom_range_prop_concept_set.contains(&range_con) {
                    continue;
                }
                self.stat_domain_propagation_count += 1;
                let mut worklist: Vec<RoleSubRoleChainDataItem> = self
                    .role_sub_role_chain_data_hash
                    .get(&role_id)
                    .map(|v| {
                        v.iter()
                            .map(|d| RoleSubRoleChainDataItem::new(*d))
                            .collect()
                    })
                    .unwrap_or_default();
                let mut prop_concept = ConceptId::NONE;

                while let Some(item) = (!worklist.is_empty()).then(|| worklist.remove(0)) {
                    let data = item.chain_data;
                    let inversed_to_original = item.negated ^ data.inverse;
                    let chain = arenas.role_chain(data.role_chain);
                    let (first_sub, last_sub) = if inversed_to_original {
                        let inv = chain.get_inverse_role_chain_linker();
                        let (Some(&f), Some(&l)) = (inv.first(), inv.last()) else {
                            continue;
                        };
                        let (Some(fi), Some(li)) = (
                            self.get_inverse_role(arenas, f, true),
                            self.get_inverse_role(arenas, l, true),
                        ) else {
                            continue;
                        };
                        (fi, li)
                    } else {
                        let fwd = chain.get_role_chain_linker();
                        let (Some(&f), Some(&l)) = (fwd.first(), fwd.last()) else {
                            continue;
                        };
                        (f, l)
                    };

                    let first_supers: Vec<(RoleId, bool)> = arenas
                        .role(first_sub)
                        .indirect_super_roles
                        .iter()
                        .map(|l| (l.target, l.negated))
                        .collect();
                    let last_supers: Vec<(RoleId, bool)> = arenas
                        .role(last_sub)
                        .indirect_super_roles
                        .iter()
                        .map(|l| (l.target, l.negated))
                        .collect();
                    if self.has_propagation_concept(
                        arenas,
                        range_con_neg,
                        range_con,
                        role_id,
                        &first_supers,
                        false,
                    ) || (item.allow_propagated
                        && self.has_propagated_concept(
                            arenas,
                            range_con_neg,
                            range_con,
                            &last_supers,
                            false,
                        ))
                    {
                        continue;
                    }
                    if prop_concept == ConceptId::NONE {
                        prop_concept = self.create_transition_concept(
                            arenas,
                            role_id,
                            TranslationType::Normal,
                        );
                        arenas
                            .concept_mut(prop_concept)
                            .set_operator_code(op::CCALL);
                        self.append_transition_operand(
                            arenas,
                            prop_concept,
                            range_con,
                            range_con_neg,
                        );
                    }
                    dom_range_prop_concept_set.insert(prop_concept);
                    arenas.role_mut(first_sub).add_domain_concept_linker(
                        super::super::model::substrate::NegLink {
                            target: prop_concept,
                            negated: false,
                        },
                    );
                    self.stat_created_range_propagation_count += 1;
                    if let Some(datas) = self.role_sub_role_chain_data_hash.get(&first_sub) {
                        for d in datas.clone() {
                            worklist.push(RoleSubRoleChainDataItem::new_negated(d, false));
                        }
                    }
                }
            }
        }
    }

    // ---------------------------------------------------------------------
    // the driver
    // ---------------------------------------------------------------------

    /// Port of `preprocess(ontology, context)`: run every pass in Konclude's
    /// order. The `isComplexRoleUsed` build flag becomes a scan (the arenas
    /// carry no build-construct flags).
    pub fn preprocess(&mut self, arenas: &mut OntologyArenas) {
        let complex_used =
            (0..arenas.role_count()).any(|i| arenas.role(RoleId::new(i)).is_complex_role());
        if !complex_used {
            return;
        }
        self.begin(arenas);
        self.collect_sub_role_chains(arenas);
        self.create_missing_inverse_chained_roles(arenas);
        self.create_inverse_role_chain_linkers(arenas);
        self.transform_value_restrictions(arenas);
        self.create_domain_range_propagations(arenas);
        self.create_recursive_traversal_data(arenas);
        self.transform_forall_propagations(arenas);
    }

    /// Port of `continuePreprocessing` (incremental re-entry after new
    /// concepts were added).
    pub fn continue_preprocessing(&mut self, arenas: &mut OntologyArenas) {
        self.next_concept_tag = (0..arenas.concept_count())
            .map(|i| arenas.concept(ConceptId::new(i)).get_concept_tag())
            .max()
            .unwrap_or(-1)
            + 1;
        self.transform_value_restrictions(arenas);
        self.transform_forall_propagations(arenas);
    }
}

impl Default for RoleChainAutomataTransformationPreProcess {
    fn default() -> Self {
        RoleChainAutomataTransformationPreProcess::new()
    }
}
