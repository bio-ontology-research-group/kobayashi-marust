//! `process::analized_concept_expansion` — port of
//! `CIndividualNodeAnalizedConceptExpansionData` and
//! `CAnalizedConceptExpansionLinker`.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id};
use super::context::ProcessContext;
use super::ConDescId;

/// `CAnalizedConceptExpansionLinker*` → `AnalizedConceptExpansionLinkerId`.
pub type AnalizedConceptExpansionLinkerId = Id<AnalizedConceptExpansionLinker>;
/// `CIndividualNodeAnalizedConceptExpansionData*` →
/// `IndividualNodeAnalizedConceptExpansionDataId`.
pub type IndividualNodeAnalizedConceptExpansionDataId =
    Id<IndividualNodeAnalizedConceptExpansionData>;

/// Port of `CAnalizedConceptExpansionLinker`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnalizedConceptExpansionLinker {
    next: AnalizedConceptExpansionLinkerId,
    dependend_con_des_linker: Vec<ConDescId>,
    con_des: ConDescId,
}

impl Default for AnalizedConceptExpansionLinker {
    fn default() -> Self {
        Self::new()
    }
}

impl AnalizedConceptExpansionLinker {
    /// Port of `CAnalizedConceptExpansionLinker::CAnalizedConceptExpansionLinker`.
    pub fn new() -> Self {
        Self {
            next: AnalizedConceptExpansionLinkerId::NONE,
            dependend_con_des_linker: Vec::new(),
            con_des: ConDescId::NONE,
        }
    }

    /// Port of `initAnalizedConceptExpansion`.
    pub fn init_analized_concept_expansion(
        &mut self,
        dependend_con_des_linker: Vec<ConDescId>,
        con_des: ConDescId,
    ) -> &mut Self {
        self.dependend_con_des_linker = dependend_con_des_linker;
        self.con_des = con_des;
        self
    }

    /// Port of `addDependendConceptDescriptorLinker`.
    pub fn add_dependend_concept_descriptor_linker(
        &mut self,
        mut dependend_con_des_linker: Vec<ConDescId>,
    ) -> &mut Self {
        if !dependend_con_des_linker.is_empty() {
            dependend_con_des_linker.extend(self.dependend_con_des_linker.iter().copied());
            self.dependend_con_des_linker = dependend_con_des_linker;
        }
        self
    }

    /// Port of `setConceptDescriptor`.
    pub fn set_concept_descriptor(&mut self, con_des: ConDescId) -> &mut Self {
        self.con_des = con_des;
        self
    }

    /// Port of `getConceptDescriptor`.
    pub fn get_concept_descriptor(&self) -> ConDescId {
        self.con_des
    }

    /// Port of `getDependendConceptDescriptorLinker`.
    pub fn get_dependend_concept_descriptor_linker(&self) -> &[ConDescId] {
        &self.dependend_con_des_linker
    }

    /// Port of `hasMultipleDependencies`.
    pub fn has_multiple_dependencies(&self) -> bool {
        self.dependend_con_des_linker.len() > 1
    }

    /// Port-facing equivalent of `CLinkerBase::getNext`.
    pub fn get_next(&self) -> AnalizedConceptExpansionLinkerId {
        self.next
    }

    /// Port-facing equivalent of `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: AnalizedConceptExpansionLinkerId) -> &mut Self {
        self.next = next;
        self
    }

    /// Port-facing equivalent of `CLinkerBase::clearNext`.
    pub fn clear_next(&mut self) -> &mut Self {
        self.next = AnalizedConceptExpansionLinkerId::NONE;
        self
    }

    /// Port-facing equivalent of `CLinkerBase::hasNext`.
    pub fn has_next(&self) -> bool {
        self.next.is_some()
    }
}

/// Port of `CIndividualNodeAnalizedConceptExpansionData`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndividualNodeAnalizedConceptExpansionData {
    rev_ana_con_exp_linker: AnalizedConceptExpansionLinkerId,
    last_con_des: ConDescId,
    last_concept_signature: Cint64,
    last_concept_count: Cint64,
    min_valid_concept_count_limit: Cint64,
    exp_count: Cint64,
    invalid_blocker: bool,
    non_det_expansion_linker: Vec<ConDescId>,
}

impl Default for IndividualNodeAnalizedConceptExpansionData {
    fn default() -> Self {
        Self::new()
    }
}

impl IndividualNodeAnalizedConceptExpansionData {
    /// Port of `CIndividualNodeAnalizedConceptExpansionData::CIndividualNodeAnalizedConceptExpansionData`.
    pub fn new() -> Self {
        Self {
            rev_ana_con_exp_linker: AnalizedConceptExpansionLinkerId::NONE,
            last_con_des: ConDescId::NONE,
            last_concept_signature: 0,
            last_concept_count: 0,
            min_valid_concept_count_limit: 0,
            exp_count: 0,
            invalid_blocker: false,
            non_det_expansion_linker: Vec::new(),
        }
    }

    /// Port of `initBlockingExplorationData`.
    pub fn init_blocking_exploration_data(&mut self, prev_data: Option<&Self>) -> &mut Self {
        if let Some(prev_data) = prev_data {
            self.last_concept_count = prev_data.last_concept_count;
            self.last_con_des = prev_data.last_con_des;
            self.rev_ana_con_exp_linker = prev_data.rev_ana_con_exp_linker;
            self.min_valid_concept_count_limit = prev_data.min_valid_concept_count_limit;
            self.exp_count = prev_data.exp_count;
            self.last_concept_signature = prev_data.last_concept_signature;
            self.invalid_blocker = prev_data.invalid_blocker;
            self.non_det_expansion_linker = prev_data.non_det_expansion_linker.clone();
        } else {
            self.last_concept_count = 0;
            self.last_con_des = ConDescId::NONE;
            self.rev_ana_con_exp_linker = AnalizedConceptExpansionLinkerId::NONE;
            self.exp_count = 0;
            self.min_valid_concept_count_limit = 0;
            self.last_concept_signature = 0;
            self.invalid_blocker = false;
            self.non_det_expansion_linker.clear();
        }
        self
    }

    /// Port of `getReverseAnalizedConceptExpansionLinker`.
    pub fn get_reverse_analized_concept_expansion_linker(
        &self,
    ) -> AnalizedConceptExpansionLinkerId {
        self.rev_ana_con_exp_linker
    }

    /// Port of `getLastConceptDescriptor`.
    pub fn get_last_concept_descriptor(&self) -> ConDescId {
        self.last_con_des
    }

    /// Port of `getLastConceptSignature`.
    pub fn get_last_concept_signature(&self) -> Cint64 {
        self.last_concept_signature
    }

    /// Port of `getLastConceptCount`.
    pub fn get_last_concept_count(&self) -> Cint64 {
        self.last_concept_count
    }

    /// Port of `getExpansionConceptCount`.
    pub fn get_expansion_concept_count(&self) -> Cint64 {
        self.exp_count
    }

    /// Port of `getMinimalValidConceptCountLimit`.
    pub fn get_minimal_valid_concept_count_limit(&self) -> Cint64 {
        self.min_valid_concept_count_limit
    }

    /// Port of `isInvalidBlocker`.
    pub fn is_invalid_blocker(&self) -> bool {
        self.invalid_blocker
    }

    /// Port of `setLastConceptDescriptor`.
    pub fn set_last_concept_descriptor(&mut self, con_des: ConDescId) -> &mut Self {
        self.last_con_des = con_des;
        self
    }

    /// Port of `setLastConceptSignature`.
    pub fn set_last_concept_signature(&mut self, signature: Cint64) -> &mut Self {
        self.last_concept_signature = signature;
        self
    }

    /// Port of `setLastConceptCount`.
    pub fn set_last_concept_count(&mut self, con_count: Cint64) -> &mut Self {
        self.last_concept_count = con_count;
        self
    }

    /// Port of `setMinimalValidConceptCountLimit`.
    pub fn set_minimal_valid_concept_count_limit(&mut self, con_count: Cint64) -> &mut Self {
        self.min_valid_concept_count_limit = con_count;
        self
    }

    /// Port of `setInvalidBlocker`.
    pub fn set_invalid_blocker(&mut self, invalid: bool) -> &mut Self {
        self.invalid_blocker = invalid;
        self
    }

    /// Port of `addAnalizedConceptExpansionLinker`.
    pub fn add_analized_concept_expansion_linker(
        &mut self,
        process_context: &mut ProcessContext,
        linker: AnalizedConceptExpansionLinkerId,
    ) -> &mut Self {
        self.exp_count += process_context.analized_con_exp_linker_count(linker);
        if self.rev_ana_con_exp_linker.is_some() {
            self.rev_ana_con_exp_linker =
                process_context.analized_con_exp_linker_append(linker, self.rev_ana_con_exp_linker);
        } else {
            self.rev_ana_con_exp_linker = linker;
        }
        self
    }

    /// Port of `getAnalysedNonDeterministicConceptExpansionLinker`.
    pub fn get_analysed_non_deterministic_concept_expansion_linker(&self) -> &[ConDescId] {
        &self.non_det_expansion_linker
    }

    /// Port of `setAnalysedNonDeterministicConceptExpansionLinker`.
    pub fn set_analysed_non_deterministic_concept_expansion_linker(
        &mut self,
        linker: Vec<ConDescId>,
    ) -> &mut Self {
        self.non_det_expansion_linker = linker;
        self
    }

    /// Port of `addAnalysedNonDeterministicConceptExpansionLinker`.
    pub fn add_analysed_non_deterministic_concept_expansion_linker(
        &mut self,
        mut linker: Vec<ConDescId>,
    ) -> &mut Self {
        if !linker.is_empty() {
            linker.extend(self.non_det_expansion_linker.iter().copied());
            self.non_det_expansion_linker = linker;
        }
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn init_blocking_exploration_data_copies_previous_or_nulls() {
        let mut prev = IndividualNodeAnalizedConceptExpansionData::new();
        let rev_linker = AnalizedConceptExpansionLinkerId::new(3);
        let last_con = ConDescId::new(11);
        prev.rev_ana_con_exp_linker = rev_linker;
        prev.set_last_concept_descriptor(last_con)
            .set_last_concept_count(7)
            .set_last_concept_signature(13)
            .set_minimal_valid_concept_count_limit(5)
            .set_invalid_blocker(true)
            .set_analysed_non_deterministic_concept_expansion_linker(vec![ConDescId::new(17)]);
        prev.exp_count = 19;

        let mut data = IndividualNodeAnalizedConceptExpansionData::new();
        data.init_blocking_exploration_data(Some(&prev));
        assert_eq!(
            data.get_reverse_analized_concept_expansion_linker(),
            rev_linker
        );
        assert_eq!(data.get_last_concept_descriptor(), last_con);
        assert_eq!(data.get_last_concept_count(), 7);
        assert_eq!(data.get_last_concept_signature(), 13);
        assert_eq!(data.get_minimal_valid_concept_count_limit(), 5);
        assert_eq!(data.get_expansion_concept_count(), 19);
        assert!(data.is_invalid_blocker());
        assert_eq!(
            data.get_analysed_non_deterministic_concept_expansion_linker(),
            &[ConDescId::new(17)]
        );

        data.init_blocking_exploration_data(None);
        assert!(data
            .get_reverse_analized_concept_expansion_linker()
            .is_none());
        assert!(data.get_last_concept_descriptor().is_none());
        assert_eq!(data.get_last_concept_count(), 0);
        assert_eq!(data.get_expansion_concept_count(), 0);
        assert!(!data.is_invalid_blocker());
        assert!(data
            .get_analysed_non_deterministic_concept_expansion_linker()
            .is_empty());
    }

    #[test]
    fn add_analized_concept_expansion_linker_prepends_chain_and_counts_it() {
        let mut ctx = ProcessContext::new();
        let mut first = AnalizedConceptExpansionLinker::new();
        first.init_analized_concept_expansion(vec![ConDescId::new(1)], ConDescId::new(10));
        let first = ctx.alloc_analized_con_exp_linker(first);
        let mut second = AnalizedConceptExpansionLinker::new();
        second.init_analized_concept_expansion(vec![ConDescId::new(2)], ConDescId::new(20));
        let second = ctx.alloc_analized_con_exp_linker(second);
        ctx.analized_con_exp_linker_mut(first).set_next(second);

        let old = ctx.alloc_analized_con_exp_linker(AnalizedConceptExpansionLinker::new());
        let mut data = IndividualNodeAnalizedConceptExpansionData::new();
        data.add_analized_concept_expansion_linker(&mut ctx, old);
        data.add_analized_concept_expansion_linker(&mut ctx, first);

        assert_eq!(data.get_expansion_concept_count(), 3);
        assert_eq!(data.get_reverse_analized_concept_expansion_linker(), first);
        assert_eq!(ctx.analized_con_exp_linker(first).get_next(), second);
        assert_eq!(ctx.analized_con_exp_linker(second).get_next(), old);
    }
}
