//! `process::unsat_retrieval` — unsatisfiable-cache retrieval data attached to
//! individual process nodes.
//!
//! Ports `CIndividualNodeUnsatisfiableOccurenceCacheRetrievalData`.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id};
use super::ConDescId;

/// `CIndividualNodeUnsatisfiableOccurenceCacheRetrievalData*`.
pub type IndividualNodeUnsatisfiableOccurenceCacheRetrievalDataId =
    Id<IndividualNodeUnsatisfiableOccurenceCacheRetrievalData>;

/// Port of `CIndividualNodeUnsatisfiableOccurenceCacheRetrievalData`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct IndividualNodeUnsatisfiableOccurenceCacheRetrievalData {
    /// `mLastRetCachingTag`.
    pub last_ret_caching_tag: Cint64,
    /// `mLastRetConceptDes`.
    pub last_ret_concept_des: ConDescId,
}

impl Default for IndividualNodeUnsatisfiableOccurenceCacheRetrievalData {
    fn default() -> Self {
        Self {
            last_ret_caching_tag: 0,
            last_ret_concept_des: ConDescId::NONE,
        }
    }
}

impl IndividualNodeUnsatisfiableOccurenceCacheRetrievalData {
    /// Port of `CIndividualNodeUnsatisfiableOccurenceCacheRetrievalData::CIndividualNodeUnsatisfiableOccurenceCacheRetrievalData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initUnsatisfiableOccurenceCacheRetrievalData`.
    pub fn init_unsatisfiable_occurence_cache_retrieval_data(
        &mut self,
        prev_data: Option<&IndividualNodeUnsatisfiableOccurenceCacheRetrievalData>,
    ) -> &mut Self {
        if let Some(prev) = prev_data {
            self.last_ret_caching_tag = prev.last_ret_caching_tag;
            self.last_ret_concept_des = prev.last_ret_concept_des;
        } else {
            self.last_ret_caching_tag = 0;
            self.last_ret_concept_des = ConDescId::NONE;
        }
        self
    }

    /// Port of `getLastRetrievalCachingTag`.
    pub fn get_last_retrieval_caching_tag(&self) -> Cint64 {
        self.last_ret_caching_tag
    }

    /// Port of `setLastRetrievalCachingTag`.
    pub fn set_last_retrieval_caching_tag(&mut self, tag: Cint64) -> &mut Self {
        self.last_ret_caching_tag = tag;
        self
    }

    /// Port of `getLastRetrievalConceptDescriptor`.
    pub fn get_last_retrieval_concept_descriptor(&self) -> ConDescId {
        self.last_ret_concept_des
    }

    /// Port of `setLastRetrievalConceptDescriptor`.
    pub fn set_last_retrieval_concept_descriptor(&mut self, con_des: ConDescId) -> &mut Self {
        self.last_ret_concept_des = con_des;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::super::context::ProcessContext;
    use super::super::descriptor::ConceptDescriptor;
    use super::super::node::IndividualProcessNode;
    use super::*;

    #[test]
    fn unsat_occurrence_retrieval_data_init_and_accessors_match_konclude() {
        let mut prev = IndividualNodeUnsatisfiableOccurenceCacheRetrievalData::new();
        let con_des = ConDescId::new(7);
        prev.set_last_retrieval_caching_tag(13)
            .set_last_retrieval_concept_descriptor(con_des);

        let mut copied = IndividualNodeUnsatisfiableOccurenceCacheRetrievalData::new();
        copied.init_unsatisfiable_occurence_cache_retrieval_data(Some(&prev));
        assert_eq!(copied.get_last_retrieval_caching_tag(), 13);
        assert_eq!(copied.get_last_retrieval_concept_descriptor(), con_des);

        copied.init_unsatisfiable_occurence_cache_retrieval_data(None);
        assert_eq!(copied.get_last_retrieval_caching_tag(), 0);
        assert_eq!(
            copied.get_last_retrieval_concept_descriptor(),
            ConDescId::NONE
        );
    }

    #[test]
    fn node_unsat_retrieval_data_points_to_real_process_context_arena() {
        let mut ctx = ProcessContext::new();
        let con_des = ctx.alloc_con_desc(ConceptDescriptor::new());
        let mut data = IndividualNodeUnsatisfiableOccurenceCacheRetrievalData::new();
        data.set_last_retrieval_caching_tag(21)
            .set_last_retrieval_concept_descriptor(con_des);
        let data_id = ctx.alloc_unsat_cache_ret_data(data);

        let node = ctx.alloc_node(IndividualProcessNode::new(Id::NONE));
        ctx.node_mut(node)
            .set_individual_unsatisfiable_cache_retrieval_data(data_id);

        assert_eq!(
            ctx.node(node)
                .individual_unsatisfiable_cache_retrieval_data(false),
            data_id
        );
        assert_eq!(
            ctx.unsat_cache_ret_data(data_id)
                .get_last_retrieval_caching_tag(),
            21
        );
        assert_eq!(
            ctx.unsat_cache_ret_data(data_id)
                .get_last_retrieval_concept_descriptor(),
            con_des
        );
    }
}
