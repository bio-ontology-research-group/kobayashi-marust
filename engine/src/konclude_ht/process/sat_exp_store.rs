//! Per-node write cursor for Konclude's signature satisfiable-expander cache.
//!
//! Direct port of
//! `CIndividualNodeSatisfiableExpandingCacheStoringData`. The cursor records
//! the last label head/signature written for one completion-graph node, so a
//! later label extension can publish the exact `previous signature -> new
//! signature` expansion edge used by `CSatisfiableExpanderCacheHandler`.

use super::super::model::substrate::{Cint64, Id};
use super::ConDescId;

pub type IndividualNodeSatisfiableExpandingCacheStoringDataId =
    Id<IndividualNodeSatisfiableExpandingCacheStoringData>;

#[derive(Clone, Debug)]
pub struct IndividualNodeSatisfiableExpandingCacheStoringData {
    node_or_successor_branched: bool,
    previous_cached: bool,
    last_cached_signature: Cint64,
    last_cached_concept_descriptor: ConDescId,
    caching_error: bool,
    minimal_individual_node_branching_tag: Cint64,
    previous_satisfiable_cached: bool,
}

impl Default for IndividualNodeSatisfiableExpandingCacheStoringData {
    fn default() -> Self {
        Self {
            node_or_successor_branched: false,
            previous_cached: false,
            last_cached_signature: 0,
            last_cached_concept_descriptor: ConDescId::NONE,
            caching_error: false,
            minimal_individual_node_branching_tag: -1,
            previous_satisfiable_cached: false,
        }
    }
}

impl IndividualNodeSatisfiableExpandingCacheStoringData {
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initSatisfiableExpandingCacheRetrievalData`.
    pub fn init_from_previous(&mut self, previous: Option<&Self>) -> &mut Self {
        if let Some(previous) = previous {
            *self = previous.clone();
        } else {
            *self = Self::default();
        }
        self
    }

    pub fn has_individual_node_or_successor_branched_concept(&self) -> bool {
        self.node_or_successor_branched
    }

    pub fn set_individual_node_or_successor_branched_concept(
        &mut self,
        branched: bool,
    ) -> &mut Self {
        self.node_or_successor_branched = branched;
        self
    }

    pub fn has_previous_cached(&self) -> bool {
        self.previous_cached
    }

    pub fn set_previous_cached(&mut self, cached: bool) -> &mut Self {
        self.previous_cached = cached;
        self
    }

    pub fn last_cached_signature(&self) -> Cint64 {
        self.last_cached_signature
    }

    pub fn set_last_cached_signature(&mut self, signature: Cint64) -> &mut Self {
        self.last_cached_signature = signature;
        self
    }

    pub fn last_cached_concept_descriptor(&self) -> ConDescId {
        self.last_cached_concept_descriptor
    }

    pub fn set_last_cached_concept_descriptor(&mut self, descriptor: ConDescId) -> &mut Self {
        self.last_cached_concept_descriptor = descriptor;
        self
    }

    pub fn minimal_individual_node_branching_tag(&self) -> Cint64 {
        self.minimal_individual_node_branching_tag
    }

    pub fn set_minimal_individual_node_branching_tag(&mut self, tag: Cint64) -> &mut Self {
        self.minimal_individual_node_branching_tag = tag;
        self
    }

    pub fn has_caching_error(&self) -> bool {
        self.caching_error
    }

    pub fn set_caching_error(&mut self, error: bool) -> &mut Self {
        self.caching_error = error;
        self
    }

    pub fn has_previous_satisfiable_cached(&self) -> bool {
        self.previous_satisfiable_cached
    }

    pub fn set_previous_satisfiable_cached(&mut self, cached: bool) -> &mut Self {
        self.previous_satisfiable_cached = cached;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn storing_cursor_defaults_and_localizes_exact_state() {
        let mut previous = IndividualNodeSatisfiableExpandingCacheStoringData::new();
        previous
            .set_individual_node_or_successor_branched_concept(true)
            .set_previous_cached(true)
            .set_last_cached_signature(41)
            .set_last_cached_concept_descriptor(ConDescId::new(7))
            .set_minimal_individual_node_branching_tag(13)
            .set_caching_error(true)
            .set_previous_satisfiable_cached(true);

        let mut localized = IndividualNodeSatisfiableExpandingCacheStoringData::new();
        localized.init_from_previous(Some(&previous));

        assert!(localized.has_individual_node_or_successor_branched_concept());
        assert!(localized.has_previous_cached());
        assert_eq!(localized.last_cached_signature(), 41);
        assert_eq!(
            localized.last_cached_concept_descriptor(),
            ConDescId::new(7)
        );
        assert_eq!(localized.minimal_individual_node_branching_tag(), 13);
        assert!(localized.has_caching_error());
        assert!(localized.has_previous_satisfiable_cached());

        localized.init_from_previous(None);
        assert!(!localized.has_individual_node_or_successor_branched_concept());
        assert!(!localized.has_previous_cached());
        assert_eq!(localized.last_cached_signature(), 0);
        assert!(localized.last_cached_concept_descriptor().is_none());
        assert_eq!(localized.minimal_individual_node_branching_tag(), -1);
        assert!(!localized.has_caching_error());
        assert!(!localized.has_previous_satisfiable_cached());
    }
}
