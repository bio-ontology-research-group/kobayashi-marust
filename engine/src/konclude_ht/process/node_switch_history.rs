//! `process::node_switch_history` — port of `CNodeSwitchHistory`.
//!
//! Konclude keeps a linked/skip structure of switch-history data allocated from
//! the process memory pool. The skip levels only accelerate minimum queries; the
//! observable state is the newest-first list of switch entries.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::node::IndividualProcessNode;

pub type NodeSwitchHistoryId = Id<NodeSwitchHistory>;

/// Port of `CNodeSwitchHistory::CNodeSwitchHistoryLinkData`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NodeSwitchHistoryLinkData {
    pub node_switch_tag: Cint64,
    pub node_ancestor_depth: Cint64,
    pub node_individual_id: Cint64,
}

/// Port of `CNodeSwitchHistory`.
#[derive(Clone, Debug)]
pub struct NodeSwitchHistory {
    pub context: Cint64,
    pub leveling_count: Cint64,
    pub entries: Vec<NodeSwitchHistoryLinkData>,
}

impl Default for NodeSwitchHistory {
    fn default() -> Self {
        Self::new(INVALID)
    }
}

impl NodeSwitchHistory {
    /// Port of `CNodeSwitchHistory::CNodeSwitchHistory`.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            context: process_context,
            leveling_count: 5,
            entries: Vec::new(),
        }
    }

    /// Port of `CNodeSwitchHistory::initSwitchHistory`.
    pub fn init_switch_history(
        &mut self,
        prev_switch_history: Option<&NodeSwitchHistory>,
    ) -> &mut Self {
        if let Some(prev) = prev_switch_history {
            // KONCLUDE-PORT-NOTE[ownership]: C++ copies the head pointer into the
            // previous memory-pool chain. Rust clones the immutable raw entries
            // into this arena object; later updates mutate only this history.
            self.entries = prev.entries.clone();
            self.leveling_count = prev.leveling_count;
        } else {
            self.entries.clear();
            self.leveling_count = 5;
        }
        self
    }

    /// Port of `CNodeSwitchHistory::addIndividualProcessNodeSwitch(CIndividualProcessNode*, cint64)`.
    pub fn add_individual_process_node_switch_for_node(
        &mut self,
        individual: &IndividualProcessNode,
        indi_switch_tag: Cint64,
    ) -> &mut Self {
        self.add_individual_process_node_switch(
            individual.individual_ancestor_depth(),
            individual.individual_node_id(),
            indi_switch_tag,
        )
    }

    /// Port of `CNodeSwitchHistory::addIndividualProcessNodeSwitch(cint64, cint64, cint64)`.
    pub fn add_individual_process_node_switch(
        &mut self,
        indi_anc_depth: Cint64,
        indi_id: Cint64,
        indi_switch_tag: Cint64,
    ) -> &mut Self {
        // KONCLUDE-PORT-NOTE[memory-pool]: the C++ object stores `mNextData`,
        // `mUpData`, and periodic upper aggregate nodes. Here the raw chain is a
        // newest-first vector; `updateUpperData` is not represented because it is
        // a query accelerator and the query methods fold over the raw entries.
        self.entries.insert(
            0,
            NodeSwitchHistoryLinkData {
                node_switch_tag: indi_switch_tag,
                node_ancestor_depth: indi_anc_depth,
                node_individual_id: indi_id,
            },
        );
        self
    }

    /// Port of `CNodeSwitchHistory::updateLastIndividualProcessNodeSwitch`.
    pub fn update_last_individual_process_node_switch(
        &mut self,
        indi_anc_depth: Cint64,
        indi_id: Cint64,
    ) -> &mut Self {
        if let Some(data) = self.entries.first_mut() {
            data.node_ancestor_depth = data.node_ancestor_depth.min(indi_anc_depth);
            data.node_individual_id = data.node_individual_id.min(indi_id);
        }
        self
    }

    /// Port of `CNodeSwitchHistory::getMinIndividualAncestorDepth`.
    pub fn get_min_individual_ancestor_depth(&self, indi_switch_tag: Cint64) -> Cint64 {
        let (_, min_anc_depth, _) =
            self.get_min_individual_ancestor_depth_and_node_id(indi_switch_tag);
        min_anc_depth
    }

    /// Port of `CNodeSwitchHistory::getMinIndividualNodeID`.
    pub fn get_min_individual_node_id(&self, indi_switch_tag: Cint64) -> Cint64 {
        let (_, _, min_indi_id) =
            self.get_min_individual_ancestor_depth_and_node_id(indi_switch_tag);
        min_indi_id
    }

    /// Port of `CNodeSwitchHistory::getMinIndividualAncestorDepthAndNodeID`.
    pub fn get_min_individual_ancestor_depth_and_node_id(
        &self,
        indi_switch_tag: Cint64,
    ) -> (bool, Cint64, Cint64) {
        let mut min_anc_depth = Cint64::MAX;
        let mut min_indi_id = Cint64::MAX;

        for data in &self.entries {
            if data.node_switch_tag == indi_switch_tag {
                return (true, min_anc_depth, min_indi_id);
            }
            if data.node_switch_tag < indi_switch_tag {
                break;
            }
            min_anc_depth = min_anc_depth.min(data.node_ancestor_depth);
            min_indi_id = min_indi_id.min(data.node_individual_id);
        }

        (true, min_anc_depth, min_indi_id)
    }
}
