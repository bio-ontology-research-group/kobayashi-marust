//! `process::blocking_follow` - port of `CBlockingFollowSet`.
//!
//! Konclude source:
//! `Source/Reasoner/Kernel/Process/CBlockingFollowSet.{h,cpp}`.
//! The C++ type derives from `CPROCESSSET<cint64>` and
//! `CBlockingFollowUpdateTag`; it only adds copy/initialisation over the process
//! tagger's current blocking-follow tag.

#![allow(dead_code)]

use std::collections::HashSet;

use super::super::model::substrate::{Cint64, Id};

/// `CBlockingFollowSet*` -> `BlockingFollowSetId`.
pub type BlockingFollowSetId = Id<BlockingFollowSet>;

/// Port of `CBlockingFollowUpdateTag`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct BlockingFollowUpdateTag {
    blocking_follow_tag: Cint64,
}

impl BlockingFollowUpdateTag {
    /// Port of `CBlockingFollowUpdateTag::initBlockingFollowTag`.
    pub fn init_blocking_follow_tag(&mut self, tag: Cint64) -> &mut Self {
        self.blocking_follow_tag = tag;
        self
    }

    /// Port of `CBlockingFollowUpdateTag::getBlockingFollowTag`.
    pub fn get_blocking_follow_tag(&self) -> Cint64 {
        self.blocking_follow_tag
    }
}

/// Port of `CBlockingFollowSet` (`: public CPROCESSSET<cint64>`).
#[derive(Clone, Debug, Default)]
pub struct BlockingFollowSet {
    follow_set: HashSet<Cint64>,
    update_tag: BlockingFollowUpdateTag,
}

impl BlockingFollowSet {
    /// Port of `CBlockingFollowSet::CBlockingFollowSet`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CBlockingFollowSet::initBlockingFollowSet`.
    pub fn init_blocking_follow_set(
        &mut self,
        sig_block_follow_set: Option<&BlockingFollowSet>,
        current_blocking_follow_tag: Cint64,
    ) -> &mut Self {
        if let Some(sig_block_follow_set) = sig_block_follow_set {
            self.follow_set = sig_block_follow_set.follow_set.clone();
            self.update_tag
                .init_blocking_follow_tag(sig_block_follow_set.get_blocking_follow_tag());
        } else {
            self.follow_set.clear();
            self.update_tag
                .init_blocking_follow_tag(current_blocking_follow_tag);
        }
        self
    }

    /// Port of `CPROCESSSET<cint64>::insert`.
    pub fn insert(&mut self, individual_node_id: Cint64) -> bool {
        self.follow_set.insert(individual_node_id)
    }

    /// Port of `CPROCESSSET<cint64>::remove`.
    pub fn remove(&mut self, individual_node_id: Cint64) -> bool {
        self.follow_set.remove(&individual_node_id)
    }

    /// Port of `CPROCESSSET<cint64>::empty`.
    pub fn is_empty(&self) -> bool {
        self.follow_set.is_empty()
    }

    /// Port of `CPROCESSSET<cint64>::contains`.
    pub fn contains(&self, individual_node_id: Cint64) -> bool {
        self.follow_set.contains(&individual_node_id)
    }

    /// Snapshot equivalent of `constBegin()/constEnd()`.
    pub fn iter_snapshot(&self) -> Vec<Cint64> {
        self.follow_set.iter().copied().collect()
    }

    /// Port of inherited `getBlockingFollowTag`.
    pub fn get_blocking_follow_tag(&self) -> Cint64 {
        self.update_tag.get_blocking_follow_tag()
    }
}
