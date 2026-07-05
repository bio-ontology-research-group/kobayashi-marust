//! `process::branching_tree` — port of `CBranchingTree`.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::{BranchNodeId, DependencyId};

pub type BranchingTreeId = Id<BranchingTree>;

/// Port of `CBranchingTree`.
#[derive(Clone, Debug)]
pub struct BranchingTree {
    pub process_context: Cint64,
    pub root_node: BranchNodeId,
    pub curr_node: BranchNodeId,
    pub prev_curr_node: BranchNodeId,
    pub base_dep_node: DependencyId,
}

impl Default for BranchingTree {
    fn default() -> Self {
        Self::new(INVALID)
    }
}

impl BranchingTree {
    /// Port of `CBranchingTree::CBranchingTree`.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            process_context,
            root_node: BranchNodeId::NONE,
            curr_node: BranchNodeId::NONE,
            prev_curr_node: BranchNodeId::NONE,
            base_dep_node: DependencyId::NONE,
        }
    }

    /// Port of `CBranchingTree::initBranchingTree`.
    pub fn init_branching_tree(&mut self, tree: Option<&BranchingTree>) -> &mut Self {
        self.root_node = BranchNodeId::NONE;
        self.curr_node = BranchNodeId::NONE;
        self.prev_curr_node = BranchNodeId::NONE;
        self.base_dep_node = DependencyId::NONE;
        if let Some(tree) = tree {
            self.prev_curr_node = tree.prev_curr_node;
            self.root_node = tree.root_node;
            self.base_dep_node = tree.base_dep_node;
        }
        self
    }

    /// Port of `CBranchingTree::getBranchTreeNode`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: allocation and branch-node initialization
    /// are implemented as `ProcessContext` helpers because this tree is itself
    /// arena-owned by the same context that allocates `CBranchTreeNode`s.
    pub fn get_branch_tree_node(&self) -> BranchNodeId {
        self.curr_node
    }

    /// Port of `CBranchingTree::getBaseDependencyNode`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: lazy allocation lives on `ProcessContext`
    /// for the same arena-borrow reason as `getBranchTreeNode`.
    pub fn get_base_dependency_node(&self) -> DependencyId {
        self.base_dep_node
    }
}
