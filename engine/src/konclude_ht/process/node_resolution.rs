//! `process::node_resolution` — the node-resolution keystone.
//!
//! Ports Konclude's individual-node resolution protocol: the
//! `getUpToDateIndividual` / `getLocalizedIndividual` / `getSuccessorIndividual` /
//! `getAncestorIndividual` / `getAvailableUpToDateIndividual` family from
//! `Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`
//! (`.cpp` 22477–22510, 26412–26488), plus the two small Process-layer types they
//! stand on: the per-individual node vector (`CIndividualProcessNodeVector`,
//! `Process/CIndividualProcessNodeVector.{h,cpp}`) and the process tagger
//! (`CProcessTagger`, `Process/CProcessTagger.{h,cpp}`).
//!
//! These five resolvers are the keystone dozens of deferred completion bodies
//! need: every rule that walks a successor edge, follows an ancestor, or touches
//! a (possibly relocalised / merged) node first routes it through one of these to
//! get the *current* node in *this* branch's localisation.
//!
//! KONCLUDE-PORT-NOTE[ownership]: in C++ these are methods of the algorithm
//! (`CCalculationTableauCompletionTaskHandleAlgorithm`) that are pure functions of
//! `calcAlgContext`. The port lifts them onto `CalculationAlgorithmContextBase`
//! (which owns both the `ProcessingDataBox` — holding the node vector — and the
//! `ProcessContext` — holding the node arena + the tagger), so that ANY completion
//! body holding a `&mut CalculationAlgorithmContextBase` can call
//! `ctx.get_up_to_date_individual(...)` directly. The old algorithm-method stubs in
//! `completion/u36.rs` are kept and marked `// superseded by ctx.*`.

#![allow(dead_code)]

use super::super::completion::context::CalculationAlgorithmContextBase;
use super::super::model::substrate::{Cint64, Id};
use super::node::IndividualProcessNode;
use super::{EdgeId, NodeId};

// ===========================================================================
// CProcessTagger (Process/CProcessTagger.{h,cpp}).
// ===========================================================================

/// Port of `CProcessTagger`.
///
/// The per-test monotone tag counters. Only the localization tag participates in
/// node resolution (`getCurrentLocalizationTag`); the rest are carried for layout
/// fidelity and the branching / blocking / label-set-modification protocols that
/// other waves drive. Replaces the W3-DEFER opaque `Cint64` placeholder the struct
/// wave left on `ProcessContext::used_process_tagger`.
#[derive(Debug, Clone)]
pub struct ProcessTagger {
    /// `mLocalizationTag`.
    pub localization_tag: Cint64,
    /// `mBranchingTag`.
    pub branching_tag: Cint64,
    /// `mProcessingTag`.
    pub processing_tag: Cint64,
    /// `mBlockingAddTag`.
    pub blocking_add_tag: Cint64,
    /// `mNodeSwitchTag`.
    pub node_switch_tag: Cint64,
    /// `mConceptLabelSetModificationTag`.
    pub concept_label_set_modification_tag: Cint64,
    /// `mCurrentBlockingFollowTag`.
    pub current_blocking_follow_tag: Cint64,
}

impl Default for ProcessTagger {
    /// Port of `CProcessTagger::CProcessTagger` — every counter starts 0.
    fn default() -> Self {
        ProcessTagger {
            localization_tag: 0,
            branching_tag: 0,
            processing_tag: 0,
            blocking_add_tag: 0,
            node_switch_tag: 0,
            concept_label_set_modification_tag: 0,
            current_blocking_follow_tag: 0,
        }
    }
}

impl ProcessTagger {
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CProcessTagger::setCurrentLocalizationTag`.
    pub fn set_current_localization_tag(&mut self, loc_tag: Cint64) -> &mut Self {
        self.localization_tag = loc_tag;
        self
    }
    /// Port of `CProcessTagger::getCurrentLocalizationTag`.
    pub fn get_current_localization_tag(&self) -> Cint64 {
        self.localization_tag
    }
    /// Port of `CProcessTagger::getCurrentProcessingTag`.
    pub fn get_current_processing_tag(&self) -> Cint64 {
        self.processing_tag
    }
    /// Port of `CProcessTagger::getCurrentProcessingTagAndInc`.
    pub fn get_current_processing_tag_and_inc(&mut self) -> Cint64 {
        let t = self.processing_tag;
        self.processing_tag += 1;
        t
    }
    /// Port of `CProcessTagger::getCurrentBranchingTag`.
    pub fn get_current_branching_tag(&self) -> Cint64 {
        self.branching_tag
    }
    /// Port of `CProcessTagger::getCurrentBlockingAddTag`.
    pub fn get_current_blocking_add_tag(&self) -> Cint64 {
        self.blocking_add_tag
    }
    /// Port of `CProcessTagger::getCurrentNodeSwitchTag`.
    pub fn get_current_node_switch_tag(&self) -> Cint64 {
        self.node_switch_tag
    }
    /// Port of `CProcessTagger::getCurrentConceptLabelSetModificationTag`.
    pub fn get_current_concept_label_set_modification_tag(&self) -> Cint64 {
        self.concept_label_set_modification_tag
    }
    /// Port of `CProcessTagger::getCurrentBlockingFollowTag`.
    pub fn get_current_blocking_follow_tag(&self) -> Cint64 {
        self.current_blocking_follow_tag
    }

    /// Port of `CProcessTagger::incLocalizationTag`.
    pub fn inc_localization_tag(&mut self) -> &mut Self {
        self.localization_tag += 1;
        self
    }
    /// Port of `CProcessTagger::incProcessingTag`.
    pub fn inc_processing_tag(&mut self) -> &mut Self {
        self.processing_tag += 1;
        self
    }
    /// Port of `CProcessTagger::incBranchingTag`.
    pub fn inc_branching_tag(&mut self) -> &mut Self {
        self.branching_tag += 1;
        self
    }
    /// Port of `CProcessTagger::incBlockingAddTag`.
    pub fn inc_blocking_add_tag(&mut self) -> &mut Self {
        self.blocking_add_tag += 1;
        self
    }
    /// Port of `CProcessTagger::incNodeSwitchTag`.
    pub fn inc_node_switch_tag(&mut self) -> &mut Self {
        self.node_switch_tag += 1;
        self
    }
    /// Port of `CProcessTagger::incConceptLabelSetModificationTag`.
    pub fn inc_concept_label_set_modification_tag(&mut self) -> &mut Self {
        self.concept_label_set_modification_tag += 1;
        self
    }
    /// Port of `CProcessTagger::incCurrentBlockingFollowTag`.
    pub fn inc_current_blocking_follow_tag(&mut self) -> &mut Self {
        self.current_blocking_follow_tag += 1;
        self
    }
}

// ===========================================================================
// CIndividualProcessNodeVector (Process/CIndividualProcessNodeVector.{h,cpp}).
// ===========================================================================

/// Port of `CIndividualProcessNodeVector`
/// (a `CDefaultDoubleDynamicReferenceVector<CIndividualProcessNode*>`): the
/// databox's `mIndiProcessVector`, the per-individual map from a signed individual
/// node id to the current node for it in this branch. Merging / relocalisation
/// updates this vector, so `get_data(id)` already yields the up-to-date (merge
/// target / relocalised) node — this is what makes `getUpToDateIndividual` a single
/// lookup rather than a chain walk.
///
/// KONCLUDE-PORT-NOTE[ownership]: a `CIndividualProcessNode*` becomes a `NodeId`
/// into the `ProcessContext::nodes` arena (`Id::NONE` == the C++ `nullptr`).
/// KONCLUDE-PORT-NOTE[int-width]: the C++ "double dynamic" vector is keyed by a
/// SIGNED `cint64` id — nominals carry negative ids (`indiID <= 0`) — so the store
/// is two-sided: non-negative ids index `pos`, negative ids index `neg`.
/// KONCLUDE-PORT-NOTE[unclear]: the C++ container also carries a local-overlay
/// `setLocalData` vs base `setData` save/restore for backtracking; that
/// branch-overlay protocol is a separate process unit. Here `set_local_data` is a
/// single store (correct within one branch); the overlay rewind lands with the
/// databox save/restore wave.
#[derive(Debug, Default, Clone)]
pub struct IndividualProcessNodeVector {
    /// ids `>= 0` → `pos[id]`.
    pos: Vec<NodeId>,
    /// ids `< 0` → `neg[-id]`.
    neg: Vec<NodeId>,
}

impl IndividualProcessNodeVector {
    /// Port of `CIndividualProcessNodeVector::CIndividualProcessNodeVector`.
    pub fn new() -> Self {
        IndividualProcessNodeVector { pos: Vec::new(), neg: Vec::new() }
    }

    #[inline]
    fn side(&self, id: Cint64) -> (&Vec<NodeId>, usize) {
        if id >= 0 {
            (&self.pos, id as usize)
        } else {
            (&self.neg, (-id) as usize)
        }
    }

    /// Port of `CDefaultDoubleDynamicReferenceVector::getData(cint64)` — the stored
    /// node for `id`, or `Id::NONE` (`nullptr`) if none.
    pub fn get_data(&self, id: Cint64) -> NodeId {
        let (vec, idx) = self.side(id);
        vec.get(idx).copied().unwrap_or(NodeId::NONE)
    }

    /// Port of `CDefaultDoubleDynamicReferenceVector::hasData(cint64)`.
    pub fn has_data(&self, id: Cint64) -> bool {
        self.get_data(id).is_some()
    }

    /// Port of `CDefaultDoubleDynamicReferenceVector::setLocalData(cint64, T)`.
    pub fn set_local_data(&mut self, id: Cint64, node: NodeId) -> &mut Self {
        if id >= 0 {
            let idx = id as usize;
            if idx >= self.pos.len() {
                self.pos.resize(idx + 1, NodeId::NONE);
            }
            self.pos[idx] = node;
        } else {
            let idx = (-id) as usize;
            if idx >= self.neg.len() {
                self.neg.resize(idx + 1, NodeId::NONE);
            }
            self.neg[idx] = node;
        }
        self
    }

    /// `setData` (the base-store setter). Same single store as `set_local_data`
    /// until the branch overlay lands (see the type's `[unclear]` note).
    pub fn set_data(&mut self, id: Cint64, node: NodeId) -> &mut Self {
        self.set_local_data(id, node)
    }

    /// Port of `CDynamicExpandingDoubleVector::getItemMinIndex` — the lowest
    /// (most-negative) stored id (the negative side grows down from -1).
    pub fn get_item_min_index(&self) -> Cint64 {
        -((self.neg.len() as Cint64) - 1).max(0)
    }
    /// Port of `getItemMaxIndex` — one past the highest non-negative stored id.
    pub fn get_item_max_index(&self) -> Cint64 {
        self.pos.len() as Cint64
    }
    /// Port of `getItemCount` — total slots over both sides.
    pub fn get_item_count(&self) -> Cint64 {
        (self.pos.len() + self.neg.len().saturating_sub(1)) as Cint64
    }
}

// ===========================================================================
// The resolution methods — lifted onto CalculationAlgorithmContextBase.
// ===========================================================================

impl CalculationAlgorithmContextBase {
    /// Convenience: the current localization tag of this context's process tagger
    /// (`calcAlgContext->getUsedProcessTagger()->getCurrentLocalizationTag()`).
    #[inline]
    fn current_localization_tag(&self) -> Cint64 {
        self.process_context()
            .used_process_tagger()
            .get_current_localization_tag()
    }

    /// Port of `getUpToDateIndividual(CIndividualProcessNode* indi, ...)`. `.cpp` 22485–22493.
    ///
    /// If `indi` is stale for the current localization AND was relocalised, the
    /// databox node vector holds the current node for its individual id; return
    /// that. Otherwise `indi` is already current.
    pub fn get_up_to_date_individual(&mut self, indi: NodeId) -> NodeId {
        let cur_loc_tag = self.current_localization_tag();
        let (up_to_date, relocalized, indi_node_id) = {
            let node = self.process_context().node(indi);
            (
                node.is_localization_tag_up_to_date(cur_loc_tag),
                node.is_relocalized(),
                node.individual_node_id(),
            )
        };
        if !up_to_date && relocalized {
            // STATINC(INDINODEUPDATELOADCOUNT) — stats elided.
            return self
                .processing_data_box()
                .individual_process_node_vector()
                .get_data(indi_node_id);
        }
        indi
    }

    /// Port of `getUpToDateIndividual(cint64 indiID, ...)`. `.cpp` 22506–22510+.
    ///
    /// The node-vector lookup core. When the vector already holds a node for
    /// `indi_id`, return it (the common path). The miss path — materialising a
    /// fresh temporary nominal node, loading its assertions/backend cache and
    /// queueing it — is the heavy algorithm-driven branch and stays deferred.
    pub fn get_up_to_date_individual_by_id(&mut self, indi_id: Cint64) -> NodeId {
        // STATINC(INDINODEUPDATELOADCOUNT) — stats elided.
        let up_to_date_indi = self
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(indi_id);
        if up_to_date_indi.is_some() {
            return up_to_date_indi;
        }
        // W3-DEFER[api]: the `.cpp` 22510–22580 miss path (createNewTemporaryNominalIndividual
        // + allocate a NOMINALINDIVIDUALTYPE node + initDependencyTracker +
        // setNominalIndividual + addConceptToIndividual(univConnNomValue / nominalConcept)
        // + loadIndividualNodeDataFromBackendCache + addIndividualToProcessingQueue) is
        // algorithm-driven (it calls back into the completion engine's add-concept /
        // backend-cache / queue machinery). It lands when the nominal-localisation wave
        // un-defers; the vector-hit path above is the one the successor/ancestor
        // resolvers depend on. C++ miss default before materialisation is `nullptr`.
        NodeId::NONE
    }

    /// Port of `getAvailableUpToDateIndividual(cint64 indiID, ...)`. `.cpp` 22477–22482.
    ///
    /// Like `get_up_to_date_individual_by_id` but only when the nominal node is
    /// already present in the vector (no materialisation): returns `Id::NONE` when
    /// absent.
    pub fn get_available_up_to_date_individual(&mut self, indi_id: Cint64) -> NodeId {
        if self.is_nominal_individual_node_available(indi_id) {
            return self.get_up_to_date_individual_by_id(indi_id);
        }
        NodeId::NONE
    }

    /// Port of `isNominalIndividualNodeAvailable(cint64 indiID, ...)`.
    /// `.cpp` (helper): `indiProcNodeVec->hasData(indiID)`.
    pub fn is_nominal_individual_node_available(&self, indi_id: Cint64) -> bool {
        self.processing_data_box()
            .individual_process_node_vector()
            .has_data(indi_id)
    }

    /// Port of `getLocalizedIndividual(cint64 indiID, ...)`. `.cpp` 26412–26414.
    pub fn get_localized_individual_by_id(&mut self, indi_id: Cint64) -> NodeId {
        let up = self.get_up_to_date_individual_by_id(indi_id);
        self.get_localized_individual(up, false)
    }

    /// Port of `getLocalizedIndividual(CIndividualProcessNode* indi, bool updateIndividual, ...)`.
    /// `.cpp` 26416–26444.
    ///
    /// If `indi` is not localisation-up-to-date, allocate a fresh node, hand the
    /// predecessor's state to it (`initIndividualProcessNode`), seed it current, and
    /// record it in the databox node vector under the individual id.
    pub fn get_localized_individual(&mut self, indi: NodeId, update_individual: bool) -> NodeId {
        let cur_loc_tag = self.current_localization_tag();
        if self.process_context().node(indi).is_localization_tag_up_to_date(cur_loc_tag) {
            return indi;
        }
        let mut indi = indi;
        if update_individual {
            indi = self.get_up_to_date_individual(indi);
        }
        if self.process_context().node(indi).is_localization_tag_up_to_date(cur_loc_tag) {
            return indi;
        }
        // STATINC(INDINODELOCALIZEDLOADCOUNT) — stats elided.
        // localicedIndi = new CIndividualProcessNode(processContext);
        // localicedIndi->initIndividualProcessNode(indi);
        let new_id = self
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));
        // KONCLUDE-PORT-NOTE[ownership]: `initIndividualProcessNode` reads the
        // predecessor and writes the new node — both live in the same arena, so the
        // predecessor is lifted out with `mem::replace` (the established lazy-getter
        // pattern in `process/context.rs`), the new node is initialised against it,
        // then the predecessor is restored. `initIndividualProcessNode` flips the
        // predecessor's `relocalized` flag, which is preserved on restore.
        let mut prev = std::mem::replace(
            self.process_context_mut().node_mut(indi),
            IndividualProcessNode::default(),
        );
        self.process_context_mut()
            .node_mut(new_id)
            .init_individual_process_node(indi, &mut prev);
        *self.process_context_mut().node_mut(indi) = prev;
        // KONCLUDE-PORT-NOTE[api]: the C++ node CONSTRUCTOR seeds the localization
        // tag from `processContext->getUsedProcessTagger()` (so a freshly built node
        // is current); `init_individual_process_node` does NOT touch it. The struct
        // wave deferred that ctor seeding (`pn1::construct` sets 0), so it is applied
        // here for the localisation path — the localised node must be current.
        self.process_context_mut()
            .node_mut(new_id)
            .set_localization_tag(cur_loc_tag);
        // indiProcNodeVec->setLocalData(localicedIndi->getIndividualNodeID(), localicedIndi);
        let new_indi_id = self.process_context().node(new_id).individual_node_id();
        self.processing_data_box_mut()
            .individual_process_node_vector_mut()
            .set_local_data(new_indi_id, new_id);
        // W3-DEFER[api]: the completion-graph-cached re-flag branch (.cpp 26430–26439)
        // is gated on the algorithm's `mConfCompletionGraphCaching` config (not
        // reachable from the ctx receiver) AND `hasCompletionGraphCachedIndividualNodes()`;
        // it only clears/re-sets PRF cache flags + tracks a referred dependence. Inert
        // when completion-graph caching is disabled (the ORE default); it lands with
        // the completion-graph-cache wave.
        new_id
    }

    /// Port of `getSuccessorIndividual(CIndividualProcessNode*& indi, CIndividualLinkEdge* link, ...)`.
    /// `.cpp` 26446–26461.
    ///
    /// The opposite end of `link` from `indi`. If the link is current the opposite is
    /// returned directly; otherwise, when the opposite is stale-but-relocalised, the
    /// node vector yields its current node.
    pub fn get_successor_individual(&mut self, indi: &mut NodeId, link: EdgeId) -> NodeId {
        let cur_loc_tag = self.current_localization_tag();
        if self.process_context().edge(link).is_localization_tag_up_to_date(cur_loc_tag) {
            return self.edge_opposite_individual(link, *indi);
        }
        // STATINC(INDINODEUPDATELOADCOUNT) — stats elided.
        let succ_indi = self.edge_opposite_individual(link, *indi);
        let (up_to_date, relocalized) = {
            let node = self.process_context().node(succ_indi);
            (node.is_localization_tag_up_to_date(cur_loc_tag), node.is_relocalized())
        };
        if !up_to_date && relocalized {
            let succ_indi_id = self.edge_opposite_individual_id(link, *indi);
            return self
                .processing_data_box()
                .individual_process_node_vector()
                .get_data(succ_indi_id);
        }
        succ_indi
    }

    /// Port of `getLocalizedSuccessorIndividual(...)`. `.cpp` 26464–26477.
    pub fn get_localized_successor_individual(&mut self, indi: &mut NodeId, link: EdgeId) -> NodeId {
        let cur_loc_tag = self.current_localization_tag();
        if self.process_context().edge(link).is_localization_tag_up_to_date(cur_loc_tag) {
            return self.edge_opposite_individual(link, *indi);
        }
        // STATINC(INDINODEUPDATELOADCOUNT) — stats elided.
        let succ_indi_id = self.edge_opposite_individual_id(link, *indi);
        let succ_indi = self
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(succ_indi_id);
        self.get_localized_individual(succ_indi, false)
    }

    /// Port of `getAncestorIndividual(CIndividualProcessNode*& indi, ...)`. `.cpp` 26480–26488.
    pub fn get_ancestor_individual(&mut self, indi: &mut NodeId) -> NodeId {
        let anc_link = self.process_context().node(*indi).get_ancestor_link();
        if anc_link.is_some() {
            return self.get_successor_individual(indi, anc_link);
        }
        NodeId::NONE
    }

    // -----------------------------------------------------------------------
    // Edge opposite-individual helpers (port of CNodeEdge::getOppositeIndividual /
    // getOppositeIndividualID, `.cpp` 91–118). They compare by INDIVIDUAL NODE ID
    // (not arena identity), so a localised copy with the same individual id resolves
    // correctly; they need the node arena, hence they are ctx-level.
    // -----------------------------------------------------------------------

    /// Port of `CNodeEdge::getOppositeIndividual(CIndividualProcessNode* indi)`
    /// (→ the `cint64` overload). The node at the other end of `link` from `indi`.
    fn edge_opposite_individual(&self, link: EdgeId, indi: NodeId) -> NodeId {
        if indi.is_none() {
            return NodeId::NONE;
        }
        let indi_id = self.process_context().node(indi).individual_node_id();
        let edge = self.process_context().edge(link);
        let (src, dst) = (edge.get_source_individual(), edge.get_destination_individual());
        let src_id = self.process_context().node(src).individual_node_id();
        if src_id == indi_id {
            dst
        } else {
            src
        }
    }

    /// Port of `CNodeEdge::getOppositeIndividualID(CIndividualProcessNode* indi)`
    /// (→ the `cint64` overload).
    fn edge_opposite_individual_id(&self, link: EdgeId, indi: NodeId) -> Cint64 {
        let opp = self.edge_opposite_individual(link, indi);
        if opp.is_none() {
            return 0;
        }
        self.process_context().node(opp).individual_node_id()
    }
}
