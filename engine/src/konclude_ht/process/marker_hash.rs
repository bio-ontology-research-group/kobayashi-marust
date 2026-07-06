//! `process::marker_hash` — port of Konclude
//! `CMarkerIndividualNode{Data,Hash}`.
//!
//! The marker hash indexes marker concepts to the individual nodes carrying them,
//! with the nondeterministic flag kept as part of the occurrence identity.

use std::collections::{HashMap, HashSet};

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::ConceptId;
use super::context::ProcessContext;
use super::NodeId;

/// `CMarkerIndividualNodeHash*` → `MarkerIndividualNodeHashId`.
pub type MarkerIndividualNodeHashId = Id<MarkerIndividualNodeHash>;
/// `CMarkerIndividualNodeData*` → `MarkerIndividualNodeDataId`.
pub type MarkerIndividualNodeDataId = Id<MarkerIndividualNodeData>;

/// Port of `CMarkerIndividualNodeData`.
#[derive(Clone)]
pub struct MarkerIndividualNodeData {
    pub context: Cint64,
    pub marker_individual_node_linker: Vec<(NodeId, bool)>,
    pub use_marker_individual_node_set: HashSet<(Cint64, bool)>,
    pub loc_marker_individual_node_set: HashSet<(Cint64, bool)>,
}

impl Default for MarkerIndividualNodeData {
    fn default() -> Self {
        MarkerIndividualNodeData {
            context: INVALID,
            marker_individual_node_linker: Vec::new(),
            use_marker_individual_node_set: HashSet::new(),
            loc_marker_individual_node_set: HashSet::new(),
        }
    }
}

impl MarkerIndividualNodeData {
    /// Port of `CMarkerIndividualNodeData(CProcessContext*)`.
    pub fn new(context: Cint64) -> Self {
        MarkerIndividualNodeData {
            context,
            ..Self::default()
        }
    }

    /// Port of `initMarkerIndividualNodeData`.
    pub fn init_marker_individual_node_data(
        &mut self,
        prev: Option<&MarkerIndividualNodeData>,
    ) -> &mut Self {
        self.loc_marker_individual_node_set.clear();
        self.marker_individual_node_linker = prev
            .map(|prev| prev.marker_individual_node_linker.clone())
            .unwrap_or_default();
        self.use_marker_individual_node_set = prev
            .map(|prev| prev.use_marker_individual_node_set.clone())
            .unwrap_or_default();
        self
    }

    /// Port of `addMarkerIndividualNodeLinker`.
    pub fn add_marker_individual_node_linker(
        &mut self,
        individual_node_id: Cint64,
        individual: NodeId,
        nondeterministic: bool,
    ) -> bool {
        let key = (individual_node_id, nondeterministic);
        if self.use_marker_individual_node_set.contains(&key)
            || self.loc_marker_individual_node_set.contains(&key)
        {
            return false;
        }
        self.marker_individual_node_linker
            .insert(0, (individual, nondeterministic));
        self.loc_marker_individual_node_set.insert(key);
        self.use_marker_individual_node_set.insert(key);
        true
    }

    /// Port of `getMarkerIndividualNodeLinker`.
    pub fn marker_individual_node_linker(&self) -> &[(NodeId, bool)] {
        &self.marker_individual_node_linker
    }
}

#[derive(Clone, Copy)]
pub struct MarkerIndividualNodeHashData {
    pub marker_indi_node_data: MarkerIndividualNodeDataId,
    pub prev_marker_indi_node_data: MarkerIndividualNodeDataId,
}

impl Default for MarkerIndividualNodeHashData {
    fn default() -> Self {
        MarkerIndividualNodeHashData {
            marker_indi_node_data: Id::NONE,
            prev_marker_indi_node_data: Id::NONE,
        }
    }
}

/// Port of `CMarkerIndividualNodeHash`.
#[derive(Clone)]
pub struct MarkerIndividualNodeHash {
    pub context: Cint64,
    pub marker_individual_node_hash: HashMap<ConceptId, MarkerIndividualNodeHashData>,
}

impl Default for MarkerIndividualNodeHash {
    fn default() -> Self {
        MarkerIndividualNodeHash {
            context: INVALID,
            marker_individual_node_hash: HashMap::new(),
        }
    }
}

impl MarkerIndividualNodeHash {
    /// Port of `CMarkerIndividualNodeHash(CProcessContext*)`.
    pub fn new(context: Cint64) -> Self {
        MarkerIndividualNodeHash {
            context,
            marker_individual_node_hash: HashMap::new(),
        }
    }

    /// Port of `initMarkerIndividualNodeHash`.
    pub fn init_marker_individual_node_hash(
        &mut self,
        prev: Option<&MarkerIndividualNodeHash>,
    ) -> &mut Self {
        if let Some(prev) = prev {
            self.marker_individual_node_hash = prev
                .marker_individual_node_hash
                .iter()
                .map(|(concept, data)| {
                    (
                        *concept,
                        MarkerIndividualNodeHashData {
                            marker_indi_node_data: Id::NONE,
                            prev_marker_indi_node_data: data.prev_marker_indi_node_data,
                        },
                    )
                })
                .collect();
        } else {
            self.marker_individual_node_hash.clear();
        }
        self
    }

    /// Port of `getMarkerIndividualNodeData`.
    pub fn get_marker_individual_node_data(
        ctx: &mut ProcessContext,
        this: MarkerIndividualNodeHashId,
        marker_concept: ConceptId,
        create: bool,
    ) -> MarkerIndividualNodeDataId {
        if create {
            let (current, prev) = {
                let hash = ctx.marker_indi_node_hash_mut(this);
                let data = hash
                    .marker_individual_node_hash
                    .entry(marker_concept)
                    .or_default();
                (data.marker_indi_node_data, data.prev_marker_indi_node_data)
            };
            if current.is_none() {
                let new_data =
                    ctx.alloc_marker_indi_node_data(MarkerIndividualNodeData::new(INVALID));
                if prev.is_some() {
                    let taken = std::mem::replace(
                        ctx.marker_indi_node_data_mut(prev),
                        MarkerIndividualNodeData::new(INVALID),
                    );
                    ctx.marker_indi_node_data_mut(new_data)
                        .init_marker_individual_node_data(Some(&taken));
                    *ctx.marker_indi_node_data_mut(prev) = taken;
                } else {
                    ctx.marker_indi_node_data_mut(new_data)
                        .init_marker_individual_node_data(None);
                }
                let data = ctx
                    .marker_indi_node_hash_mut(this)
                    .marker_individual_node_hash
                    .get_mut(&marker_concept)
                    .unwrap();
                data.marker_indi_node_data = new_data;
                data.prev_marker_indi_node_data = new_data;
                new_data
            } else {
                current
            }
        } else {
            ctx.marker_indi_node_hash(this)
                .marker_individual_node_hash
                .get(&marker_concept)
                .map(|data| data.prev_marker_indi_node_data)
                .unwrap_or(MarkerIndividualNodeDataId::NONE)
        }
    }

    /// Port of `addMarkerIndividualNode`.
    pub fn add_marker_individual_node(
        ctx: &mut ProcessContext,
        this: MarkerIndividualNodeHashId,
        marker_concept: ConceptId,
        individual: NodeId,
        nondeterministic: bool,
    ) -> bool {
        let data = Self::get_marker_individual_node_data(ctx, this, marker_concept, true);
        let individual_node_id = ctx.node(individual).individual_node_id();
        ctx.marker_indi_node_data_mut(data)
            .add_marker_individual_node_linker(individual_node_id, individual, nondeterministic)
    }

    /// Port of `getMarkerIndividualNodeLinker`.
    pub fn get_marker_individual_node_linker(
        ctx: &ProcessContext,
        this: MarkerIndividualNodeHashId,
        marker_concept: ConceptId,
    ) -> Vec<(NodeId, bool)> {
        let data = ctx
            .marker_indi_node_hash(this)
            .marker_individual_node_hash
            .get(&marker_concept)
            .map(|data| data.prev_marker_indi_node_data)
            .unwrap_or(MarkerIndividualNodeDataId::NONE);
        if data.is_none() {
            return Vec::new();
        }
        ctx.marker_indi_node_data(data)
            .marker_individual_node_linker()
            .to_vec()
    }
}
