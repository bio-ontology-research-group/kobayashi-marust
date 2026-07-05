//! `process::dependency` — the dependency / proof-tracking spine (Konclude
//! `Source/Reasoner/Kernel/Process/Dependency/`).
//!
//! This is the SD-5 struct-definition unit (manifest/05-process-units.md §4):
//! the `DependencyNode` tagged enum + `DepKind` discriminant + the track-point /
//! dependency-link / branch-tree / branching-instruction records. Method bodies
//! are filled later (DEP-1 / DEP-2); here only the data model is defined.
//!
//! ## Why one enum for ~63 classes
//! Konclude has one concrete `C*DependencyNode` class per `DEPENDENCNODEYTYPE`
//! tag. Nearly all are *tag-only*: they add no data over their base, differing
//! only in the `mDepNodeType` discriminant the rest of the reasoner branches on.
//! The handful that carry data add 0/1/2 embedded `CDependency` back-edges (det
//! subclasses) or the non-deterministic branch bookkeeping (`CNonDeterministic*`),
//! plus one `CXLinker<cint64>` outlier (`CREUSEBACKENDEXPANSIONMODESDependencyNode`).
//! So the zoo collapses to **7 structural variants** carrying a full 64-value
//! `DepKind` tag — `kind` stays exact for per-rule dispatch.
//!
//! KONCLUDE-PORT-NOTE[ownership]: every `CXxx*` back-pointer is a typed arena id
//! (`DependencyId`/`TrackPointId`/…); `nullptr` → `Id::NONE`. Intrusive
//! `CLinkerBase`/`CXLinker`/`CSortedNegLinker` chains → `Vec`/`next`-id, per
//! `model/substrate.rs`. See that file for the single global decision.

#![allow(dead_code)]

use super::super::model::{Cint64, ConceptId, IndividualId, NegLink, RoleId, INVALID};
use super::representative::RepresentativePropagationMap;
use super::varbind::{RepresentativeVariableBindingPathMap, VarBindingPathId};
use super::{BranchNodeId, ClashDescId, ConDescId, DepLinkId, DependencyId, NodeId, TrackPointId};

/// Port of `CDependencyNode::DEPENDENCNODEYTYPE` (`CDependencyNode.h` 75–97).
///
/// The discriminant stored in `DepNodeBase::kind` and branched on across the
/// completion engine. Values and order mirror the C++ enum exactly (starting at
/// `Undefined = 0`), so a raw cast round-trips with the original.
///
/// KONCLUDE-PORT-NOTE[unclear]: the manifest called this a "62-value" tag; the
/// actual `DEPENDENCNODEYTYPE` has **64** members — `Undefined` (a sentinel with
/// no class) + `IndependentBase` + 62 rule kinds. 63 of the 64 have a concrete
/// `C*DependencyNode` class; `Undefined` does not. Two extra classes
/// (`CRepresentativeResolveDependencyNode`, `CRepresentativeSelectDependencyNode`)
/// are intermediate *bases* of the `…RESOLVEREPRESENTATIVE` / `…REPRESENTATIVE*`
/// tags (distinguished at runtime by `isRepresentative{Resolve,Select}…()`), not
/// separate tags — hence 64 tags but 65 class files. The full 64 are reproduced
/// here verbatim; this is the faithful source of truth.
#[repr(i64)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum DepKind {
    /// `DNTUNDEFINED` → (no class; sentinel).
    Undefined = 0,
    /// `DNTINDEPENDENTBASE` → `CIndependentBaseDependencyNode` (variant `IndependentBase`).
    IndependentBase = 1,
    /// `DNTANDDEPENDENCY` → `CANDDependencyNode` (det, tag-only).
    And = 2,
    /// `DNTAUTOMATCHOOSEDEPENDENCY` → `CAUTOMATCHOOSEDependencyNode` (det, tag-only).
    AutomatChoose = 3,
    /// `DNTORDEPENDENCY` → `CORDependencyNode` (variant `Or`).
    Or = 4,
    /// `DNTALLDEPENDENCY` → `CALLDependencyNode` (det, 1 back-edge).
    All = 5,
    /// `DNTAUTOMATTRANSACTIONDEPENDENCY` → `CAUTOMATTRANSACTIONDependencyNode` (det, 1 back-edge).
    AutomatTransaction = 6,
    /// `DNTSOMEDEPENDENCY` → `CSOMEDependencyNode` (det, tag-only).
    Some = 7,
    /// `DNTSELFDEPENDENCY` → `CSELFDependencyNode` (det, tag-only).
    Self_ = 8,
    /// `DNTVALUEDEPENDENCY` → `CVALUEDependencyNode` (det, 1 back-edge).
    Value = 9,
    /// `DNTNEGVALUEDEPENDENCY` → `CNEGVALUEDependencyNode` (det, 1 back-edge).
    NegValue = 10,
    /// `DNTDISTINCTDEPENDENCY` → `CDISTINCTDependencyNode` (det, tag-only).
    Distinct = 11,
    /// `DNTATLEASTDEPENDENCY` → `CATLEASTDependencyNode` (det, tag-only).
    AtLeast = 12,
    /// `DNTMERGEDCONCEPT` → `CMERGEDCONCEPTDependencyNode` (det, 1 back-edge).
    MergedConcept = 13,
    /// `DNTMERGEDLINK` → `CMERGEDLINKDependencyNode` (det, 1 back-edge).
    MergedLink = 14,
    /// `DNTMERGEDINDIVIDUAL` → `CMERGEDIndividualDependencyNode` (det, 1 back-edge).
    MergedIndividual = 15,
    /// `DNTMERGEDEPENDENCY` → `CMERGEDependencyNode` (non-det).
    Merge = 16,
    /// `DNTATMOSTDEPENDENCY` → `CATMOSTDependencyNode` (non-det).
    AtMost = 17,
    /// `DNTQUALIFYDEPENDENCY` → `CQUALIFYDependencyNode` (non-det).
    Qualify = 18,
    /// `DNTFUNCTIONALDEPENDENCY` → `CFUNCTIONALDependencyNode` (det, **2** back-edges).
    Functional = 19,
    /// `DNTNOMINALDEPENDENCY` → `CNOMINALDependencyNode` (det, 1 back-edge).
    Nominal = 20,
    /// `DNTIMPLICATIONDEPENDENCY` → `CIMPLICATIONDependencyNode` (det, tag-only).
    Implication = 21,
    /// `DNTEXPANDEDDEPENDENCY` → `CEXPANDEDDependencyNode` (det, tag-only).
    Expanded = 22,
    /// `DNTCONNECTIONDEPENDENCY` → `CCONNECTIONDependencyNode` (det, tag-only).
    Connection = 23,
    /// `DNTREUSEINDIVIDUALDEPENDENCY` → `CREUSEINDIVIDUALDependencyNode` (non-det).
    ReuseIndividual = 24,
    /// `DNTREUSECONCEPTSDEPENDENCY` → `CREUSECONCEPTSDependencyNode` (non-det).
    ReuseConcepts = 25,
    /// `DNTREUSECOMPLETIONGRAPHDEPENDENCY` → `CREUSECOMPLETIONGRAPHDependencyNode` (non-det).
    ReuseCompletionGraph = 26,
    /// `DNTDATATYPETRIGGERDEPENDENCY` → `CDATATYPETRIGGERDependencyNode` (det, tag-only).
    DatatypeTrigger = 27,
    /// `DNTDATATYPECONNECTIONDEPENDENCY` → `CDATATYPECONNECTIONDependencyNode` (det, tag-only).
    DatatypeConnection = 28,
    /// `DNTROLEASSERTIONDEPENDENCY` → `CROLEASSERTIONDependencyNode` (det, 1 back-edge).
    RoleAssertion = 29,
    /// `DNTDATAASSERTIONDEPENDENCY` → `CDATAASSERTIONDependencyNode` (det, 1 back-edge).
    DataAssertion = 30,
    /// `DNTMERGEPOSSIBLEINSTANCEINDIVIDUALDEPENDENCY` → `CMERGEPOSSIBLEINSTANCEINDIVIDUALDependencyNode` (non-det).
    MergePossibleInstanceIndividual = 31,
    /// `DNTSAMEINDIVIDUALSMERGEDEPENDENCY` → `CSAMEINDIVIDUALSMERGEDependencyNode` (det, 1 back-edge).
    SameIndividualsMerge = 32,
    /// `DNTORONLYOPTIONDEPENDENCY` → `CORONLYOPTIONDependencyNode` (det, tag-only).
    OrOnlyOption = 33,
    /// `DNTBINDVARIABLEDEPENDENCY` → `CBINDVARIABLEDependencyNode` (det, tag-only).
    BindVariable = 34,
    /// `DNTPROPAGATEBINDINGDEPENDENCY` → `CPROPAGATEBINDINGDependencyNode` (det, tag-only).
    PropagateBinding = 35,
    /// `DNTBINDPROPAGATEAND` → `CBINDPROPAGATEANDDependencyNode` (det, tag-only).
    BindPropagateAnd = 36,
    /// `DNTBINDPROPAGATEIMPLICATION` → `CBINDPROPAGATEIMPLICATIONDependencyNode` (det, tag-only).
    BindPropagateImplication = 37,
    /// `DNTPROPAGATEBINDINGSUCCESSORDEPENDENCY` → `CPROPAGATEBINDINGSSUCCESSORDependencyNode` (det, 1 back-edge).
    PropagateBindingSuccessor = 38,
    /// `DNTBINDPROPAGATEALL` → `CBINDPROPAGATEALLDependencyNode` (det, 1 back-edge).
    BindPropagateAll = 39,
    /// `DNTBINDPROPAGATECYCLE` → `CBINDPROPAGATECYCLEDependencyNode` (det, 1 back-edge).
    BindPropagateCycle = 40,
    /// `DNTPROPAGATECONNECTIONDEPENDENCY` → `CPROPAGATECONNECTIONDependencyNode` (det, tag-only).
    PropagateConnection = 41,
    /// `DNTPROPAGATECONNECTIONAWAYDEPENDENCY` → `CPROPAGATECONNECTIONAWAYDependencyNode` (det, tag-only).
    PropagateConnectionAway = 42,
    /// `DNTBINDPROPAGATEGROUNDINGDEPENDENCY` → `CBINDPROPAGATEGROUNDINGDependencyNode` (det, tag-only).
    BindPropagateGrounding = 43,
    /// `DNTVARBINDPROPAGATEAND` → `CVARBINDPROPAGATEANDDependencyNode` (det, tag-only).
    VarBindPropagateAnd = 44,
    /// `DNTPROPAGATEVARIABLEBINDINGDEPENDENCY` → `CPROPAGATEVARIABLEBINDINGDependencyNode` (det, tag-only).
    PropagateVariableBinding = 45,
    /// `DNTVARBINDPROPAGATEALL` → `CVARBINDPROPAGATEALLDependencyNode` (det, 1 back-edge).
    VarBindPropagateAll = 46,
    /// `DNTPROPAGATEVARIABLEBINDINGSUCCESSORDEPENDENCY` → `CPROPAGATEVARIABLEBINDINGSSUCCESSORDependencyNode` (det, 1 back-edge).
    PropagateVariableBindingSuccessor = 47,
    /// `DNTVARBINDVARIABLEDEPENDENCY` → `CVARBINDVARIABLEDependencyNode` (det, tag-only).
    VarBindVariable = 48,
    /// `DNTVARBINDPROPAGATEJOIN` → `CVARBINDPROPAGATEJOINDependencyNode` (det, 1 back-edge).
    VarBindPropagateJoin = 49,
    /// `DNTVARBINDPROPAGATEGROUNDINGDEPENDENCY` → `CVARBINDPROPAGATEGROUNDINGDependencyNode` (det, tag-only).
    VarBindPropagateGrounding = 50,
    /// `DNTPROPAGATEVARIABLECONNECTIONDEPENDENCY` → `CPROPAGATEVARIABLECONNECTIONDependencyNode` (det, tag-only).
    PropagateVariableConnection = 51,
    /// `DNTVARBINDPROPAGATEIMPLICATION` → `CVARBINDPROPAGATEIMPLICATIONDependencyNode` (det, tag-only).
    VarBindPropagateImplication = 52,
    /// `DNTRESOLVEREPRESENTATIVE` → `CRESOLVEREPRESENTATIVEDependencyNode` (det, 1 back-edge `mAdditionalDep`).
    ResolveRepresentative = 53,
    /// `DNTREPRESENTATIVEAND` → `CREPRESENTATIVEANDDependencyNode` (det, tag-only).
    RepresentativeAnd = 54,
    /// `DNTREPRESENTATIVEALL` → `CREPRESENTATIVEALLDependencyNode` (det, 1 back-edge).
    RepresentativeAll = 55,
    /// `DNTREPRESENTATIVEIMPLICATION` → `CREPRESENTATIVEIMPLICATIONDependencyNode` (det, tag-only).
    RepresentativeImplication = 56,
    /// `DNTREPRESENTATIVEBINDVARIABLE` → `CREPRESENTATIVEBINDVARIABLEDependencyNode` (det, tag-only; base `CRepresentativeSelectDependencyNode`).
    RepresentativeBindVariable = 57,
    /// `DNTREPRESENTATIVEJOIN` → `CREPRESENTATIVEJOINDependencyNode` (det, 1 back-edge).
    RepresentativeJoin = 58,
    /// `DNTREPRESENTATIVEGROUNDING` → `CREPRESENTATIVEGROUNDINGDependencyNode` (det, tag-only; base `CRepresentativeSelectDependencyNode`).
    RepresentativeGrounding = 59,
    /// `DNTREUSEBACKENDEXPANSIONMODESDEPENDENCY` → `CREUSEBACKENDEXPANSIONMODESDependencyNode` (variant `ReuseBackendModes`; `CXLinker<cint64>` outlier).
    ReuseBackendExpansionModes = 60,
    /// `DNTREUSEBACKENDFIXEDINDIVIDUALEXPANSIONDEPENDENCY` → `CREUSEBACKENDFIXEDINDIVIDUALEXPANSIONDependencyNode` (non-det).
    ReuseBackendFixedIndividualExpansion = 61,
    /// `DNTREUSEBACKENDPRIORITIZEDINDIVIDUALEXPANSIONDEPENDENCY` → `CREUSEBACKENDPRIORITIZEDINDIVIDUALEXPANSIONDependencyNode` (non-det).
    ReuseBackendPrioritizedIndividualExpansion = 62,
    /// `DNTREUSEBACKENDVALUEDEPENDENCY` → `CREUSEBACKENDVALUEDependencyNode` (det, 1 back-edge).
    ReuseBackendValue = 63,
}

impl DepKind {
    /// True for the deterministic family (`CDeterministicDependencyNode` and its
    /// subclasses): the node *is* its own continuation track point.
    /// Mirrors `CDeterministicDependencyNode::isDeterministiDependencyNode()`.
    #[inline]
    pub fn is_deterministic(self) -> bool {
        !self.is_non_deterministic()
    }

    /// True for the non-deterministic family (`CNonDeterministicDependencyNode`
    /// and subclasses, incl. `Or` and `ReuseBackendModes`).
    /// Mirrors `CDependencyNode::isNonDeterministiDependencyNode()`.
    #[inline]
    pub fn is_non_deterministic(self) -> bool {
        matches!(
            self,
            DepKind::Or
                | DepKind::Merge
                | DepKind::AtMost
                | DepKind::Qualify
                | DepKind::ReuseIndividual
                | DepKind::ReuseConcepts
                | DepKind::ReuseCompletionGraph
                | DepKind::MergePossibleInstanceIndividual
                | DepKind::ReuseBackendExpansionModes
                | DepKind::ReuseBackendFixedIndividualExpansion
                | DepKind::ReuseBackendPrioritizedIndividualExpansion
        )
    }
}

/// Shared base of every `C*DependencyNode`, from `CProcessTag` → `CProcessingTag`
/// → `CDependencyNode` (`CDependencyNode.h` 155–164). Carried by every variant.
#[derive(Clone, Debug)]
pub struct DepNodeBase {
    /// `CProcessTag::mProcessTag`.
    pub process_tag: Cint64,
    /// `CDependencyNode::mConceptDescriptor` (`CConceptDescriptor*`).
    pub concept_descriptor: ConDescId,
    /// `CDependencyNode::mIndividualNode` (`CIndividualProcessNode*`).
    pub individual_node: NodeId,
    /// `CDependencyNode::mDepNodeType` — the 64-value discriminant.
    pub kind: DepKind,
    /// `CDependencyNode::mDepTrackPoint` — the *previous* track point this node
    /// continues from. For a deterministic node the *continuation* point is the
    /// node itself (materialised lazily), so this is only the predecessor.
    pub dep_track_point: TrackPointId,
    /// `CDependencyNode::mAdditionalAfterDepLinker` — head of the additional
    /// after-dependency chain (`CDependency*`).
    pub additional_after: DepLinkId,
    /// `CRepresentativeSelectDependencyNode::mSelectedVarBindPath`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: only `RepresentativeBindVariable` /
    /// `RepresentativeGrounding` use this intermediate-base payload in C++;
    /// folding it into the shared base keeps the enum shape stable while the
    /// `DepKind` predicate preserves the original virtual type test.
    pub selected_var_bind_path: VarBindingPathId,
    /// `CRepresentativeResolveDependencyNode::mResolveVarBindPathMap`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: Konclude stores a pointer to a by-value
    /// representative variable-binding-path map. In Rust that map is itself a
    /// by-value struct, so the dependency node carries an optional clone of the
    /// pointed-to map (`None == nullptr`).
    pub resolve_var_bind_path_map: Option<RepresentativeVariableBindingPathMap>,
    /// `CRepresentativeResolveDependencyNode::mResolveRepPropMap`.
    ///
    /// Same ownership translation as `resolve_var_bind_path_map`.
    pub resolve_rep_prop_map: Option<RepresentativePropagationMap>,
    /// `CROLEASSERTIONDependencyNode::mBaseAssertionRole`.
    ///
    /// Only meaningful when `kind == DepKind::RoleAssertion`; `Id::NONE`
    /// corresponds to Konclude's `nullptr`.
    pub base_assertion_role: RoleId,
    /// `CROLEASSERTIONDependencyNode::mBaseAssertionIndi`.
    ///
    /// Only meaningful when `kind == DepKind::RoleAssertion`; `Id::NONE`
    /// corresponds to Konclude's `nullptr`.
    pub base_assertion_individual: IndividualId,
}

/// The non-deterministic node bookkeeping, from `CNonDeterministicDependencyNode`
/// (`CNonDeterministicDependencyNode.h` 106–114). Present on `NonDeterministic`,
/// `Or`, and `ReuseBackendModes` variants.
#[derive(Clone, Debug)]
pub struct NonDetData {
    /// `mBranchTrackPoints` — head of the opened branch track-point list.
    pub branch_track_points: TrackPointId,
    /// `mClashTrackPoint` — value-typed `CNonDeterministicDependencyTrackPoint`
    /// in C++; ported as an id into the shared track-point arena.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ member is by-value (inline), not a
    /// pointer; an arena slot is allocated for it so the single `TrackPointId`
    /// space addresses it uniformly. Behaviour identical.
    pub clash_track_point: TrackPointId,
    /// `mDependencyClashes` (`CClashedDependencyDescriptor*`).
    pub dependency_clashes: ClashDescId,
    /// `mBranchNode` (`CBranchTreeNode*`).
    pub branch_node: BranchNodeId,
    /// `mBranchTag`.
    pub branch_tag: Cint64,
    /// `mClosingTrackPoint`.
    pub closing_track_point: TrackPointId,
    /// `mClosedTrackPoint`.
    pub closed_track_point: TrackPointId,
}

/// The `⊔`-disjunct extra data, from `CORDisjunctDependencyTrackPoint`
/// (`CORDisjunctDependencyTrackPoint.h` 85–86). Present only on the `Or` variant.
#[derive(Clone, Debug)]
pub struct OrDisjunctTrackData {
    /// `mDisjunctConceptLinker` — `CSortedNegLinker<CConcept*>` → `Vec<NegLink<ConceptId>>`.
    pub disjunct_concept_linker: Vec<NegLink<ConceptId>>,
    /// `mDisjunctBranchStats` — `CDisjunctBranchingStatistics*` (opaque side object).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: held as an opaque id-like `Cint64` until
    /// `CDisjunctBranchingStatistics` is ported; `INVALID` when unset.
    pub disjunct_branch_stats: Cint64,
}

impl Default for OrDisjunctTrackData {
    fn default() -> Self {
        Self {
            disjunct_concept_linker: Vec::new(),
            disjunct_branch_stats: INVALID,
        }
    }
}

/// Port of the `C*DependencyNode` class hierarchy, collapsed to 7 structural
/// variants (manifest/05 §4). The 64-value `base.kind` keeps per-rule dispatch
/// exact; the variant only fixes the payload shape.
#[derive(Clone, Debug)]
pub enum DependencyNode {
    /// `CIndependentBaseDependencyNode` — the search-root sentinel (`DNTINDEPENDENTBASE`).
    IndependentBase { base: DepNodeBase },
    /// `CDeterministicDependencyNode` tag-only kinds (≈29): no extra payload.
    Deterministic { base: DepNodeBase },
    /// Deterministic kinds with **one** embedded `CDependency` back-edge (≈21),
    /// e.g. `CALLDependencyNode::mPrevLinkDep`.
    DetLink { base: DepNodeBase, prev: DepLinkId },
    /// `CFUNCTIONALDependencyNode` — the only kind with **two** back-edges
    /// (`mPrevLink1Dep`, `mPrevLink2Dep`).
    DetLink2 {
        base: DepNodeBase,
        prev1: DepLinkId,
        prev2: DepLinkId,
    },
    /// `CNonDeterministicDependencyNode` family (`Merge`/`AtMost`/`Qualify`/
    /// `Reuse*` etc.).
    NonDeterministic { base: DepNodeBase, nd: NonDetData },
    /// `CORDependencyNode` — non-deterministic + the `⊔`-disjunct track data.
    Or {
        base: DepNodeBase,
        nd: NonDetData,
        disj: OrDisjunctTrackData,
    },
    /// `CREUSEBACKENDEXPANSIONMODESDependencyNode` — non-deterministic + the
    /// `CXLinker<cint64>` involved-individual-id list outlier.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: C++ keeps two `CXLinker<cint64>` chains
    /// (`mAffectedIndividualIdLinker` as a `QAtomicPointer`,
    /// `mInvolvedIndividualIdLinker`) plus two extra reuse track points
    /// (`mFixedReuseDepTrackPoint`, `mPriorizedReuseDepTrackPoint`). The linker
    /// chains flatten to `Vec<Cint64>` (insertion order preserved); the affected
    /// compare-and-swap API is modelled as an expected-slice comparison before
    /// replacing the vector.
    ReuseBackendModes {
        base: DepNodeBase,
        nd: NonDetData,
        fixed_reuse_dep_track_point: TrackPointId,
        priorized_reuse_dep_track_point: TrackPointId,
        involved: Vec<Cint64>,
        affected: Vec<Cint64>,
    },
}

impl DependencyNode {
    /// `CDependencyNode::getDependencyType()` — the stored discriminant.
    #[inline]
    pub fn kind(&self) -> DepKind {
        self.base().kind
    }

    /// Shared accessor for the embedded `DepNodeBase` (every variant carries one).
    #[inline]
    pub fn base(&self) -> &DepNodeBase {
        match self {
            DependencyNode::IndependentBase { base }
            | DependencyNode::Deterministic { base }
            | DependencyNode::DetLink { base, .. }
            | DependencyNode::DetLink2 { base, .. }
            | DependencyNode::NonDeterministic { base, .. }
            | DependencyNode::Or { base, .. }
            | DependencyNode::ReuseBackendModes { base, .. } => base,
        }
    }

    /// Mutable counterpart of [`Self::base`].
    #[inline]
    pub fn base_mut(&mut self) -> &mut DepNodeBase {
        match self {
            DependencyNode::IndependentBase { base }
            | DependencyNode::Deterministic { base }
            | DependencyNode::DetLink { base, .. }
            | DependencyNode::DetLink2 { base, .. }
            | DependencyNode::NonDeterministic { base, .. }
            | DependencyNode::Or { base, .. }
            | DependencyNode::ReuseBackendModes { base, .. } => base,
        }
    }

    /// `CDependencyNode::getConceptDescriptor()`.
    #[inline]
    pub fn concept_descriptor(&self) -> ConDescId {
        self.base().concept_descriptor
    }

    /// `CDependencyNode::getAppropriateIndividualNode()`.
    #[inline]
    pub fn individual_node(&self) -> NodeId {
        self.base().individual_node
    }

    /// Port of `CRepresentativeSelectDependencyNode::getSelectedVariableBindingPath`.
    pub fn selected_variable_binding_path(&self) -> VarBindingPathId {
        self.base().selected_var_bind_path
    }

    /// Port of `CRepresentativeResolveDependencyNode::getResolveRepresentativeVariableBindingPathMap`.
    pub fn resolve_representative_variable_binding_path_map(
        &self,
    ) -> Option<&RepresentativeVariableBindingPathMap> {
        self.base().resolve_var_bind_path_map.as_ref()
    }

    /// Port of `CRepresentativeResolveDependencyNode::getResolveRepresentativePropagationMap`.
    pub fn resolve_representative_propagation_map(&self) -> Option<&RepresentativePropagationMap> {
        self.base().resolve_rep_prop_map.as_ref()
    }

    /// `CDependencyNode::isDeterministiDependencyNode()`.
    #[inline]
    pub fn is_deterministic(&self) -> bool {
        self.kind().is_deterministic()
    }
}

/// Port of `CDependencyTrackPoint` (`CDependencyTrackPoint.h`, base
/// `CBranchingTag : CProcessTag`) folded with its subclasses
/// `CNonDeterministicDependencyTrackPoint` + `CORDisjunctDependencyTrackPoint`,
/// since all three share the single `TrackPointId` arena.
///
/// A *deterministic* node is its own track point — it does not allocate a
/// distinct record; its continuation point is materialised lazily from the node.
/// The fields below the base are populated only for non-deterministic /
/// disjunct track points; they stay `Id::NONE`/empty otherwise.
///
/// KONCLUDE-PORT-NOTE[ownership]: `CBranchingTag` adds no own data member (the
/// branching tag derives from the inherited `mProcessTag` via the process
/// tagger), so only `process_tag` is carried from the tag bases.
#[derive(Clone, Debug)]
pub struct DependencyTrackPoint {
    /// `CProcessTag::mProcessTag` (the branching tag derives from this).
    pub process_tag: Cint64,
    /// `CDependencyTrackPoint::mDepNode` — the node this point belongs to.
    pub dep_node: DependencyId,
    /// `CDependencyTrackPoint::mRelevantFlag`.
    pub relevant_flag: bool,

    // --- CNonDeterministicDependencyTrackPoint extension (NONE for det points) ---
    /// `mClashes` (`CClashedDependencyDescriptor*`).
    pub clashes: ClashDescId,
    /// `mBranchNode` (`CBranchTreeNode*`).
    pub branch_node: BranchNodeId,
    /// `mClashedIrelevant`.
    pub clashed_irrelevant: bool,
    /// `mInvolvedIndiLinker` — `CXLinker<cint64>*` → `Vec<Cint64>`.
    pub involved_indi_ids: Vec<Cint64>,
    /// `CLinkerBase` next-link chaining sibling branch track points.
    pub next: TrackPointId,

    // --- CORDisjunctDependencyTrackPoint extension (empty unless an OR point) ---
    /// `mDisjunctConceptLinker` — `CSortedNegLinker<CConcept*>` → `Vec<NegLink<ConceptId>>`.
    pub disjunct_concept_linker: Vec<NegLink<ConceptId>>,
    /// `mDisjunctBranchStats` — `CDisjunctBranchingStatistics*` (opaque; `INVALID` unset).
    pub disjunct_branch_stats: Cint64,
}

impl DependencyTrackPoint {
    /// `CDependencyTrackPoint::getDependencyNode()`.
    #[inline]
    pub fn dependency_node(&self) -> DependencyId {
        self.dep_node
    }
    /// `CDependencyTrackPoint::isDependencyRelevant()`.
    #[inline]
    pub fn is_dependency_relevant(&self) -> bool {
        self.relevant_flag
    }
    /// `CDependencyTrackPoint::setDependencyRelevance(bool)`.
    #[inline]
    pub fn set_dependency_relevance(&mut self, relevant: bool) {
        self.relevant_flag = relevant;
    }
}

/// Port of `CDependency` (`CDependency.h`, base `CLinkerBase<CDependency*,…>`):
/// an intrusive dependency back-edge in the additional-dependency chain.
///
/// Named `DependencyLink` to match `process/mod.rs` (`DepLinkId =
/// Id<dependency::DependencyLink>`); the C++ class is `CDependency`.
#[derive(Clone, Debug)]
pub struct DependencyLink {
    /// `CDependency::mDepTrackPoint` — the previous track point this edge depends on.
    pub dep_track_point: TrackPointId,
    /// `CLinkerBase` next link — the next additional dependency in the chain.
    pub next: DepLinkId,
}

impl DependencyLink {
    /// `CDependency::getPreviousDependencyTrackPoint()`.
    #[inline]
    pub fn previous_dependency_track_point(&self) -> TrackPointId {
        self.dep_track_point
    }
    /// `CDependency::getNextAdditionalDependency()`.
    #[inline]
    pub fn next_additional_dependency(&self) -> DepLinkId {
        self.next
    }
}

/// Port of `CBranchTreeNode` (`CBranchTreeNode.h`, base `CBranchingTag`): a node
/// in the search/branching tree — the backjumping spine.
///
/// KONCLUDE-PORT-NOTE[ownership]: `mSatCalcTask` (`CSatisfiableCalculationTask*`)
/// is an upstream task object not yet ported; held as an opaque `Cint64` handle
/// (`INVALID` unset) until the Task layer lands.
#[derive(Clone, Debug)]
pub struct BranchTreeNode {
    /// `CProcessTag::mProcessTag` (branching tag derives from this, via `CBranchingTag`).
    pub process_tag: Cint64,
    /// `mParentNode`.
    pub parent_node: BranchNodeId,
    /// `mRootNode`.
    pub root_node: BranchNodeId,
    /// `mBranchedDepTrackPoint` (`CNonDeterministicDependencyTrackPoint*`).
    pub branched_dep_track_point: TrackPointId,
    /// `mSatCalcTask` (`CSatisfiableCalculationTask*`) — opaque handle, see note.
    pub sat_calc_task: Cint64,
}

impl BranchTreeNode {
    /// `CBranchTreeNode::isRootNode()`.
    #[inline]
    pub fn is_root_node(&self) -> bool {
        self.parent_node.is_none()
    }
    /// `CBranchTreeNode::getParentNode()`.
    #[inline]
    pub fn parent_node(&self) -> BranchNodeId {
        self.parent_node
    }
    /// `CBranchTreeNode::getDependencyTrackPoint()`.
    #[inline]
    pub fn dependency_track_point(&self) -> TrackPointId {
        self.branched_dep_track_point
    }
}

/// Port of `CBranchingInstruction::BRANCHINGINSTRUCTIONTYPE`
/// (`CBranchingInstruction.h` 62): the recorded branch-decision discriminant.
#[repr(i64)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum BranchingInstructionType {
    /// `BIADDINDIVIDUALCONCEPTSTYPE` → `CBranchingInstructionAddIndividualConcepts`.
    AddIndividualConcepts = 0,
}

/// Port of `CBranchingInstruction` (`CBranchingInstruction.h`) folded with its
/// sole concrete subclass `CBranchingInstructionAddIndividualConcepts`: a
/// recorded branch decision replayed on restore.
///
/// KONCLUDE-PORT-NOTE[ownership]: the abstract base + single subclass collapse to
/// one struct keyed by `kind`. The `AddIndividualConcepts` payload fields are
/// only meaningful when `kind == AddIndividualConcepts` (the only variant today).
#[derive(Clone, Debug)]
pub struct BranchingInstruction {
    /// `CBranchingInstruction::getBranchingInstructionType()`.
    pub kind: BranchingInstructionType,
    /// `mAddingIndividualNode` (`CIndividualProcessNode*`).
    pub adding_individual_node: NodeId,
    /// `mAddingConceptLinker` — `CSortedNegLinker<CConcept*>` → `Vec<NegLink<ConceptId>>`.
    pub adding_concept_linker: Vec<NegLink<ConceptId>>,
    /// `mAddingDepTrackPoint` (`CDependencyTrackPoint*`).
    pub adding_dep_track_point: TrackPointId,
}

impl BranchingInstruction {
    /// `CBranchingInstructionAddIndividualConcepts::getBranchingInstructionType()`.
    #[inline]
    pub fn branching_instruction_type(&self) -> BranchingInstructionType {
        self.kind
    }
    /// `CBranchingInstructionAddIndividualConcepts::getAddingIndividualNode()`.
    #[inline]
    pub fn adding_individual_node(&self) -> NodeId {
        self.adding_individual_node
    }
    /// `CBranchingInstructionAddIndividualConcepts::getAddingDependencyTrackPoint()`.
    #[inline]
    pub fn adding_dependency_track_point(&self) -> TrackPointId {
        self.adding_dep_track_point
    }
}
