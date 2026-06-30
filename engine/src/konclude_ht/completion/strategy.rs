//! `completion::strategy` — faithful port of `Reasoner/Kernel/Strategy/`.
//!
//! Ports the four rule-application priority / unsatisfiable-cache-retrieval
//! policy interfaces and their concrete implementations that the completion
//! engine consults:
//!
//! | C++ interface                          | enum here                              | concrete(s) |
//! |----------------------------------------|----------------------------------------|-------------|
//! | `CConceptProcessingPriorityStrategy`   | `ConceptProcessingPriorityStrategy`    | `CConcreteConceptProcessingOperatorPriorityStrategy` |
//! | `CIndividualProcessingPriorityStrategy`| `IndividualProcessingPriorityStrategy` | `CIndividualAncestorDepthMaximumConceptProcessingPriorityStrategy` |
//! | `CTaskProcessingPriorityStrategy`      | `TaskProcessingPriorityStrategy`       | `CEqualDepthTaskProcessingPriorityStrategy`, `CEqualDepthCacheOrientatedProcessingPriorityStrategy` |
//! | `CUnsatisfiableCacheRetrievalStrategy` | `UnsatisfiableCacheRetrievalStrategy`  | `CGenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy` |
//!
//! KONCLUDE-PORT-NOTE[ownership]: per PORT.md §"Memory model" + manifest/09 §3,
//! the C++ engine `new`s exactly one concrete per interface and hands the raw
//! pointer to the per-thread context (stored as `mXxxStrategy` + `mUsedXxxStrategy`).
//! The closed concrete set + single-instantiation make `Box<dyn Trait>` pointless,
//! so each interface becomes a **tagged enum held BY VALUE** in the context (no
//! arena, no `Id`). This file SUPERSEDES the five `completion::stubs`
//! `Id<…Strategy>` placeholder markers (`ConceptProcessingPriorityStrategy`,
//! `IndividualProcessingPriorityStrategy`, `TaskProcessingPriorityStrategy`,
//! `UnsatisfiableCacheRetrievalStrategy`,
//! `IndividualAncestorDepthMaximumConceptProcessingPriorityStrategy`); when this
//! file is wired, those stubs reconcile to the enums below.
//!
//! KONCLUDE-PORT-NOTE[threading]: strategies are per-worker-thread (one context
//! per thread), so they are owned by value and need no `Send`/`Sync`/locking. The
//! C++ `mUsed*` runtime-swap seam (CB cache reuse can repoint the pointer) is
//! expressed as reassigning the enum value in the context.
//!
//! KONCLUDE-PORT-NOTE[ownership]: every strategy method dereferences raw
//! `CIndividualProcessNode* / CConceptDescriptor* / CSatisfiableCalculationTask*`
//! pointers. Per the global arena decision these are `Id`s resolved through the
//! per-test `ProcessContext` (process-graph objects) and the read-shared
//! `OntologyArenas` (the static `CConcept` operands), both threaded as borrowed
//! params. Deep cross-layer reaches whose layers are not yet ported (the Task
//! answerer-propagation controller; the Consistence model data; the Ontology
//! `CDisjunctBranchingStatistics`; the `CConceptProcessingQueue` satellite) are
//! reproduced as `// W6-DEFER[api]` stubs that preserve the exact branch/loop
//! structure and order of operations, leaving the as-yet-unreachable value at its
//! minimal default.

#![allow(
    unused_variables,
    unused_mut,
    dead_code,
    clippy::collapsible_if,
    clippy::collapsible_else_if,
    clippy::needless_return
)]

use super::super::model::op::{
    CCALL, CCAND, CCAQALL, CCAQAND, CCAQCHOOCE, CCAQSOME, CCATLEAST, CCATMOST, CCATOM, CCBACKACTIVIMPL,
    CCBACKACTIVTRIG, CCBOTTOM, CCBRANCHALL, CCBRANCHAQALL, CCBRANCHAQAND, CCBRANCHIMPL,
    CCBRANCHTRIG, CCDATALITERAL, CCDATALITERALIMPLI, CCDATARESTRICTION, CCDATARESTRICTIONIMPLI,
    CCDATATYPE, CCDATATYPEIMPLI, CCEQ, CCIMPL, CCIMPLALL, CCIMPLAQALL, CCIMPLAQAND, CCIMPLTRIG,
    CCNOMINAL, CCNOMINALIMPLI, CCOR, CCPBINDALL, CCPBINDAND, CCPBINDAQAND, CCPBINDCYCLE,
    CCPBINDGROUND, CCPBINDIMPL, CCPBINDTRIG, CCPBINDVARIABLE, CCSELF, CCSOME, CCSUB, CCTOP,
    CCVALUE, CCVARBINDALL, CCVARBINDAND, CCVARBINDAQALL, CCVARBINDAQAND, CCVARBINDFINALZE,
    CCVARBINDGROUND, CCVARBINDIMPL, CCVARBINDJOIN, CCVARBINDPREPARE, CCVARBINDTRIG,
    CCVARBINDVARIABLE, CCVARPBACKAQALL, CCVARPBACKAQAND, CCVARPBACKALL, CCVARPBACKTRIG,
};
use super::super::model::ontology::OntologyArenas;
use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::ConceptId;
use super::super::process::context::ProcessContext;
use super::super::process::descriptor::ConceptProcessPriority;
use super::super::process::node::IndividualProcessNodePriority;
use super::super::process::{ConDescId, ConProcDescId, NodeId};
use super::stubs::SatisfiableCalculationTask;

// KONCLUDE-PORT-NOTE[api]: `CSatisfiableCalculationTask*` task handles + the
// `CDisjunctBranchingStatistics*` / `CSortedNegLinker<CConcept*>*` /
// `CPROCESSINGLIST<…>*` arguments belong to the Task / Ontology layers that are
// not yet ported. Until they land, a task pointer is an `Id<SatisfiableCalculationTask>`
// (the `completion::stubs` marker; `Id::NONE` == `nullptr`), a single sorted-neg
// linker element is a `NegLink<ConceptId>` (`getData()` -> `.target`,
// `isNegated()` -> `.negated`), and the branch-statistics / disjunct-list pointers
// are opaque `Cint64` handles (`INVALID` == `nullptr`).
type SatCalcTaskId = Id<SatisfiableCalculationTask>;

// ===========================================================================
// STR-1 — concept-processing priority (`CConceptProcessingPriorityStrategy`)
// ===========================================================================

/// Port of `CConcreteConceptProcessingOperatorPriorityStrategy`.
///
/// THE substantive strategy: a FaCT++-`IAOEFLG`-style operator-code -> priority
/// table. C++ keeps `double priorities[200]` plus the interior alias
/// `symAccessPri = priorities + priCount/2` so signed concept op-codes index
/// +/-100 around the array midpoint.
pub struct ConcreteConceptProcessingOperatorPriorityStrategy {
    /// Port of `priCount` (always 200).
    pri_count: Cint64,
    /// Port of `double *priorities` (the owned 200-slot table).
    ///
    /// KONCLUDE-PORT-NOTE[pointer-alias]: C++ heap-allocates `new double[200]`
    /// and stores `symAccessPri = priorities + 100`. Ported as an owned
    /// `[f64; 200]` with the alias replaced by index arithmetic
    /// (`priorities[(priCount/2 + code) as usize]`) in `set_sym` / `sym`.
    priorities: [f64; 200],
    /// Port of `mDisjDelConsidPriOffset`.
    disj_del_consid_pri_offset: f64,
    /// Port of `mDisjDelProcessPriOffset`.
    disj_del_process_pri_offset: f64,
    /// Port of `mVariableBindingsPreparationDelaying`.
    variable_bindings_preparation_delaying: bool,
}

impl ConcreteConceptProcessingOperatorPriorityStrategy {
    /// Port of `CConcreteConceptProcessingOperatorPriorityStrategy::set` access to
    /// `symAccessPri[code] = priority`. See the `priorities` field
    /// `[pointer-alias]` note: `symAccessPri = priorities + priCount/2`.
    #[inline]
    fn set_sym(&mut self, code: Cint64, priority: Cint64) {
        self.priorities[(self.pri_count / 2 + code) as usize] = priority as f64;
    }

    /// Port of `symAccessPri[code]` read (same `[pointer-alias]` index arithmetic).
    #[inline]
    fn sym(&self, code: Cint64) -> f64 {
        self.priorities[(self.pri_count / 2 + code) as usize]
    }

    /// Port of `CConcreteConceptProcessingOperatorPriorityStrategy::CConcreteConceptProcessingOperatorPriorityStrategy`.
    ///
    /// Fills the priority table verbatim; the FaCT++ `IAOEFLG` comment block from
    /// the C++ ctor is preserved.
    pub fn new() -> Self {
        // priCount = 200; priorities = new double[200] (zeroed); symAccessPri = priorities+100.
        let mut s = ConcreteConceptProcessingOperatorPriorityStrategy {
            pri_count: 200,
            priorities: [0.0; 200],
            disj_del_consid_pri_offset: 0.0,
            disj_del_process_pri_offset: 0.0,
            variable_bindings_preparation_delaying: false,
        };

        // The following priorities are similar to the FaCT++ standard IAOEFLG
        // options and have the same meaning.
        //
        // FaCT++ register "IAOEFLG" option:
        // Option 'IAOEFLG' define the priorities of different operations in TODO
        // list. Possible values are 7-digit strings with only possible digit are
        // 0-6. The digits on the places 1, 2, ..., 7 are for priority of Id, And,
        // Or, Exists, Forall, LE and GE operations respectively. The smaller
        // number means the higher priority. All other constructions (TOP, BOTTOM,
        // etc) has priority 0.
        //
        // The operations are ordered in a priority queue and are applied also from
        // lower to highest priority.
        //   symAccessPri[CCATOM]    = 2;
        //   symAccessPri[CCAND]     = 3;
        //   symAccessPri[CCOR]      = 7;
        //   symAccessPri[CCSOME]    = 4;
        //   symAccessPri[CCALL]     = 1;
        //   symAccessPri[CCATLEAST] = 1;
        //   symAccessPri[CCATMOST]  = 6;
        let mut next_priority: Cint64 = 14;

        s.set_sym(CCTOP, next_priority);
        s.set_sym(-CCBOTTOM, next_priority);
        s.set_sym(CCATOM, next_priority);
        s.set_sym(-CCATOM, next_priority);

        next_priority = 13;

        s.set_sym(CCAND, next_priority);
        s.set_sym(-CCOR, next_priority);
        s.set_sym(CCSUB, next_priority);
        s.set_sym(CCEQ, next_priority);
        s.set_sym(CCIMPLTRIG, next_priority);
        s.set_sym(CCBRANCHTRIG, next_priority);
        s.set_sym(CCPBINDTRIG, next_priority);
        s.set_sym(CCPBINDAND, next_priority);
        s.set_sym(CCVARBINDTRIG, next_priority);
        s.set_sym(CCVARBINDAND, next_priority);
        s.set_sym(CCVARPBACKTRIG, next_priority);
        s.set_sym(CCBACKACTIVTRIG, next_priority);

        s.set_sym(CCVARBINDPREPARE, next_priority);
        s.set_sym(CCVARBINDFINALZE, next_priority);

        s.set_sym(CCOR, next_priority);
        s.set_sym(-CCAND, next_priority);
        s.set_sym(-CCEQ, next_priority);
        s.set_sym(CCDATATYPE, next_priority);
        s.set_sym(-CCDATATYPE, next_priority);
        s.set_sym(CCDATALITERAL, next_priority);
        s.set_sym(-CCDATALITERAL, next_priority);
        s.set_sym(CCDATARESTRICTION, next_priority);
        s.set_sym(-CCDATARESTRICTION, next_priority);

        s.disj_del_consid_pri_offset = -9.0;
        s.disj_del_process_pri_offset = -11.5;

        next_priority = 12;

        s.set_sym(CCALL, next_priority);
        s.set_sym(-CCSOME, next_priority);
        s.set_sym(CCAQALL, next_priority);
        s.set_sym(CCIMPLALL, next_priority);
        s.set_sym(CCBRANCHALL, next_priority);
        s.set_sym(CCIMPLAQALL, next_priority);
        s.set_sym(CCBRANCHAQALL, next_priority);
        s.set_sym(CCPBINDALL, next_priority);
        s.set_sym(CCVARBINDALL, next_priority);
        s.set_sym(CCVARBINDAQALL, next_priority);
        s.set_sym(CCVARPBACKAQALL, next_priority);
        s.set_sym(CCVARPBACKALL, next_priority);

        next_priority = 11;

        s.set_sym(CCAQAND, next_priority);
        s.set_sym(CCIMPLAQAND, next_priority);
        s.set_sym(CCBRANCHAQAND, next_priority);
        s.set_sym(CCPBINDAQAND, next_priority);
        s.set_sym(CCVARBINDAQAND, next_priority);
        s.set_sym(CCVARPBACKAQAND, next_priority);

        next_priority = 10;

        s.set_sym(CCAQCHOOCE, next_priority);
        s.set_sym(-CCAQCHOOCE, next_priority);

        next_priority = 9;

        s.set_sym(CCIMPL, next_priority);
        s.set_sym(CCNOMINALIMPLI, next_priority);
        s.set_sym(CCDATATYPEIMPLI, next_priority);
        s.set_sym(CCDATALITERALIMPLI, next_priority);
        s.set_sym(CCDATARESTRICTIONIMPLI, next_priority);
        s.set_sym(CCBRANCHIMPL, next_priority);
        s.set_sym(CCPBINDIMPL, next_priority);
        s.set_sym(CCPBINDVARIABLE, next_priority);
        s.set_sym(CCPBINDCYCLE, next_priority);
        s.set_sym(CCVARBINDJOIN, next_priority);
        s.set_sym(CCVARBINDVARIABLE, next_priority);
        s.set_sym(CCBACKACTIVIMPL, next_priority);
        s.set_sym(CCVARBINDIMPL, next_priority);

        next_priority = 8;
        s.set_sym(CCSELF, next_priority);
        s.set_sym(-CCSELF, next_priority);
        s.set_sym(CCVALUE, next_priority);
        s.set_sym(-CCVALUE, next_priority);

        // intermediately processing limit

        next_priority = 7;

        s.set_sym(CCNOMINAL, next_priority);
        s.set_sym(-CCNOMINAL, next_priority);

        next_priority = 6;

        s.set_sym(CCPBINDGROUND, next_priority);
        s.set_sym(CCVARBINDGROUND, next_priority);
        s.set_sym(-CCPBINDGROUND, next_priority);
        s.set_sym(-CCVARBINDGROUND, next_priority);

        next_priority = 5;

        s.set_sym(CCATLEAST, next_priority);
        s.set_sym(-CCATMOST, next_priority);

        next_priority = 4;

        s.set_sym(CCSOME, next_priority);
        s.set_sym(-CCALL, next_priority);
        s.set_sym(CCAQSOME, next_priority);

        // deterministic processing limit

        next_priority = 3;

        s.set_sym(CCATMOST, next_priority);
        s.set_sym(-CCATLEAST, next_priority);

        next_priority = 2;

        // disjunctions + processing offsets

        s.variable_bindings_preparation_delaying = false;

        s
    }

    /// Port of `CConcreteConceptProcessingOperatorPriorityStrategy::readCalculationConfig`.
    pub fn read_calculation_config(&mut self, sat_calc_task: SatCalcTaskId) {
        self.variable_bindings_preparation_delaying = false;
        // W6-DEFER[api]: CCalculationConfigurationExtension *config =
        //     satCalcTask->getCalculationConfiguration();
        // (read but unused after; the Task layer + config extension are not ported)
        //
        // W6-DEFER[api]: the answerer-propagation-steering reach (Task + answerer
        // layers not yet ported) sets the delaying flag:
        //   CSatisfiableTaskAnswererBindingPropagationAdapter* answererMessageAdapter
        //       = satCalcTask->getSatisfiableAnswererBindingPropagationAdapter();
        //   if (answererMessageAdapter) {
        //       CAnsweringPropagationSteeringController* propagationSteeringController
        //           = answererMessageAdapter->getAnswererPropagationSteeringController();
        //       if (propagationSteeringController) {
        //           if (propagationSteeringController->finalizeWithClashing()) {
        //               mVariableBindingsPreparationDelaying = true;
        //           }
        //       }
        //   }
    }

    /// Port of `CConcreteConceptProcessingOperatorPriorityStrategy::getPriorityOffsetForDisjunctionDelayedConsidering`.
    pub fn get_priority_offset_for_disjunction_delayed_considering(
        &self,
        concept_descriptor: ConDescId,
        individual: NodeId,
    ) -> f64 {
        self.disj_del_consid_pri_offset
    }

    /// Port of `CConcreteConceptProcessingOperatorPriorityStrategy::getPriorityOffsetForDisjunctionDelayedProcessing`.
    pub fn get_priority_offset_for_disjunction_delayed_processing(
        &self,
        concept_descriptor: ConDescId,
        individual: NodeId,
    ) -> f64 {
        self.disj_del_process_pri_offset
    }

    /// Port of `CConcreteConceptProcessingOperatorPriorityStrategy::getPriorityForConcept`.
    pub fn get_priority_for_concept(
        &self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        concept_descriptor: ConDescId,
        individual: NodeId,
    ) -> ConceptProcessPriority {
        // qint64 cCode = conceptDescriptor->getData()->getOperatorCode();
        // (CConceptDescriptor::getData() == getConcept() -> the CConcept* operand.)
        let mut c_code: Cint64 = onto
            .concept(ctx.con_desc(concept_descriptor).get_concept())
            .get_operator_code();
        let mut negated = false;
        if ctx.con_desc(concept_descriptor).is_negated() {
            c_code *= -1;
            negated = true;
        }
        let mut priority: f64 = 0.0;
        priority = self.sym(c_code);

        if c_code == CCVARBINDPREPARE {
            // if (!conceptDescriptor->getData()->getVariable())
            if onto
                .concept(ctx.con_desc(concept_descriptor).get_concept())
                .get_variable()
                .is_none()
            {
                if self.variable_bindings_preparation_delaying {
                    priority = 3.5;
                } else if !ctx.node(individual).is_nominal_individual_node() {
                    priority = 3.5;
                }
            }
        }

        // CSortedNegLinker<CConcept *> *opConLinkerIt = conceptDescriptor->getData()->getOperandList();
        // (`!opConLinkerIt` -> the operand list is empty / null.)
        let op_con_linker_empty = onto
            .concept(ctx.con_desc(concept_descriptor).get_concept())
            .get_operand_list()
            .is_empty();
        if c_code == CCATMOST {
            let mut param: Cint64 = onto
                .concept(ctx.con_desc(concept_descriptor).get_concept())
                .get_parameter();
            param = param - 1 * (negated as Cint64);
            if param <= 1 && op_con_linker_empty {
                priority = 5.5;
            } else {
                let priority_offset = (-(param as f64) / 1000.0).exp() * 0.5;
                priority += priority_offset;
            }
        } else if c_code == CCATLEAST {
            let mut param: Cint64 = onto
                .concept(ctx.con_desc(concept_descriptor).get_concept())
                .get_parameter();
            param = param + 1 * (negated as Cint64);
            if param <= 2 && op_con_linker_empty {
                priority = 5.0;
            } else {
                let priority_offset = (1.0 - (-(param as f64) / 1000.0).exp()) * 0.5;
                priority += priority_offset;
            }
        }
        ConceptProcessPriority::new(priority)
    }
}

impl Default for ConcreteConceptProcessingOperatorPriorityStrategy {
    fn default() -> Self {
        Self::new()
    }
}

/// Port of the `CConceptProcessingPriorityStrategy` interface (one concrete:
/// `CConcreteConceptProcessingOperatorPriorityStrategy`).
///
/// Tagged-enum dispatch supersedes the abstract base's pure virtuals; the empty
/// abstract `.cpp` bodies contribute nothing beyond the dispatch surface.
pub enum ConceptProcessingPriorityStrategy {
    /// Port of `CConcreteConceptProcessingOperatorPriorityStrategy`.
    ConcreteOperator(ConcreteConceptProcessingOperatorPriorityStrategy),
}

impl ConceptProcessingPriorityStrategy {
    /// The single concrete the engine constructs
    /// (`mConceptPriorityStrategy = new CConcreteConceptProcessingOperatorPriorityStrategy()`).
    pub fn new_concrete_operator() -> Self {
        ConceptProcessingPriorityStrategy::ConcreteOperator(
            ConcreteConceptProcessingOperatorPriorityStrategy::new(),
        )
    }

    /// Port of `CConceptProcessingPriorityStrategy::readCalculationConfig`.
    pub fn read_calculation_config(&mut self, sat_calc_task: SatCalcTaskId) {
        match self {
            Self::ConcreteOperator(s) => s.read_calculation_config(sat_calc_task),
        }
    }

    /// Port of `CConceptProcessingPriorityStrategy::getPriorityForConcept`.
    pub fn get_priority_for_concept(
        &self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        concept_descriptor: ConDescId,
        individual: NodeId,
    ) -> ConceptProcessPriority {
        match self {
            Self::ConcreteOperator(s) => {
                s.get_priority_for_concept(ctx, onto, concept_descriptor, individual)
            }
        }
    }

    /// Port of `CConceptProcessingPriorityStrategy::getPriorityOffsetForDisjunctionDelayedConsidering`.
    pub fn get_priority_offset_for_disjunction_delayed_considering(
        &self,
        concept_descriptor: ConDescId,
        individual: NodeId,
    ) -> f64 {
        match self {
            Self::ConcreteOperator(s) => {
                s.get_priority_offset_for_disjunction_delayed_considering(concept_descriptor, individual)
            }
        }
    }

    /// Port of `CConceptProcessingPriorityStrategy::getPriorityOffsetForDisjunctionDelayedProcessing`.
    pub fn get_priority_offset_for_disjunction_delayed_processing(
        &self,
        concept_descriptor: ConDescId,
        individual: NodeId,
    ) -> f64 {
        match self {
            Self::ConcreteOperator(s) => {
                s.get_priority_offset_for_disjunction_delayed_processing(concept_descriptor, individual)
            }
        }
    }
}

// ===========================================================================
// STR-2 — individual-processing priority (`CIndividualProcessingPriorityStrategy`)
// KONCLUDE-PORT-NOTE[api]: DORMANT in this build — `getPriorityForIndividual` has
// no call site anywhere in `Reasoner/` (only `configureStrategy` is invoked).
// Ported for fidelity; flagged currently-unreached.
// ===========================================================================

/// Port of `CIndividualAncestorDepthMaximumConceptProcessingPriorityStrategy`.
///
/// (Filename says "ConceptProcessing" but it extends the *individual* interface.)
pub struct IndividualAncestorDepthMaximumConceptProcessingPriorityStrategy {
    /// Port of `mStrictIndiNodeProcessing`.
    strict_indi_node_processing: bool,
    /// Port of `mAddIDIndiPriorization`.
    add_id_indi_priorization: bool,
}

impl IndividualAncestorDepthMaximumConceptProcessingPriorityStrategy {
    /// Port of `CIndividualAncestorDepthMaximumConceptProcessingPriorityStrategy::CIndividualAncestorDepthMaximumConceptProcessingPriorityStrategy`.
    pub fn new() -> Self {
        IndividualAncestorDepthMaximumConceptProcessingPriorityStrategy {
            strict_indi_node_processing: false,
            add_id_indi_priorization: false,
        }
    }

    /// Port of `CIndividualAncestorDepthMaximumConceptProcessingPriorityStrategy::configureStrategy`.
    pub fn configure_strategy(
        &mut self,
        strict_indi_node_processing: bool,
        additional_id_indi_priorization: bool,
    ) {
        self.strict_indi_node_processing = strict_indi_node_processing;
        self.add_id_indi_priorization = additional_id_indi_priorization;
    }

    /// Port of `CIndividualAncestorDepthMaximumConceptProcessingPriorityStrategy::getPriorityForIndividual`.
    pub fn get_priority_for_individual(
        &self,
        ctx: &ProcessContext,
        individual: NodeId,
    ) -> IndividualProcessNodePriority {
        let mut con_priority: f64 = 0.0;
        // W6-DEFER[api]: CConceptProcessingQueue* conProQueue =
        //     individual->getConceptProcessingQueue(false);
        // if (conProQueue) {
        //     CConceptProcessPriority conProPriority;
        //     if (conProQueue->getNextConceptProcessPriority(&conProPriority)) {
        //         conPriority = conProPriority.getPriority();
        //     }
        // }
        // The CConceptProcessingQueue satellite (a `process::stubs` marker) and its
        // getNextConceptProcessPriority are not yet ported; the branch is preserved
        // and con_priority stays 0.

        // double indiPriority = individual->getIndividualAncestorDepth();
        let mut indi_priority: f64 = ctx.node(individual).individual_ancestor_depth() as f64;
        if self.add_id_indi_priorization {
            indi_priority +=
                -1.0 / ((10 + ctx.node(individual).individual_node_id()) as f64) + 0.1;
        }
        // return CIndividualProcessNodePriority(conPriority, indiPriority, mStrictIndiNodeProcessing);
        IndividualProcessNodePriority {
            priority_con: con_priority,
            priority_ind: indi_priority,
            strict_order: self.strict_indi_node_processing,
        }
    }
}

impl Default for IndividualAncestorDepthMaximumConceptProcessingPriorityStrategy {
    fn default() -> Self {
        Self::new()
    }
}

/// Port of the `CIndividualProcessingPriorityStrategy` interface (one concrete:
/// `CIndividualAncestorDepthMaximumConceptProcessingPriorityStrategy`).
pub enum IndividualProcessingPriorityStrategy {
    /// Port of `CIndividualAncestorDepthMaximumConceptProcessingPriorityStrategy`.
    AncestorDepthMaximum(IndividualAncestorDepthMaximumConceptProcessingPriorityStrategy),
}

impl IndividualProcessingPriorityStrategy {
    /// The single concrete the engine constructs
    /// (`mIndiAncDepthMasConProcPriStr = new CIndividualAncestorDepthMaximum…()`).
    pub fn new_ancestor_depth_maximum() -> Self {
        IndividualProcessingPriorityStrategy::AncestorDepthMaximum(
            IndividualAncestorDepthMaximumConceptProcessingPriorityStrategy::new(),
        )
    }

    /// Port of `CIndividualAncestorDepthMaximumConceptProcessingPriorityStrategy::configureStrategy`.
    pub fn configure_strategy(
        &mut self,
        strict_indi_node_processing: bool,
        additional_id_indi_priorization: bool,
    ) {
        match self {
            Self::AncestorDepthMaximum(s) => {
                s.configure_strategy(strict_indi_node_processing, additional_id_indi_priorization)
            }
        }
    }

    /// Port of `CIndividualProcessingPriorityStrategy::getPriorityForIndividual` (DORMANT).
    pub fn get_priority_for_individual(
        &self,
        ctx: &ProcessContext,
        individual: NodeId,
    ) -> IndividualProcessNodePriority {
        match self {
            Self::AncestorDepthMaximum(s) => s.get_priority_for_individual(ctx, individual),
        }
    }
}

// ===========================================================================
// STR-3 — task-processing priority (`CTaskProcessingPriorityStrategy`)
// ===========================================================================

/// Port of `CEqualDepthTaskProcessingPriorityStrategy`.
///
/// Stateless base concrete; all four methods are `parentDepth + 1.` with small
/// `+0.1` / `-branchNumber/(10*maxBranchCount)` tweaks.
pub struct EqualDepthTaskProcessingPriorityStrategy;

impl EqualDepthTaskProcessingPriorityStrategy {
    /// Port of `CEqualDepthTaskProcessingPriorityStrategy::CEqualDepthTaskProcessingPriorityStrategy`.
    pub fn new() -> Self {
        EqualDepthTaskProcessingPriorityStrategy
    }

    /// Port of `CEqualDepthTaskProcessingPriorityStrategy::getPriorityForTaskBranching`.
    pub fn get_priority_for_task_branching(
        &self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        branching_task: SatCalcTaskId,
        parent_task: SatCalcTaskId,
        indi_process_node: NodeId,
        branching_concept: ConDescId,
        branched_concept: NegLink<ConceptId>,
        branch_number: Cint64,
        branch_stats: Cint64,
    ) -> f64 {
        // W6-DEFER[api]: double parentDepth = parentTask->getTaskDepth();
        let parent_depth: f64 = 0.0;
        let mut priority: f64 = 0.0;
        // double maxBranchCount = branchingConcept->getConcept()->getOperandCount();
        let max_branch_count: f64 = onto
            .concept(ctx.con_desc(branching_concept).get_concept())
            .get_operand_count() as f64;
        // W6-DEFER[api]: double parentPriority = parentTask->getTaskPriority();
        let parent_priority: f64 = 0.0;
        // priority = parentDepth + 1. + (0.1 - branchNumber / ((1+parentDepth) * 10 * maxBranchCount));
        priority = parent_depth
            + 1.0
            + (0.1 - branch_number as f64 / (10.0 * max_branch_count));
        priority
    }

    /// Port of `CEqualDepthTaskProcessingPriorityStrategy::getPriorityForTaskQualifing`.
    pub fn get_priority_for_task_qualifing(
        &self,
        branching_task: SatCalcTaskId,
        parent_task: SatCalcTaskId,
        qualifing_negated: bool,
    ) -> f64 {
        // W6-DEFER[api]: double parentDepth = parentTask->getTaskDepth();
        let parent_depth: f64 = 0.0;
        let mut priority: f64 = 0.0;
        // W6-DEFER[api]: double parentPriority = parentTask->getTaskPriority();
        let parent_priority: f64 = 0.0;
        priority = parent_depth + 1.0;
        if qualifing_negated {
            priority += 0.1;
        }
        priority
    }

    /// Port of `CEqualDepthTaskProcessingPriorityStrategy::getPriorityForTaskMerging`.
    pub fn get_priority_for_task_merging(
        &self,
        branching_task: SatCalcTaskId,
        parent_task: SatCalcTaskId,
    ) -> f64 {
        // W6-DEFER[api]: double parentDepth = parentTask->getTaskDepth();
        let parent_depth: f64 = 0.0;
        let mut priority: f64 = 0.0;
        // W6-DEFER[api]: double parentPriority = parentTask->getTaskPriority();
        let parent_priority: f64 = 0.0;
        priority = parent_depth + 1.0;
        priority
    }

    /// Port of `CEqualDepthTaskProcessingPriorityStrategy::getPriorityForTaskReusing`.
    pub fn get_priority_for_task_reusing(
        &self,
        branching_task: SatCalcTaskId,
        parent_task: SatCalcTaskId,
        reusing_alternative: bool,
    ) -> f64 {
        // W6-DEFER[api]: double parentDepth = parentTask->getTaskDepth();
        let parent_depth: f64 = 0.0;
        let mut priority: f64 = 0.0;
        // W6-DEFER[api]: double parentPriority = parentTask->getTaskPriority();
        let parent_priority: f64 = 0.0;
        priority = parent_depth + 1.0;
        if reusing_alternative {
            priority += 0.1;
        }
        priority
    }
}

impl Default for EqualDepthTaskProcessingPriorityStrategy {
    fn default() -> Self {
        Self::new()
    }
}

/// Port of `CEqualDepthCacheOrientatedProcessingPriorityStrategy`.
///
/// Extends `CEqualDepthTaskProcessingPriorityStrategy`; overrides ONLY
/// `getPriorityForTaskBranching` (a completion-graph-cache hit check + a
/// branch-statistics learning offset). The other three task methods are
/// inherited (dispatched to the base in the enum).
pub struct EqualDepthCacheOrientatedProcessingPriorityStrategy;

impl EqualDepthCacheOrientatedProcessingPriorityStrategy {
    /// Port of `CEqualDepthCacheOrientatedProcessingPriorityStrategy::CEqualDepthCacheOrientatedProcessingPriorityStrategy`.
    pub fn new() -> Self {
        EqualDepthCacheOrientatedProcessingPriorityStrategy
    }

    /// Port of `CEqualDepthCacheOrientatedProcessingPriorityStrategy::getPriorityForTaskBranching`.
    pub fn get_priority_for_task_branching(
        &self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        branching_task: SatCalcTaskId,
        parent_task: SatCalcTaskId,
        indi_process_node: NodeId,
        branching_concept: ConDescId,
        branched_concept: NegLink<ConceptId>,
        branch_number: Cint64,
        branch_stats: Cint64,
    ) -> f64 {
        // W6-DEFER[api]: double parentDepth = parentTask->getTaskDepth();
        let parent_depth: f64 = 0.0;
        let mut priority: f64 = 0.0;
        // double maxBranchCount = branchingConcept->getConcept()->getOperandCount();
        let max_branch_count: f64 = onto
            .concept(ctx.con_desc(branching_concept).get_concept())
            .get_operand_count() as f64;
        // W6-DEFER[api]: double parentPriority = parentTask->getTaskPriority();
        let parent_priority: f64 = 0.0;

        let mut disjunct_cached = false;

        // W6-DEFER[api]: the completion-graph-cache hit check reaches the
        // Consistence model + a cached task's process databox (Consistence/model
        // + Process layers not wired here). Control flow preserved; the lookup
        // result stays `false`:
        //
        //   CConcreteOntology* ontology = branchingTask->getProcessingDataBox()->getOntology();
        //   CConsistence* consistence = ontology->getConsistence();
        //   if (consistence) {
        //       CConsistenceData* consData = consistence->getConsistenceModelData();
        //       if (consData) {
        //           CConsistenceTaskData* consTaskData = dynamic_cast<CConsistenceTaskData*>(consData);
        //           if (consTaskData) {
        //               CSatisfiableCalculationTask* compGraphCachedCalcTask =
        //                   consTaskData->getCompletionGraphCachedSatisfiableTask();
        //               if (compGraphCachedCalcTask) {
        //                   CIndividualProcessNodeVector* compGraphCachedProcNodeVec =
        //                       compGraphCachedCalcTask->getProcessingDataBox()->getIndividualProcessNodeVector();
        //                   if (indiProcessNode->getIndividualNodeID() <= compGraphCachedProcNodeVec->getItemMaxIndex()) {
        //                       CIndividualProcessNode* compIndiProcNode =
        //                           compGraphCachedProcNodeVec->getData(indiProcessNode->getIndividualNodeID());
        //                       if (compIndiProcNode && compIndiProcNode->getReapplyConceptLabelSet(false)
        //                               ->containsConcept(branchedConcept->getData(), branchedConcept->isNegated())) {
        //                           disjunctCached = true;
        //                       }
        //                   }
        //               }
        //           }
        //       }
        //   }

        let mut priority_sub_offset = 0.2;
        if disjunct_cached {
            priority_sub_offset = 0.3;
        }

        let mut learning_offset = 0.0;
        let mut branch_offset = -(branch_number as f64) / (10.0 * max_branch_count);
        // if (branchStats) — the CDisjunctBranchingStatistics* (Ontology layer)
        // is an opaque handle here; `INVALID` == nullptr.
        if branch_stats != INVALID {
            // W6-DEFER[api]: cint64 clashCount = branchStats->getClashInvolvedCount();
            let clash_count: Cint64 = 0;
            // W6-DEFER[api]: cint64 expandedCount = branchStats->getExpandedCount();
            let expanded_count: Cint64 = 0;
            // W6-DEFER[api]: cint64 satCount = branchStats->getSatisfiableOccurrenceCount();
            let sat_count: Cint64 = 0;
            if clash_count != 0 || expanded_count != 0 || sat_count != 0 {
                branch_offset = -(branch_number as f64) / (100000.0 * max_branch_count);
            }
            let mut clash_factor = 0.0;
            if expanded_count != 0 {
                clash_factor =
                    (clash_count as f64 / expanded_count as f64).min(1.0).max(0.0);
            } else if clash_count != 0 {
                clash_factor = 1.0 / (clash_count as f64 * 10.0);
            }
            let mut sat_factor = 0.0;
            if expanded_count != 0 {
                sat_factor = (sat_count as f64 / expanded_count as f64).min(1.0).max(0.0);
            } else if sat_count != 0 {
                sat_factor = 1.0 / (sat_count as f64 * 10.0);
            }
            learning_offset = 0.0;
            learning_offset += sat_factor - clash_factor;
            learning_offset = learning_offset / 10.0;
            if expanded_count != 0 {
                learning_offset += 1.0 / (expanded_count as f64 * 10000.0);
            }
        }

        priority = parent_depth + 1.0 + priority_sub_offset + learning_offset + branch_offset;
        priority
    }
}

impl Default for EqualDepthCacheOrientatedProcessingPriorityStrategy {
    fn default() -> Self {
        Self::new()
    }
}

/// Port of the `CTaskProcessingPriorityStrategy` interface (two concretes:
/// `CEqualDepthTaskProcessingPriorityStrategy` and the cache-orientated subclass
/// that overrides only `getPriorityForTaskBranching`).
///
/// The engine constructs the cache-orientated concrete
/// (`mTaskProcessingStrategy = new CEqualDepthCacheOrientatedProcessingPriorityStrategy()`;
/// the plain `CEqualDepthTask…` ctor line is commented out).
pub enum TaskProcessingPriorityStrategy {
    /// Port of `CEqualDepthTaskProcessingPriorityStrategy`.
    EqualDepth(EqualDepthTaskProcessingPriorityStrategy),
    /// Port of `CEqualDepthCacheOrientatedProcessingPriorityStrategy`.
    EqualDepthCacheOrientated(EqualDepthCacheOrientatedProcessingPriorityStrategy),
}

impl TaskProcessingPriorityStrategy {
    /// The concrete the engine constructs.
    pub fn new_equal_depth_cache_orientated() -> Self {
        TaskProcessingPriorityStrategy::EqualDepthCacheOrientated(
            EqualDepthCacheOrientatedProcessingPriorityStrategy::new(),
        )
    }

    /// Port of `CTaskProcessingPriorityStrategy::getPriorityForTaskBranching`.
    pub fn get_priority_for_task_branching(
        &self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        branching_task: SatCalcTaskId,
        parent_task: SatCalcTaskId,
        indi_process_node: NodeId,
        branching_concept: ConDescId,
        branched_concept: NegLink<ConceptId>,
        branch_number: Cint64,
        branch_stats: Cint64,
    ) -> f64 {
        match self {
            Self::EqualDepth(s) => s.get_priority_for_task_branching(
                ctx,
                onto,
                branching_task,
                parent_task,
                indi_process_node,
                branching_concept,
                branched_concept,
                branch_number,
                branch_stats,
            ),
            Self::EqualDepthCacheOrientated(s) => s.get_priority_for_task_branching(
                ctx,
                onto,
                branching_task,
                parent_task,
                indi_process_node,
                branching_concept,
                branched_concept,
                branch_number,
                branch_stats,
            ),
        }
    }

    /// Port of `CTaskProcessingPriorityStrategy::getPriorityForTaskQualifing`.
    pub fn get_priority_for_task_qualifing(
        &self,
        branching_task: SatCalcTaskId,
        parent_task: SatCalcTaskId,
        qualifing_negated: bool,
    ) -> f64 {
        match self {
            Self::EqualDepth(s) => {
                s.get_priority_for_task_qualifing(branching_task, parent_task, qualifing_negated)
            }
            // INHERITED from CEqualDepthTaskProcessingPriorityStrategy.
            Self::EqualDepthCacheOrientated(_) => EqualDepthTaskProcessingPriorityStrategy
                .get_priority_for_task_qualifing(branching_task, parent_task, qualifing_negated),
        }
    }

    /// Port of `CTaskProcessingPriorityStrategy::getPriorityForTaskMerging`.
    pub fn get_priority_for_task_merging(
        &self,
        branching_task: SatCalcTaskId,
        parent_task: SatCalcTaskId,
    ) -> f64 {
        match self {
            Self::EqualDepth(s) => s.get_priority_for_task_merging(branching_task, parent_task),
            // INHERITED from CEqualDepthTaskProcessingPriorityStrategy.
            Self::EqualDepthCacheOrientated(_) => EqualDepthTaskProcessingPriorityStrategy
                .get_priority_for_task_merging(branching_task, parent_task),
        }
    }

    /// Port of `CTaskProcessingPriorityStrategy::getPriorityForTaskReusing`.
    pub fn get_priority_for_task_reusing(
        &self,
        branching_task: SatCalcTaskId,
        parent_task: SatCalcTaskId,
        reusing_alternative: bool,
    ) -> f64 {
        match self {
            Self::EqualDepth(s) => {
                s.get_priority_for_task_reusing(branching_task, parent_task, reusing_alternative)
            }
            // INHERITED from CEqualDepthTaskProcessingPriorityStrategy.
            Self::EqualDepthCacheOrientated(_) => EqualDepthTaskProcessingPriorityStrategy
                .get_priority_for_task_reusing(branching_task, parent_task, reusing_alternative),
        }
    }
}

// ===========================================================================
// STR-4 — unsatisfiable-cache retrieval (`CUnsatisfiableCacheRetrievalStrategy`)
// ===========================================================================

/// Port of `CGenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy`.
///
/// Trivial policy: `testUnsatisfiableCacheForProcessing` -> `false`, the other
/// six -> `true`. Stateless.
pub struct GenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy;

impl GenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy {
    /// Port of `CGenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy::CGenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy`.
    pub fn new() -> Self {
        GenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy
    }

    /// Port of `…::testUnsatisfiableCacheForProcessing`.
    pub fn test_unsatisfiable_cache_for_processing(
        &self,
        con_pro_des: ConProcDescId,
        indi: NodeId,
    ) -> bool {
        false
    }

    /// Port of `…::testUnsatisfiableCacheForDisjunctionBranching`.
    ///
    /// `disjunctList` (`CPROCESSINGLIST<CSortedNegLinker<CConcept*>*>*`) is an
    /// opaque handle here (Process/Ontology list not yet ported).
    pub fn test_unsatisfiable_cache_for_disjunction_branching(
        &self,
        con_pro_des: ConProcDescId,
        indi: NodeId,
        disjunct_list: Cint64,
    ) -> bool {
        true
    }

    /// Port of `…::testUnsatisfiableCacheForMergingInitialization`.
    pub fn test_unsatisfiable_cache_for_merging_initialization(
        &self,
        con_pro_des: ConProcDescId,
        indi: NodeId,
    ) -> bool {
        true
    }

    /// Port of `…::testUnsatisfiableCacheForSuccessorGeneration`.
    pub fn test_unsatisfiable_cache_for_successor_generation(
        &self,
        con_pro_des: ConProcDescId,
        indi: NodeId,
    ) -> bool {
        true
    }

    /// Port of `…::testUnsatisfiableCacheForBranchedDisjuncts`.
    pub fn test_unsatisfiable_cache_for_branched_disjuncts(
        &self,
        con_pro_des: ConProcDescId,
        indi: NodeId,
        or_disjunct_concept: NegLink<ConceptId>,
    ) -> bool {
        true
    }

    /// Port of `…::testUnsatisfiableCacheForMergedIndividualNodes`.
    pub fn test_unsatisfiable_cache_for_merged_individual_nodes(
        &self,
        con_pro_des: ConProcDescId,
        indi: NodeId,
        merged_indi: NodeId,
    ) -> bool {
        true
    }

    /// Port of `…::testUnsatisfiableCacheForQualifiedIndividualNodes`.
    pub fn test_unsatisfiable_cache_for_qualified_individual_nodes(
        &self,
        con_pro_des: ConProcDescId,
        indi: NodeId,
        merged_indi: NodeId,
    ) -> bool {
        true
    }
}

impl Default for GenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy {
    fn default() -> Self {
        Self::new()
    }
}

/// Port of the `CUnsatisfiableCacheRetrievalStrategy` interface (one concrete:
/// `CGenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy`).
pub enum UnsatisfiableCacheRetrievalStrategy {
    /// Port of `CGenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy`.
    GenerativeNonDeterministic(GenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy),
}

impl UnsatisfiableCacheRetrievalStrategy {
    /// The single concrete the engine constructs
    /// (`mUnsatCachRetStrategy = new CGenerativeNonDeterministic…()`).
    pub fn new_generative_non_deterministic() -> Self {
        UnsatisfiableCacheRetrievalStrategy::GenerativeNonDeterministic(
            GenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy::new(),
        )
    }

    /// Port of `CUnsatisfiableCacheRetrievalStrategy::testUnsatisfiableCacheForProcessing`.
    pub fn test_unsatisfiable_cache_for_processing(
        &self,
        con_pro_des: ConProcDescId,
        indi: NodeId,
    ) -> bool {
        match self {
            Self::GenerativeNonDeterministic(s) => {
                s.test_unsatisfiable_cache_for_processing(con_pro_des, indi)
            }
        }
    }

    /// Port of `CUnsatisfiableCacheRetrievalStrategy::testUnsatisfiableCacheForDisjunctionBranching`.
    pub fn test_unsatisfiable_cache_for_disjunction_branching(
        &self,
        con_pro_des: ConProcDescId,
        indi: NodeId,
        disjunct_list: Cint64,
    ) -> bool {
        match self {
            Self::GenerativeNonDeterministic(s) => {
                s.test_unsatisfiable_cache_for_disjunction_branching(con_pro_des, indi, disjunct_list)
            }
        }
    }

    /// Port of `CUnsatisfiableCacheRetrievalStrategy::testUnsatisfiableCacheForMergingInitialization`.
    pub fn test_unsatisfiable_cache_for_merging_initialization(
        &self,
        con_pro_des: ConProcDescId,
        indi: NodeId,
    ) -> bool {
        match self {
            Self::GenerativeNonDeterministic(s) => {
                s.test_unsatisfiable_cache_for_merging_initialization(con_pro_des, indi)
            }
        }
    }

    /// Port of `CUnsatisfiableCacheRetrievalStrategy::testUnsatisfiableCacheForSuccessorGeneration`.
    pub fn test_unsatisfiable_cache_for_successor_generation(
        &self,
        con_pro_des: ConProcDescId,
        indi: NodeId,
    ) -> bool {
        match self {
            Self::GenerativeNonDeterministic(s) => {
                s.test_unsatisfiable_cache_for_successor_generation(con_pro_des, indi)
            }
        }
    }

    /// Port of `CUnsatisfiableCacheRetrievalStrategy::testUnsatisfiableCacheForBranchedDisjuncts`.
    pub fn test_unsatisfiable_cache_for_branched_disjuncts(
        &self,
        con_pro_des: ConProcDescId,
        indi: NodeId,
        or_disjunct_concept: NegLink<ConceptId>,
    ) -> bool {
        match self {
            Self::GenerativeNonDeterministic(s) => {
                s.test_unsatisfiable_cache_for_branched_disjuncts(con_pro_des, indi, or_disjunct_concept)
            }
        }
    }

    /// Port of `CUnsatisfiableCacheRetrievalStrategy::testUnsatisfiableCacheForMergedIndividualNodes`.
    pub fn test_unsatisfiable_cache_for_merged_individual_nodes(
        &self,
        con_pro_des: ConProcDescId,
        indi: NodeId,
        merged_indi: NodeId,
    ) -> bool {
        match self {
            Self::GenerativeNonDeterministic(s) => {
                s.test_unsatisfiable_cache_for_merged_individual_nodes(con_pro_des, indi, merged_indi)
            }
        }
    }

    /// Port of `CUnsatisfiableCacheRetrievalStrategy::testUnsatisfiableCacheForQualifiedIndividualNodes`.
    pub fn test_unsatisfiable_cache_for_qualified_individual_nodes(
        &self,
        con_pro_des: ConProcDescId,
        indi: NodeId,
        merged_indi: NodeId,
    ) -> bool {
        match self {
            Self::GenerativeNonDeterministic(s) => {
                s.test_unsatisfiable_cache_for_qualified_individual_nodes(con_pro_des, indi, merged_indi)
            }
        }
    }
}
