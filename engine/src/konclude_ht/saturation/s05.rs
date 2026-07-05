//! `saturation::s05` — Datatype / data-literal saturation rules (port unit #5 of 12).
//!
//! Faithful port of the datatype rule group of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`
//! (manifest `03-saturation-calc.md`, PU-SAT-5 "Datatype rules"; cpp ranges
//! 5760–5803, 5806–5970, 5998–6002):
//!
//!   * `applyDATATYPERule`     (cpp 5760–5793),
//!   * `applyDATALITERALRule`  (cpp 5795–5803),
//!   * `handleDatatypeValueSpaceTriggers`    (cpp 5806–5823),
//!   * `tryHandleDatatypeValueSpaceTriggers` (cpp 5826–5846),
//!   * `associateDataLiteralWithNode`        (cpp 5850–5970),
//!   * `applyNotDATATYPERule`  (cpp 5998–6002).
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauApproximationSaturationTaskHandleAlgorithm`, so it becomes
//! `&mut self`. The C++ `CIndividualSaturationProcessNode*& processIndi` in/out
//! pointer-reference becomes `&mut SatNodeId` (an arena id into the per-test
//! `sat_nodes` pool); the `CConceptSaturationProcessLinker* conProLinker` becomes
//! `ConceptSaturationProcessLinkerId` (a `process::stubs` marker id). `CDatatype*`
//! / `CDataLiteral*` / `CDatatypeValueSpaceTriggers*` / `CDatatypeValueSpacesTriggers*`
//! are unported ontology datatype-model classes; matching `model/concept.rs`
//! (`mDatatype`/`mDataLiteral` are opaque `Cint64`), they are carried as opaque
//! `Cint64` (sentinel `INVALID` == `nullptr`).
//!
//! KONCLUDE-PORT-NOTE[pointer-alias]: the C++ `apply*Rule` signatures take only
//! `(processIndi, conProLinker)` and reach the context through the `mCalcAlgContext`
//! member (which the struct wave aliased to an opaque `Cint64`, so it cannot resolve
//! arenas). Per the port-wide context convention, the shared
//! `CCalculationAlgorithmContextBase*` is threaded explicitly as a trailing
//! `calc_alg_context: &mut CalculationAlgorithmContextBase` on EVERY method here
//! (the three `handle/try/associate` helpers already declare it in C++). Sibling
//! `apply*Rule` / status-flag / queue methods land in other `s01..s12` units and
//! are called as `self.x(...)`.
//!
//! KONCLUDE-PORT-NOTE[api]: this rule group bottoms out in two not-yet-ported
//! subsystems, both flagged inline `// W4-DEFER[api]`:
//!   1. the per-node datatype satellite `CSaturationIndividualNodeDatatypeData`
//!      (reached via `processIndi->getAppliedDatatypeData(create)`; its
//!      get/set-AppliedDatatype / get/set-AppliedDataLiteral accessors gate the
//!      applied-value bookkeeping), and
//!   2. the ontology datatype value-space-trigger model
//!      (`CDatatypeValueSpacesTriggers` / `CDatatypeValueSpaceTriggers` /
//!      `CDatatypeValueSpaceStringTriggers`) plus the `CDataLiteral` /
//!      `CDataLiteralValue` (+ Boolean/Float/Double/String/Real subtype) value
//!      classes whose `dynamic_cast` ladder decides datatype-value validity.
//! The descriptor→concept resolution (`conProLinker->getConceptSaturationDescriptor()
//! ->getConcept()`) likewise routes through the `process::stubs` markers
//! `CConceptSaturationProcessLinker` / `CConceptSaturationDescriptor`. Control flow
//! is transcribed faithfully with the unported leaf operations deferred (no logic
//! dropped); the portable leaves (the `self.*` sibling calls + the
//! `setDataValueApplied` node mutation) are emitted as real code.

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]

use super::super::completion::context::CalculationAlgorithmContextBase;
use super::super::model::substrate::{Cint64, INVALID};
use super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags;
use super::super::process::stubs::ConceptSaturationProcessLinkerId;
use super::super::process::SatNodeId;

impl super::algorithm::SaturationTaskHandleAlgorithm {
    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyDATATYPERule`
    /// (cpp 5760–5793).
    pub fn apply_datatype_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W4-DEFER[api]: conProLinker->getConceptSaturationDescriptor()->getConcept()->getDatatype()
        //   — CConceptSaturationProcessLinker / CConceptSaturationDescriptor are
        //   `process::stubs` markers and CDatatype is unported (opaque Cint64); the
        //   descriptor/concept/datatype resolution lands on reconcile.
        //   CConceptSaturationDescriptor* conDes = conProLinker->getConceptSaturationDescriptor();
        //   CConcept* concept = conDes->getConcept();
        //   CDatatype* datatype = concept->getDatatype();
        let datatype: Cint64 = INVALID;
        let datatype_tag: Cint64 = INVALID; // datatype->getDatatypeTag()

        if datatype != INVALID && datatype_tag != 1 {
            // W4-DEFER[api]: processIndi->getAppliedDatatypeData(true) —
            //   CSaturationIndividualNodeDatatypeData satellite not yet ported; the
            //   applied-datatype gating below is transcribed structurally.
            //   CSaturationIndividualNodeDatatypeData* appliedDatatypeData = processIndi->getAppliedDatatypeData(true);
            let applied_datatype_present: bool = false; // appliedDatatypeData->getAppliedDatatype()

            if !applied_datatype_present {
                // processIndi->setDataValueApplied(true);
                calc_alg_context
                    .process_context_mut()
                    .sat_node_mut(*process_indi)
                    .set_data_value_applied(true);

                let mut data_value_trivially_sat = true;
                let mut data_value_trivially_unsat = false;

                if data_value_trivially_sat && !data_value_trivially_unsat {
                    self.handle_datatype_value_space_triggers(
                        process_indi,
                        datatype,
                        &mut data_value_trivially_sat,
                        &mut data_value_trivially_unsat,
                        calc_alg_context,
                    );
                }

                if data_value_trivially_unsat {
                    self.update_direct_adding_individual_status_flags(
                        *process_indi,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
                        calc_alg_context,
                    );
                } else if !data_value_trivially_sat {
                    self.update_direct_adding_individual_status_flags(
                        *process_indi,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                        calc_alg_context,
                    );
                    self.set_insufficient_node_occured(calc_alg_context);
                }

                // W4-DEFER[api]: appliedDatatypeData->setAppliedDatatype(datatype);
            } else {
                // C++: else if (datatype != appliedDatatypeData->getAppliedDatatype())
                // W4-DEFER[api]: the datatype-mismatch guard resolves with the satellite.
                self.update_direct_adding_individual_status_flags(
                    *process_indi,
                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                    calc_alg_context,
                );
                self.set_insufficient_node_occured(calc_alg_context);
            }
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyDATALITERALRule`
    /// (cpp 5795–5803).
    pub fn apply_data_literal_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W4-DEFER[api]: conProLinker->getConceptSaturationDescriptor() (CConceptSaturationDescriptor
        //   stub) -> getNegation() / getConcept()->getDataLiteral() / getConcept()->getDatatype();
        //   the descriptor/concept resolution lands on reconcile, CDataLiteral / CDatatype
        //   stay opaque Cint64.
        //   CConceptSaturationDescriptor* conDes = conProLinker->getConceptSaturationDescriptor();
        //   bool conNegation = conDes->getNegation();   // dead local in C++ (unused below)
        //   CConcept* concept = conDes->getConcept();
        //   CDataLiteral* dataLiteral = concept->getDataLiteral();
        //   CDatatype* datatype = concept->getDatatype();
        let data_literal: Cint64 = INVALID;
        let datatype: Cint64 = INVALID;

        self.associate_data_literal_with_node(
            process_indi,
            data_literal,
            datatype,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::handleDatatypeValueSpaceTriggers`
    /// (cpp 5806–5823).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ `bool& dataValueTriviallySat` /
    /// `bool& dataValueTriviallyUnsat` out-params become `&mut bool`.
    pub fn handle_datatype_value_space_triggers(
        &mut self,
        process_indi: &mut SatNodeId,
        datatype: Cint64,
        data_value_trivially_sat: &mut bool,
        data_value_trivially_unsat: &mut bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W4-DEFER[api]: mCalcAlgContext->getUsedProcessingDataBox()->getOntology()
        //   ->getDataBoxes()->getMBox()->getValueSpacesTriggers(false) — the ontology
        //   value-space-trigger model (CDatatypeValueSpacesTriggers /
        //   CDatatypeValueSpaceTriggers) is not ported; the trigger lookup + the
        //   concept-trigger-count gate are transcribed structurally.
        //   CDatatypeValueSpacesTriggers* valueSpaceTriggers = ...->getValueSpacesTriggers(false);
        let value_space_triggers: Cint64 = INVALID;

        if value_space_triggers != INVALID {
            // CDatatypeValueSpaceTriggers* datatypeValueSpaceTrigger =
            //     valueSpaceTriggers->getValueSpaceTriggers(datatype->getValueSpaceType());
            let datatype_value_space_trigger: Cint64 = INVALID;

            if datatype_value_space_trigger != INVALID {
                // if (datatypeValueSpaceTrigger->getConceptTriggerCount() > 0)
                let concept_trigger_count: Cint64 = 0; // datatypeValueSpaceTrigger->getConceptTriggerCount()

                if concept_trigger_count > 0 {
                    let triggers_handled = self.try_handle_datatype_value_space_triggers(
                        process_indi,
                        datatype_value_space_trigger,
                        value_space_triggers,
                        datatype,
                        calc_alg_context,
                    );

                    if !triggers_handled {
                        *data_value_trivially_sat = false;
                    }
                }
            }
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::tryHandleDatatypeValueSpaceTriggers`
    /// (cpp 5826–5846).
    pub fn try_handle_datatype_value_space_triggers(
        &mut self,
        process_indi: &mut SatNodeId,
        datatype_value_space_trigger: Cint64,
        value_space_triggers: Cint64,
        datatype: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut triggers_handled = false;

        // W4-DEFER[api]: datatype->getValueSpaceType()->getValueSpaceType() ==
        //   CDatatypeValueSpaceType::VALUESPACESTRINGTYPE — the CDatatypeValueSpaceType
        //   / CDatatypeValueSpaceStringTriggers string value-space model is unported.
        let value_space_type_is_string: bool = false;

        if value_space_type_is_string {
            // CDatatypeValueSpaceStringTriggers* stringDatatypeValueSpaceTrigger =
            //     valueSpaceTriggers->getStringValueSpaceTriggers();
            // if (!stringDatatypeValueSpaceTrigger->getNonLanguageTagConceptTriggeringData()
            //     || !stringDatatypeValueSpaceTrigger->getNonLanguageTagConceptTriggeringData()->hasPartialConceptTriggers()) {
            //   if (!stringDatatypeValueSpaceTrigger->getValueSpaceTriggeringMap()
            //       || stringDatatypeValueSpaceTrigger->getValueSpaceTriggeringMap()->isEmpty()) {
            //     for (CDatatypeValueSpaceConceptTriggerLinker* triggerLinkerIt =
            //              datatypeValueSpaceTrigger->getValueSpaceConceptTriggeringData()->getPartialConceptTriggerLinker();
            //          triggerLinkerIt; triggerLinkerIt = triggerLinkerIt->getNext()) {
            //       self.add_concept_filtered_to_individual(
            //           triggerLinkerIt->getTriggerConcept(), false, process_indi, calc_alg_context);
            //     }
            //     triggersHandled = true;
            //   }
            // }
            // W4-DEFER[api]: the partial-trigger / value-space-map gates and the
            //   trigger-concept iteration resolve with the string value-space-trigger
            //   model; the leaf is the sibling `addConceptFilteredToIndividual`
            //   (group K, other s-unit). `triggers_handled` is set there.
        }

        triggers_handled
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::associateDataLiteralWithNode`
    /// (cpp 5850–5970).
    pub fn associate_data_literal_with_node(
        &mut self,
        process_indi: &mut SatNodeId,
        data_literal: Cint64,
        mut datatype: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W4-DEFER[api]: processIndi->getAppliedDatatypeData(true) —
        //   CSaturationIndividualNodeDatatypeData satellite not yet ported; the
        //   applied-datatype / applied-data-literal gating below is transcribed.
        //   CSaturationIndividualNodeDatatypeData* appliedDatatypeData = processIndi->getAppliedDatatypeData(true);

        // if (!datatype) { datatype = dataLiteral->getDatatype(); }
        // else if (datatype != dataLiteral->getDatatype()) { insufficient; setInsufficient; }
        if datatype == INVALID {
            // W4-DEFER[api]: datatype = dataLiteral->getDatatype();  (CDataLiteral::getDatatype())
            datatype = INVALID;
        } else {
            // C++: else if (datatype != dataLiteral->getDatatype())
            // W4-DEFER[api]: the datatype-vs-literal-datatype mismatch guard resolves
            //   when CDataLiteral is ported; the body is the two `self.*` calls below.
            // self.update_direct_adding_individual_status_flags(
            //     *process_indi, INDSATFLAGINSUFFICIENT, calc_alg_context);
            // self.set_insufficient_node_occured(calc_alg_context);
        }

        // applied-datatype gate (W4-DEFER[api] satellite: appliedDatatypeData->getAppliedDatatype())
        let applied_datatype_present: bool = false;
        if !applied_datatype_present {
            // processIndi->setDataValueApplied(true);
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(*process_indi)
                .set_data_value_applied(true);
            // W4-DEFER[api]: appliedDatatypeData->setAppliedDatatype(datatype);
        } else {
            // C++: else if (datatype != appliedDatatypeData->getAppliedDatatype())  — W4-DEFER[api]
            self.update_direct_adding_individual_status_flags(
                *process_indi,
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                calc_alg_context,
            );
            self.set_insufficient_node_occured(calc_alg_context);
        }

        // applied-data-literal gate (W4-DEFER[api] satellite: appliedDatatypeData->getAppliedDataLiteral())
        let applied_data_literal_present: bool = false;
        if !applied_data_literal_present {
            // processIndi->setDataValueApplied(true);
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(*process_indi)
                .set_data_value_applied(true);
            // W4-DEFER[api]: appliedDatatypeData->setAppliedDataLiteral(dataLiteral);

            // CDataLiteralValue* dataLitValue = dataLiteral->getDataLiteralValue();  // W4-DEFER[api]
            let mut data_value_trivially_sat = true;
            let mut data_value_trivially_unsat = false;

            // if (!dataLitValue && datatype) dataValueTriviallySat = false;  — W4-DEFER[api]
            //   (depends on CDataLiteral::getDataLiteralValue())

            if data_value_trivially_sat && !data_value_trivially_unsat && datatype != INVALID {
                self.handle_datatype_value_space_triggers(
                    process_indi,
                    datatype,
                    &mut data_value_trivially_sat,
                    &mut data_value_trivially_unsat,
                    calc_alg_context,
                );
            }

            if data_value_trivially_sat && !data_value_trivially_unsat && datatype != INVALID {
                // W4-DEFER[api]: the CDataLiteralValue dynamic_cast value-validity ladder
                //   (CDatatype::DATATYPE_TYPE switch over DT_BOOLEAN / DT_FLOAT / DT_DOUBLE /
                //   DT_PLAINLITERAL / DT_STRING[hasLanguageTag => triviallyUnsat] / DT_RATIONAL /
                //   DT_DECIMAL / DT_INTEGER, each a dynamic_cast to the matching
                //   CDataLiteral*Value subtype + CDataLiteralRealValue::hasFlag check) sets
                //   `valueValid` / `dataValueTriviallyUnsat`, then
                //   `if (!valueValid) dataValueTriviallySat = false;`. Transcribed
                //   structurally; resolves when CDataLiteral / CDataLiteralValue + subtypes
                //   (Boolean/Float/Double/String/Real) and CDatatype::getDatatypeType() land.
            }

            if data_value_trivially_unsat {
                self.update_direct_adding_individual_status_flags(
                    *process_indi,
                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
                    calc_alg_context,
                );
            } else if !data_value_trivially_sat {
                self.update_direct_adding_individual_status_flags(
                    *process_indi,
                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                    calc_alg_context,
                );
                self.set_insufficient_node_occured(calc_alg_context);
            }
        } else {
            // C++: else if (dataLiteral != appliedDatatypeData->getAppliedDataLiteral())  — W4-DEFER[api]
            self.update_direct_adding_individual_status_flags(
                *process_indi,
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                calc_alg_context,
            );
            self.set_insufficient_node_occured(calc_alg_context);
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyNotDATATYPERule`
    /// (cpp 5998–6002).
    pub fn apply_not_datatype_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        self.update_direct_adding_individual_status_flags(
            *process_indi,
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
            calc_alg_context,
        );
        self.set_insufficient_node_occured(calc_alg_context);
        // applyORRule(processIndi, conProLinker) — sibling rule, lands in PU-SAT-3 (group D).
        self.apply_or_rule(process_indi, con_pro_linker, calc_alg_context);
    }
}
