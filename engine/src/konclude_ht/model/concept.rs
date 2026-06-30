//! `model::concept` — port of Konclude `Reasoner/Ontology/CConcept.{h,cpp}`.
//!
//! `CConcept` inherits `CTagItem` (field `mTag`), `CNamedItem` (field
//! `mNameLinker`) and `CAllocationObject` (pool marker, no state). Rust has no
//! implementation inheritance, so the two inherited fields and the handful of
//! base accessors `CConcept` actually uses (`mTag`/`initTag`, `hasName`/
//! `setNameLinker`/`addNameLinker`/`getNameLinker`) are inlined here and tagged.
//! The original C++ symbol name is kept in each item's doc-comment so the two
//! trees diff method-by-method.

#![allow(dead_code)]

use super::op::{
    ConceptOperator, CCAND, CCATLEAST, CCATMOST, CCALL, CCBOTTOM, CCEQ, CCNONE, CCSOME, CCSUB,
    CCTOP,
};
use super::stubs::NameId;
use super::substrate::{Arena, Cint64, NegLink, INVALID};
use super::{ConceptId, IndividualId, RoleId, VariableId};

// KONCLUDE-PORT-NOTE[ownership]: several pointer targets referenced by `CConcept`
// are not (yet) ported model types — `CTerminology*` (the owning terminology),
// `CLinker<CName*>*` (name linker), `CDataLiteral*`, `CDatatype*` and
// `CConceptData*`. Konclude addresses each by a raw pointer; with no arena/`Id<T>`
// for them yet the port stores their stable `cint64` id as an opaque `Cint64`
// (sentinel `INVALID` == `nullptr`). See `substrate.rs` for the global decision.

/// Port of `CConcept`.
///
/// KONCLUDE-PORT-NOTE[ownership]: every raw `CXxx*` field becomes a typed arena
/// id (`CRole*`→`RoleId`, `CIndividual*`→`IndividualId`) or, for not-yet-ported
/// types, an opaque `Cint64` id; the `CSortedNegLinker<CConcept*>* operands`
/// intrusive list becomes a `Vec<NegLink<ConceptId>>` and the
/// `CSortedLinker<CVariable*>*`/`CLinker<CName*>*` lists become `Vec`s. See
/// `substrate.rs` for the one global `[ownership]` rationale these point at.
pub struct Concept {
    // --- inherited from CTagItem ---
    /// `CTagItem::mTag` (the concept tag; `CConcept::mTag`).
    pub tag: Cint64,

    // --- inherited from CNamedItem ---
    // KONCLUDE-PORT-NOTE[ownership]: `CLinker<CName *>* mNameLinker` (intrusive
    // list) → `Vec<NameId>`; list head kept at index 0 (see
    // `add_class_name_linker`), matching `CNamedItem::addNameLinker`'s prepend.
    /// `CNamedItem::mNameLinker`.
    pub name_linker: Vec<NameId>,

    // --- CConcept own fields (in declaration order) ---
    // KONCLUDE-PORT-NOTE[ownership]: `CTerminology* tax` — opaque id, no
    // CTerminology port; `INVALID` == `nullptr`.
    /// `CConcept::tax`.
    pub tax: Cint64,
    /// `CConcept::mOperatorCode` (the `CConceptOperator*` tag → value).
    pub operator_code: ConceptOperator,
    /// `CConcept::opParameter`.
    pub op_parameter: Cint64,
    /// `CConcept::operandCount`.
    pub operand_count: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `CRole* operatorRole` → `RoleId`.
    /// `CConcept::operatorRole`.
    pub operator_role: RoleId,
    // KONCLUDE-PORT-NOTE[ownership]: `CSortedNegLinker<CConcept*>* operands`
    // (intrusive sorted list with a per-entry negation bit) → `Vec<NegLink<ConceptId>>`.
    /// `CConcept::operands`.
    pub operands: Vec<NegLink<ConceptId>>,
    // KONCLUDE-PORT-NOTE[ownership]: `CIndividual* mNominalIndiviual` → `IndividualId`.
    /// `CConcept::mNominalIndiviual`.
    pub nominal_individual: IndividualId,
    // KONCLUDE-PORT-NOTE[ownership]: `CSortedLinker<CVariable*>* mVariableLinker`
    // (intrusive sorted list) → `Vec<VariableId>`.
    /// `CConcept::mVariableLinker`.
    pub variable_linker: Vec<VariableId>,
    // KONCLUDE-PORT-NOTE[ownership]: `CDataLiteral* mDataLiteral` — opaque id.
    /// `CConcept::mDataLiteral`.
    pub data_literal: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `CDatatype* mDatatype` — opaque id.
    /// `CConcept::mDatatype`.
    pub datatype: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `CConceptData* mConceptData` — opaque id.
    /// `CConcept::mConceptData`.
    pub concept_data: Cint64,
    /// `CConcept::mMappingNegated`.
    pub mapping_negated: bool,
}

impl Concept {
    /// Port of `CConcept::CConcept()` (the constructor calls `initConcept()`).
    pub fn new() -> Self {
        let mut concept = Concept {
            tag: 0,
            name_linker: Vec::new(),
            tax: INVALID,
            operator_code: ConceptOperator::new(CCNONE),
            op_parameter: 0,
            operand_count: 0,
            operator_role: RoleId::NONE,
            operands: Vec::new(),
            nominal_individual: IndividualId::NONE,
            variable_linker: Vec::new(),
            data_literal: INVALID,
            datatype: INVALID,
            concept_data: INVALID,
            mapping_negated: false,
        };
        concept.init_concept();
        concept
    }

    /// Port of `CConcept::initConcept`.
    pub fn init_concept(&mut self) -> &mut Self {
        self.tag = 0;
        self.operator_code = ConceptOperator::new(CCNONE);
        self.operand_count = 0;
        self.operands = Vec::new(); // operands = 0
        self.op_parameter = 0;
        self.operator_role = RoleId::NONE; // operatorRole = 0
        self.tax = INVALID; // tax = 0
        self.name_linker = Vec::new(); // mNameLinker = 0
        self.nominal_individual = IndividualId::NONE;
        self.concept_data = INVALID;
        self.variable_linker = Vec::new();
        self.mapping_negated = false;
        self.data_literal = INVALID;
        self.datatype = INVALID;
        self
    }

    /// Port of `CConcept::init(CConcept *concept)`.
    // KONCLUDE-PORT-NOTE[overload]: `init(CConcept*)` vs `init(qint64)` →
    // distinct names `init_from_concept` / `init_with_tag`.
    pub fn init_from_concept(&mut self, concept: &Concept) -> &mut Self {
        self.name_linker = concept.get_class_name_linker().to_vec();
        self.tag = concept.tag;
        self.operator_code = concept.operator_code;
        self.operand_count = concept.operand_count;
        self.operands = Vec::new(); // operands = 0
        self.op_parameter = concept.op_parameter;
        self.operator_role = concept.operator_role;
        self.tax = INVALID; // tax = 0
        self.nominal_individual = concept.nominal_individual;
        // KONCLUDE-PORT-NOTE[ownership]: C++ shares the `mVariableLinker` pointer;
        // the port clones the `Vec` (same contents, distinct storage).
        self.variable_linker = concept.variable_linker.clone();
        self.mapping_negated = concept.mapping_negated;
        self.concept_data = INVALID;
        self.data_literal = concept.data_literal;
        self.datatype = concept.datatype;
        self
    }

    /// Port of `CConcept::init(qint64 conTag)`.
    pub fn init_with_tag(&mut self, con_tag: Cint64) -> &mut Self {
        self.init_tag(con_tag); // initTag(conTag)
        self.tag = con_tag;
        self.operator_code = ConceptOperator::new(CCNONE);
        self.operand_count = 0;
        self.operands = Vec::new(); // operands = 0
        self.op_parameter = 0;
        self.operator_role = RoleId::NONE; // operatorRole = 0
        self.tax = INVALID; // tax = 0
        self.nominal_individual = IndividualId::NONE;
        self.concept_data = INVALID;
        self.variable_linker = Vec::new();
        self.mapping_negated = false;
        self.data_literal = INVALID;
        self.datatype = INVALID;
        self
    }

    /// Port of `CConcept::initConceptCopy`.
    // KONCLUDE-PORT-NOTE[memory-pool]: the C++ takes a `CMemoryAllocationManager*`
    // and only copies the operand/variable lists `while (memMan && ...)`, allocating
    // each new linker node from the pool. The port has no allocator; it always
    // copies (pushes ported entries into the arena-backed `Vec`s). Result is identical.
    pub fn init_concept_copy(&mut self, concept: &Concept) -> &mut Self {
        self.name_linker = concept.get_class_name_linker().to_vec();
        self.tag = concept.tag;
        self.operator_code = concept.operator_code;
        self.operand_count = concept.operand_count;
        self.op_parameter = concept.op_parameter;
        self.operator_role = concept.operator_role;
        self.tax = INVALID; // tax = 0
        self.operands = Vec::new(); // operands = 0
        self.nominal_individual = concept.nominal_individual;
        self.mapping_negated = concept.mapping_negated;
        self.data_literal = concept.data_literal;
        self.datatype = concept.datatype;
        self.variable_linker = Vec::new(); // mVariableLinker = nullptr
        self.concept_data = INVALID; // mConceptData = nullptr

        // while (memMan && opIt) { ... addOperandLinker(opLinker); opIt = opIt->getNext(); }
        for op in concept.operands.iter() {
            let con = op.target;
            let negated = op.negated;
            self.add_operand_linker(con, negated);
        }

        // while (memMan && varIt) { ... addVariableLinker(varLinker); varIt = varIt->getNext(); }
        for var in concept.variable_linker.iter() {
            self.add_variable_linker(*var);
        }

        self
    }

    // --- inherited CTagItem accessor used by the ports above ---

    /// Port of `CTagItem::initTag`.
    pub fn init_tag(&mut self, tag: Cint64) -> &mut Self {
        self.tag = tag;
        self
    }

    // --- variable linker (CVariable) ---

    /// Port of `CConcept::getVariable`.
    pub fn get_variable(&self) -> Option<VariableId> {
        if let Some(var) = self.variable_linker.first() {
            return Some(*var);
        }
        None
    }

    /// Port of `CConcept::getVariableLinker`.
    pub fn get_variable_linker(&self) -> &[VariableId] {
        &self.variable_linker
    }

    /// Port of `CConcept::setVariableLinker`.
    // KONCLUDE-PORT-NOTE[ownership]: the C++ arg is a whole `CSortedLinker<CVariable*>*`
    // list; ported as the equivalent `Vec<VariableId>` (replace).
    pub fn set_variable_linker(&mut self, variable_linker: Vec<VariableId>) -> &mut Self {
        self.variable_linker = variable_linker;
        self
    }

    /// Port of `CConcept::addVariableLinker`.
    // KONCLUDE-PORT-NOTE[ownership]: C++ inserts one variable via
    // `insertSortedNextSorted` (sorted by variable). The sort key needs the
    // `CVariable` behind the id, which is not available here, so the port appends
    // and relies on callers adding variables in sorted order (see substrate note).
    pub fn add_variable_linker(&mut self, variable: VariableId) -> &mut Self {
        self.variable_linker.push(variable);
        self
    }

    // --- concept tag (CConcept::mTag) ---

    /// Port of `CConcept::setConceptTag`.
    pub fn set_concept_tag(&mut self, con_tag: Cint64) -> &mut Self {
        self.tag = con_tag;
        self
    }

    /// Port of `CConcept::getConceptTag`.
    pub fn get_concept_tag(&self) -> Cint64 {
        self.tag
    }

    // --- operator code / operator ---

    /// Port of `CConcept::setOperatorCode`.
    pub fn set_operator_code(&mut self, op_code: Cint64) -> &mut Self {
        self.operator_code = ConceptOperator::new(op_code);
        self
    }

    /// Port of `CConcept::getOperatorCode`.
    pub fn get_operator_code(&self) -> Cint64 {
        self.operator_code.get_operator_code()
    }

    /// Port of `CConcept::getConceptOperator`.
    // KONCLUDE-PORT-NOTE[ownership]: C++ returns the shared `CConceptOperator*`;
    // `ConceptOperator` is a 16-byte `Copy` value, so the port returns it by value.
    pub fn get_concept_operator(&self) -> ConceptOperator {
        self.operator_code
    }

    /// Port of `CConcept::setOperatorTag`.
    pub fn set_operator_tag(&mut self, op_tag: Cint64) -> &mut Self {
        self.operator_code = ConceptOperator::new(op_tag);
        self
    }

    /// Port of `CConcept::getDefinitionOperatorTag`.
    pub fn get_definition_operator_tag(&self) -> Cint64 {
        self.get_operator_code()
    }

    /// Port of `CConcept::getProcessingOperatorTag`.
    pub fn get_processing_operator_tag(&self) -> Cint64 {
        let mut tag = self.get_operator_code();
        if tag == CCEQ || tag == CCSUB {
            tag = CCAND;
        }
        tag
    }

    // --- terminology (CTerminology) ---

    /// Port of `CConcept::setTerminology`.
    // KONCLUDE-PORT-NOTE[unclear]: `CTerminology` is not modeled; `setTerminology`
    // stores the terminology's id (opaque `Cint64`) rather than a back-pointer to
    // the object. `getTerminologyTag` therefore returns it directly instead of
    // calling `terminology->getTerminologyID()`. Same observable tag.
    pub fn set_terminology(&mut self, terminology: Cint64) -> &mut Self {
        self.tax = terminology;
        self
    }

    /// Port of `CConcept::getTerminology`.
    pub fn get_terminology(&self) -> Cint64 {
        self.tax
    }

    /// Port of `CConcept::getTerminologyTag`.
    pub fn get_terminology_tag(&self) -> Cint64 {
        let mut tax_tag = 0;
        if self.tax != INVALID {
            // C++: taxTag = tax->getTerminologyID(); opaque port stores it in `tax`.
            tax_tag = self.tax;
        }
        tax_tag
    }

    /// Port of `CConcept::getTerminologyConceptTagPair`.
    // KONCLUDE-PORT-NOTE[api]: `QPair<qint64,qint64>` → a Rust `(Cint64, Cint64)` tuple.
    pub fn get_terminology_concept_tag_pair(&self) -> (Cint64, Cint64) {
        (self.get_terminology_tag(), self.tag)
    }

    // --- parameter ---

    /// Port of `CConcept::setParameter`.
    pub fn set_parameter(&mut self, parameter: Cint64) -> &mut Self {
        self.op_parameter = parameter;
        self
    }

    /// Port of `CConcept::getParameter`.
    pub fn get_parameter(&self) -> Cint64 {
        self.op_parameter
    }

    // --- operand count ---

    /// Port of `CConcept::setOperandCount`.
    pub fn set_operand_count(&mut self, count: Cint64) -> &mut Self {
        self.operand_count = count;
        self
    }

    /// Port of `CConcept::incOperandCount` (default `incCount = 1`).
    pub fn inc_operand_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.operand_count += inc_count;
        self
    }

    /// Port of `CConcept::getOperandCount`.
    pub fn get_operand_count(&self) -> Cint64 {
        self.operand_count
    }

    // --- operand list (CSortedNegLinker<CConcept*>) ---

    /// Port of `CConcept::setOperandList`.
    // KONCLUDE-PORT-NOTE[ownership]: the C++ arg is a whole
    // `CSortedNegLinker<CConcept*>*` list head; ported as the equivalent
    // `Vec<NegLink<ConceptId>>` (replace).
    pub fn set_operand_list(&mut self, operand_list: Vec<NegLink<ConceptId>>) -> &mut Self {
        self.operands = operand_list;
        self
    }

    /// Port of `CConcept::addOperandLinker`.
    // KONCLUDE-PORT-NOTE[ownership]: C++ inserts one operand linker via
    // `insertSortedNextSorted` (sorted by concept tag). The sort key needs the
    // `CConcept` behind the id (an arena lookup), so the port appends a `NegLink`
    // and relies on callers adding operands in sorted order (see substrate note).
    // The original takes a pre-built linker; the port takes its data `(id, negated)`.
    pub fn add_operand_linker(&mut self, concept_id: ConceptId, negation: bool) -> &mut Self {
        self.operands.push(NegLink { target: concept_id, negated: negation });
        self
    }

    /// Port of `CConcept::getOperandList`.
    pub fn get_operand_list(&self) -> &[NegLink<ConceptId>] {
        &self.operands
    }

    // --- comparison operators ---

    /// Port of `CConcept::operator<=`.
    // KONCLUDE-PORT-NOTE[overload]: C++ `operator<=` → inherent method `le`.
    pub fn le(&self, concept: &Concept) -> bool {
        if self.tag < concept.tag {
            true
        } else if self.tag > concept.tag {
            false
        } else {
            self.get_terminology_tag() <= concept.get_terminology_tag()
        }
    }

    /// Port of `CConcept::operator==`.
    // KONCLUDE-PORT-NOTE[overload]: C++ `operator==` → inherent method `eq`;
    // pointer equality `tax == concept.tax` becomes opaque-id equality.
    pub fn eq(&self, concept: &Concept) -> bool {
        self.tag == concept.tag && self.tax == concept.tax
    }

    // --- operator role (CRole) ---

    /// Port of `CConcept::setRole`.
    pub fn set_role(&mut self, role: RoleId) -> &mut Self {
        self.operator_role = role;
        self
    }

    /// Port of `CConcept::getRole`.
    pub fn get_role(&self) -> RoleId {
        self.operator_role
    }

    // --- nominal individual (CIndividual) ---

    /// Port of `CConcept::getNominalIndividual`.
    pub fn get_nominal_individual(&self) -> IndividualId {
        self.nominal_individual
    }

    /// Port of `CConcept::hasNominalIndividual`.
    pub fn has_nominal_individual(&self) -> bool {
        self.nominal_individual.is_some()
    }

    /// Port of `CConcept::setNominalIndividual`.
    pub fn set_nominal_individual(&mut self, nominal_individual: IndividualId) -> &mut Self {
        self.nominal_individual = nominal_individual;
        self
    }

    // --- generating-operator classification ---

    /// Port of `CConcept::isGeneratingOperator` (default `negated = false`).
    pub fn is_generating_operator(&self, negated: bool) -> bool {
        let operator_tag = self.operator_code.get_operator_code();
        if !negated {
            operator_tag == CCSOME || operator_tag == CCATLEAST
        } else {
            operator_tag == CCALL || operator_tag == CCATMOST
        }
    }

    /// Port of `CConcept::isNegatedGeneratingOperator`.
    pub fn is_negated_generating_operator(&self) -> bool {
        self.is_generating_operator(true)
    }

    /// Port of `CConcept::isNonGeneratingOperator`.
    pub fn is_non_generating_operator(&self) -> bool {
        !self.is_generating_operator(false)
    }

    // --- class name (CNamedItem) ---

    /// Port of `CConcept::hasClassName` (→ `CNamedItem::hasName`).
    pub fn has_class_name(&self) -> bool {
        !self.name_linker.is_empty()
    }

    /// Port of `CConcept::setClassNameLinker` (→ `CNamedItem::setNameLinker`).
    // KONCLUDE-PORT-NOTE[ownership]: the C++ arg is a whole `CLinker<CName*>*`
    // list; ported as the equivalent `Vec<NameId>` (replace).
    pub fn set_class_name_linker(&mut self, concept_name_linker: Vec<NameId>) -> &mut Self {
        self.name_linker = concept_name_linker;
        self
    }

    /// Port of `CConcept::addClassNameLinker` (→ `CNamedItem::addNameLinker`).
    // KONCLUDE-PORT-NOTE[ownership]: `CNamedItem::addNameLinker` prepends the given
    // linker; one name is added at a time here, so it goes to the head (index 0).
    pub fn add_class_name_linker(&mut self, name: NameId) -> &mut Self {
        self.name_linker.insert(0, name);
        self
    }

    /// Port of `CConcept::getClassNameLinker` (→ `CNamedItem::getNameLinker`).
    pub fn get_class_name_linker(&self) -> &[NameId] {
        &self.name_linker
    }

    // --- BOTTOM / TOP tests ---

    /// Port of `CConcept::isEqualsToBOTTOM` (default `negated = false`).
    pub fn is_equals_to_bottom(&self, negated: bool) -> bool {
        let operator_tag = self.operator_code.get_operator_code();
        // C++: (!negated && tag == CCBOTTOM || negated && tag == CCTOP)
        (!negated && operator_tag == CCBOTTOM) || (negated && operator_tag == CCTOP)
    }

    /// Port of `CConcept::isEqualsToTOP` (default `negated = false`).
    pub fn is_equals_to_top(&self, negated: bool) -> bool {
        let operator_tag = self.operator_code.get_operator_code();
        // C++: (negated && tag == CCBOTTOM || !negated && tag == CCTOP)
        (negated && operator_tag == CCBOTTOM) || (!negated && operator_tag == CCTOP)
    }

    // --- operand membership queries ---
    //
    // KONCLUDE-PORT-NOTE[ownership]: the C++ `hasOperandConceptTag` walks the
    // operand linkers calling `opIt->getData()->getConceptTag()`, i.e. it
    // dereferences each operand `CConcept*`. Operands are `ConceptId`s here, so the
    // ported tag-based queries take an extra `concepts: &Arena<Concept>` to
    // dereference them (see `substrate.rs`). The early `return false` on
    // `opConTag > conTag` is kept — it is correct because operands are stored
    // sorted by concept tag.

    /// Port of `CConcept::hasOperandConceptTag(CConcept *concept)`.
    // KONCLUDE-PORT-NOTE[overload]: the four `hasOperandConceptTag` overloads →
    // `_`/`_for_tag`/`_negation`/`_for_tag_negation` suffixes.
    pub fn has_operand_concept_tag(&self, concept: ConceptId, concepts: &Arena<Concept>) -> bool {
        self.has_operand_concept_tag_for_tag(concepts.get(concept).get_concept_tag(), concepts)
    }

    /// Port of `CConcept::hasOperandConceptTag(qint64 conTag)`.
    pub fn has_operand_concept_tag_for_tag(&self, con_tag: Cint64, concepts: &Arena<Concept>) -> bool {
        for op in self.operands.iter() {
            let op_con_tag = concepts.get(op.target).get_concept_tag();
            if op_con_tag == con_tag {
                return true;
            } else if op_con_tag > con_tag {
                return false;
            }
        }
        false
    }

    /// Port of `CConcept::hasOperandConceptTag(CConcept *concept, bool negation)`.
    pub fn has_operand_concept_tag_negation(
        &self,
        concept: ConceptId,
        negation: bool,
        concepts: &Arena<Concept>,
    ) -> bool {
        self.has_operand_concept_tag_for_tag_negation(
            concepts.get(concept).get_concept_tag(),
            negation,
            concepts,
        )
    }

    /// Port of `CConcept::hasOperandConceptTag(qint64 conTag, bool negation)`.
    pub fn has_operand_concept_tag_for_tag_negation(
        &self,
        con_tag: Cint64,
        negation: bool,
        concepts: &Arena<Concept>,
    ) -> bool {
        for op in self.operands.iter() {
            let op_con_tag = concepts.get(op.target).get_concept_tag();
            let op_neg = op.negated;
            if op_con_tag == con_tag && negation == op_neg {
                return true;
            } else if op_con_tag > con_tag {
                return false;
            }
        }
        false
    }

    /// Port of `CConcept::hasOperandConcept(CConcept *concept)`.
    // KONCLUDE-PORT-NOTE[ownership]: pointer identity `opConcept == concept` →
    // `ConceptId` equality; no arena dereference needed.
    pub fn has_operand_concept(&self, concept: ConceptId) -> bool {
        for op in self.operands.iter() {
            let op_concept = op.target;
            if op_concept == concept {
                return true;
            }
        }
        false
    }

    /// Port of `CConcept::hasOperandConcept(CConcept *concept, bool negation)`.
    pub fn has_operand_concept_negation(&self, concept: ConceptId, negation: bool) -> bool {
        for op in self.operands.iter() {
            let op_concept = op.target;
            let op_neg = op.negated;
            if op_concept == concept && negation == op_neg {
                return true;
            }
        }
        false
    }

    // --- concept data (CConceptData) ---

    /// Port of `CConcept::getConceptData`.
    pub fn get_concept_data(&self) -> Cint64 {
        self.concept_data
    }

    /// Port of `CConcept::setConceptData`.
    pub fn set_concept_data(&mut self, concept_data: Cint64) -> &mut Self {
        self.concept_data = concept_data;
        self
    }

    /// Port of `CConcept::hasConceptData`.
    pub fn has_concept_data(&self) -> bool {
        self.concept_data != INVALID
    }

    // --- mapping negation ---

    /// Port of `CConcept::hasMappingNegation`.
    pub fn has_mapping_negation(&self) -> bool {
        self.mapping_negated
    }

    /// Port of `CConcept::setMappingNegation`.
    pub fn set_mapping_negation(&mut self, negation: bool) -> &mut Self {
        self.mapping_negated = negation;
        self
    }

    // --- data literal (CDataLiteral) ---

    /// Port of `CConcept::getDataLiteral`.
    pub fn get_data_literal(&self) -> Cint64 {
        self.data_literal
    }

    /// Port of `CConcept::setDataLiteral`.
    pub fn set_data_literal(&mut self, data_literal: Cint64) -> &mut Self {
        self.data_literal = data_literal;
        self
    }

    // --- datatype (CDatatype) ---

    /// Port of `CConcept::getDatatype`.
    pub fn get_datatype(&self) -> Cint64 {
        self.datatype
    }

    /// Port of `CConcept::setDatatype`.
    pub fn set_datatype(&mut self, datatype: Cint64) -> &mut Self {
        self.datatype = datatype;
        self
    }
}

impl Default for Concept {
    /// Port of `CConcept::CConcept()`.
    fn default() -> Self {
        Concept::new()
    }
}
