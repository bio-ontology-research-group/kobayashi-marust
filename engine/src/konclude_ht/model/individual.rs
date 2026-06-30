//! `model::individual` — port of Konclude `Reasoner/Ontology/CIndividual.{h,cpp}`
//! and `CVariable.{h,cpp}`.
//!
//! `CIndividual` inherits `CIndividualIdentifier` (→ `CTagItem`, field `mTag`),
//! `CNamedItem` (field `mNameLinker`) and `CAllocationObject` (pool marker, no
//! state). Rust has no implementation inheritance, so the inherited fields and
//! their accessors are inlined here and tagged. The original C++ symbol name is
//! kept in each item's doc-comment so the two trees diff method-by-method.

#![allow(dead_code)]

use super::stubs::NameId;
use super::substrate::{Cint64, NegLink, INVALID};
use super::{ConceptId, IndividualId, RoleId};

// KONCLUDE-PORT-NOTE[ownership]: several pointer targets referenced by
// `CIndividual` are not (yet) ported model types — `CName*` (name linker),
// `CDataLiteral*` (data assertion), `CIndividualData*`, and the foreign
// `CRoleAssertionLinker*` a reverse-assertion points at. Konclude addresses each
// by a raw pointer; with no arena/`Id<T>` for them yet, the port stores their
// stable `cint64` id as an opaque `Cint64` (sentinel `INVALID` == `nullptr`).
// Behaviour is identical; only the representation differs.

/// Port of one `CConceptAssertionLinker` entry (a `CNegLinkerBase<CConcept*>`):
/// an asserted concept plus its negation bit. See `NegLink` in `substrate`.
pub type ConceptAssertion = NegLink<ConceptId>;

/// Port of one `CRoleAssertionLinker` entry (`CLinkerBase<CRole*>` carrying
/// `mIndividual`): the role and the individual the role assertion points to.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct RoleAssertion {
    /// `CRoleAssertionLinker::getRole()` (the linker `data`).
    pub role: RoleId,
    /// `CRoleAssertionLinker::getIndividual()` (`mIndividual`).
    pub individual: IndividualId,
}

/// Port of one `CDataAssertionLinker` entry (`CLinkerBase<CRole*>` carrying
/// `mDataLiteral`): the data role and the asserted data literal.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct DataAssertion {
    /// `CDataAssertionLinker::getRole()` (the linker `data`).
    pub role: RoleId,
    // KONCLUDE-PORT-NOTE[ownership]: `CDataLiteral*` — opaque id, no CDataLiteral port.
    /// `CDataAssertionLinker::getDataLiteral()` (`mDataLiteral`).
    pub data_literal: Cint64,
}

/// Port of one `CReverseRoleAssertionLinker` entry
/// (`CLinkerBase<CRoleAssertionLinker*>` carrying `mIndividual`).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct ReverseRoleAssertion {
    /// `CReverseRoleAssertionLinker::getIndividual()` (`mIndividual`).
    pub individual: IndividualId,
    // KONCLUDE-PORT-NOTE[ownership]: `CRoleAssertionLinker*` into another
    // individual's role-linker list — no stable arena id; stored opaque.
    /// `CReverseRoleAssertionLinker::getRoleAssertion()` (the linker `data`).
    pub role_assertion: Cint64,
}

/// Port of `CIndividual`.
pub struct Individual {
    // --- inherited from CTagItem / CIndividualIdentifier ---
    /// `CTagItem::mTag` (the individual id; `CIndividualIdentifier::mTag`).
    pub tag: Cint64,

    // --- inherited from CNamedItem ---
    // KONCLUDE-PORT-NOTE[ownership]: `CLinker<CName*>* mNameLinker` (intrusive
    // list) → `Vec<NameId>`; list head kept at index 0 (see add).
    /// `CNamedItem::mNameLinker`.
    pub name_linker: Vec<NameId>,

    // --- CIndividual own fields ---
    // KONCLUDE-PORT-NOTE[ownership]: each `CXxxAssertionLinker*` intrusive list
    // → `Vec` of ported entries; the list head (most recently added) is index 0,
    // matching Konclude's `append`-prepend so iteration order is identical.
    /// `CIndividual::mAssertionConceptLinker`.
    pub assertion_concept_linker: Vec<ConceptAssertion>,
    /// `CIndividual::mAssertionRoleLinker`.
    pub assertion_role_linker: Vec<RoleAssertion>,
    /// `CIndividual::mAssertionDataLinker`.
    pub assertion_data_linker: Vec<DataAssertion>,
    /// `CIndividual::mReverseAssertionRoleLinker`.
    pub reverse_assertion_role_linker: Vec<ReverseRoleAssertion>,
    // KONCLUDE-PORT-NOTE[ownership]: `CConcept* mNominalConcept` → `ConceptId`.
    /// `CIndividual::mNominalConcept`.
    pub nominal_concept: ConceptId,
    /// `CIndividual::mAnonymousIndividual`.
    pub anonymous_individual: bool,
    /// `CIndividual::mTemporaryIndividual`.
    pub temporary_individual: bool,
    /// `CIndividual::mFakeIndividual`.
    pub fake_individual: bool,
    // KONCLUDE-PORT-NOTE[ownership]: `CIndividualData* mIndividualData` — opaque
    // id, no CIndividualData port; `INVALID` == `nullptr`.
    /// `CIndividual::mIndividualData`.
    pub individual_data: Cint64,
}

impl Individual {
    /// Port of `CIndividual::CIndividual(qint64 id)` (default `id = 0`).
    /// Also runs the base `CIndividualIdentifier(id)` → `CTagItem(id)` chain
    /// (sets `mTag = id`) and `CNamedItem()` (sets `mNameLinker = 0`).
    pub fn new(id: Cint64) -> Self {
        Individual {
            tag: id,
            name_linker: Vec::new(),
            assertion_concept_linker: Vec::new(),
            assertion_role_linker: Vec::new(),
            assertion_data_linker: Vec::new(),
            reverse_assertion_role_linker: Vec::new(),
            nominal_concept: ConceptId::NONE,
            anonymous_individual: false,
            temporary_individual: false,
            fake_individual: false,
            individual_data: INVALID,
        }
    }

    // --- inherited CTagItem / CIndividualIdentifier accessors ---

    /// Port of `CTagItem::getTag`.
    pub fn get_tag(&self) -> Cint64 {
        self.tag
    }
    /// Port of `CTagItem::setTag`.
    pub fn set_tag(&mut self, tag: Cint64) -> &mut Self {
        self.tag = tag;
        self
    }
    /// Port of `CTagItem::initTag`.
    pub fn init_tag(&mut self, tag: Cint64) -> &mut Self {
        self.tag = tag;
        self
    }
    /// Port of `CIndividualIdentifier::getIndividualID`.
    pub fn get_individual_id(&self) -> Cint64 {
        self.tag
    }
    /// Port of `CIndividualIdentifier::setIndividualID`.
    pub fn set_individual_id(&mut self, id: Cint64) -> &mut Self {
        self.tag = id;
        self
    }

    // --- name (CNamedItem, exposed via CIndividual::*IndividualName*) ---

    /// Port of `CIndividual::hasIndividualName` (→ `CNamedItem::hasName`).
    pub fn has_individual_name(&self) -> bool {
        !self.name_linker.is_empty()
    }

    /// Port of `CIndividual::setIndividualNameLinker` (→ `CNamedItem::setNameLinker`).
    // KONCLUDE-PORT-NOTE[ownership]: the C++ arg is a whole `CLinker<CName*>*`
    // list; ported as the equivalent `Vec<NameId>` (replace).
    pub fn set_individual_name_linker(&mut self, name_linker: Vec<NameId>) -> &mut Self {
        self.name_linker = name_linker;
        self
    }

    /// Port of `CIndividual::addIndividualNameLinker` (→ `CNamedItem::addNameLinker`).
    // KONCLUDE-PORT-NOTE[ownership]: C++ prepends the given linker
    // (`nameLinker->append(mNameLinker); mNameLinker = nameLinker;`). One name is
    // added at a time here, so the new id is inserted at the head (index 0).
    pub fn add_individual_name_linker(&mut self, name: NameId) -> &mut Self {
        self.name_linker.insert(0, name);
        self
    }

    /// Port of `CIndividual::getIndividualNameLinker` (→ `CNamedItem::getNameLinker`).
    pub fn get_individual_name_linker(&self) -> &[NameId] {
        &self.name_linker
    }

    // --- nominal concept ---

    /// Port of `CIndividual::getIndividualNominalConcept`.
    pub fn get_individual_nominal_concept(&self) -> ConceptId {
        self.nominal_concept
    }
    /// Port of `CIndividual::setIndividualNominalConcept`.
    pub fn set_individual_nominal_concept(&mut self, nom_concept: ConceptId) -> &mut Self {
        self.nominal_concept = nom_concept;
        self
    }

    // --- asserted concepts ---

    /// Port of `CIndividual::getAssertionConceptLinker`.
    pub fn get_assertion_concept_linker(&self) -> &[ConceptAssertion] {
        &self.assertion_concept_linker
    }
    /// Port of `CIndividual::addAssertionConceptLinker`.
    // KONCLUDE-PORT-NOTE[ownership]: `mAssertionConceptLinker =
    // assConLinker->append(mAssertionConceptLinker)` prepends; head → index 0.
    pub fn add_assertion_concept_linker(&mut self, ass_con_linker: ConceptAssertion) -> &mut Self {
        self.assertion_concept_linker.insert(0, ass_con_linker);
        self
    }
    /// Port of `CIndividual::setAssertionConceptLinker`.
    pub fn set_assertion_concept_linker(
        &mut self,
        ass_con_linker: Vec<ConceptAssertion>,
    ) -> &mut Self {
        self.assertion_concept_linker = ass_con_linker;
        self
    }

    // --- asserted roles ---

    /// Port of `CIndividual::getAssertionRoleLinker`.
    pub fn get_assertion_role_linker(&self) -> &[RoleAssertion] {
        &self.assertion_role_linker
    }
    /// Port of `CIndividual::addAssertionRoleLinker`.
    pub fn add_assertion_role_linker(&mut self, ass_role_linker: RoleAssertion) -> &mut Self {
        self.assertion_role_linker.insert(0, ass_role_linker);
        self
    }
    /// Port of `CIndividual::setAssertionRoleLinker`.
    pub fn set_assertion_role_linker(&mut self, ass_role_linker: Vec<RoleAssertion>) -> &mut Self {
        self.assertion_role_linker = ass_role_linker;
        self
    }

    // --- asserted data ---

    /// Port of `CIndividual::getAssertionDataLinker`.
    pub fn get_assertion_data_linker(&self) -> &[DataAssertion] {
        &self.assertion_data_linker
    }
    /// Port of `CIndividual::addAssertionDataLinker`.
    pub fn add_assertion_data_linker(&mut self, ass_data_linker: DataAssertion) -> &mut Self {
        self.assertion_data_linker.insert(0, ass_data_linker);
        self
    }
    /// Port of `CIndividual::setAssertionDataLinker`.
    pub fn set_assertion_data_linker(&mut self, ass_data_linker: Vec<DataAssertion>) -> &mut Self {
        self.assertion_data_linker = ass_data_linker;
        self
    }

    // --- reverse asserted roles ---

    /// Port of `CIndividual::getReverseAssertionRoleLinker`.
    pub fn get_reverse_assertion_role_linker(&self) -> &[ReverseRoleAssertion] {
        &self.reverse_assertion_role_linker
    }
    /// Port of `CIndividual::addReverseAssertionRoleLinker`.
    pub fn add_reverse_assertion_role_linker(
        &mut self,
        rev_ass_role_linker: ReverseRoleAssertion,
    ) -> &mut Self {
        self.reverse_assertion_role_linker.insert(0, rev_ass_role_linker);
        self
    }
    /// Port of `CIndividual::setReverseAssertionRoleLinker`.
    pub fn set_reverse_assertion_role_linker(
        &mut self,
        rev_ass_role_linker: Vec<ReverseRoleAssertion>,
    ) -> &mut Self {
        self.reverse_assertion_role_linker = rev_ass_role_linker;
        self
    }

    // --- init / copy ---

    /// Port of `CIndividual::initIndividual` (default `indiID = 0`).
    /// Resets `mTag`, the concept linker, nominal concept and the three flags;
    /// faithfully leaves role/data/reverse linkers, name and data untouched.
    pub fn init_individual(&mut self, indi_id: Cint64) -> &mut Self {
        self.tag = indi_id;
        self.assertion_concept_linker = Vec::new(); // mAssertionConceptLinker = nullptr
        self.nominal_concept = ConceptId::NONE;
        self.anonymous_individual = false;
        self.temporary_individual = false;
        self.fake_individual = false;
        self
    }

    /// Port of `CIndividual::initIndividualCopy`.
    // KONCLUDE-PORT-NOTE[memory-pool]: the C++ allocates each copied
    // `CConceptAssertionLinker` from a `CMemoryAllocationManager`; here the entry
    // is a value pushed into the `Vec`, so no allocator argument is needed.
    pub fn init_individual_copy(&mut self, individual: &Individual) -> &mut Self {
        // mNameLinker = individual->getIndividualNameLinker();
        self.name_linker = individual.name_linker.clone();
        // mTag = individual->mTag;
        self.tag = individual.tag;
        // Iterate the source concept-assertion list head→tail; each
        // addAssertionConceptLinker prepends, so the resulting order is reversed
        // relative to the source — reproduced exactly here.
        for ass_con_it in individual.assertion_concept_linker.iter() {
            let con = ass_con_it.target;
            let negated = ass_con_it.negated;
            // assLinker->initNegLinker(con, negated)
            let ass_linker = ConceptAssertion { target: con, negated };
            self.add_assertion_concept_linker(ass_linker);
        }
        self.nominal_concept = individual.nominal_concept;
        self.anonymous_individual = individual.anonymous_individual;
        self.fake_individual = individual.fake_individual;
        self.temporary_individual = individual.temporary_individual;
        self
    }

    /// Port of `CIndividual::hasAssertedConcept`.
    // KONCLUDE-PORT-NOTE[ownership]: C++ compares
    // `assConcept->getConceptTag() == concept->getConceptTag()`. With concepts
    // addressed by their stable arena `ConceptId`, comparing the ids is the same
    // identity test; the original took a `CConcept*`.
    pub fn has_asserted_concept(&self, concept: ConceptId) -> bool {
        for ass_con in self.assertion_concept_linker.iter() {
            let ass_concept = ass_con.target;
            if ass_concept == concept {
                return true;
            }
        }
        false
    }

    // --- flags ---

    /// Port of `CIndividual::setAnonymousIndividual`.
    pub fn set_anonymous_individual(&mut self, anonymous: bool) -> &mut Self {
        self.anonymous_individual = anonymous;
        self
    }
    /// Port of `CIndividual::isAnonymousIndividual`.
    pub fn is_anonymous_individual(&self) -> bool {
        self.anonymous_individual
    }

    /// Port of `CIndividual::setTemporaryFakeIndividual`
    /// (`mFakeIndividual = mTemporaryIndividual = temporaryFake`).
    pub fn set_temporary_fake_individual(&mut self, temporary_fake: bool) -> &mut Self {
        self.temporary_individual = temporary_fake;
        self.fake_individual = temporary_fake;
        self
    }
    /// Port of `CIndividual::setTemporaryIndividual`.
    pub fn set_temporary_individual(&mut self, temporary: bool) -> &mut Self {
        self.temporary_individual = temporary;
        self
    }
    /// Port of `CIndividual::isTemporaryIndividual`.
    pub fn is_temporary_individual(&self) -> bool {
        self.temporary_individual
    }

    /// Port of `CIndividual::setFakeIndividual`.
    pub fn set_fake_individual(&mut self, fake: bool) -> &mut Self {
        self.fake_individual = fake;
        self
    }
    /// Port of `CIndividual::isFakeIndividual`.
    pub fn is_fake_individual(&self) -> bool {
        self.fake_individual
    }

    // --- individual data ---

    /// Port of `CIndividual::hasIndividualData` (`mIndividualData != nullptr`).
    pub fn has_individual_data(&self) -> bool {
        self.individual_data != INVALID
    }
    /// Port of `CIndividual::getIndividualData`.
    pub fn get_individual_data(&self) -> Cint64 {
        self.individual_data
    }
    /// Port of `CIndividual::setIndividualData`.
    pub fn set_individual_data(&mut self, individual_data: Cint64) -> &mut Self {
        self.individual_data = individual_data;
        self
    }
}

/// Port of `CVariable`.
pub struct Variable {
    // KONCLUDE-PORT-NOTE[ownership]: `CConcept* mNominalConcept` → `ConceptId`.
    /// `CVariable::mNominalConcept`.
    pub nominal_concept: ConceptId,
    /// `CVariable::mPathVariableID`.
    pub path_variable_id: Cint64,
    // KONCLUDE-PORT-NOTE[unclear]: C++ guards `mDebugVariableName` behind
    // `#ifndef KONCLUDE_FORCE_ALL_DEBUG_DEACTIVATED`; kept unconditionally here.
    /// `CVariable::mDebugVariableName`.
    pub debug_variable_name: String,
}

impl Variable {
    /// Port of `CVariable::CVariable()` (`mNominalConcept = nullptr`).
    // KONCLUDE-PORT-NOTE[uninit]: C++ leaves `mPathVariableID` uninitialised in
    // the constructor (set later by `initVariable`); defaulted to `INVALID` here.
    pub fn new() -> Self {
        Variable {
            nominal_concept: ConceptId::NONE,
            path_variable_id: INVALID,
            debug_variable_name: String::new(),
        }
    }

    /// Port of `CVariable::initVariable`.
    pub fn init_variable(&mut self, nominal_concept: ConceptId, path_variable_id: Cint64) -> &mut Self {
        self.nominal_concept = nominal_concept;
        self.path_variable_id = path_variable_id;
        self
    }

    /// Port of `CVariable::isNominalVariable` (`mNominalConcept != nullptr`).
    pub fn is_nominal_variable(&self) -> bool {
        self.nominal_concept.is_some()
    }

    /// Port of `CVariable::getNominalVariableConcept`.
    pub fn get_nominal_variable_concept(&self) -> ConceptId {
        self.nominal_concept
    }

    /// Port of `CVariable::getPathVariableID`.
    pub fn get_path_variable_id(&self) -> Cint64 {
        self.path_variable_id
    }

    /// Port of `CVariable::operator<=(const CVariable& beforeData)`
    /// (`return this <= &beforeData;`).
    // KONCLUDE-PORT-NOTE[pointer-alias]: the original orders two variables by
    // their object addresses, not by any field. Reproduced with raw-pointer
    // comparison; this is identity/address ordering, with no semantic meaning.
    pub fn le(&self, before_data: &Variable) -> bool {
        (self as *const Variable) <= (before_data as *const Variable)
    }

    /// Port of `CVariable::operator<=(const CVariable*& beforeData)`
    /// (`return this <= beforeData;`).
    // KONCLUDE-PORT-NOTE[overload]: Rust has no operator overloading; the
    // pointer-arg overload becomes a separate method. [pointer-alias] as above.
    pub fn le_ptr(&self, before_data: *const Variable) -> bool {
        (self as *const Variable) <= before_data
    }
}

impl Default for Variable {
    fn default() -> Self {
        Variable::new()
    }
}
