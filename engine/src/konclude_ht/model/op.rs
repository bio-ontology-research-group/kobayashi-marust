//! `op` — operator codes (`CCxxx`) + the `CConceptOperator` flag-group dispatch.
//!
//! Faithful port of two Konclude headers:
//!   * `Reasoner/Ontology/OntologySettings.h`  — the `static const qint64 CCxxx`
//!     concept-constructor codes (the *codes*, with their +/- polarity).
//!   * `Reasoner/Ontology/CConceptOperator.{h,cpp}` — the runtime wrapper that
//!     maps a code to a single bit (`CCF_*`) and exposes the grouped bit-tests
//!     (`CCFS_*`) used to classify a concept operator at a glance.
//!
//! Every integer value and polarity is kept EXACTLY. The bit flags are kept at
//! their EXACT bit positions; the `CCFS_*` groups are kept as the EXACT bitwise
//! OR of their members. Predicate methods translate each group test one-to-one.

#![allow(dead_code)]

use super::substrate::Cint64;

// =============================================================================
// Concept Constructor Codes  (port of OntologySettings.h, lines ~91-183)
//
// These are the `static const qint64 CCxxx` codes. The +/- polarity is part of
// the encoding (a constructor and its dual share |code|, opposite sign — e.g.
// CCAND = 3 / CCOR = -3, CCALL = 5 / CCSOME = -5). Kept verbatim.
// =============================================================================

/// Port of `CCNONE`.
pub const CCNONE: Cint64 = 0;
/// Port of `CCATOM`.
pub const CCATOM: Cint64 = 0;

/// Port of `CCTOP`.
pub const CCTOP: Cint64 = 1;
/// Port of `CCBOTTOM`.
pub const CCBOTTOM: Cint64 = -1;

/// Port of `CCNOT`.
pub const CCNOT: Cint64 = -2;

/// Port of `CCAND`.
pub const CCAND: Cint64 = 3;
/// Port of `CCOR`.
pub const CCOR: Cint64 = -3;

/// Port of `CCATMOST`.
pub const CCATMOST: Cint64 = 4;
/// Port of `CCATLEAST`.
pub const CCATLEAST: Cint64 = -4;

/// Port of `CCALL`.
pub const CCALL: Cint64 = 5;
/// Port of `CCSOME`.
pub const CCSOME: Cint64 = -5;

/// Port of `CCEQ`.
pub const CCEQ: Cint64 = 6;
/// Port of `CCSUB`.
pub const CCSUB: Cint64 = 7;

/// Port of `CCNOMINAL`.
pub const CCNOMINAL: Cint64 = 8;

/// Port of `CCSELF`.
pub const CCSELF: Cint64 = 9;

/// Port of `CCAQCHOOCE`.
pub const CCAQCHOOCE: Cint64 = 10;
/// Port of `CCAQALL`.
pub const CCAQALL: Cint64 = 11;
/// Port of `CCAQSOME`.
pub const CCAQSOME: Cint64 = -11;
/// Port of `CCAQAND`.
pub const CCAQAND: Cint64 = 12;

/// Port of `CCVALUE`.
pub const CCVALUE: Cint64 = 13;

/// Port of `CCNOMVAR`.
pub const CCNOMVAR: Cint64 = 14;
/// Port of `CCNOMTEMPLREF`.
pub const CCNOMTEMPLREF: Cint64 = 15;

/// Port of `CCIMPL`.
pub const CCIMPL: Cint64 = 16;
/// Port of `CCIMPLTRIG`.
pub const CCIMPLTRIG: Cint64 = 17;
/// Port of `CCIMPLALL`.
pub const CCIMPLALL: Cint64 = 18;
/// Port of `CCIMPLAQALL`.
pub const CCIMPLAQALL: Cint64 = 19;
/// Port of `CCIMPLAQAND`.
pub const CCIMPLAQAND: Cint64 = 20;

/// Port of `CCBRANCHIMPL`.
pub const CCBRANCHIMPL: Cint64 = 21;
/// Port of `CCBRANCHTRIG`.
pub const CCBRANCHTRIG: Cint64 = 22;
/// Port of `CCBRANCHALL`.
pub const CCBRANCHALL: Cint64 = 23;
/// Port of `CCBRANCHAQALL`.
pub const CCBRANCHAQALL: Cint64 = 24;
/// Port of `CCBRANCHAQAND`.
pub const CCBRANCHAQAND: Cint64 = 25;

/// Port of `CCEQCAND`.
pub const CCEQCAND: Cint64 = 26;

/// Port of `CCPBINDTRIG`.
pub const CCPBINDTRIG: Cint64 = 27;
/// Port of `CCPBINDIMPL`.
pub const CCPBINDIMPL: Cint64 = 28;
/// Port of `CCPBINDGROUND`.
pub const CCPBINDGROUND: Cint64 = 29;
/// Port of `CCPBINDALL`.
pub const CCPBINDALL: Cint64 = 30;
/// Port of `CCPBINDAND`.
pub const CCPBINDAND: Cint64 = 31;
/// Port of `CCPBINDAQAND`.
pub const CCPBINDAQAND: Cint64 = 32;
/// Port of `CCPBINDAQALL`.
pub const CCPBINDAQALL: Cint64 = 33;
/// Port of `CCPBINDVARIABLE`.
pub const CCPBINDVARIABLE: Cint64 = 34;
/// Port of `CCPBINDCYCLE`.
pub const CCPBINDCYCLE: Cint64 = 35;

/// Port of `CCVARBINDTRIG`.
pub const CCVARBINDTRIG: Cint64 = 36;
/// Port of `CCVARBINDJOIN`.
pub const CCVARBINDJOIN: Cint64 = 37;
/// Port of `CCVARBINDGROUND`.
pub const CCVARBINDGROUND: Cint64 = 38;
/// Port of `CCVARBINDALL`.
pub const CCVARBINDALL: Cint64 = 39;
/// Port of `CCVARBINDAND`.
pub const CCVARBINDAND: Cint64 = 40;
/// Port of `CCVARBINDAQAND`.
pub const CCVARBINDAQAND: Cint64 = 41;
/// Port of `CCVARBINDAQALL`.
pub const CCVARBINDAQALL: Cint64 = 42;
/// Port of `CCVARBINDVARIABLE`.
pub const CCVARBINDVARIABLE: Cint64 = 43;
/// Port of `CCVARBINDIMPL`.
pub const CCVARBINDIMPL: Cint64 = 44;

/// Port of `CCVARPBACKTRIG`.
pub const CCVARPBACKTRIG: Cint64 = 45;
/// Port of `CCVARPBACKALL`.
pub const CCVARPBACKALL: Cint64 = 46;
/// Port of `CCVARPBACKAQAND`.
pub const CCVARPBACKAQAND: Cint64 = 47;
/// Port of `CCVARPBACKAQALL`.
pub const CCVARPBACKAQALL: Cint64 = 48;

/// Port of `CCBACKACTIVTRIG`.
pub const CCBACKACTIVTRIG: Cint64 = 49;
/// Port of `CCBACKACTIVIMPL`.
pub const CCBACKACTIVIMPL: Cint64 = 50;

/// Port of `CCDATATYPE`.
pub const CCDATATYPE: Cint64 = 51;
/// Port of `CCDATALITERAL`.
pub const CCDATALITERAL: Cint64 = 52;
/// Port of `CCDATARESTRICTION`.
pub const CCDATARESTRICTION: Cint64 = 53;

/// Port of `CCMARKER`.
pub const CCMARKER: Cint64 = 54;

/// Port of `CCNOMINALIMPLI`.
pub const CCNOMINALIMPLI: Cint64 = 55;
/// Port of `CCDATATYPEIMPLI`.
pub const CCDATATYPEIMPLI: Cint64 = 56;
/// Port of `CCDATALITERALIMPLI`.
pub const CCDATALITERALIMPLI: Cint64 = 57;
/// Port of `CCDATARESTRICTIONIMPLI`.
pub const CCDATARESTRICTIONIMPLI: Cint64 = 58;

/// Port of `CCVARBINDPREPARE`.
pub const CCVARBINDPREPARE: Cint64 = 59;
/// Port of `CCVARBINDFINALZE`.
pub const CCVARBINDFINALZE: Cint64 = 60;

// =============================================================================
// Concept-operator type flags  (port of CConceptOperator.h, lines ~67-135)
//
// Each code maps to a single set bit. Kept at their EXACT bit positions.
// Konclude writes these as `Q_UINT64_C(0x....)`; the port uses i64 (== Cint64),
// so the only one that differs in textual form is the sign bit CCF_SPECIAL.
// =============================================================================

/// Port of `CConceptOperator::CCF_NONE`.
pub const CCF_NONE: Cint64 = 0x0000000000000001;
/// Port of `CConceptOperator::CCF_ATOM`.
pub const CCF_ATOM: Cint64 = 0x0000000000000001;
/// Port of `CConceptOperator::CCF_TOP`.
pub const CCF_TOP: Cint64 = 0x0000000000000002;
/// Port of `CConceptOperator::CCF_BOTTOM`.
pub const CCF_BOTTOM: Cint64 = 0x0000000000000004;
/// Port of `CConceptOperator::CCF_NOT`.
pub const CCF_NOT: Cint64 = 0x0000000000000008;
/// Port of `CConceptOperator::CCF_AND`.
pub const CCF_AND: Cint64 = 0x0000000000000010;
/// Port of `CConceptOperator::CCF_OR`.
pub const CCF_OR: Cint64 = 0x0000000000000020;
/// Port of `CConceptOperator::CCF_ATMOST`.
pub const CCF_ATMOST: Cint64 = 0x0000000000000040;
/// Port of `CConceptOperator::CCF_ATLEAST`.
pub const CCF_ATLEAST: Cint64 = 0x0000000000000080;
/// Port of `CConceptOperator::CCF_ALL`.
pub const CCF_ALL: Cint64 = 0x0000000000000100;
/// Port of `CConceptOperator::CCF_SOME`.
pub const CCF_SOME: Cint64 = 0x0000000000000200;
/// Port of `CConceptOperator::CCF_EQ`.
pub const CCF_EQ: Cint64 = 0x0000000000000400;
/// Port of `CConceptOperator::CCF_SUB`.
pub const CCF_SUB: Cint64 = 0x0000000000000800;
/// Port of `CConceptOperator::CCF_NOMINAL`.
pub const CCF_NOMINAL: Cint64 = 0x0000000000001000;
/// Port of `CConceptOperator::CCF_SELF`.
pub const CCF_SELF: Cint64 = 0x0000000000002000;
/// Port of `CConceptOperator::CCF_AQCHOOCE`.
pub const CCF_AQCHOOCE: Cint64 = 0x0000000000004000;
/// Port of `CConceptOperator::CCF_AQALL`.
pub const CCF_AQALL: Cint64 = 0x0000000000008000;
/// Port of `CConceptOperator::CCF_AQSOME`.
pub const CCF_AQSOME: Cint64 = 0x0000000000010000;
/// Port of `CConceptOperator::CCF_AQAND`.
pub const CCF_AQAND: Cint64 = 0x0000000000020000;
/// Port of `CConceptOperator::CCF_VALUE`.
pub const CCF_VALUE: Cint64 = 0x0000000000040000;
/// Port of `CConceptOperator::CCF_NOMVAR`.
pub const CCF_NOMVAR: Cint64 = 0x0000000000080000;
/// Port of `CConceptOperator::CCF_NOMTEMPLREF`.
pub const CCF_NOMTEMPLREF: Cint64 = 0x0000000000100000;
/// Port of `CConceptOperator::CCF_IMPL`.
pub const CCF_IMPL: Cint64 = 0x0000000000200000;
/// Port of `CConceptOperator::CCF_IMPLTRIG`.
pub const CCF_IMPLTRIG: Cint64 = 0x0000000000400000;
/// Port of `CConceptOperator::CCF_IMPLALL`.
pub const CCF_IMPLALL: Cint64 = 0x0000000000800000;
/// Port of `CConceptOperator::CCF_IMPLAQALL`.
pub const CCF_IMPLAQALL: Cint64 = 0x0000000001000000;
/// Port of `CConceptOperator::CCF_IMPLAQAND`.
pub const CCF_IMPLAQAND: Cint64 = 0x0000000002000000;
/// Port of `CConceptOperator::CCF_BRANCHIMPL`.
pub const CCF_BRANCHIMPL: Cint64 = 0x0000000004000000;
/// Port of `CConceptOperator::CCF_BRANCHTRIG`.
pub const CCF_BRANCHTRIG: Cint64 = 0x0000000008000000;
/// Port of `CConceptOperator::CCF_BRANCHALL`.
pub const CCF_BRANCHALL: Cint64 = 0x0000000010000000;
/// Port of `CConceptOperator::CCF_BRANCHAQALL`.
pub const CCF_BRANCHAQALL: Cint64 = 0x0000000020000000;
/// Port of `CConceptOperator::CCF_BRANCHAQAND`.
pub const CCF_BRANCHAQAND: Cint64 = 0x0000000040000000;
/// Port of `CConceptOperator::CCF_EQCAND`.
pub const CCF_EQCAND: Cint64 = 0x0000000080000000;
/// Port of `CConceptOperator::CCF_PBINDTRIG`.
pub const CCF_PBINDTRIG: Cint64 = 0x0000000100000000;
/// Port of `CConceptOperator::CCF_PBINDIMPL`.
pub const CCF_PBINDIMPL: Cint64 = 0x0000000200000000;
/// Port of `CConceptOperator::CCF_PBINDGROUND`.
pub const CCF_PBINDGROUND: Cint64 = 0x0000000400000000;
/// Port of `CConceptOperator::CCF_PBINDALL`.
pub const CCF_PBINDALL: Cint64 = 0x0000000800000000;
/// Port of `CConceptOperator::CCF_PBINDAND`.
pub const CCF_PBINDAND: Cint64 = 0x0000001000000000;
/// Port of `CConceptOperator::CCF_PBINDAQAND`.
pub const CCF_PBINDAQAND: Cint64 = 0x0000002000000000;
/// Port of `CConceptOperator::CCF_PBINDAQALL`.
pub const CCF_PBINDAQALL: Cint64 = 0x0000004000000000;
/// Port of `CConceptOperator::CCF_PBINDVARIABLE`.
pub const CCF_PBINDVARIABLE: Cint64 = 0x0000008000000000;
/// Port of `CConceptOperator::CCF_PBINDCYCLE`.
pub const CCF_PBINDCYCLE: Cint64 = 0x0000010000000000;
/// Port of `CConceptOperator::CCF_VARBINDTRIG`.
pub const CCF_VARBINDTRIG: Cint64 = 0x0000020000000000;
/// Port of `CConceptOperator::CCF_VARBINDJOIN`.
pub const CCF_VARBINDJOIN: Cint64 = 0x0000040000000000;
/// Port of `CConceptOperator::CCF_VARBINDGROUND`.
pub const CCF_VARBINDGROUND: Cint64 = 0x0000080000000000;
/// Port of `CConceptOperator::CCF_VARBINDALL`.
pub const CCF_VARBINDALL: Cint64 = 0x0000100000000000;
/// Port of `CConceptOperator::CCF_VARBINDAND`.
pub const CCF_VARBINDAND: Cint64 = 0x0000200000000000;
/// Port of `CConceptOperator::CCF_VARBINDAQAND`.
pub const CCF_VARBINDAQAND: Cint64 = 0x0000400000000000;
/// Port of `CConceptOperator::CCF_VARBINDAQALL`.
pub const CCF_VARBINDAQALL: Cint64 = 0x0000800000000000;
/// Port of `CConceptOperator::CCF_VARBINDVARIABLE`.
pub const CCF_VARBINDVARIABLE: Cint64 = 0x0001000000000000;
/// Port of `CConceptOperator::CCF_VARBINDIMPL`.
pub const CCF_VARBINDIMPL: Cint64 = 0x0002000000000000;
/// Port of `CConceptOperator::CCF_VARPBACKTRIG`.
pub const CCF_VARPBACKTRIG: Cint64 = 0x0004000000000000;
/// Port of `CConceptOperator::CCF_VARPBACKALL`.
pub const CCF_VARPBACKALL: Cint64 = 0x0008000000000000;
/// Port of `CConceptOperator::CCF_VARPBACKAQAND`.
pub const CCF_VARPBACKAQAND: Cint64 = 0x0010000000000000;
/// Port of `CConceptOperator::CCF_VARPBACKAQALL`.
pub const CCF_VARPBACKAQALL: Cint64 = 0x0020000000000000;
/// Port of `CConceptOperator::CCF_BACKACTIVTRIG`.
pub const CCF_BACKACTIVTRIG: Cint64 = 0x0040000000000000;
/// Port of `CConceptOperator::CCF_BACKACTIVIMPL`.
pub const CCF_BACKACTIVIMPL: Cint64 = 0x0080000000000000;

/// Port of `CConceptOperator::CCF_DATATYPE`.
pub const CCF_DATATYPE: Cint64 = 0x0100000000000000;
/// Port of `CConceptOperator::CCF_DATALITERAL`.
pub const CCF_DATALITERAL: Cint64 = 0x0200000000000000;
/// Port of `CConceptOperator::CCF_DATARESTRICTION`.
pub const CCF_DATARESTRICTION: Cint64 = 0x0400000000000000;

/// Port of `CConceptOperator::CCF_MARKER`.
pub const CCF_MARKER: Cint64 = 0x0800000000000000;

// In the C++ header CCF_NOMINALIMPLI/CCF_DATATYPEIMPLI/CCF_DATALITERALIMPLI/
// CCF_DATARESTRICTIONIMPLI (bits 60-63) are commented out; the sign bit is
// reused for CCF_SPECIAL. Preserved as the same commented-out set.
//
//   const static cint64 CCF_NOMINALIMPLI        = 0x1000000000000000;
//   const static cint64 CCF_DATATYPEIMPLI       = 0x2000000000000000;
//   const static cint64 CCF_DATALITERALIMPLI    = 0x4000000000000000;
//   const static cint64 CCF_DATARESTRICTIONIMPLI= 0x8000000000000000;

/// Port of `CConceptOperator::CCF_SPECIAL`.
///
/// KONCLUDE-PORT-NOTE[int-width]: the C++ value is `Q_UINT64_C(0x8000000000000000)`
/// (bit 63). `Cint64` is `i64`, so this is the sign bit; written as a `u64`
/// literal cast to `i64` to keep the EXACT bit pattern (== `i64::MIN`). Used only
/// through bitwise `&` masks, so the signed interpretation is irrelevant.
pub const CCF_SPECIAL: Cint64 = 0x8000000000000000u64 as Cint64;

// =============================================================================
// Grouped flag sets  (port of CConceptOperator.h, lines ~144-178)
//
// Each `CCFS_*` is the EXACT bitwise OR of its member `CCF_*` flags, in the
// same order as the source.
// =============================================================================

/// Port of `CConceptOperator::CCFS_AND_TYPE`.
pub const CCFS_AND_TYPE: Cint64 = CCF_AND | CCF_PBINDAND | CCF_VARBINDAND | CCF_TOP;
/// Port of `CConceptOperator::CCFS_TRIG_TYPE`.
pub const CCFS_TRIG_TYPE: Cint64 =
    CCF_IMPLTRIG | CCF_BRANCHTRIG | CCF_PBINDTRIG | CCF_VARBINDTRIG | CCF_VARPBACKTRIG;
/// Port of `CConceptOperator::CCFS_ALL_TYPE`.
pub const CCFS_ALL_TYPE: Cint64 =
    CCF_VARPBACKALL | CCF_VARBINDALL | CCF_PBINDALL | CCF_BRANCHALL | CCF_IMPLALL | CCF_ALL;

/// Port of `CConceptOperator::CCFS_AQAND_TYPE`.
pub const CCFS_AQAND_TYPE: Cint64 = CCF_AQAND
    | CCF_IMPLAQAND
    | CCF_BRANCHAQAND
    | CCF_PBINDAQAND
    | CCF_VARBINDAQAND
    | CCF_VARPBACKAQAND;
/// Port of `CConceptOperator::CCFS_AQALL_TYPE`.
pub const CCFS_AQALL_TYPE: Cint64 = CCF_AQALL
    | CCF_IMPLAQALL
    | CCF_BRANCHAQALL
    | CCF_PBINDAQALL
    | CCF_VARBINDAQALL
    | CCF_VARPBACKAQALL;

/// Port of `CConceptOperator::CCFS_AQ_TYPE`.
pub const CCFS_AQ_TYPE: Cint64 = CCFS_AQAND_TYPE | CCFS_AQALL_TYPE;
/// Port of `CConceptOperator::CCFS_ALL_AQALL_TYPE`.
pub const CCFS_ALL_AQALL_TYPE: Cint64 = CCFS_ALL_TYPE | CCFS_AQALL_TYPE;
/// Port of `CConceptOperator::CCFS_TRIG_AND_AQAND_TYPE`.
pub const CCFS_TRIG_AND_AQAND_TYPE: Cint64 = CCFS_AND_TYPE | CCFS_TRIG_TYPE | CCFS_AQAND_TYPE;
/// Port of `CConceptOperator::CCFS_AND_AQAND_TYPE`.
pub const CCFS_AND_AQAND_TYPE: Cint64 = CCFS_AND_TYPE | CCFS_AQAND_TYPE;
/// Port of `CConceptOperator::CCFS_AQAND_AQALL_TYPE`.
pub const CCFS_AQAND_AQALL_TYPE: Cint64 = CCFS_AQAND_TYPE | CCFS_AQALL_TYPE;

/// Port of `CConceptOperator::CCFS_SOME_TYPE`.
pub const CCFS_SOME_TYPE: Cint64 = CCF_SOME | CCF_AQSOME;

/// Port of `CConceptOperator::CCFS_IMPL_TYPE`.
pub const CCFS_IMPL_TYPE: Cint64 =
    CCF_VARBINDIMPL | CCF_PBINDIMPL | CCF_BRANCHIMPL | CCF_IMPL | CCF_BACKACTIVIMPL;
// CCFS_EXT_IMPL_TYPE is commented out in the source (depends on the disabled
// CCF_*IMPLI flags); preserved as a comment:
//   CCFS_EXT_IMPL_TYPE = CCFS_IMPL_TYPE | CCF_NOMINALIMPLI | CCF_DATATYPEIMPLI
//                        | CCF_DATALITERALIMPLI | CCF_DATARESTRICTIONIMPLI;

/// Port of `CConceptOperator::CCFS_PROPAGATION_BIND_TYPE`.
pub const CCFS_PROPAGATION_BIND_TYPE: Cint64 = CCF_PBINDTRIG
    | CCF_PBINDIMPL
    | CCF_PBINDGROUND
    | CCF_PBINDALL
    | CCF_PBINDAND
    | CCF_PBINDAQAND
    | CCF_PBINDAQALL
    | CCF_PBINDVARIABLE
    | CCF_PBINDCYCLE;
/// Port of `CConceptOperator::CCFS_VARIABLE_BIND_TYPE`.
pub const CCFS_VARIABLE_BIND_TYPE: Cint64 = CCF_VARBINDTRIG
    | CCF_VARBINDJOIN
    | CCF_VARBINDGROUND
    | CCF_VARBINDALL
    | CCF_VARBINDAND
    | CCF_VARBINDAQAND
    | CCF_VARBINDAQALL
    | CCF_VARBINDVARIABLE
    | CCF_VARBINDIMPL;
/// Port of `CConceptOperator::CCFS_BACK_PROPAGATION_TYPE`.
pub const CCFS_BACK_PROPAGATION_TYPE: Cint64 = CCF_VARPBACKTRIG
    | CCF_VARPBACKALL
    | CCF_VARPBACKAQAND
    | CCF_VARPBACKAQALL
    | CCF_BACKACTIVTRIG
    | CCF_BACKACTIVIMPL;

/// Port of `CConceptOperator::CCFS_PROPAGATION_TYPE`.
pub const CCFS_PROPAGATION_TYPE: Cint64 =
    CCFS_PROPAGATION_BIND_TYPE | CCFS_VARIABLE_BIND_TYPE | CCFS_BACK_PROPAGATION_TYPE;

/// Port of `CConceptOperator::CCFS_PROPAGATION_ALL_TYPE`.
pub const CCFS_PROPAGATION_ALL_TYPE: Cint64 = CCF_PBINDALL
    | CCF_VARBINDALL
    | CCF_VARPBACKALL
    | CCF_PBINDAQALL
    | CCF_VARBINDAQALL
    | CCF_VARPBACKAQALL;

/// Port of `CConceptOperator::CCFS_PROPAGATION_AND_TYPE`.
pub const CCFS_PROPAGATION_AND_TYPE: Cint64 = CCF_PBINDTRIG
    | CCF_VARBINDTRIG
    | CCF_VARPBACKTRIG
    | CCF_PBINDAND
    | CCF_VARBINDAND
    | CCF_PBINDAQAND
    | CCF_VARBINDAQAND
    | CCF_BACKACTIVTRIG;

/// Port of `CConceptOperator::CCFS_POSSIBLE_ROLE_CREATION_TYPE`.
pub const CCFS_POSSIBLE_ROLE_CREATION_TYPE: Cint64 =
    CCF_SOME | CCF_AQSOME | CCF_ALL | CCF_ATLEAST | CCF_ATMOST;

/// Port of `CConceptOperator::CCFS_ABSORPTION_RELEVANT_TYPE`.
pub const CCFS_ABSORPTION_RELEVANT_TYPE: Cint64 = CCFS_TRIG_TYPE
    | CCFS_IMPL_TYPE
    | CCF_IMPLAQALL
    | CCF_BRANCHAQALL
    | CCF_PBINDAQALL
    | CCF_VARBINDAQALL
    | CCF_VARPBACKAQALL
    | CCF_IMPLAQAND
    | CCF_BRANCHAQAND
    | CCF_PBINDAQAND
    | CCF_VARBINDAQAND
    | CCF_VARPBACKAQAND;

/// Port of `CConceptOperator::CCFS_DATATYPE_RELATED_TYPE`.
pub const CCFS_DATATYPE_RELATED_TYPE: Cint64 = CCF_DATATYPE | CCF_DATALITERAL | CCF_DATARESTRICTION;

// =============================================================================
// CConceptOperator
// =============================================================================

/// Port of `CConceptOperator`.
///
/// Wraps a concept-constructor code (`mOperatorCode`) and the single type bit it
/// maps to (`mTypeFlag`). The bit is computed once in the constructor; the
/// flag-group predicates below are `(mTypeFlag & CCFS_*)` tests, mirroring how
/// the engine classifies an operator.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct ConceptOperator {
    /// Port of `CConceptOperator::mOperatorCode`.
    operator_code: Cint64,
    /// Port of `CConceptOperator::mTypeFlag`.
    type_flag: Cint64,
}

impl ConceptOperator {
    /// Port of `CConceptOperator::CConceptOperator(cint64 opCode)`.
    ///
    /// Maps the operator code to its single type bit. Anything not explicitly
    /// listed (including the disabled `CC*IMPLI` codes and `CCVARBIND{PREPARE,
    /// FINALZE}`) falls through to `CCF_SPECIAL`, exactly as the C++ else-branch.
    pub fn new(op_code: Cint64) -> ConceptOperator {
        let type_flag = if op_code == CCNONE {
            CCF_NONE
        } else if op_code == CCTOP {
            CCF_TOP
        } else if op_code == CCBOTTOM {
            CCF_BOTTOM
        } else if op_code == CCNOT {
            CCF_NOT
        } else if op_code == CCAND {
            CCF_AND
        } else if op_code == CCOR {
            CCF_OR
        } else if op_code == CCATMOST {
            CCF_ATMOST
        } else if op_code == CCATLEAST {
            CCF_ATLEAST
        } else if op_code == CCALL {
            CCF_ALL
        } else if op_code == CCSOME {
            CCF_SOME
        } else if op_code == CCEQ {
            CCF_EQ
        } else if op_code == CCSUB {
            CCF_SUB
        } else if op_code == CCNOMINAL {
            CCF_NOMINAL
        } else if op_code == CCSELF {
            CCF_SELF
        } else if op_code == CCAQCHOOCE {
            CCF_AQCHOOCE
        } else if op_code == CCAQALL {
            CCF_AQALL
        } else if op_code == CCAQSOME {
            CCF_AQSOME
        } else if op_code == CCAQAND {
            CCF_AQAND
        } else if op_code == CCVALUE {
            CCF_VALUE
        } else if op_code == CCNOMVAR {
            CCF_NOMVAR
        } else if op_code == CCNOMTEMPLREF {
            CCF_NOMTEMPLREF
        } else if op_code == CCIMPL {
            CCF_IMPL
        } else if op_code == CCIMPLTRIG {
            CCF_IMPLTRIG
        } else if op_code == CCIMPLALL {
            CCF_IMPLALL
        } else if op_code == CCIMPLAQALL {
            CCF_IMPLAQALL
        } else if op_code == CCIMPLAQAND {
            CCF_IMPLAQAND
        } else if op_code == CCBRANCHIMPL {
            CCF_BRANCHIMPL
        } else if op_code == CCBRANCHTRIG {
            CCF_BRANCHTRIG
        } else if op_code == CCBRANCHALL {
            CCF_BRANCHALL
        } else if op_code == CCBRANCHAQALL {
            CCF_BRANCHAQALL
        } else if op_code == CCBRANCHAQAND {
            CCF_BRANCHAQAND
        } else if op_code == CCEQCAND {
            CCF_EQCAND
        } else if op_code == CCPBINDTRIG {
            CCF_PBINDTRIG
        } else if op_code == CCPBINDIMPL {
            CCF_PBINDIMPL
        } else if op_code == CCPBINDGROUND {
            CCF_PBINDGROUND
        } else if op_code == CCPBINDALL {
            CCF_PBINDALL
        } else if op_code == CCPBINDAND {
            CCF_PBINDAND
        } else if op_code == CCPBINDAQAND {
            CCF_PBINDAQAND
        } else if op_code == CCPBINDAQALL {
            CCF_PBINDAQALL
        } else if op_code == CCPBINDVARIABLE {
            CCF_PBINDVARIABLE
        } else if op_code == CCPBINDCYCLE {
            CCF_PBINDCYCLE
        } else if op_code == CCVARBINDTRIG {
            CCF_VARBINDTRIG
        } else if op_code == CCVARBINDJOIN {
            CCF_VARBINDJOIN
        } else if op_code == CCVARBINDGROUND {
            CCF_VARBINDGROUND
        } else if op_code == CCVARBINDALL {
            CCF_VARBINDALL
        } else if op_code == CCVARBINDAND {
            CCF_VARBINDAND
        } else if op_code == CCVARBINDAQAND {
            CCF_VARBINDAQAND
        } else if op_code == CCVARBINDAQALL {
            CCF_VARBINDAQALL
        } else if op_code == CCVARBINDVARIABLE {
            CCF_VARBINDVARIABLE
        } else if op_code == CCVARBINDIMPL {
            CCF_VARBINDIMPL
        } else if op_code == CCVARPBACKTRIG {
            CCF_VARPBACKTRIG
        } else if op_code == CCVARPBACKALL {
            CCF_VARPBACKALL
        } else if op_code == CCVARPBACKAQAND {
            CCF_VARPBACKAQAND
        } else if op_code == CCVARPBACKAQALL {
            CCF_VARPBACKAQALL
        } else if op_code == CCBACKACTIVTRIG {
            CCF_BACKACTIVTRIG
        } else if op_code == CCBACKACTIVIMPL {
            CCF_BACKACTIVIMPL
        } else if op_code == CCDATATYPE {
            CCF_DATATYPE
        } else if op_code == CCDATALITERAL {
            CCF_DATALITERAL
        } else if op_code == CCDATARESTRICTION {
            CCF_DATARESTRICTION
        } else if op_code == CCMARKER {
            CCF_MARKER
        // The CC*IMPLI branches are commented out in the C++ constructor (their
        // CCF_*IMPLI flags are disabled), so those codes fall through to SPECIAL:
        //   } else if op_code == CCNOMINALIMPLI { CCF_NOMINALIMPLI
        //   } else if op_code == CCDATATYPEIMPLI { CCF_DATATYPEIMPLI
        //   } else if op_code == CCDATALITERALIMPLI { CCF_DATALITERALIMPLI
        //   } else if op_code == CCDATARESTRICTIONIMPLI { CCF_DATARESTRICTIONIMPLI
        } else {
            CCF_SPECIAL
        };
        ConceptOperator {
            operator_code: op_code,
            type_flag,
        }
    }

    /// Port of `CConceptOperator::getOperatorCode()`.
    pub fn get_operator_code(&self) -> Cint64 {
        self.operator_code
    }

    /// Port of `CConceptOperator::getOperatorFlag()`.
    pub fn get_operator_flag(&self) -> Cint64 {
        self.type_flag
    }

    /// Port of `CConceptOperator::hasPartialOperatorCodeFlag(cint64)`.
    ///
    /// True iff the operator's type bit intersects `operator_code_flag`.
    pub fn has_partial_operator_code_flag(&self, operator_code_flag: Cint64) -> bool {
        (self.type_flag & operator_code_flag) != 0
    }

    /// Port of `CConceptOperator::hasAllOperatorCodeFlags(cint64)`.
    ///
    /// KONCLUDE-PORT-NOTE[unclear]: the C++ body is
    /// `return (mTypeFlag & operatorCodeFlags) != operatorCodeFlags;` — i.e. it
    /// returns true when the operator does NOT carry all of `operatorCodeFlags`
    /// (the opposite of what the name suggests). Ported verbatim, including the
    /// apparent inversion, to stay byte-faithful; callers (if any) rely on the
    /// actual C++ behaviour, not the name.
    pub fn has_all_operator_code_flags(&self, operator_code_flags: Cint64) -> bool {
        (self.type_flag & operator_code_flags) != operator_code_flags
    }

    // -------------------------------------------------------------------------
    // Flag-group predicates.
    //
    // KONCLUDE-PORT-NOTE[api]: Konclude does not declare one named method per
    // `CCFS_*` group; call sites write
    // `op->hasPartialOperatorCodeFlag(CConceptOperator::CCFS_X)` inline. The port
    // exposes one predicate per group (named `is_<group>_type`) that performs the
    // exact same `hasPartialOperatorCodeFlag(CCFS_X)` test, so the call sites
    // read identically and the bit logic is unchanged. The originating group
    // constant is named in each doc-comment.
    // -------------------------------------------------------------------------

    /// `hasPartialOperatorCodeFlag(CCFS_AND_TYPE)`.
    pub fn is_and_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_AND_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_TRIG_TYPE)`.
    pub fn is_trig_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_TRIG_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_ALL_TYPE)`.
    pub fn is_all_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_ALL_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_AQAND_TYPE)`.
    pub fn is_aqand_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_AQAND_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_AQALL_TYPE)`.
    pub fn is_aqall_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_AQALL_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_AQ_TYPE)`.
    pub fn is_aq_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_AQ_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_ALL_AQALL_TYPE)`.
    pub fn is_all_aqall_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_ALL_AQALL_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_TRIG_AND_AQAND_TYPE)`.
    pub fn is_trig_and_aqand_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_TRIG_AND_AQAND_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_AND_AQAND_TYPE)`.
    pub fn is_and_aqand_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_AND_AQAND_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_AQAND_AQALL_TYPE)`.
    pub fn is_aqand_aqall_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_AQAND_AQALL_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_SOME_TYPE)`.
    pub fn is_some_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_SOME_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_IMPL_TYPE)`.
    pub fn is_impl_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_IMPL_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_PROPAGATION_BIND_TYPE)`.
    pub fn is_propagation_bind_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_PROPAGATION_BIND_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_VARIABLE_BIND_TYPE)`.
    pub fn is_variable_bind_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_VARIABLE_BIND_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_BACK_PROPAGATION_TYPE)`.
    pub fn is_back_propagation_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_BACK_PROPAGATION_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_PROPAGATION_TYPE)`.
    pub fn is_propagation_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_PROPAGATION_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_PROPAGATION_ALL_TYPE)`.
    pub fn is_propagation_all_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_PROPAGATION_ALL_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_PROPAGATION_AND_TYPE)`.
    pub fn is_propagation_and_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_PROPAGATION_AND_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_POSSIBLE_ROLE_CREATION_TYPE)`.
    pub fn is_possible_role_creation_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_POSSIBLE_ROLE_CREATION_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_ABSORPTION_RELEVANT_TYPE)`.
    pub fn is_absorption_relevant_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_ABSORPTION_RELEVANT_TYPE)
    }
    /// `hasPartialOperatorCodeFlag(CCFS_DATATYPE_RELATED_TYPE)`.
    pub fn is_datatype_related_type(&self) -> bool {
        self.has_partial_operator_code_flag(CCFS_DATATYPE_RELATED_TYPE)
    }
}

// KONCLUDE-PORT-NOTE[threading]: the C++ class also keeps a process-wide
// `CConceptOperator** mConceptOperatorVector` lazily populated under a
// `QMutex` (`getConceptOperator`/`generateConceptOperators`), indexed by the
// (possibly negative) operator code via a pointer shifted to the array middle.
// `ConceptOperator` is a 16-byte `Copy` value here, so callers can just build
// one on demand with `ConceptOperator::new(code)`; the global cache + mutex are
// an allocation optimisation with no behavioural effect and are intentionally
// not ported. If a cache is later wanted, mirror the offset indexing
// (`vector[code + operatorCount/2]`) over a `Vec<ConceptOperator>`.

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flag_mapping_matches_codes() {
        assert_eq!(ConceptOperator::new(CCAND).get_operator_flag(), CCF_AND);
        assert_eq!(ConceptOperator::new(CCOR).get_operator_flag(), CCF_OR);
        assert_eq!(ConceptOperator::new(CCSOME).get_operator_flag(), CCF_SOME);
        assert_eq!(ConceptOperator::new(CCALL).get_operator_flag(), CCF_ALL);
        // Unlisted / disabled codes fall through to CCF_SPECIAL.
        assert_eq!(
            ConceptOperator::new(CCNOMINALIMPLI).get_operator_flag(),
            CCF_SPECIAL
        );
        assert_eq!(
            ConceptOperator::new(CCVARBINDFINALZE).get_operator_flag(),
            CCF_SPECIAL
        );
    }

    #[test]
    fn group_predicates() {
        // ALL is in both ALL_TYPE and the combined ALL_AQALL_TYPE.
        let all = ConceptOperator::new(CCALL);
        assert!(all.is_all_type());
        assert!(all.is_all_aqall_type());
        assert!(all.is_possible_role_creation_type());
        assert!(!all.is_some_type());

        // SOME and AQSOME are the SOME group; SOME is also role-creation.
        assert!(ConceptOperator::new(CCSOME).is_some_type());
        assert!(ConceptOperator::new(CCAQSOME).is_some_type());

        // AND group includes TOP (per CCFS_AND_TYPE).
        assert!(ConceptOperator::new(CCAND).is_and_type());
        assert!(ConceptOperator::new(CCTOP).is_and_type());

        // Datatype-related grouping.
        assert!(ConceptOperator::new(CCDATATYPE).is_datatype_related_type());
        assert!(ConceptOperator::new(CCDATARESTRICTION).is_datatype_related_type());
    }

    #[test]
    fn special_sign_bit_pattern() {
        // CCF_SPECIAL is exactly the i64 sign bit.
        assert_eq!(CCF_SPECIAL, i64::MIN);
    }
}
