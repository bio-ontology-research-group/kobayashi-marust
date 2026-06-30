# 04 — Konclude static ontology model (CConcept / CRole / CIndividual + operator tags)

Source of truth for the Rust port of the static concept/role/individual model that the
completion engine (`CCalculationTableauCompletionTaskHandleAlgorithm.cpp`) reads. All
types live under `Source/Reasoner/Ontology/`. The "tag enum" is NOT a C++ `enum`: it is a
set of `static const qint64` *concept constructor codes* defined in `OntologySettings.h`,
wrapped at runtime by `CConceptOperator` (which adds bitflag dispatch groups).

## Header paths

| Type | Header |
|------|--------|
| CConcept | `Source/Reasoner/Ontology/CConcept.h` |
| CRole | `Source/Reasoner/Ontology/CRole.h` |
| CIndividual | `Source/Reasoner/Ontology/CIndividual.h` |
| operator tag codes (CCxxx) | `Source/Reasoner/Ontology/OntologySettings.h` (lines ~91-184) |
| operator wrapper + dispatch flags (CCF_/CCFS_) | `Source/Reasoner/Ontology/CConceptOperator.h` |

`CConcept`/`CRole` derive from `CTagItem` + `CNamedItem` (CConcept also `CAllocationObject`);
`CIndividual` derives from `CIndividualIdentifier` + `CNamedItem` + `CAllocationObject`.

---

## CConcept — fields (protected) and key accessors

The concept is a uniform node: an operator code + a parameter (cardinality) + a role pointer
+ an operand linked list. The same struct represents AND/OR/SOME/ALL/ATLEAST/NOMINAL/SELF/...
distinguished only by `mOperatorCode`.

Fields:
| Field | Type | Meaning |
|-------|------|---------|
| `tax` | `CTerminology*` | owning terminology (TBox) |
| `mOperatorCode` | `CConceptOperator*` | the constructor tag wrapper (dispatch key) |
| `opParameter` | `qint64` | parameter, e.g. the n of ATLEAST/ATMOST cardinality |
| `operandCount` | `qint64` | number of operands in the list |
| `operatorRole` | `CRole*` | role for SOME/ALL/ATLEAST/ATMOST/SELF/VALUE |
| `operands` | `CSortedNegLinker<CConcept*>*` | operand list (each entry carries a negation bit) |
| `mNominalIndiviual` | `CIndividual*` | bound individual for NOMINAL/VALUE |
| `mVariableLinker` | `CSortedLinker<CVariable*>*` | variables (rules/role-chain binding) |
| `mDataLiteral` | `CDataLiteral*` | literal for CCDATALITERAL |
| `mDatatype` | `CDatatype*` | datatype for CCDATATYPE |
| `mConceptData` | `CConceptData*` | side data (caching/marker) |
| `mMappingNegated` | `bool` | mapping-negation flag |

Plus the inherited `CTagItem` concept tag (`setConceptTag`/`getConceptTag`) — the unique
concept id used as array index.

Key accessors:
- tag/id: `getConceptTag()`, `getTerminologyConceptTagPair()`
- operator: `getOperatorCode()` (qint64 code), `getConceptOperator()` (wrapper w/ flags),
  `isGeneratingOperator()`/`isNonGeneratingOperator()` (SOME/ATLEAST generate successors),
  `isEqualsToTOP/BOTTOM()`
- cardinality: `getParameter()` / `setParameter()`
- role: `getRole()` / `setRole()`
- operands: `getOperandList()` (head of `CSortedNegLinker`), `getOperandCount()`,
  `hasOperandConcept(c, negation)`, `addOperandLinker()`
- nominal: `getNominalIndividual()`, `hasNominalIndividual()`
- data: `getDataLiteral()`, `getDatatype()`, `getConceptData()`
- class names: `getClassNameLinker()` / `hasClassName()`

---

## CRole — fields (private) and key accessors

Fields: `mRoleData` (CRoleData*), `tax` (CTerminology*), boolean property flags
`mTransetive`, `mFunctional`, `mInvFunctional`, `mAsymmetric`, `mSymmetric`, `mReflexive`,
`mIrreflexive`, `mComplexity` (complex vs simple role), `mDataRole`; `mInverseRole` (CRole*);
domain/range `rangeLinker`/`domainLinker` (`CSortedNegLinker<CConcept*>*`); role hierarchy
`superRoles` + `indirectSuperRoles`; `mInverseEquivalentRoles`, `mDisjointRoles`
(all `CSortedNegLinker<CRole*>*`); role-chain sharing `mRoleChainSuperSharingLinker` /
`mRoleChainSubSharingLinker` (`CXLinker<CRoleChain*>*`).

Hierarchy/property accessors:
- inverse: `getInverseRole()`, `getInverseRoleList()`, `getInverseEquivalentRoleList()`
- hierarchy: `getSuperRoleList()` / `hasSuperRole()`, `getIndirectSuperRoleList()`,
  `getEquivalentRoleList()`, `getDisjointRoleList()`
- characteristics: `isTransitive()`, `isFunctional()`, `isInverseFunctional()`,
  `isSymmetric()`, `isAsymmetric()`, `isReflexive()`, `isIrreflexive()`,
  `isComplexRole()`/`isSimpleRole()`, `isDataRole()`/`isObjectRole()`
- domain/range: `getDomainConceptList()`, `getRangeConceptList()`,
  `getRelativeRangeConceptList(roleInversed)`, `getDomainRangeConceptList(roleInversed)`
- role chains: `getRoleChainSubSharingLinker()`, `getRoleChainSuperSharingLinker()`
- tag/id: `getRoleTag()` (inherited CTagItem), `getRoleData()`

---

## CIndividual — fields (protected) and key accessors

Fields: `mAssertionConceptLinker` (CConceptAssertionLinker*), `mAssertionRoleLinker`
(CRoleAssertionLinker*), `mAssertionDataLinker` (CDataAssertionLinker*),
`mReverseAssertionRoleLinker` (CReverseRoleAssertionLinker*), `mNominalConcept` (CConcept* —
the NOMINAL concept representing {this}), bools `mAnonymousIndividual`/`mTemporaryIndividual`/
`mFakeIndividual`, `mIndividualData` (CIndividualData*). Identity id via base
`CIndividualIdentifier` (`getIndividualID()`).

Accessors: `getIndividualNominalConcept()`, `getAssertionConceptLinker()`,
`getAssertionRoleLinker()`, `getAssertionDataLinker()`, `getReverseAssertionRoleLinker()`,
`hasAssertedConcept()`, `isAnonymousIndividual()`/`isTemporaryIndividual()`/
`isFakeIndividual()`, `getIndividualNameLinker()`.

---

## FULL operator tag codes (OntologySettings.h "Concept Constructor Codes")

Polarity convention: a *positive* code and its NEGATION are encoded as +n / -n of the same
magnitude (e.g. AND=3 / OR=-3, ALL=5 / SOME=-5, ATMOST=4 / ATLEAST=-4). The completion
algorithm dispatches on these (often via `CConceptOperator` flag groups, not raw ==).

Core DL constructors (the ones an apply*Rule keys on):
| Code | Value | Meaning / rule |
|------|-------|----------------|
| CCNONE / CCATOM | 0 | atomic concept (no operator; a class name) |
| CCTOP | 1 | ⊤ |
| CCBOTTOM | -1 | ⊥ (clash) |
| CCNOT | -2 | negation marker |
| CCAND | 3 | ⊓ — AND-rule (add all operands) |
| CCOR | -3 | ⊔ — OR-rule (branch over operands) |
| CCATMOST | 4 | ≤n R.C — ATMOST/merge-rule (uses opParameter=n, role) |
| CCATLEAST | -4 | ≥n R.C — ATLEAST/choose-generate (opParameter=n, role) |
| CCALL | 5 | ∀ R.C — ALL/forall-rule (propagate to R-successors) |
| CCSOME | -5 | ∃ R.C — SOME/exists-rule (generate R-successor) |
| CCEQ | 6 | equivalence axiom concept |
| CCSUB | 7 | subsumption/implication axiom concept |
| CCNOMINAL | 8 | {a} nominal (mNominalIndiviual) |
| CCSELF | 9 | ∃R.Self (role, self loop) |
| CCAQCHOOCE | 10 | qualified-cardinality choose (NN/choose) |
| CCAQALL | 11 | qualified ∀ (AQALL) for ≤/≥ qualification |
| CCAQSOME | -11 | qualified ∃ (AQSOME) |
| CCAQAND | 12 | qualified AND (AQAND) |
| CCVALUE | 13 | role value / hasValue (role + nominal individual) |
| CCNOMVAR | 14 | nominal variable |
| CCNOMTEMPLREF | 15 | nominal template reference |

Absorption / implication machinery (trigger + implication forms — used by
absorption-based lazy unfolding, dispatched via CCFS_TRIG_TYPE / CCFS_IMPL_TYPE):
| CCIMPL 16, CCIMPLTRIG 17, CCIMPLALL 18, CCIMPLAQALL 19, CCIMPLAQAND 20 |
| CCBRANCHIMPL 21, CCBRANCHTRIG 22, CCBRANCHALL 23, CCBRANCHAQALL 24, CCBRANCHAQAND 25 |
| CCEQCAND 26 |

Propagation-bind (role-chain / propagation) family:
| CCPBINDTRIG 27, CCPBINDIMPL 28, CCPBINDGROUND 29, CCPBINDALL 30, CCPBINDAND 31, CCPBINDAQAND 32, CCPBINDAQALL 33, CCPBINDVARIABLE 34, CCPBINDCYCLE 35 |

Variable-bind (rule / join) family:
| CCVARBINDTRIG 36, CCVARBINDJOIN 37, CCVARBINDGROUND 38, CCVARBINDALL 39, CCVARBINDAND 40, CCVARBINDAQAND 41, CCVARBINDAQALL 42, CCVARBINDVARIABLE 43, CCVARBINDIMPL 44 |

Back-propagation family:
| CCVARPBACKTRIG 45, CCVARPBACKALL 46, CCVARPBACKAQAND 47, CCVARPBACKAQALL 48 |
| CCBACKACTIVTRIG 49, CCBACKACTIVIMPL 50 |

Datatype / data family:
| CCDATATYPE 51, CCDATALITERAL 52, CCDATARESTRICTION 53 |
| CCMARKER 54 |
| CCNOMINALIMPLI 55, CCDATATYPEIMPLI 56, CCDATALITERALIMPLI 57, CCDATARESTRICTIONIMPLI 58 |
| CCVARBINDPREPARE 59, CCVARBINDFINALZE 60 |

### CConceptOperator dispatch flag groups (CConceptOperator.h)

The algorithm rarely tests a raw code; it tests bitflag *type groups* via
`getConceptOperator()->hasPartialOperatorCodeFlag(CConceptOperator::CCFS_xxx)`. The groups
collapse the impl/branch/pbind/varbind variants of each constructor back to one logical
operator. Key groups:
- `CCFS_AND_TYPE` = AND | PBINDAND | VARBINDAND | TOP
- `CCFS_ALL_TYPE` = ALL | IMPLALL | BRANCHALL | PBINDALL | VARBINDALL | VARPBACKALL
- `CCFS_SOME_TYPE` = SOME | AQSOME
- `CCFS_AQALL_TYPE` / `CCFS_AQAND_TYPE` (qualified-cardinality ∀/⊓ variants)
- `CCFS_ALL_AQALL_TYPE` = ALL_TYPE | AQALL_TYPE (∀-propagation rule key)
- `CCFS_TRIG_TYPE`, `CCFS_IMPL_TYPE` (absorption trigger/implication)
- `CCFS_POSSIBLE_ROLE_CREATION_TYPE` = SOME | AQSOME | ALL | ATLEAST | ATMOST (operators that need a role)
- `CCFS_PROPAGATION_*_TYPE` (role-chain propagation bind/varbind/back groups)
- `CCFS_ABSORPTION_RELEVANT_TYPE`, `CCFS_DATATYPE_RELATED_TYPE`

For the Rust port: the minimal SROIQ tableau dispatch needs only the core constructors
(TOP, BOTTOM, AND, OR, ALL, SOME, ATLEAST, ATMOST, NOMINAL, SELF, VALUE, AQALL/AQSOME/AQAND
for qualified cardinality, DATATYPE/DATALITERAL/DATARESTRICTION). The IMPL/BRANCH/PBIND/
VARBIND/VARPBACK families are absorption + role-chain-automaton internals — port them only
when implementing lazy unfolding / role chains.

---

## Operand linking — CSortedNegLinker

`Source/Reasoner/Ontology/Utilities/CSortedNegLinker.hpp` — a singly-linked, sorted list
node where each node carries a data pointer plus a *negation bit*. Operands of AND/OR (and
role lists on CRole) are these chains. API:
- `getData() -> T*`, `getNext() -> CSortedNegLinker<T*>*`, `isNegated() -> bool`,
  `setNegated(bool)`, `init(data, isNegated, next)`.
- "Sorted" = kept in tag order so membership tests (`hasOperandConcept`) and set ops are linear merges.

So an operand list entry = (concept ptr, negated flag). The negation bit is how Konclude
stores `¬C` operands without a separate negated-concept object. The Rust port models this as
`Vec<(ConceptId, bool)>` (or a `(ConceptRef, neg)` linked node) per concept.

`CSortedLinker` (no neg bit) is used for `mVariableLinker`. `CXLinker<CRoleChain*>` carries
role-chain sharing on CRole. Domain/range/hierarchy lists on CRole are all
`CSortedNegLinker<CRole*>` / `CSortedNegLinker<CConcept*>`.

## Roles — hierarchy / inverse / characteristics summary

- Inverse: single `mInverseRole` pointer plus an `mInverseRoleList` / inverse-equivalent list
  (a role may have several syntactic inverses that are equivalent).
- Hierarchy: `superRoles` (direct asserted) + `indirectSuperRoles` (transitive closure),
  both `CSortedNegLinker<CRole*>`; `equivalentRoleList`; `disjointRoleList`.
- Characteristics: separate bool flags — transitive, functional, inverse-functional,
  symmetric, asymmetric, reflexive, irreflexive. `mComplexity` distinguishes complex
  (role-chain / transitive-involving) vs simple roles (simple roles are the ones allowed
  under number restrictions / Self).
- Role chains: not on CRole directly as a chain object but via the two
  `CXLinker<CRoleChain*>` sub/super sharing linkers (CRoleChain is its own type).
