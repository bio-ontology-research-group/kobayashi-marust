# v1.7.0 C0 parser differential

653 inputs outside the v1.6.2 fragment F.

| Lean | Rust | inputs |
|---|---|---:|
| ok | ok | 539 |
| rejected | ok | 114 |

Lean rejection reasons:

- 114 x `out of fragment: DLSafeRule (rule)`

Both accept: 539; no disagreement at all: 307.

| disagreeing field | inputs |
|---|---:|
| objectProperties | 232 |

Object-property disagreements where no name is Lean-only and every Rust-only name is a Lean data property or the top or bottom object or data property (the Lean model has ObjProp.top / .bot and DataProp.top / .bot, not IRIs): 232 of 232; inputs where Rust lists a top or bottom property: 3.


Axiom kinds in the accepted inputs (Lean counts; all agree with heads.py):

| kind | axioms | inputs |
|---|---:|---:|
| declareClass | 3712 | 539 |
| subClassOf | 1701 | 524 |
| equivalentClasses | 1591 | 468 |
| declareObjectProperty | 1504 | 528 |
| declareNamedIndividual | 808 | 279 |
| declareDataProperty | 444 | 233 |
| disjointClasses | 268 | 199 |
| functional | 234 | 192 |
| classAssertion | 155 | 118 |
| objectPropertyAssertion | 131 | 98 |
| subObjectPropertyOf | 129 | 98 |
| dataPropertyAssertion | 104 | 77 |
| functionalData | 96 | 79 |
| dataDomain | 95 | 79 |
| inverseFunctional | 24 | 22 |
| sameIndividual | 11 | 10 |
| domain | 6 | 4 |
| transitive | 6 | 6 |
| dataRange | 5 | 4 |
| inverseObjectProperties | 4 | 4 |
| differentIndividuals | 3 | 3 |
| range | 3 | 3 |
| symmetric | 2 | 2 |
| disjointUnion | 1 | 1 |
| equivalentObjectProperties | 1 | 1 |
| subDataPropertyOf | 1 | 1 |
| asymmetric | 0 | 0 |
| datatypeDefinition | 0 | 0 |
| declareAnnotationProperty | 0 | 0 |
| declareDatatype | 0 | 0 |
| disjointDataProperties | 0 | 0 |
| disjointObjectProperties | 0 | 0 |
| equivalentDataProperties | 0 | 0 |
| hasKey | 0 | 0 |
| irreflexive | 0 | 0 |
| negativeDataPropertyAssertion | 0 | 0 |
| negativeObjectPropertyAssertion | 0 | 0 |
| reflexive | 0 | 0 |
