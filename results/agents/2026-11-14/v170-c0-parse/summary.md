# v1.7.0 C0 parser differential

609 ORE inputs outside the v1.6.2 fragment F.

| Lean | Rust | inputs |
|---|---|---:|
| ok | ok | 603 |
| rejected | ok | 6 |

Lean rejection reasons:

- 6 x `out of fragment: DLSafeRule (rule)`

Both accept: 603; no disagreement at all: 351.

| disagreeing field | inputs |
|---|---:|
| objectProperties | 252 |

Object-property disagreements where no name is Lean-only and every Rust-only name is a Lean data property or the top or bottom object or data property (the Lean model has ObjProp.top / .bot and DataProp.top / .bot, not IRIs): 252 of 252; inputs where Rust lists a top or bottom property: 38.


Axiom kinds in the accepted inputs (Lean counts; all agree with heads.py):

| kind | axioms | inputs |
|---|---:|---:|
| classAssertion | 13444100 | 459 |
| subClassOf | 7716216 | 571 |
| declareClass | 4801264 | 603 |
| objectPropertyAssertion | 1474920 | 255 |
| equivalentClasses | 590696 | 244 |
| dataPropertyAssertion | 399281 | 123 |
| sameIndividual | 139058 | 60 |
| declareObjectProperty | 51902 | 582 |
| subObjectPropertyOf | 34353 | 408 |
| disjointClasses | 34243 | 276 |
| range | 22934 | 326 |
| domain | 20777 | 314 |
| declareDataProperty | 8911 | 228 |
| dataDomain | 7010 | 184 |
| dataRange | 6542 | 201 |
| inverseObjectProperties | 5562 | 260 |
| subDataPropertyOf | 3501 | 104 |
| differentIndividuals | 2590 | 88 |
| transitive | 2215 | 291 |
| functional | 1987 | 142 |
| functionalData | 1493 | 81 |
| symmetric | 572 | 155 |
| inverseFunctional | 513 | 45 |
| equivalentObjectProperties | 258 | 31 |
| declareDatatype | 137 | 1 |
| equivalentDataProperties | 80 | 28 |
| reflexive | 39 | 14 |
| irreflexive | 30 | 7 |
| disjointUnion | 16 | 2 |
| asymmetric | 9 | 5 |
| disjointObjectProperties | 2 | 2 |
| datatypeDefinition | 0 | 0 |
| declareAnnotationProperty | 0 | 0 |
| declareNamedIndividual | 0 | 0 |
| disjointDataProperties | 0 | 0 |
| hasKey | 0 | 0 |
| negativeDataPropertyAssertion | 0 | 0 |
| negativeObjectPropertyAssertion | 0 | 0 |
