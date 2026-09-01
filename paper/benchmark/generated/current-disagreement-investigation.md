# Current-corpus expressive disagreement investigation

This ledger accompanies the strict final aggregate from job 51036367.  The
aggregate accepted all 1,512 expected result records and contains 17
expressive-reasoner relation disagreements: 14 on independently profiled
OWL 2 DL inputs and three outside OWL 2 DL.  No majority is promoted to gold
automatically.  Source-level evidence below establishes selected defects;
the remaining rows stay explicitly unresolved.

## Exact set differences established so far

For DOID, KM's complete named relation is a strict subset of the common
HermiT/Konclude/Openllet relation.  It contains 152,033 pairs versus 152,034;
the sole omission is:

```
DOID_1024  SubClassOf  DOID_7
```

The prior independent MORe probe has the same relation digest as HermiT,
Konclude, and Openllet.  KM has no pair absent from that external relation.

For CVDO, KM has 6,301 pairs and HermiT/Konclude have 7,393.  All 6,301 KM
pairs occur in the external relation; KM omits 1,092.  JFact has 7,392 pairs:
it shares those 1,092 omissions with KM but also lacks the KM/external pair
`DOID_8517 SubClassOf DOID_8514`.  A representative KM omission is:

```
CVDO_0000010  SubClassOf  CVDO_0000546
```

The prior Openllet and MORe probes match HermiT and Konclude on CVDO.  These
facts establish incompleteness for the KM outputs in both cases, rather than
an unsound extra relation.

## Source-level witnesses

Job 51034333 used the pinned HermiT 1.4.5.519 artifact to extract a STAR
locality module and a black-box justification for each representative query.
The helper JAR was compiled for Java 11 and has SHA-256
`4ef0527e488a0a59f2c253d6e85a31a0dd228dbc944810b9f24aae3b166f79ef`.
Exact module and explanation hashes are in `disagreement-evidence.tsv`.

The 18-axiom DOID witness exposes a disjunctive common-consequence pattern.
`DOID_1024` is a disease and has an `RO_0004026` successor in a four-member
union.  Each union branch, together with disease membership, matches a named
defined class.  Each of those four classes reaches `DOID_7` through an
asserted named hierarchy.  Therefore every branch implies `DOID_7`, hence so
does `DOID_1024`.  KM publishes the disease hierarchy and restriction but
misses the consequence common to all four live branches.

The five-axiom CVDO witness exposes nested filler propagation.  In abbreviated
form, the relevant axioms are:

```
CVDO_0000010  SubClassOf  DOID_0060000
DOID_0060000  SubClassOf  OGMS_0000031
DOID_0060000  SubClassOf
  exists BFO_0000054.(OGMS_0000063 and exists BFO_0000117.CVDO_0000405)
CVDO_0000405  SubClassOf  CVDO_0000403
CVDO_0000546  EquivalentTo
  OGMS_0000031 and
  exists BFO_0000054.(OGMS_0000063 and exists BFO_0000117.CVDO_0000403)
```

Monotonicity of the nested existential restriction replaces
`CVDO_0000405` by its superclass `CVDO_0000403`; conjunction then matches the
definition of `CVDO_0000546`.  This yields the query directly.  The complete
source-bound module and five-axiom explanation are archived under
`generated/disagreement-evidence/cvdo/`.

## JFact/HermiT exact differences

Jobs 51037051 and 51037136 performed streaming merge differences over the
sorted full-IRI subsumption and named-unsatisfiable rows for the twelve
provisional JFact/HermiT splits.  The comparator fails on malformed,
duplicate, or unsorted rows and binds both input taxonomies by SHA-256.  Eleven
JFact subsumption relations are strict subsets of HermiT's: CHMO omits 14
pairs, CVDO one, FIDEO 30, INO 45, OBCS 134, OBIB 12, PROCO five, PSDO 19,
STATO 26, TXPO 12, and UO 56.  KISAO has 157 JFact-only ordinary subsumption
rows.

The KISAO direction is not evidence of JFact-only entailments.  KM, Konclude,
HermiT, and Openllet agree on 158 named-unsatisfiable classes, whereas JFact
reports 104.  All 54 JFact omissions are in the HermiT unsatisfiable set.  The
ordinary JFact parent rows arise for classes that the other systems represent
in the separate bottom block.

Job 51037137 extracted an eight-axiom source-bound justification for one such
case, `KISAO_0000086 SubClassOf owl:Nothing`.  In summary, property domain and
range axioms force `KISAO_0000106` into two disjoint classes.  Existential
restrictions propagate bottom successively through `KISAO_0000261`,
`KISAO_0000064`, and the definition of `KISAO_0000435`; the asserted
`KISAO_0000086 SubClassOf KISAO_0000435` completes the derivation.  The finite
certificate checker now replays these eight premises independently of an OWL
reasoner.  This establishes at least one JFact incompleteness witness for the
54-class bottom omission.

The unsatisfiable sets agree for ten of the other eleven ontologies.  STATO is
the exception: JFact alone reports `STATO_0000073` unsatisfiable, while HermiT
and Konclude agree on no named-unsatisfiable class.  Job 51037832 extracted a
STAR locality module for the disputed bottom query.  The module contains 2,072
axioms, including 443 logical axioms, and is bound to the frozen source and
query by hashes in `generated/disagreement-evidence/stato/`.  JFact completes
the module and reproduces its one-class bottom result.  HermiT answers that
the bottom entailment is false, and Openllet completes the same module with no
unsatisfiable named class.  This gives two independent expressive systems
against a reproducible JFact-only result.  We therefore classify the JFact
bottom result as a baseline defect rather than a contested gold case.

## UO singleton-nominal split

The completed UO records separate into three exact relation sets.  HermiT,
Konclude, Openllet, and KM share one relation digest with 1,665 named
subsumptions.  JFact is its strict subset by 56, with 1,609.  ELK and Whelk
share a third digest with 1,611: this is a strict subset of the common
expressive/KM relation by 54 and contains two relations absent from JFact.
All seven report the ontology consistent.  The OWLAPI profile report places
the frozen input in OWL 2 EL, and neither EL terminal record reports an
unsupported axiom.

The omitted family has a direct nominal-equality explanation.  For example,
the source contains:

```
UO_0000244  EquivalentTo  { UO_0000244 }
UO_0000329  EquivalentTo  { UO_0000329 }
UO_0000329  SubClassOf    UO_0000244
```

Class and individual uses of each IRI are legal OWL 2 punning.  The two
equivalences interpret the classes as singleton sets.  The asserted subclass
axiom therefore forces the two denoted individuals equal, so the singleton
sets are equal and `UO_0000244 SubClassOf UO_0000329` follows.  That reverse
inclusion is among the EL systems' 54 omissions.  The same pattern explains the
equivalences among prefixed unit classes.  This is source-level evidence that
ELK does not complete the nominal-induced equality consequences in this
input; it is not evidence against the common expressive/KM relation.  The
strict final aggregate retains these counts unchanged.

The representative three-axiom argument is archived in
`generated/disagreement-evidence/uo/`.  Its verifier checks the singleton
punning and reverse-query shape, replays the equality argument, and records
that all three premises occurred verbatim in the frozen source with SHA-256
`b6f4a0fa082b6357dd34801d09bbf4041667698374aaf8474b900f819f15ffa7`.

`verify_disagreement_witnesses.py` checks all three arguments independently of an
OWL reasoner.  It first verifies each explanation digest against
`disagreement-evidence.tsv`, then requires every premise used by the stated
derivation.  Its deliberately small certificate vocabulary includes
named-class transitivity, equivalence projection, conjunction introduction,
existential monotonicity and bottom propagation, property domain and range,
pairwise disjointness, and finite case analysis over an existential union.  The
machine-readable result is `disagreement-witness-verification.json`.  This is
not a replacement general-purpose reasoner; it makes the two manual logical
arguments explicit and replayable.

## Inconsistency normalization

CHEMINF appeared as a relation split in the first strict aggregate even though
HermiT, JFact, Konclude, and Openllet all report the ontology inconsistent.
HermiT, JFact, and Openllet serialize no named subsumptions or bottom classes;
Konclude serializes 860 named bottom classes.  Under OWL Direct Semantics an
inconsistent ontology entails every named subsumption, so these are output
conventions for the same semantic result.  The final aggregate uses one
`semantic:inconsistent` relation key when at least two completing
consistency-capable systems all report false, and applies that key to every
completing reasoner for the ontology.  A regression test covers empty, bottom,
and arbitrary relation serializations.  This removes CHEMINF from the
disagreement table without selecting a reasoner as gold.

## Remaining unresolved rows

The final table adds CDAO, FOODON, MIAPA, and PBPKO to the previously inspected
set.  CDAO, FOODON, and MIAPA split MORe from the other completing expressive
systems, while PBPKO splits JFact from Konclude and MORe.  Job 51041775
materialized the transitive closure of Konclude's PBPKO OWL/XML taxonomy and
established that JFact's 7,556-pair relation is a strict subset of Konclude's
7,568-pair relation, with no JFact-only pair.  The exact 12 omitted pairs are
recorded in `disagreement-evidence/pbpko/jfact-vs-konclude.json`; the generated
Konclude relation has SHA-256
`2ee9a712f0aa561d458844f672c2bd9d674da1305d911f2451b0b3f87fefecea`.
This localizes PBPKO in the same way as the other JFact strict-subset cases,
but does not by itself prove the 12 larger-relation pairs from source axioms.
Three of the 17
rows, MIAPA, PROCO, and TXPO, are outside OWL 2 DL.  These observations identify the
exact completing-system groups but do not decide which relation is entailed.
They remain unresolved in `current-disagreements.tsv`.

For CHMO, FIDEO, INO, OBCS, OBIB, PROCO, PSDO, and TXPO, streaming differences
show that JFact's relation is a strict subset of HermiT's and that named-bottom
sets agree.  This is strong defect-localisation evidence, but unlike the KISAO,
STATO, and UO cases it is not yet a source-level entailment adjudication.
The paper therefore reports the exact split without calling the larger
relation gold.  Future artifact revisions can add source-level witnesses
without changing the frozen benchmark records.
