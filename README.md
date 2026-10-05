# Kobayashi-MaRust

**An experimental SROIQ / OWL 2 DL reasoner written in Rust.**

[![CI](https://github.com/bio-ontology-research-group/kobayashi-marust/actions/workflows/ci.yml/badge.svg)](https://github.com/bio-ontology-research-group/kobayashi-marust/actions/workflows/ci.yml)
[![License: BSD-3-Clause](https://img.shields.io/badge/License-BSD--3--Clause-blue.svg)](LICENSE)
[![Rust](https://img.shields.io/badge/engine-Rust-orange.svg)](engine)
[![Lean 4](https://img.shields.io/badge/formalisation-Lean%204-brightgreen.svg)](lean)

Kobayashi-MaRust, or KM, combines a disjunctive consequence-based engine, an
EL++ completion path, and feature-gated completion procedures in one automatic
OWL classifier. The default command profiles an ontology and chooses a route
without access to the expected answer.

## Highlights

- v1.4.5 compares classification, incremental reasoning, and justifications
  against nine baseline reasoners. See the [benchmark results](#v145-benchmarks).
- The classification panel retains all 1,920 inputs, including invalid-input
  refusals and resource-limit failures.
- KM accepts OWL functional syntax, OWL/XML, RDF/XML, and Turtle.
- Conversion, routing, and certification paths fail closed when they cannot
  justify a complete result.
- Source-level transactional incremental reasoning supports retained sessions
  and state reuse, with documented exact-rebuild boundaries and atomic route
  migration. The benchmarks distinguish internal reuse from a retained process.
- The native CLI and OWLAPI/Protégé integration return verified, subset-minimal
  source-axiom explanations for every advertised entailment kind.
- Lean provides sorry-free soundness and completeness certification for the
  production ELC, hypertableau, and CB publication boundaries and for their
  automatic routing composition. Accepted routed taxonomies are bound to the
  exact source clauses and requested named-class signature.
- Performance comparisons use paired, verified outcomes. Timeouts, incomplete
  answers, and missing references remain visible in coverage totals.

## Install

KM requires a recent stable Rust toolchain.

```sh
git clone https://github.com/bio-ontology-research-group/kobayashi-marust.git
cd kobayashi-marust/engine
cargo build --release --locked
./target/release/km --help
```

The main executable is `engine/target/release/km`.

## Classify an ontology

```sh
km classify ontology.owl
```

Write the JSON classification result to a file:

```sh
km classify ontology.owl > classification.json
```

Inspect the accepted options and worker commands:

```sh
km classify --help
km profile ontology.owl
km explain ontology.owl subclass EX:Child EX:Parent
```

`km classify` accepts the standard OWL serializations listed above. It converts
the input to KM's normalized clause representation, profiles its features, and
selects a compatible reasoning route. Worker entry points are also available
as `km ofn`, `km elc`, `km engine`, and `km tableau` for development and
diagnostics.

Version 1.4.4 adds inverse expressions in role chains and
extends DL-safe SWRL reasoning. Its input checks reject malformed ontologies
before reasoning. For example, `"text"^^rdfs:Literal` has no literal lexical
mapping: use of `rdfs:Literal` as a data range does not make it a valid literal
datatype. KM explains the violation and exits with code 2 without rewriting
the input or producing a classification. A valid construct whose complete
execution cannot be established is a separate refusal (exit code 3).

The final validation inventory covers 1,920 unchanged corpus files: 1,708
pass its implemented checks and 212 are refused. Independent audits verified
all 212 violations, including the 33 additional anonymous-tree diagnoses.
The anonymous-individual check follows the formal condition in
[OWL 2 section 11.2](https://www.w3.org/TR/owl2-syntax/#Global_Restrictions_on_Axioms_in_OWL_2_DL):
each anonymous tree must contain a node with at most one object-property
assertion to a named individual. The named-star example immediately after
that condition contradicts it; KM follows the explicit condition. The v1.4.4 release
passed 2,822 Rust tests and all four production Lean gates.
The final 1,920-input classification run reports 1,622 successes, 212 input
rejections, and 86 non-completions. The output audit verifies every successful
output, zero dropped axioms, and all refusals as invalid inputs. No unsupported
input or unexplained engine-error outcomes remain in this run. The
592-input gold comparison has 552 Konclude matches, two successes without
gold, 35 invalid-input refusals, two memory-limit failures, and one timeout.
These figures describe v1.4.4; the v1.4.5 benchmark results follow.

## v1.4.5 benchmarks

**[Full benchmark results: counts, average and median times](results/benchmarks/2026-10-04-v1.4.5-comparative/benchmark-summary.md)**
include all three panels and initialization costs.
The [machine-readable summary](results/benchmarks/2026-10-04-v1.4.5-comparative/benchmark-counts-times.json) contains the
individual times and references used for these tables.

**Limits: 240 seconds per attempt, 20 GiB memory, one CPU.** Times below are
wall-clock seconds. “Average” is the arithmetic mean; “median” is the middle
recorded time. Both use only the verified solved attempts in that row.

For classification and updates, **verified solved** means a complete audited
answer with known consistency that agrees with at least one different full-DL
reasoner (KM, HermiT, Konclude, Openllet, or JFact). Complete outputs without
that corroboration appear only in the output column. This conservative count
does not incorporate separate case-specific proofs or treat unknown consistency
as agreement. For justifications, solved means independently verified source
membership, entailment, and subset-minimality.

Failed and timed-out attempts remain in the denominators. The successful
subsets differ between reasoners, so read the times together with the solved
counts; a low average alone does not imply better overall coverage.

### Classification

The corpus contains **1,920 inputs: 1,708 pass the input checks and 212 are
invalid**. The table counts the 1,708 admitted inputs; invalid-input refusals
are reported separately and do not count as solved ontologies.

| Reasoner | Complete outputs | Verified solved / attempts | Average time (s) | Median time (s) |
|---|---:|---:|---:|---:|
| KM | 1,594 | 1,591 / 1,708 | 10.892 | 0.691 |
| ELK | 1,701 | 1,411 / 1,708 | 11.971 | 4.777 |
| HermiT | 1,540 | 1,539 / 1,708 | 15.764 | 4.988 |
| JFact | 1,238 | 1,101 / 1,708 | 17.430 | 5.208 |
| Konclude | 1,697 | 1,655 / 1,708 | 2.923 | 0.269 |
| MORe | 1,584 | 0 / 1,708 | n/a | n/a |
| Openllet | 1,411 | 1,402 / 1,708 | 16.335 | 4.890 |
| RustDL | 1,220 | 1,212 / 1,708 | 5.139 | 0.331 |
| Sequoia | 630 | 629 / 1,708 | 18.676 | 7.375 |
| Whelk | 1,647 | 1,380 / 1,708 | 17.705 | 6.198 |

MORe produces taxonomy outputs but its adapter does not establish consistency,
so these outputs do not enter the verified column. KM's three uncorroborated
outputs are ORE 1194, 3794, and 4669; the full evidence includes the separate
adjudications for 3794 and 4669. They are excluded by the same automatic
corroboration rule used for every reasoner in this summary.

### Incremental reasoning

**80 sources × four updates × three repetitions = 960 update attempts per
method.** One source failed preparation; its 12 update attempts remain in the
denominator. Repeated runs count separately, so these are update attempts,
not 960 distinct ontologies. Initialization is excluded from the table and
reported separately in the full summary.

Fresh-process rows restart the reasoner for each revision. Retained-session
rows keep the process running across revisions. RustDL, MORe, and Sequoia have
fresh-process results only.

| Reasoner | Mode | Complete outputs | Verified solved / attempts | Average time (s) | Median time (s) |
|---|---|---:|---:|---:|---:|
| KM | Fresh process | 918 | 906 / 960 | 13.066 | 0.784 |
| KM | Retained session | 821 | 821 / 960 | 16.276 | 0.646 |
| ELK | Fresh process | 925 | 769 / 960 | 14.670 | 5.655 |
| ELK | Retained session | 924 | 768 / 960 | 6.778 | 1.274 |
| HermiT | Fresh process | 852 | 852 / 960 | 17.664 | 5.006 |
| HermiT | Retained session | 852 | 852 / 960 | 10.532 | 1.370 |
| JFact | Fresh process | 636 | 564 / 960 | 14.172 | 4.324 |
| JFact | Retained session | 636 | 540 / 960 | 12.988 | 0.474 |
| Konclude | Fresh process | 936 | 936 / 960 | 4.147 | 0.318 |
| Konclude | Retained session | 930 | 896 / 960 | 10.517 | 0.542 |
| MORe | Fresh process | 862 | 0 / 960 | n/a | n/a |
| Openllet | Fresh process | 739 | 727 / 960 | 13.142 | 4.620 |
| Openllet | Retained session | 725 | 713 / 960 | 5.624 | 0.911 |
| RustDL | Fresh process | 647 | 647 / 960 | 6.203 | 0.452 |
| Sequoia | Fresh process | 348 | 348 / 960 | 14.992 | 8.432 |
| Whelk | Fresh process | 912 | 768 / 960 | 22.214 | 6.847 |
| Whelk | Retained session | 908 | 764 / 960 | 14.557 | 2.286 |

A retained process does not guarantee internal reuse. Of KM's 948 prepared
post-initialization attempts, 206 used incremental updates and 615 rebuilt
exactly; 121 were skipped after session failure and six timed out. The 12
completed cold KM update outputs on ORE 1194 lack an independent reference and
are excluded from the verified count. Fresh and retained rows can solve
different subsets; their separate averages are not a paired speedup measure.

### Justifications

**124 queries × three repetitions = 372 attempts per reasoner.** These queries
come from 42 of the 80 selected sources; 24 sources failed preparation and 14
had no eligible query. Those sources were not replaced. Times measure
justification generation; independent verification has its own 240-second
limit and is reported separately.

| Reasoner | Verified solved / attempts | Average time (s) | Median time (s) |
|---|---:|---:|---:|
| KM | 336 / 372 | 0.268 | 0.076 |
| ELK | 366 / 372 | 3.516 | 3.094 |
| HermiT | 372 / 372 | 3.184 | 2.796 |
| JFact | 354 / 372 | 5.913 | 3.754 |
| Konclude | 249 / 372 | 30.109 | 15.791 |
| MORe | 264 / 372 | 30.529 | 12.140 |
| Openllet | 372 / 372 | 3.323 | 2.836 |
| RustDL | 369 / 372 | 1.636 | 0.043 |
| Sequoia | 207 / 372 | 36.786 | 22.856 |
| Whelk | 318 / 372 | 7.315 | 2.659 |

### Validation and detailed evidence

The measured v1.4.5 candidate passed 2,835 Rust tests (8 ignored), 31 Java
tests, plugin installation checks, all four Lean certification gates without
`sorryAx`, and 68 benchmark-harness tests. The detailed reports retain failed
measurements, raw disagreements, preparation costs, and verification costs.
Earlier 592-input ORE benchmark results used different panels and validation
rules and should not be compared directly with these totals.

- [Detailed paired comparisons and preparation costs](results/benchmarks/2026-10-04-v1.4.5-comparative/benchmark-report-53234931.md)
- [Classification results](results/benchmarks/2026-10-04-v1.4.5-comparative/classification-report-v4-full-global-dependency-53234888.json)
- [Incremental results](results/benchmarks/2026-10-04-v1.4.5-comparative/updates-report-v5-full-global-dependency-53234889.json)
- [Justification results](results/benchmarks/2026-10-04-v1.4.5-comparative/justification-report-v4-full-global-dependency-53234890.json)
- [Evidence index and validation receipts](results/benchmarks/2026-10-04-v1.4.5-comparative/release-evidence-index.json)

## Protégé plugin

Build the plugin with Maven:

```sh
cd protege
mvn package
```

Copy the generated JAR from `target/` into Protégé's `plugins/` directory and
place the `km` executable on `PATH`. Restart Protégé, select KM from the
reasoner menu, and start the reasoner. Detailed setup and troubleshooting are
in [`protege/README.md`](protege/README.md).

## Lean certification

The Lean development is under [`lean/`](lean/). Build it with:

```sh
cd lean
lake exe cache get
LEAN_NUM_THREADS=1 taskset -c 0-3 lake build
```

Lake derives its scheduler width from the CPUs visible to the process. The
`taskset` boundary therefore limits the build to four CPUs, while
`LEAN_NUM_THREADS=1` prevents each Lean process from creating an additional
worker pool.

Run the production HT certification gate from the repository root:

```sh
./lean/run-ht-certification-gate.sh
```

Run the production ELC certification gate with:

```sh
./lean/run-elc-certification-gate.sh
```

Run the production CB certification gate with:

```sh
./lean/run-cb-certification-gate.sh
```

Run the automatic-routing certification gate with:

```sh
./lean/run-routing-certification-gate.sh
```

The certified production boundary consists of four layers:

- ELC checks source normalization, NF1–NF7 closure, residual compilation,
  materialized state, inconsistency, and the complete named taxonomy.
- HT checks ordinary, mixed, bundle, cardinality, and native-ABox projections;
  bounded search; blocking and frontier growth; and exact taxonomy or global
  publications.
- CB checks the chronological retained derivation, all local and
  inter-context production rule families, quiescence, canonical closure, and
  every positive or countermodel-backed negative taxonomy cell.
- Routing checks the ordered selector, specialist fallback order, exact source
  identity, the requested named-class signature, and evidence dispatch to the
  ELC, HT, or CB checker. Profile choices can affect performance and coverage,
  but cannot make an unchecked answer sound.
- Incremental publication checks bind every revision to its exact post-update
  source and complete taxonomy. Explanation checks derive entailment from the
  same accepted source-bound cells, use exact global SAT/UNSAT publications
  for inconsistency, and prove subset minimality from checked one-axiom
  deletion failures plus OWL entailment monotonicity.

Every public capstone is audited for `sorryAx`. Their axiom reports contain
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
The four local gates build the relevant Lean surface and executable checkers,
run tamper-rejection fixtures, and exercise the Rust-to-Lean publication paths.

This is a proof-carrying publication boundary. Lean proves the semantics of an
answer whose exact source, requested signature, execution evidence, and output
are accepted. Routing completeness requires the concrete selected route or its
retained fallback to publish accepted evidence. The formalization does not
verify the Rust compiler, operating system, scheduler, resource limits, or an
execution that bypasses the mandatory checker.

Version 1.0.0 records the integrated ELC, HT, CB, and automatic-routing
certification milestone.

Every full KM release, including v1.3.0 and later releases, must pass all Lean
certification gates from the exact source commit that is tagged. A corpus
benchmark, Rust test suite, or interface test cannot replace this requirement.
If a release adds a new answer-publication path, that path must be included in
the Lean certification boundary and its no-`sorryAx` audit before the release is
tagged. For v1.3.0 this includes incremental publications and source-axiom
explanations.

## Repository layout

- [`engine/`](engine/) – Rust reasoner, frontends, orchestration, and tests
- [`lean/`](lean/) – Lean definitions, proofs, and executable checkers
- [`protege/`](protege/) – Protégé integration
- [`docs/`](docs/) – architecture, formats, benchmarks, and operational notes
- [`CHANGELOG.md`](CHANGELOG.md) – release history and detailed proof milestones

## License

KM is distributed under the [BSD 3-Clause License](LICENSE).
