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

- `km classify` completes 591 of 592 ORE 2015 ontologies under the documented
  240-second and 20-GiB benchmark contract.
- Those results comprise 588 exact retained or independently derived full-IRI
  signatures and three independently adjudicated cases: 2669, 15516, and
  10860. Ontology 1194 is the remaining non-completing input.
- KM accepts OWL functional syntax, OWL/XML, RDF/XML, and Turtle.
- Conversion, routing, and certification paths fail closed when they cannot
  justify a complete result.
- A Protégé 5.6 plugin, ontology profiling, bounded explanations, and
  incremental reasoning interfaces are included.
- Lean provides sorry-free soundness and completeness certification for the
  production ELC, hypertableau, and CB publication boundaries and for their
  automatic routing composition. Accepted routed taxonomies are bound to the
  exact source clauses and requested named-class signature.
- On the completed ORE panel, the automatic route has lower mean and median
  wall time and peak process-tree RSS than the retained correct-completion
  results for ELK, HermiT, Konclude, and Sequoia.

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

## ORE 2015 benchmark

The table reports the automatic KM route, not an oracle-selected union of
manually chosen configurations. Correct counts require agreement with the
retained or independently adjudicated full-IRI result signature. Times and
memory are computed over correct completions.

| Reasoner | Tested version / commit | Correct completions | Mean time (s) | Median time (s) | Mean peak RSS (MiB) | Median peak RSS (MiB) |
|---|---|---:|---:|---:|---:|---:|
| KM | v1.1.0; binary `fd9d7f1a…b6a88a` | 591/592 | 1.3997 | 0.1303 | 225.70 | 27.02 |
| ELK | 0.6.0 | 531/592 | 1.5208 | 0.7520 | 493.33 | 234.30 |
| Konclude | v0.7.0-1138; `0002e8063540` | 587/592 | 3.2765 | 0.2814 | 559.90 | 76.87 |
| Sequoia | 0.6.1-alpha; `c5248ec7be30` | 339/592 | 7.3704 | 2.5371 | 2207.35 | 536.15 |
| HermiT | 1.4.6.519-SNAPSHOT | 557/592 | 13.1172 | 1.8782 | 1331.72 | 714.22 |

Metrics are computed independently over each reasoner's correct completions;
incorrect, incomplete, timed-out, and failed runs do not make a reasoner look
faster. The final KM row is accepted only when the release binary's SHA-256 is
recorded by all 592 result, profile, and checkpoint records and the aggregate
gate passes strictly on all four metrics.

The benchmark corpus, limits, canonical signatures, adjudications, special
cases, and route history are documented in
[`docs/SOLVED-ONTOLOGIES.md`](docs/SOLVED-ONTOLOGIES.md),
[`docs/HARD-RESIDUAL-AUDIT.md`](docs/HARD-RESIDUAL-AUDIT.md), and
[`results/benchmarks/`](results/benchmarks/). The table records the exact
tested artifacts; it is not automatically attributed to later source releases.

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

## Repository layout

- [`engine/`](engine/) – Rust reasoner, frontends, orchestration, and tests
- [`lean/`](lean/) – Lean definitions, proofs, and executable checkers
- [`protege/`](protege/) – Protégé integration
- [`docs/`](docs/) – architecture, formats, benchmarks, and operational notes
- [`CHANGELOG.md`](CHANGELOG.md) – release history and detailed proof milestones

## License

KM is distributed under the [BSD 3-Clause License](LICENSE).
