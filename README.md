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
  supported production hypertableau families and the source-bound ELC
  publication path. Certification of CB and automatic routing remains in
  progress.

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

| Reasoner | Tested version / commit | Correct | Completed | Mean time (s) | Median time (s) | Mean peak RSS (MiB) | Median peak RSS (MiB) |
|---|---|---:|---:|---:|---:|---:|---:|
| KM | v0.2.36; benchmark binary `bbef8d7` | 591/592 | 591/592 | 3.2383 | 0.1628 | 427.88 | 35.39 |
| Konclude | v0.7.0-1138; `0002e8063540` | 587/592 | 589/592 | 3.2657 | 0.2813 | 558.09 | 76.53 |

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
lake build -j 4
```

Run the production HT certification gate from the repository root:

```sh
./lean/run-ht-certification-gate.sh
```

Run the production ELC certification gate with:

```sh
./lean/run-elc-certification-gate.sh
```

### Current certified HT boundary

`ContextCalculus.HypertableauCertificationSurface` exports the current
production capstones for:

- global HT classification;
- regular taxonomy classification;
- equality and cardinality taxonomy classification;
- native-ABox taxonomy classification; and
- native-ABox cardinality taxonomy classification.

Given a checked production-route structure, Lean proves termination of its
bounded search and sound and complete classification relative to the checked
source projection and finite semantic problem. The development covers the
production control order for clauses, existential witnesses, equality,
inequality, minimum cardinality, maximum cardinality, blocking, forbidden-pair
learning, and iterative budget growth. Accepted SAT results carry a checked
finite model. Accepted UNSAT and taxonomy results carry checked recursive
evidence.

The gate builds the complete Lean development and the explicit capstone,
audits its axiom report for `sorryAx`, checks that its inventory matches all 32
HT checker executables declared in `lakefile.toml`, builds and runs those
checkers, and executes the Rust-to-Lean integration tests. The exported
capstones currently report only Lean's standard `propext`, `Classical.choice`,
and `Quot.sound` axioms.

This is a proof-carrying checker boundary. It proves the semantics of results
whose source projection and evidence are accepted by the Lean-derived checker
contracts. It does not verify the Rust compiler, operating system, process
supervision, or arbitrary unchecked Rust execution.

The public surface now includes executable global and complete-taxonomy
dispatchers. Their route tag is decoded from the publication document, and
each ordinary, cardinality, native-ABox, or native-ABox-cardinality branch
checks source semantics, the retained production run, and exact result binding
as one object. The older `CertifiedHT…Route` theorems remain internal totality
lemmas rather than the executable publication boundary. Raw `Ht` certificate
constructors build evidence but do not publish a certified answer. The
`tableau_cli` certified publication path requires the executable dispatcher;
the gate checks that rejection suppresses output for all four HT families.

### Current certified ELC boundary

`ContextCalculus.ELCompletion.DecodedCertificate.checkV5_publication_semantics`
is the public ELC capstone. A successful executable check proves source-level
inconsistency and complete taxonomy publication for both pure EL inputs and
inputs partitioned into direct clauses, canonical witnesses, and finitely
checked residual clauses. It checks NF1–NF7 closure, reflexive roles, backward
bottom propagation, the complete optimized Rust state, source normalization,
the finite symbol table, and exact ID-level and named output.

Set `KM_ELC_LEAN_REQUIRED=1` and point `KM_ELC_LEAN_CERT_CHECKER` at the built
`elc-cert-check` executable to use this fail-closed boundary. Missing,
malformed, or rejected evidence produces no ELC result. The positive-ABox
rewrite and incremental reasoning API are outside this ELC publication
boundary; certified mode declines the former, while native-ABox publication is
covered by the separately certified HT layer.

The ELC capstone has no admitted theorem. Its axiom report contains only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

### Certification roadmap

Certification releases are made only for complete layers:

1. complete production HT certification (v0.3.205);
2. complete ELC soundness and completeness certification (v0.3.206);
3. complete CB soundness and completeness certification;
4. complete automatic-routing soundness and completeness certification; and
5. an integrated cross-layer audit followed by v1.0.0.

CB and routing are not claimed complete until their respective public capstones,
executable correspondence, axiom audits, and integration gates all pass.

## Repository layout

- [`engine/`](engine/) – Rust reasoner, frontends, orchestration, and tests
- [`lean/`](lean/) – Lean definitions, proofs, and executable checkers
- [`protege/`](protege/) – Protégé integration
- [`docs/`](docs/) – architecture, formats, benchmarks, and operational notes
- [`CHANGELOG.md`](CHANGELOG.md) – release history and detailed proof milestones

## License

KM is distributed under the [BSD 3-Clause License](LICENSE).
