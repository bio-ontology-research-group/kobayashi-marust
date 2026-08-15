# Kobayashi-MaRust

**An experimental SROIQ / OWL 2 DL reasoner written in Rust.**

[![CI](https://github.com/bio-ontology-research-group/kobayashi-marust/actions/workflows/ci.yml/badge.svg)](https://github.com/bio-ontology-research-group/kobayashi-marust/actions/workflows/ci.yml)
[![License: BSD-3-Clause](https://img.shields.io/badge/License-BSD--3--Clause-blue.svg)](LICENSE)
[![Rust](https://img.shields.io/badge/engine-Rust-orange.svg)](engine)
[![Lean 4](https://img.shields.io/badge/formalisation-Lean%204-brightgreen.svg)](lean)

Kobayashi-MaRust, or KM, combines a disjunctive consequence-based engine, an
EL++ completion path, and feature-gated completion procedures in one automatic
classifier. The default command profiles an ontology and selects a route
without using the expected answer.

## Highlights

- `km classify` completes **591 of 592** ORE 2015 ontologies under the
  240-second, 20-GiB benchmark contract.
- The automatic results comprise **588 exact retained or independently derived
  full-IRI signatures** and three independently adjudicated results: contested
  consistency cases 2669 and 15516, and inconsistent ontology 10860. Ontology
  1194 is the only remaining non-completing input.
- KM accepts OWL functional syntax, OWL/XML, RDF/XML, and Turtle and fails
  closed when conversion, routing, or reasoning cannot produce a complete
  answer.
- The CLI also provides ontology profiles, bounded source-axiom explanations,
  and incremental reasoning. A Protégé 5.6 plugin is included.
- A separate Lean development proves results about selected abstract calculus
  components. It does not verify the complete Rust executable.

## Install

KM requires a recent stable Rust toolchain.

```sh
git clone https://github.com/bio-ontology-research-group/kobayashi-marust.git
cd kobayashi-marust/engine
cargo build --release --locked
./target/release/km --help
```

The main executable is `engine/target/release/km`. Versioned source releases
are available from the repository tags; the current release is `v0.2.35`.

## Classify an ontology

```sh
cd engine
./target/release/km classify ../examples/ontologies/kinship.ofn
./target/release/km classify ontology.owl
./target/release/km classify ontology.owx
./target/release/km classify ontology.ttl
```

The result is JSON containing named-class subsumptions, unsatisfiable classes,
consistency, and completion status. Plain `km classify` uses automatic routing.
It never needs Python.

Useful commands:

```sh
# Inspect ontology features and the selected route
./target/release/km profile ontology.owl

# List explicit routes
./target/release/km routes

# Force a named route for testing
./target/release/km classify --route production_all ontology.owl

# Explain a named-class subsumption
./target/release/km explain ontology.ofn subclass \
  http://example.org/A http://example.org/B

# Start a JSONL incremental-reasoning session
./target/release/km incremental
```

Use explicit routes for diagnostics and reproducibility. For ordinary inputs,
use the default automatic route. Route definitions and safety gates are in
[`docs/ROUTING.md`](docs/ROUTING.md).

### Input contract

KM detects functional syntax, OWL/XML, RDF/XML, and Turtle from content and
filename. Use `--format functional|owlxml|rdfxml|turtle` to override detection.
The CLI does not fetch imports. Supply a self-contained ontology with its
imports already merged. See [`docs/INPUT-FORMATS.md`](docs/INPUT-FORMATS.md).

## Current ORE 2015 result

The production benchmark covers one deployable command, `km classify`, over all
592 ontologies. Order-balanced paired job `50552285` verifies every result,
checkpoint, route trace, collision-sensitive full-IRI fingerprint, and binary
identity. The tested release-candidate binary is `d289f0e4c8c1…`.

| procedure | tested source | empirically correct | `status=ok` | wall mean s | wall median s | peak mean MiB | peak median MiB |
|---|---|---:|---:|---:|---:|---:|---:|
| **KM automatic, `km classify`** | `v0.2.35` / `d9c251a` (binary `d289f0e4c8c1…`) | **591** | **591** | 3.3302 | **0.1621** | **417.04** | **35.02** |
| Konclude | `v0.7.0-1138` / `0002e8063540` | 587 | 589 | **3.2657** | 0.2813 | 558.09 | 76.53 |

Values are measured on exclusive Intel Xeon Gold 6248 nodes with a 240-second
timeout and 20-GiB memory cap. All 592 paired comparisons agree in status,
verdict, consistency, selected route, solved state, answer counts, and full-IRI
signature. KM remains below Konclude on median wall time and both memory metrics;
mean wall time is the remaining performance target.

ORE10621 uses four bounded, independent subject-classification workers inside
its certified bridge. Three alternating same-node pairs reduce median wall time
from 83.2711 to 38.9416 seconds while preserving the gold signature. The full
sweep measures 38.8773 seconds and 1,555.30 MiB for ORE10621.

## Protégé plugin

The plugin invokes the native `km` executable and exposes the inferred named
class hierarchy and unsatisfiable classes in Protégé 5.6.

```sh
cd protege
mvn test
mvn package
```

Copy `target/kobayashi-marust-protege-0.3.0.jar` into Protégé's `plugins/`
directory and configure `KM_BIN` or `-Dkm.bin`. Platform-specific installation
and explanation integration are documented in
[`protege/README.md`](protege/README.md).

## Formalisation and correctness scope

The `lean/` directory contains a `sorry`-free Lean development for abstract
resolution, selected context-calculus constructions, inverse-role encoding,
nominal rules, and small certificate checkers. Build it separately:

```sh
cd lean
lake exe cache get
lake build
```

These theorems do not establish end-to-end soundness or completeness of the
Rust frontend, router, all completion procedures, concurrency, resource
fallbacks, or optimizations. ORE results are empirical and successful
termination alone is not accepted as correctness evidence. See
[`lean/README.md`](lean/README.md).

## Documentation

- [`engine/README.md`](engine/README.md): normalized clause engine and JSON API
- [`docs/ROUTING.md`](docs/ROUTING.md): routes, profiles, and safety gates
- [`docs/INPUT-FORMATS.md`](docs/INPUT-FORMATS.md): supported OWL syntaxes
- [`docs/EXPLANATIONS.md`](docs/EXPLANATIONS.md): explanation CLI and schema
- [`docs/INCREMENTAL-REASONING.md`](docs/INCREMENTAL-REASONING.md): incremental protocol
- [`CHANGELOG.md`](CHANGELOG.md): release and implementation history

## Repository layout

```text
engine/       Rust reasoner and `km` executable
lean/         Lean formalisation
protege/      Protégé plugin
docs/         user, architecture, and evidence documentation
results/      benchmark results and reproducibility records
validation/   small certificate examples
examples/     example ontologies
```

## License and citation

KM is available under the BSD-3-Clause license. See [LICENSE](LICENSE) and
[CITATION.cff](CITATION.cff).

The consequence-based calculus follows work by Tena-Cucala, Cuenca Grau, and
Horrocks and the Sequoia reasoner. Konclude, HermiT, and independent witnesses
provide comparison evidence where identified by the retained benchmark record.
