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

- `km classify` completes **590 of 592** ORE 2015 ontologies under the
  240-second, 20-GiB benchmark contract.
- The automatic results comprise **587 exact Konclude-signature matches** and
  three independently adjudicated inconsistent ontologies: 2669, 15516, and
  10860. Ontologies 1194 and 4669 remain non-completing.
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
are available from the repository tags; the current release is `v0.2.0`.

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

The current production claim concerns one deployable command, `km classify`,
over all 592 ontologies. Array `49721626` and independent audit `49734184`
verified every terminal row, checkpoint, route trace, and binary identity.
Metrics use the 590 successful rows.

| procedure | tested source | empirically correct | `status=ok` | wall mean s | wall median s | peak mean MiB | peak median MiB |
|---|---|---:|---:|---:|---:|---:|---:|
| **KM automatic, `km classify`** | v0.2.0 behavior, certified `4703045` binary | **590** | **590** | **6.6081** | **0.2734** | **798.90** | **43.49** |

“Empirically correct” means 587 exact retained Konclude full-IRI signatures
plus the three independently adjudicated inconsistency results. It is not a
claim of 590 Konclude matches or a proof about arbitrary OWL inputs. The two
remaining inputs are 1194, which errors without publishing a taxonomy, and
4669, which times out without publishing a taxonomy.

Per-ontology routes, evidence, and special handling are recorded in:

- [`docs/SOLVED-ONTOLOGIES.md`](docs/SOLVED-ONTOLOGIES.md)
- [`docs/CONTESTED-GOLD.md`](docs/CONTESTED-GOLD.md)
- [`docs/HARD-RESIDUAL-AUDIT.md`](docs/HARD-RESIDUAL-AUDIT.md)
- [`results/benchmarks/2026-07-18-ore-solve-routes/ontology-solve-routes.tsv`](results/benchmarks/2026-07-18-ore-solve-routes/ontology-solve-routes.tsv)

### Frozen uniform comparison

The latest completed uniform cross-reasoner panel predates v0.2.0. It ran all
listed implementations on the same hardware with the same 240-second,
20-GiB, 16-core contract. The KM row is therefore correctly labelled with its
older commit and must not be read as the current automatic result.

| procedure | tested version or commit | empirically correct | `status=ok` | wall mean s | wall median s | peak mean MiB | peak median MiB |
|---|---|---:|---:|---:|---:|---:|---:|
| KM automatic, frozen panel | `8c731f43b3c8` | 570 | 571 | 5.3000 | 0.2807 | 789.92 | 44.43 |
| Konclude | `v0.7.0-1138` (`0002e8063540`) | 587 | 589 | 3.2657 | 0.2813 | 558.09 | 76.53 |
| HermiT | `1.4.6.519-SNAPSHOT` | 557 | 558 | 13.1261 | 1.8868 | 1,330.56 | 714.01 |
| ELK | `0.6.0` | 531 | 592 | 1.7449 | 0.7466 | 505.86 | 234.11 |
| RustDL, complete mode | `0.3.31` (`8c2bb1bf43d9`) | 530 | 551 | 4.9596 | 0.1928 | 299.49 | 49.80 |
| Sequoia, strict mode | `0.6.1-alpha` (`c5248ec7be30`) | 339 | 341 | 7.3405 | 2.5371 | 2,197.31 | 536.15 |

The complete 39,072-measurement package, scoring rules, raw rows, hashes, and
receipts are in
[`results/benchmarks/2026-07-22-reproduced-route-performance/`](results/benchmarks/2026-07-22-reproduced-route-performance/).
A fresh uniform v0.2.0 panel is being run before replacing this table.

### Route-selection terminology

- **Automatic route:** `km classify` chooses from ontology features without
  knowing the expected result. This is the deployable classifier.
- **Preselected routes:** a fixed ontology-to-route map is chosen before a
  benchmark run.
- **Oracle-selected route:** after all procedures run and correctness is
  known, the fastest correct route is selected separately for each ontology.
  This is a retrospective upper bound, not a deployable classifier.

Detailed route unions and oracle-selected measurements belong in benchmark
artifacts rather than the release headline.

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
