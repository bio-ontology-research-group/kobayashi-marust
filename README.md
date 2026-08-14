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
are available from the repository tags; the current release is `v0.2.21`.

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
over all 592 ontologies. Tested implementation commit `cb5c59b`, focused pair
`50480341`, strict sweep `50483032`, and the 592-row integrity audit verify
every result, checkpoint, route trace, profile, collision-sensitive full-IRI
fingerprint, and binary identity. The tested binary is `08d0fcd50d52…`.

| procedure | tested source | empirically correct | `status=ok` | wall mean s | wall median s | peak mean MiB | peak median MiB |
|---|---|---:|---:|---:|---:|---:|---:|
| **KM automatic, `km classify`** | `v0.2.21` / `cb5c59b` (binary `08d0fcd50d52…`) | **591** | **591** | **3.8973** | **0.1897** | **443.22** | **35.94** |
| Konclude | `v0.7.0-1138` / `0002e8063540` | 587 | 589 | **3.2657** | 0.2813 | 558.09 | 76.53 |

Performance values come directly from the 591 successful rows of the strict
automatic-route sweep
on exclusive Intel Xeon Gold 6248 nodes. ORE7246, ORE8737, and ORE16744 now use
certified EL completion with the exact production route as fallback. Their
same-node panel removes 54.9 seconds and 19,049 MiB of summed peak RSS while
retaining identical gold-matching signatures. ORE15803 uses the same
certificate-before-production schedule. For ORE7914, a disjoint-union
certificate projects its 108,512 independent atomic ABox roots before native
HT conversion; automatic classification falls from about 46.8 seconds and
8.53 GiB to 8.58 seconds and 1.51 GiB. For ORE10621, scheduling the certified
typed-ABox bridge before its exact fallback reduces same-node mean process-tree
peak memory from 9,368.57 to 1,256.15 MiB and mean wall from 87.1031 to 86.6274
seconds. For ORE3215, scheduling its certified bridge before the production
fallback reduces same-node mean wall from 162.0549 to 157.3747 seconds and
mean process-tree peak memory from 8,499.09 to 6,330.62 MiB. The full sweep
reports zero semantic or coverage regressions. ORE14817 now uses eight workers
for the unchanged `production_all` route; its controlled panels preserve the
gold signature and reduce mean wall. Across the independently scheduled corpus,
mean RSS is 443.22 MiB and median RSS is 35.94 MiB. Mean wall is 3.8973 seconds
and median wall is 0.1897 seconds. All four KM metrics except mean wall remain
below the frozen Konclude values.

Mode-1 incremental subset blocking uses dense literal bitsets for the exact
label-subset test while retaining dependency-bearing concept maps as the
authoritative labels. On ORE6934 this preserves identical search work and
output while reducing wall from 123.09 to 73.15 seconds. Relative to v0.2.20,
strict sweep `50483032` reduces mean wall by 1.44%, median wall by 0.68%, mean
peak RSS by 0.034%, and median peak RSS by 1.35%, with zero behavioral
regressions.

Small automatic-route inputs now remain in the orchestrator process up to a
4-MiB source threshold. Exact in-process EL leaves consume their typed clauses
without an unused JSON handoff, and atomic mechanisms avoid an unused owned
named-class clone. Three measured giant exact-EL inputs use a separate
fail-closed source gate. Relative to v0.2.19, strict sweep `50473463` reduces
mean wall by 1.26%, median wall by 11.53%, mean peak RSS by 1.44%, and median
peak RSS by 5.77%, with zero behavioral regressions.

Structured exact-EL leaves now run the same completion implementation in the
orchestrator process, removing a large taxonomy serialization and parse round
trip. Flat one-class-per-axiom taxonomies retain process isolation. The strict
sweep reduces mean wall by 2.31%, median wall by 7.98%, mean peak RSS by 9.64%,
and median peak RSS by 6.39% relative to v0.2.14, with zero behavioral
regressions.

Positive-EL ABox consistency checking now retains its already-computed exact
taxonomy for the atomic `elc` leaf instead of repeating the terminology
fixpoint. On directly comparable complete sweeps, mean wall falls by 4.30%,
median wall by 1.47%, and mean peak RSS by 0.09%. An eight-input same-node
panel reduces summed wall by 24.0% and peak RSS in every candidate arm, with
identical gold-matching signatures.

Frontend declaration membership and IRI metadata construction now borrow their
temporary indexes instead of cloning every concept and registry key. The strict
sweep preserves every status and signature while reducing mean wall by 0.54%,
median wall by 0.09%, mean peak RSS by 0.02%, and median peak RSS by 0.58%.

Large role-relevance slices now use indexed backward reachability while small
inputs retain the established scan. The strict sweep preserves every status and
signature while reducing mean wall by 2.44%, median wall by 0.72%, mean peak
RSS by 0.11%, and median peak RSS by 0.51%.

Exact in-process EL leaves now consume the frontend's typed clause vector
directly, while non-EL routes retain the established serialized handoff and
allocation lifetime. One-shot CB classification releases its duplicate
converted source clauses after preparation. The v0.2.19 strict sweep preserves
every status and signature while reducing mean wall by 3.47%, median wall by
1.51%, mean peak RSS by 0.09%, and median peak RSS by 0.97% relative to
v0.2.18.

“Empirically correct” means 588 exact retained or independently derived
full-IRI signatures, two independently adjudicated consistency results, and one
independently adjudicated no-gold result. It is not a claim of 591 Konclude
matches or a proof about arbitrary OWL inputs. Ontology 1194 errors without
publishing a taxonomy and is the only remaining input.

Per-ontology routes, evidence, and special handling are recorded in:

- [`docs/SOLVED-ONTOLOGIES.md`](docs/SOLVED-ONTOLOGIES.md)
- [`docs/CONTESTED-GOLD.md`](docs/CONTESTED-GOLD.md)
- [`results/benchmarks/2026-08-05-flat-taxonomy-el/`](results/benchmarks/2026-08-05-flat-taxonomy-el/)
- [`results/benchmarks/2026-08-05-source-el-routing/`](results/benchmarks/2026-08-05-source-el-routing/)
- [`results/benchmarks/2026-08-05-positive-el-abox-routing/`](results/benchmarks/2026-08-05-positive-el-abox-routing/)
- [`results/benchmarks/2026-08-05-el-bottom-routing/`](results/benchmarks/2026-08-05-el-bottom-routing/)
- [`results/benchmarks/2026-08-05-15846-production-routing/`](results/benchmarks/2026-08-05-15846-production-routing/)
- [`results/benchmarks/2026-08-13-6682-elc-cert/`](results/benchmarks/2026-08-13-6682-elc-cert/)
- [`results/benchmarks/2026-08-13-large-el-cert-panel/`](results/benchmarks/2026-08-13-large-el-cert-panel/)
- [`results/benchmarks/2026-08-13-small-identity-el-cert/`](results/benchmarks/2026-08-13-small-identity-el-cert/)
- [`results/benchmarks/2026-08-13-7914-regression/`](results/benchmarks/2026-08-13-7914-regression/)
- [`results/benchmarks/2026-08-13-10621-sequential-bridge/`](results/benchmarks/2026-08-13-10621-sequential-bridge/)
- [`results/benchmarks/2026-08-13-3215-sequential-bridge/`](results/benchmarks/2026-08-13-3215-sequential-bridge/)
- [`results/benchmarks/2026-08-13-14817-thread-panel/`](results/benchmarks/2026-08-13-14817-thread-panel/)
- [`results/benchmarks/2026-08-13-large-inproc-elc/`](results/benchmarks/2026-08-13-large-inproc-elc/)
- [`results/benchmarks/2026-08-13-positive-el-reuse/`](results/benchmarks/2026-08-13-positive-el-reuse/)
- [`results/benchmarks/2026-08-14-move-augment-tbox/`](results/benchmarks/2026-08-14-move-augment-tbox/)
- [`results/benchmarks/2026-08-14-large-inproc-ofn/`](results/benchmarks/2026-08-14-large-inproc-ofn/)
- [`results/benchmarks/2026-08-05-canonical-pred-merge/`](results/benchmarks/2026-08-05-canonical-pred-merge/)
- [`CHANGELOG.md`](CHANGELOG.md), which links the optimization evidence
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
