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

- **v1.5.3** classifies `1,662 / 1,708` valid ontologies in the 1,920-file ORE
  2015 pool, verified against Konclude, HermiT, Openllet, and JFact, and refuses
  all `212 / 212` invalid inputs. Konclude solves `1,655`.
- On one core under a 240-second, 20-GiB limit, KM 1.5.3 has a mean wall time of
  `2.66 s` and a median of `0.14 s` (Konclude: `2.92 s` / `0.27 s`). On the
  `1,642` ontologies that both solve, KM takes `2.12 s` / `0.13 s` and Konclude
  `2.93 s` / `0.27 s`. See the [benchmark](#ore-2015-benchmark).
- KM accepts OWL functional syntax, OWL/XML, RDF/XML, and Turtle. Input
  validation rejects ontologies outside OWL 2 DL before reasoning.
- Conversion, routing, and certification paths fail closed when they cannot
  justify a complete result.
- Source-level transactional incremental reasoning reuses exact taxonomy rows,
  source indexes, and checked supports where eligible, with full-classification
  fallback and atomic updates. In v1.5.3 every evaluated update (`632 / 632`)
  and every completed session (`79 / 79`) is faster than reclassifying from
  scratch, on both the CLI and OWLAPI. See the
  [incremental API](docs/INCREMENTAL-REASONING.md).
- The native CLI and OWLAPI/Protégé integration return verified, subset-minimal
  source-axiom explanations for every advertised entailment kind.
- Lean provides sorry-free soundness and completeness certification for the
  production ELC, hypertableau, and CB publication boundaries and for their
  automatic routing composition. Accepted routed taxonomies are bound to the
  exact source clauses and requested named-class signature.

## Install

KM requires a recent stable Rust toolchain.

```sh
git clone https://github.com/bio-ontology-research-group/kobayashi-marust.git
cd kobayashi-marust/engine
cargo build --release --locked
./target/release/km --help
```

The main executable is `engine/target/release/km`. The measured v1.5.3 build
uses `--features mimalloc` and profile-guided optimization; see
[`docs/RELEASE-1.5.3.md`](docs/RELEASE-1.5.3.md#reproducing-and-inspecting-the-release).
Prebuilt Linux x86-64 executables and the Protégé JAR are attached to each
[GitHub release](https://github.com/bio-ontology-research-group/kobayashi-marust/releases).

## Classify an ontology

```sh
km classify ontology.owl
```

Write the JSON classification result to a file:

```sh
km classify ontology.owl > classification.json
```

For an explicit graph representation, use `km classify --json-edges ontology.owl`.
Its JSON includes `subsumptions_are_graph_edges: true`; consumers must take the
transitive closure of the `subsumptions` edges to obtain all entailed class
pairs. The graph can contain redundant edges. Consistency, unsatisfiable
classes, and dropped-axiom counts retain their usual meaning. Default JSON
continues to list expanded pairs. The graph option is incompatible with
`--lines`; `KM_JSON_GRAPH_EDGES=1` enables the same option for benchmark drivers.

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

### Input validation

Since v1.4.4, input checks reject malformed ontologies before reasoning. For
example, `"text"^^rdfs:Literal` has no literal lexical mapping: use of
`rdfs:Literal` as a data range does not make it a valid literal datatype. KM
explains the violation and exits with code 2 without rewriting the input or
producing a classification. A valid construct whose complete execution cannot
be established is a separate refusal (exit code 3).

Of the 1,920 files in the ORE 2015 pool, 1,708 pass the implemented checks and
212 are refused. Independent audits verified all 212 violations. The
anonymous-individual check follows the formal condition in
[OWL 2 section 11.2](https://www.w3.org/TR/owl2-syntax/#Global_Restrictions_on_Axioms_in_OWL_2_DL):
each anonymous tree must contain a node with at most one object-property
assertion to a named individual. The named-star example immediately after
that condition contradicts it; KM follows the explicit condition.

## ORE 2015 benchmark

### v1.5.3: full 1,920-ontology pool

The release benchmark runs `km classify` on the frozen 1,920-ontology ORE 2015
pool: 1,708 valid ontologies and 212 expected invalid-input refusals. Each run
uses one core, a 240-second timeout, and a 20,480-MiB process-tree RSS limit
on Intel Xeon Gold 6248 nodes (IBEX `cpu_intel_gold_6248`), the same hardware
as the baselines. A result counts as solved only when its taxonomy agrees with
the independent references (Konclude, HermiT, Openllet, and JFact).

KM 1.5.3 solves `1,662 / 1,708` and refuses `212 / 212` invalid inputs with
zero unresolved cases. Over its verified completions it has `2.6581 s` mean and
`0.1377 s` median wall time, and `218.23 MiB` mean and `56.27 MiB` median peak
RSS. Its taxonomies match released KM 1.5.0 on all `1,663` classifications
that both complete.

| Method | Version / commit | Verified solved / 1,708 | Mean / median (s) | Common with KM 1.5.3 | KM 1.5.3 on common, mean / median (s) | Method on common, mean / median (s) | KM 1.5.3 gained / lost |
|---|---|---:|---:|---:|---:|---:|---:|
| **KM 1.5.3** | `v1.5.3` / `ecc4b1c57bc7` | **1,662** | **2.6581 / 0.1377** | – | – | – | – |
| KM 1.5.0 | `v1.5.0` / `d95f0b840a43` | 1,661 | 3.2557 / 0.2305 | 1,661 | 2.6574 / 0.1374 | 3.2557 / 0.2305 | 1 / 0 |
| KM 1.5.2 | `v1.5.2` / `1f4fb91e61ae` | 1,660 | 5.6605 / 0.3209 | 1,660 | 2.5969 / 0.1373 | 5.6605 / 0.3209 | 2 / 0 |
| Konclude | `v0.7.0-1138` / `0002e8063540` | 1,655 | 2.9232 / 0.2690 | 1,642 | 2.1246 / 0.1336 | 2.9334 / 0.2671 | 20 / 13 |
| RustDL | `v0.4.41` / `7bf5af7e1b13` | 1,428 | 8.5060 / 0.6576 | 1,419 | 1.0699 / 0.1050 | 8.3728 / 0.6257 | 243 / 9 |
| RustDL | `v0.4.28` / `b120b1783dc8` | 1,212 | 5.1386 / 0.3312 | 1,205 | 1.0381 / 0.0979 | 5.0630 / 0.3183 | 457 / 7 |
| ELK | `v0.6.0` / `b8ac5ce83db0` | 1,411 | 11.9712 / 4.7772 | 1,399 | 1.7085 / 0.1061 | 11.7327 / 4.7464 | 263 / 12 |

Times are computed over each method's verified completions. The KM 1.5.2
figures come from a non-PGO build on different hardware; the
[release notes](docs/RELEASE-1.5.3.md#root-cause-diagnosis-of-the-v152-classification-discrepancy)
explain the discrepancy. Exact binaries, hashes, and per-case tables are in
[`docs/RELEASE-1.5.3.md`](docs/RELEASE-1.5.3.md) and the release assets
`BENCHMARKS.md` and `build-completion.json`.

### v1.5.3: incremental reasoning

The incremental benchmark uses 80 ORE 2015 ontologies, each with nine source
revisions (`r0` initial, `r1..r8` updates), five counterbalanced repetitions,
and four arms (KM 1.5.3 and KM 1.5.0, each retained and fresh). An update
counts as faster when the median of its five paired retained/fresh ratios is
below 1.0.

| Path | Candidate-complete ontologies / 80 | Update cells faster than fresh | Whole sessions faster than fresh |
|---|---:|---:|---:|
| CLI | 79 | 632 / 632 | 79 / 79 |
| OWLAPI | 79 | 632 / 632 | 79 / 79 |

No update falls back to full classification, and all 7,110 cross-arm
revision checks agree. Only `ore_ont_1194` times out in all four arms.

The corpus, limits, canonical signatures, adjudications, special cases, and
route history are documented in
[`docs/SOLVED-ONTOLOGIES.md`](docs/SOLVED-ONTOLOGIES.md),
[`docs/HARD-RESIDUAL-AUDIT.md`](docs/HARD-RESIDUAL-AUDIT.md), and
[`results/benchmarks/`](results/benchmarks/).

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
