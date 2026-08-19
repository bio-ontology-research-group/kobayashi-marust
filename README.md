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
are available from the repository tags; the current certification release is
`v0.3.55`.

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
592 ontologies. Order-balanced paired job `50554161` verifies every result,
checkpoint, route trace, collision-sensitive full-IRI fingerprint, and binary
identity. The tested release-candidate binary is `bbef8d7efbc6…`.

| procedure | tested source | empirically correct | `status=ok` | wall mean s | wall median s | peak mean MiB | peak median MiB |
|---|---|---:|---:|---:|---:|---:|---:|
| **KM automatic, `km classify`** | `v0.2.36` / `6851533` (binary `bbef8d7efbc6…`) | **591** | **591** | **3.2383** | **0.1628** | **427.88** | **35.39** |
| Konclude | `v0.7.0-1138` / `0002e8063540` | 587 | 589 | 3.2657 | 0.2813 | 558.09 | 76.53 |

Values are measured on exclusive Intel Xeon Gold 6248 nodes with a 240-second
timeout and 20-GiB memory cap. All 592 paired comparisons agree in status,
verdict, consistency, selected route, solved state, answer counts, and full-IRI
signature. KM is below the frozen Konclude measurements on mean and median wall
time and mean and median peak memory.

The automatic route uses four bounded subject workers for the large SRIQ bridge
profile represented by ORE14817 and two for the large SHI profile represented
by ORE3215. Three-pair focused gates preserve each gold signature and reduce
median wall time from 91.8347 to 75.0825 seconds and from 125.5704 to 89.1692
seconds, respectively.

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
# Native checker linking can otherwise use one compiler per workstation core.
LEAN_NUM_THREADS=2 lake build elc-cert-check
LEAN_NUM_THREADS=2 lake build ht-cert-check
LEAN_NUM_THREADS=2 lake build ht-eq-cert-check
LEAN_NUM_THREADS=2 lake build ht-taxonomy-cert-check
```

The formalization proves soundness and canonical-model completeness for the
pure ELC normal-form calculus used by the Rust worker: NF1–NF7, explicit top
and bottom, existential bottom propagation, role hierarchy, reflexive roles,
and role chains. It proves that a sound, closed materialization yields the exact
taxonomy and inconsistency result. It also proves fail-closed composition for
abstract workers, sequential fallbacks, races, and profile-based routing.

The certification build provides `elc-cert-check`, a native Lean checker for
the versioned Rust certificate wire format. Wire version 5 carries the exact
raw ELC clauses, variable signature, generated conjunction origins, normalized
ontology, completion trace, and published result. Lean recomputes and validates
the raw-to-normal transformation before checking completion. Set
`KM_ELC_LEAN_CERT_CHECKER=/path/to/elc-cert-check` to require proof-trace,
closure, and Rust-state agreement before the pure ELC worker can publish. It
also checks exact residual-compilation evidence, although the production route
still declines residual publication pending certification of the NF3 witness
rewrite and canonical-model composition. The worker fails closed if any stage
fails. This opt-in path currently publishes only the pure NF1–NF7 ELC route.

The certification build also provides `ht-cert-check`. It bounds-checks a
versioned finite HT SAT or UNSAT document, then checks guarded bodies, branch
labels and edges, existential witnesses, saturation, clashes, and exhaustive
disjunctive children. Acceptance proves that SAT evidence constructs a model or
that empty-root UNSAT evidence excludes every nonempty-domain model. The Rust HT
worker emits finite SAT evidence when
`KM_HT_LEAN_CERT_CHECKER=/path/to/ht-cert-check` and `KM_HT_GLOBAL=1` are set.
It publishes global consistency only after Lean accepts the exact normalized
clauses and terminal model, and otherwise fails closed. For default
anywhere-subset blocking, Rust materializes the finite fold as ordinary edges;
Lean exhaustively checks the folded graph, so blocker selection remains outside
the trust boundary. For inconsistent clause sets admitting a bounded finite
refutation, Rust independently constructs an exhaustive empty-root tree over
concept, role, and existential facts. An existential obligation may bind a
fresh certificate node to its semantic witness; Lean checks freshness before
accepting the added edge and filler label. Version 2 checks both global SAT and
UNSAT evidence with equality heads. SAT acceptance constructs a nonempty model
on node-equivalence classes after exhaustively checking labels, edges,
obligations, and every guarded grounding modulo equality. UNSAT children carry
the exact equality history, representative vector, and paths witnessing the
quotient. Publication occurs only after Lean accepts the evidence. Open,
node-capped, or assignment-capped search declines. Equality-aware query
countermodels and taxonomy evidence, inverse roles, nominals, native ABoxes,
QO, and complete termination/blocking correspondence remain separate HT
certification tasks.

`ht-taxonomy-cert-check` checks one complete named taxonomy matrix: one concept
decision for every named class and one subsumption decision for every ordered
pair. Positive answers carry bounded refutations and negative answers carry
finite countermodels. Position checks, exact row widths, exact row count,
bounded identifiers, and duplicate-free named classes prevent omitted,
duplicated, or reassigned cells. Set both
`KM_HT_LEAN_CERT_CHECKER=/path/to/ht-cert-check` and
`KM_HT_LEAN_TAXONOMY_CERT_CHECKER=/path/to/ht-taxonomy-cert-check`, together
with `KM_HT_GLOBAL=1`, to enable fail-closed certified taxonomy publication.
The worker derives its published taxonomy directly from the accepted matrix and
publishes nothing if either the global or taxonomy checker rejects. This covers
only the equality-free ALC(H) certificate fragment described above; it is not a
certificate for all HT inputs or for automatic routing.

The Lean development also proves semantic exactness of the direct
frontend-to-NF1–NF7 translations. The checker validates the optimized Rust ELC
state against the formal closure, the complete active concept set, the ID-level
public relation, its named-string materialization, and the inconsistency flag.
Checker-enabled Rust publishes that verified named result directly. The
OWL/frontend-clause-to-normal-form translation has semantic proofs for direct
forms, conservative n-ary auxiliary expansion, and the raw two-clause Skolem
encoding of existential introduction. Executable raw recognizers check
variable wiring, Skolem pairing, whole-list assembly, auxiliary identity, and
equality with Rust's emitted normal forms. The residual formalization proves the canonical-model composition theorem
needed by plain `CertMode::Check`, over the same live concept-only domain Rust
enumerates, and provides a proved finite checker for compiled residual clauses.
CB, concrete production routing, and the remaining HT features are not yet
certified. ORE results are empirical and successful termination alone is not
correctness evidence. See
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
