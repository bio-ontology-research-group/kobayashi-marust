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
`v0.3.164`. Lean now proves the finite equality-free, equality-aware,
equality/cardinality, and distinct-cardinality HT refutation-tree formats sound
and complete relative to their semantic finite refutation relations.
Equality-changing transitions reconstruct checked canonical representative
paths, finite branch families receive verified depth padding, and the complete
finite HT source language and finite assignments have proved lossless bounded
JSON encodings. Every accepted ordinary or equality-aware finite HT refutation
tree also has an exact recursive JSON representation, including equality
representatives and paths. The checked ELC certificate has an exact public
taxonomy and inconsistency contract, including residual-source inputs and
unsatisfiable-class bottom rows. Cardinality refutation vectors, checked node
vectors, square matrices, and canonical depth-indexed cells also have proved
lossless encodings. Every checker-accepted finite equality/cardinality
refutation now has a bounded recursive wire document that decodes to an
accepted refutation at the same depth. Checked successors are preserved;
maximum-rule diagonal cells alone are canonicalized because the checker does
not inspect them. The same recursive representability result now covers
distinct-cardinality refutations, including exact preservation of every
directed `apart` pair in checked successor states. Accepted production-global
cardinality documents now pass an executable shape check and construct typed
checked SAT or closed outcomes with their model or inconsistency semantics.
Complete cardinality taxonomy documents already provide a positive-or-negative
decision for every named concept and ordered named pair. The concrete
equality-free clause-first runtime selector is total at each finite node budget:
it refutes, reaches a canonical model, or reports explicit node exhaustion for
iterative deepening. For equality-aware search, Lean now certifies the exact
quotient-clash-first control and the following ontology-order,
finite-assignment-order scan for quotient-closed undischarged clauses.
The finite executable quotient evaluator is proved equivalent to semantic
closed matching. Lean also certifies nearest-ancestor quotient pairwise
blocking, unblocked explicit-witness selection, equality-fresh-node selection,
and reconstruction of a closed recursive witness branch. A dedicated
quotient-closed recursive equality refutation relation now matches Rust's
grounding semantics and is proved sound; concrete clash, clause, and witness
selectors reconstruct its constructors. The production equality UNSAT and
query checker now evaluates branch bodies modulo the checked equality quotient,
matching Rust's closed grounding semantics, and accepted trees prove ontology
inconsistency, subsumption, or concept unsatisfiability as appropriate. Exact
recursive completeness now constructs an accepted tree from every finite
quotient-closed refutation, and every accepted tree has an exact decodable JSON
representation. A finite measure containing ordinary HT facts and equality
pairs now proves global termination of the clash-first equality runtime at each
node budget: it refutes or reaches a blocked/saturated terminal or explicit
frontier. Blocked equality terminals become SAT only when an independently
checked finite equality fold validates the fully materialized quotient graph;
global search composes that check while preserving node exhaustion as
inconclusive. Both production equality SAT JSON formats, the normalized finite
quotient and normalized anchored fallback, now have source-level soundness
theorems directly from successful decode and `Except.ok true`. Concrete Rust
field-construction correspondence, cardinality transition-enumerator
correspondence, CB, and automatic routing remain unfinished. Equality
countermodel paths are unchanged.

The cardinality runtime refinement now covers its first four ordered controls.
Lean mirrors Rust's exact finite `apart`-list scan and proves both selected-clash
soundness and exhaustive no-clash correspondence. It then lifts the certified
quotient concept-clash selector into the distinct-cardinality calculus. A new
quotient-closed distinct-cardinality refutation relation proves the exact
`closed_holds` clause scan sound, including selected and exhausted outcomes.
The quotient-blocked existential scan now composes with an executable
distinct-fresh-node selector, proving selected witness recursion sound and
fresh-node exhaustion exact. Minimum selection now uses the exact
quotient-closed marker and blocking premises, with a proved marker-relocation
lemma for materializing pairwise-distinct witnesses. Maximum and terminal
selection remain to be connected.

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
also checks exact residual-compilation evidence, the NF3 witness rewrite, and
canonical-model composition. The production worker can publish residual
results only after this checker accepts the complete wire-v5 certificate; it
fails closed if any stage fails. Unchecked repair output is never published by
this opt-in path.

The certification build also provides `ht-cert-check`. It bounds-checks a
versioned finite HT SAT or UNSAT document, then checks guarded bodies, branch
labels and edges, existential witnesses, saturation, clashes, and exhaustive
disjunctive children. Acceptance proves that SAT evidence constructs a model or
that empty-root UNSAT evidence excludes every nonempty-domain model. The Rust HT
worker emits checked decision evidence when
`KM_HT_LEAN_CERT_CHECKER=/path/to/ht-cert-check` and `KM_HT_GLOBAL=1` are set.
For equality-free inputs, an open blocked branch produces a regular-unravelling
model certificate while a closed search produces a finite refutation. The main
checker transfers either result through checked trigger absorption,
contrapositive extension, and body-equality normalization to the original
source ontology. The worker publishes global consistency only after Lean
accepts this source-aware document, and otherwise fails closed. For default
certification-only full pairwise blocking, Rust materializes each proposed
finite fold as ordinary edges in both predecessor directions. Lean exhaustively
checks the folded graph, so blocker selection remains outside the trust
boundary. A rejected fold resumes iterative deepening and is never published.
Full pairwise-signature equality alone does not guarantee that one-round folding
is closed under multi-edge role chains; Lean includes an executable
counterexample. Moreover, inverse roles combined with counting do not have the
finite-model property. Finite folded SAT evidence is therefore a sound
acceptance path, not a completeness argument for full SROIQ. Completing HT
certification requires a checked regular/unravelled-model certificate for that
fragment. For inconsistent clause sets admitting a finite
refutation, Rust independently constructs an exhaustive empty-root tree over
concept, role, and existential facts. An existential obligation may bind a
fresh certificate node to its semantic witness; Lean checks freshness before
accepting the added edge and filler label. Version 2 checks both global SAT and
UNSAT evidence with equality heads. SAT acceptance constructs a nonempty model
on node-equivalence classes after exhaustively checking labels, edges,
obligations, and every guarded grounding modulo equality. UNSAT children carry
the exact equality history, representative vector, and paths witnessing the
quotient. Publication occurs only after Lean accepts the evidence. Certified
full-pairwise mode lazily enumerates every finite variable assignment and
deepens its node frontier whenever a branch reaches it. A genuinely open branch
or an explicitly configured diagnostic node cap still declines. Equality-aware
query countermodels and taxonomy evidence, inverse roles, nominals, native ABoxes,
QO, and runtime termination/blocking correspondence remain separate HT
certification tasks.

The formalization also defines the canonical rooted-forest domain for the
next equality/nominal regular-model stage. Anonymous witnesses retain path
identity, while every selected nominal root denotes one domain value; Lean
proves the corresponding nominal concept has a singleton extension. Lean also
defines the anchored role model, closes direct edges under the
normalized RBox, proves witness and nominal-label satisfaction, and proves its
canonical-model theorem for guarded ontologies. Executable equality/nominal
regular publication still requires equality-closure evidence connecting Rust's
representatives and nominal carriers to the checked anchored model.

The native `ht-anchored-premises-check` bounds-checks a complete regular
certificate plus its nominal-root vector. Acceptance proves clash freedom,
exact nominal-label coherence, redirected witness completion, finite residual
saturation, and normalized RBox closure, then constructs an anchored
nominal-aware model of the exact decoded ontology. Equality/nominal publication
still requires checked evidence connecting Rust's union-find representatives
to these canonical nominal roots.

The anchored checker also accepts equality heads when either equality variable
has a checked positive nominal guard in the same clause body. Lean proves that
the guard makes the endpoint canonical, so finite endpoint equality entails
semantic equality. Unguarded equality heads remain rejected.

The build additionally provides `ht-regular-cert-check`,
`ht-regular-cardinality-cert-check`, and
`ht-anchored-cardinality-cert-check`. These executables decode the bounded
regular wires and run the proved finite cover, residual-clause, witness, and
cardinality checks. The anchored cardinality checker also validates the dense
equality image, nominal roots, explicit successor slots, and exact shared
dimensions; acceptance constructs one anchored interpretation satisfying the
ontology and all cardinality definitions. The ordinary regular checker
constructs the infinite regular unravelling model rather than relying on a
finite folded graph. The Rust producer emits the ordinary regular wire through
the equality-free global certification API. The dedicated
executables remain useful lower-layer checker targets; this does not claim that
the complete production HT route is certified for every SROIQ feature. The
Rust producer emits checker-accepted regular
documents for blocked equality-free branches, including normalized role-rule
partitioning, redirect witnesses, and finite endpoint closure. Production
publication uses one checked regular-SAT/finite-refutation envelope and composes
it with source preprocessing before the main checker accepts it.

Certified mode 6 also checks before SAT serialization that every generated
node has a strictly earlier predecessor and that no full-signature-blocked node
retains a generated child. Lean proves these invariants bound every expanded
ALC(H) path by the finite role-sensitive signature vocabulary. Cross-query SAT
caches are disabled in certified construction because they have no local
blocker witness.

Over the resulting finite fact vocabulary, Lean proves strict branch growth is
well-founded and proves the exhaustive-search completeness capstone: a concrete
transition enumerator that exposes every terminal obstruction and combines all
closed children must either refute the root or reach a canonical model of the
exact guarded ontology. Instantiating those transition premises for every Rust
HT update remains in progress.

Lean now represents an equality-free HT state exactly as a finite set of label,
edge, and obligation facts. It proves round-trip decoding, strict growth for
each absent branch head and fresh witness, and exact child closure for the
disjunctive and existential `Refutes` constructors. The completeness theorem is
specialized directly to this representation. Establishing the blocked fresh
address supply and matching Rust's enumerator to these transitions remains.

Lean characterizes fresh witness nodes exactly as addresses absent from the
finite active-node set, proves a fresh node exists while that universe has
capacity, and proves a blocked path below the signature depth can be extended
by one successor slot. An unused obligation-specific extension is therefore a
valid fresh witness. The remaining tree invariant must connect used extensions
to already-discharged obligations.

`ht-taxonomy-cert-check` checks one complete named taxonomy matrix: one concept
decision for every named class and one subsumption decision for every ordered
pair. Positive answers carry finite refutations and negative answers carry
finite countermodels. Position checks, exact row widths, exact row count,
bounded identifiers, and duplicate-free named classes prevent omitted,
duplicated, or reassigned cells. Set both
`KM_HT_LEAN_CERT_CHECKER=/path/to/ht-cert-check` and
`KM_HT_LEAN_TAXONOMY_CERT_CHECKER=/path/to/ht-taxonomy-cert-check`, together
with `KM_HT_GLOBAL=1`, to enable fail-closed certified taxonomy publication.
The worker derives its published taxonomy directly from the accepted matrix and
publishes nothing if either the global or taxonomy checker rejects. This covers
the equality-free ALC(H) fragment and checker-accepted finite or anchored
equality, nominal, and cardinality countermodels. Complete correspondence
between every Rust transition and the formal search remains unfinished. This
is not a certificate for all HT inputs or for
automatic routing.

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
