# Kobayashi-MaRust

**A vibe-coded, certified OWL 2 DL reasoner in Rust.**

[![CI](https://github.com/bio-ontology-research-group/kobayashi-marust/actions/workflows/ci.yml/badge.svg)](https://github.com/bio-ontology-research-group/kobayashi-marust/actions/workflows/ci.yml)
[![License: BSD-3-Clause](https://img.shields.io/badge/License-BSD--3--Clause-blue.svg)](LICENSE)
[![Rust](https://img.shields.io/badge/engine-Rust-orange.svg)](engine)
[![Lean 4](https://img.shields.io/badge/proofs-Lean%204-brightgreen.svg)](lean)

Kobayashi-MaRust (KM) classifies OWL 2 DL ontologies. AI coding agents wrote
almost all of its code under human direction ("vibe coding"). Nobody reads
every line of such code, so KM does not ask you to trust it: Lean 4 proofs
cover the reasoning rules, and KM can hand each answer to a proof-checked
program that confirms it.

KM is one program, `km`, and a plugin for
[Protégé](https://protege.stanford.edu/).

## Highlights

- **All of OWL 2 DL.** Nominals, number restrictions, inverse and chained
  properties, datatypes and DL-safe rules. KM reads functional syntax,
  OWL/XML, RDF/XML and Turtle, and refuses input that is outside OWL 2 DL.
- **Fast and small.** On 585 held-out ORE 2015 ontologies (one core, 240 s
  limit), KM 1.7.0 solves 579, takes 1.70 s on average (median 0.14 s) and
  uses 31 MiB of memory at the median. Konclude 0.7.0 in the same run solves
  578, takes 2.06 s (median 0.17 s) and uses 49 MiB.
- **Checked answers.** With the checkers switched on, 1,618 of the 1,696
  ORE pool ontologies that KM solves come with an accepted certificate. No
  certificate was rejected. See
  [what "certified" means](#what-certified-means).
- **Works in Protégé.** The [plugin](#protégé-plugin) answers the reasoner
  queries that HermiT answers. In a comparison on 349 ontologies, KM and
  HermiT agreed on 554,406 calls, and HermiT was right in none of the calls
  where they differed.
- **More than a class hierarchy.** Types and equalities of individuals,
  property values, property hierarchies, explanations (justifications) and
  incremental re-classification after an edit.

Releases up to 1.6.5 gave wrong answers on some inputs. 1.7.0 fixes them;
the list is in [`docs/ERRATA-1.6.5.md`](docs/ERRATA-1.6.5.md). Everything new
in 1.7.0 is in the [release notes](docs/RELEASE-1.7.0.md).

## Install

Download `km` for your platform (Linux and macOS on x86-64 and ARM, Windows
on x86-64) from the
[releases page](https://github.com/bio-ontology-research-group/kobayashi-marust/releases).
It is a single file with no dependencies.

Or build it from source with a recent stable Rust:

```sh
git clone https://github.com/bio-ontology-research-group/kobayashi-marust.git
cd kobayashi-marust/engine
cargo build --release --locked --features mimalloc
./target/release/km --help
```

## Use

Classify an ontology:

```sh
km classify ontology.owl              # JSON result on standard output
km classify --lines ontology.owl      # one tab-separated row per result
```

Ask for more than the class hierarchy:

| Option | Adds |
|---|---|
| `--realize` | types of individuals, and which individuals are the same |
| `--values` | object and data property values of individuals |
| `--different` | individuals that must be different |
| `--properties`, `--data-properties` | the property hierarchies |
| `--export-model` | a model of the ontology, if it is consistent |
| `--iris full` | full IRIs in the output instead of the input's spelling |

Other commands:

```sh
km explain ontology.owl subclass EX:Child EX:Parent   # why does this hold?
km profile ontology.owl                               # which OWL features are used?
km classify --help                                    # every option
```

If the input is not valid OWL 2 DL, KM says what is wrong and exits with
code 2. If KM cannot give a complete answer, it says so and exits with
code 3. It never returns a partial answer as if it were complete.

More detail: [input formats](docs/INPUT-FORMATS.md),
[individuals](docs/REALIZATION.md), [properties](docs/PROPERTIES.md),
[explanations](docs/EXPLANATIONS.md),
[incremental reasoning](docs/INCREMENTAL-REASONING.md),
[datatypes](docs/DATATYPES.md), [rules](docs/DL-SAFE-RULES.md).

## Protégé plugin

1. Download the jar for your Protégé from the
   [releases page](https://github.com/bio-ontology-research-group/kobayashi-marust/releases):
   `kobayashi-marust-protege5-<version>.jar` for Protégé 5.6, or
   `kobayashi-marust-protege6-<version>.jar` for Protégé 6.
2. Copy it into the `plugins` folder of your Protégé and restart Protégé.
3. Choose **Reasoner → Kobayashi-MaRust → Start reasoner**.

The jar contains `km` for all five platforms, so nothing else needs to be
installed. A request to list KM under Protégé's **File → Check for
plugins** is open with the Protégé project. Setup details, the supported
queries and troubleshooting are in [`protege/README.md`](protege/README.md).

## What "certified" means

- **Proofs about the method.** The Lean 4 development in [`lean/`](lean/)
  proves that the reasoning rules only derive true consequences, and that
  they find all consequences for the EL, ALC and SHI fragments of OWL. The
  proofs contain no `sorry` and use only Lean's three standard axioms.
- **Checks of each answer.** For other inputs, KM can write a certificate,
  and a checker built from the Lean code confirms it: a model for a
  consistent ontology, a refutation for an inconsistent one. The
  `KM_LEAN_CHECKERS` setting switches this on; see
  [`docs/CHECKERS-ON.md`](docs/CHECKERS-ON.md).
- **What is not proved.** The Rust code itself, the OWL parser, the choice
  of reasoning method and the engine translated from Konclude are outside
  the proofs. For those, KM relies on the per-answer checks and on large
  comparison runs against HermiT and Konclude. About 5% of the ORE pool
  answers have no certificate yet, because a checker ran out of time or
  memory or declined the input.

Every release must pass all Lean gates on the exact tagged source. To run
them yourself:

```sh
cd lean && lake exe cache get && cd ..
./lean/run-elc-certification-gate.sh
./lean/run-ht-certification-gate.sh
./lean/run-cb-certification-gate.sh
./lean/run-routing-certification-gate.sh
./lean/run-rules-certification-gate.sh
```

The exact scope is in the [release notes](docs/RELEASE-1.7.0.md) and in
[`docs/CERTIFICATION-ROADMAP.md`](docs/CERTIFICATION-ROADMAP.md).

## How it works

`km classify` reads the ontology, looks at which OWL features it uses, and
picks a reasoning method:

- an EL completion procedure for ontologies in the EL family;
- a consequence-based engine for most other ontologies;
- a hypertableau engine, translated from Konclude, for the rest.

See [`docs/ROUTING.md`](docs/ROUTING.md).

## Known limits

- Some inputs with many nominals (classes defined by listing individuals)
  are slow, and a few synthetic ones time out.
- 12 of the 1,708 valid ORE pool ontologies are not solved within 240 s.
- Manchester syntax is not accepted.

The full list is under "Known limits" in the
[release notes](docs/RELEASE-1.7.0.md).

## Repository layout

- [`engine/`](engine/): the Rust reasoner and its tests
- [`lean/`](lean/): Lean proofs and checkers
- [`protege/`](protege/): the Protégé plugin
- [`docs/`](docs/): formats, design notes, release notes and benchmarks
- [`CHANGELOG.md`](CHANGELOG.md): release history

## Citing

See [`CITATION.cff`](CITATION.cff).

## License

KM's own code is under the [BSD 3-Clause License](LICENSE). Two parts come
from LGPL-3.0 projects: the hypertableau engine in
`engine/src/konclude_ht/` is a translation of
[Konclude](https://github.com/konclude/Konclude), and the readers for
OWL/XML, RDF/XML and Turtle use
[Horned-OWL](https://github.com/phillord/horned-owl). The `km` binary
contains both.
