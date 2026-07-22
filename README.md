# Kobayashi-MaRust

**An experimental SROIQ / OWL 2 DL reasoner with a production routing
portfolio, broad ORE 2015 evaluation, and a separate Lean formalisation of core
calculus results.**

[![CI](https://github.com/bio-ontology-research-group/kobayashi-marust/actions/workflows/ci.yml/badge.svg)](https://github.com/bio-ontology-research-group/kobayashi-marust/actions/workflows/ci.yml)
[![License: BSD-3-Clause](https://img.shields.io/badge/License-BSD--3--Clause-blue.svg)](LICENSE)
[![Rust](https://img.shields.io/badge/engine-Rust-orange.svg)](engine)
[![Lean 4](https://img.shields.io/badge/formalisation-Lean%204-brightgreen.svg)](lean)

Kobayashi-MaRust is a consequence-based ("context") reasoner for the description
logic **SROIQ** — the logic behind **OWL 2 DL** — built on the disjunctive
context calculus of Tena-Cucala, Cuenca Grau and Horrocks (the core of the
[Sequoia](https://github.com/andrewdbate/Sequoia) reasoner). The shipped
classifier is a hybrid portfolio: a consequence-based engine, an EL++
completion path, and several gated completion procedures ported from Konclude.

The repository also contains a `sorry`-free Lean development for abstract
soundness and completeness results on several calculus components, plus a
small certificate-validation suite. That formalisation does **not** verify the
current Rust implementation, its router, or every production procedure and
optimization. The benchmark and regression evidence below is therefore
reported as empirical evidence, not as a proof of the whole executable.

## Highlights

- **Complete all-route ORE matrix.** The retained benchmark runs 28 procedures
  over all 592 ORE 2015 ontologies: 16,576 isolated measurements at 240 seconds
  and 20 GiB per route. It reports successful-row average, median, and p95 wall
  time and peak memory for every procedure.
- **Broad but not universal production coverage.** The portfolio handles EL,
  disjunction, quantifiers, role hierarchies and chains, inverses, nominals,
  number restrictions, and selected rule/ABox cases. Some ontologies time out
  or require a specialized route. Three corpus cases remain explicit
  nonclaims under the current 240 second and 20 GiB limits.
- **Measured routing rather than one universal algorithm.** `km classify`
  profiles each ontology and selects among the CB engine, EL completion, exact
  nominal handling, and gated Konclude-derived completion procedures. The
  route matrix records where each procedure succeeds and where it declines.
- **Standard OWL input.** The CLI accepts OWL functional syntax, OWL/XML,
  RDF/XML, and Turtle. Conversion and imports fail closed instead of silently
  classifying a partial ontology.
- **Protégé Desktop integration.** The 0.2.0 plugin targets Protégé 5.6,
  flattens loaded imports, invokes the native `km` executable, and exposes the
  inferred named-class hierarchy and unsatisfiable classes.
- **Formal work kept in scope.** Lean files prove results about abstract
  resolution, selected context-calculus fragments, inverse-role encoding,
  nominal rules, and certificate checkers. They are useful specifications and
  supporting mathematics, but they are not a verification of the complete
  current production portfolio.

---

## Quick start

### 1. Run the reasoner

```sh
cd engine
cargo build --release
echo '{"clauses":[
  {"body":[{"kind":"concept","concept":"A","term":{"kind":"var","name":"x"}}],
   "head":[{"kind":"concept","concept":"B","term":{"kind":"var","name":"x"}},
           {"kind":"concept","concept":"C","term":{"kind":"var","name":"x"}}]},
  {"body":[{"kind":"concept","concept":"B","term":{"kind":"var","name":"x"}}],
   "head":[{"kind":"concept","concept":"D","term":{"kind":"var","name":"x"}}]},
  {"body":[{"kind":"concept","concept":"C","term":{"kind":"var","name":"x"}}],
   "head":[{"kind":"concept","concept":"D","term":{"kind":"var","name":"x"}}]}
]}' | ./target/release/kobayashi-marust
# => {"subsumptions":{"A":["D"],...},...}   (A ⊑ D, by disjunctive reasoning)
```

The engine reads normalised DL clauses as JSON on stdin and writes the entailed
subsumptions, derived clauses, and a consistency flag on stdout (see
[`engine/README.md`](engine/README.md)).

For end-to-end OWL classification, use the multi-call binary:

```sh
./target/release/km classify ontology.ofn
./target/release/km classify ontology.owl
./target/release/km classify ontology.owx
./target/release/km classify ontology.ttl
./target/release/km profile ontology.ofn
./target/release/km routes
```

`km classify` profiles the ontology and selects its measured procedure by
default. `--route NAME` selects any named procedure; `--route manual` preserves
individually supplied `KM_*` options. See [`docs/ROUTING.md`](docs/ROUTING.md)
for the exact expressivity calculation, statistics schema, option bundles, and
decision-tree validation.

KM accepts OWL functional syntax, OWL/XML, RDF/XML, and Turtle. It detects the
format from content and the filename; use
`--format functional|owlxml|rdfxml|turtle` to override detection. External
syntaxes are parsed into Horned-OWL's structural model and serialized to the
same functional syntax frontend used by native inputs. RDF-to-OWL conversion
must be complete, or KM declines instead of reasoning over a partial graph.
Ontology imports are not fetched implicitly: supply a self-contained ontology
with imports already merged. See
[`docs/INPUT-FORMATS.md`](docs/INPUT-FORMATS.md) for the exact detection,
conversion, safety, and licensing contract.

## ORE 2015 benchmark status

The current source-bound confirmation covers all 592 ORE 2015 ontologies at a
240 second timeout and 20 GiB memory cap. KM reproduces 589 sound-and-complete
classifications: 587 are exact full-IRI matches to a contemporaneous Konclude
run, and `2669` and `15516` are independently adjudicated inconsistent.

The
[commit-pinned ontology route and performance table](https://github.com/bio-ontology-research-group/kobayashi-marust/blob/2c93063c12d2acdfa421cdac9ed0df3a1aa1bb42/results/benchmarks/2026-07-22-reproduced-route-performance/ontology-route-performance.tsv)
records every ontology's KM route, exact command, environment, source revision,
binary hash, time, memory, taxonomy hash, and evidence. It also contains
Konclude, HermiT, and ELK measurements plus separate `sound` and `complete`
fields. The
[pinned receipt and aggregation code](https://github.com/bio-ontology-research-group/kobayashi-marust/tree/2c93063c12d2acdfa421cdac9ed0df3a1aa1bb42/results/benchmarks/2026-07-22-reproduced-route-performance)
make the table directly reproducible from the cited evidence.

### Coverage and empirical correctness

The correctness fields concern the named-class taxonomy against the cited
full-IRI reference, frozen local-name oracle, or explicit adjudication. They do
not claim a formal proof for all OWL inputs. `not_applicable` means no
classification answer exists to assess, while `unknown` means an answer exists
but the available oracle cannot decide the property.

| reasoner | sound yes / no / unknown / N/A | complete yes / no / unknown | sound + complete / 592 |
|---|---:|---:|---:|
| **KM** | **589 / 1 / 0 / 2** | **589 / 2 / 1** | **589** |
| Konclude | 589 / 0 / 0 / 3 | 587 / 5 / 0 | 587 |
| HermiT | 551 / 5 / 0 / 36 | 552 / 40 / 0 | 551 |
| ELK | 581 / 6 / 3 / 2 | 531 / 58 / 3 | 531 |

### Time and memory

Averages and medians use only rows whose reasoner status is `ok`; the metric
population therefore appears in every row. KM and the paired Konclude row use
the current source-bound full-IRI confirmation. HermiT and ELK use the repaired
frozen external-baseline matrix on the same Intel Xeon Gold 6248 CPU model and
limits, but not the same Slurm job.

| reasoner and measurement set | metric rows | wall mean s | wall median s | peak mean MB | peak median MB |
|---|---:|---:|---:|---:|---:|
| **KM, accepted reproduced routes** | **589** | **5.366** | **0.234** | **691** | **38** |
| Konclude 16, current paired full-IRI references | 587 | 3.376 | 0.235 | 561 | 75 |
| HermiT, repaired frozen matrix | 556 | 12.953 | 1.759 | 1,369 | 741 |
| ELK, repaired frozen matrix | 590 | 1.968 | 0.821 | 602 | 347 |

On the strict same-ontology set of 587 current full-IRI pairs, KM has mean and
median wall times of 5.384 and 0.234 seconds versus Konclude's 3.376 and 0.235
seconds. KM's mean and median peak RSS are 693 and 38 MB versus Konclude's 561
and 75 MB. KM therefore has nearly the same median wall time and about half the
median memory, but higher mean time and memory because several accepted
specialist routes are expensive.

For reference, the repaired frozen Konclude-16 baseline has 588 successful
rows, 2.129 and 0.264 second mean and median wall time, and 738 and 245 MB mean
and median peak RSS. Its ontology population differs from the paired current
row. The repaired raw matrix also has 590 successful ELK rows and 556
successful HermiT rows, superseding the pre-repair counts in the July 16
aggregate.

### Remaining nonclaims

Three ontologies remain unclosed. `4669` completes but targeted satisfiability
checks refute its KM answer, so it is unsound and its completeness remains
unknown. `10860` contains unsupported DL-safe rule atoms and lacks an
authoritative complete oracle. `1194` exceeds the 20 GiB limit on every tested
complete KM route. `10621` is no longer residual: the confirmed `ht_bridge`
route is an exact full-IRI match.

The earlier 28-procedure matrix and historical analysis remain in
[`results/benchmarks/2026-07-16-routing-complete592/`](results/benchmarks/2026-07-16-routing-complete592/).
Disputed reference results are documented in
[`docs/CONTESTED-GOLD.md`](docs/CONTESTED-GOLD.md), and the source-bound route
confirmation is documented in
[`results/benchmarks/2026-07-21-route-confirmation/`](results/benchmarks/2026-07-21-route-confirmation/).

### 2. Build the Lean formalisation

```sh
cd lean
lake exe cache get      # fetch prebuilt mathlib oleans
lake build
```

This checks the abstract calculus theorems and the checked-in small validation
examples. It does not certify the Rust source, production routing policy, or
the full ORE output.

### 3. Regenerate the small certificate examples

```sh
bash validation/run.sh
```

This exercises a fixed set of small examples and regenerates Lean-checkable
certificates for those examples. It is not the ORE benchmark and does not
certify arbitrary classifications.

## Formalisation status

The retained Lean development is `sorry`-free. It contains:

- soundness lemmas for abstract resolution and paramodulation;
- completeness results for propositional resolution, an EL completion model,
  selected disjunctive/context and equality constructions, and ordered ground
  resolution;
- formal accounts of inverse-role bridge encoding and nominal rules; and
- certificate checkers used by the small examples under `lean/Validation/`.

These are mathematical results about Lean definitions. The Rust engine includes
multiple frontends, routing decisions, specialized completion procedures,
concurrency, resource fallbacks, and many performance optimizations. No theorem
currently connects all of that executable code to one end-to-end soundness or
completeness statement. See [`lean/README.md`](lean/README.md) for theorem-level
details, but do not interpret that document as a certification of every
production route.

---

## Repository layout

```
engine/        Rust reasoner and multi-call `km` executable
  src/                 frontend, routing, reasoners, orchestration, and JSON I/O
  py/                  reference and analysis tooling
lean/          Lean 4 formalisation
  ContextCalculus/     abstract calculus theorems and certificate checkers
  Validation/          checked-in small certificate examples
validation/    small-example certificate regeneration
oracle/        HermiT cross-check (scripts, reference results, ontologies)
examples/      example OWL ontologies (.ofn)
protege/       Protégé reasoner plugin (Maven; OSGi bundle)
```

## Protégé plugin

`protege/` is a [Protégé](https://protege.stanford.edu/) **reasoner plugin**:
Kobayashi-MaRust appears in the *Reasoner* menu and computes the inferred class
hierarchy and unsatisfiable classes. It is a thin OWL API `OWLReasoner` that
serialises the loaded imports closure, invokes the pure-Rust `km` binary, and
maps the named-class subsumptions back into Protégé.

```sh
cd protege
mvn test
mvn package   # -> target/kobayashi-marust-protege-0.2.0.jar
```

The plugin does not require Python. Copy the JAR into Protégé's `plugins/`
directory and configure `KM_BIN` or `-Dkm.bin`. See
[`protege/README.md`](protege/README.md) for complete Linux, macOS, and Windows
installation instructions.

---

## The calculus, briefly

Each named concept `A` seeds a **root context** with core `{A(x)}`; anonymous
successors live in **successor contexts**. Context clauses `Γ → Δ` (a body
conjunction of predicates implying a head disjunction of literals) are derived by
the rules **Core / Hyper / Pred / Succ / Eq / Ineq / Elim**. Every rule is, model-
theoretically, related to clausal resolution or paramodulation. The Lean
development formalises abstract versions of these operations; it does not prove
that every Rust rule implementation is equivalent to those definitions. Terms
are integer-encoded as in Sequoia
(`x=0`, `y=-1`, `z_i=-(i+1)`, `f_i(x)=+i`). The engine uses a *pay-as-you-go*
expansion strategy with one successor context per function symbol. The
production classifier also uses procedures outside this CB core.

**References**

- Horrocks, Kutz, Sattler. *The Even More Irresistible SROIQ.* KR 2006.
- Motik, Shearer, Horrocks. *Hypertableau reasoning for description logics.* JAIR 2009.
- Tena-Cucala, Cuenca Grau, Horrocks. *Consequence-based reasoning for description
  logics with disjunction, inverse roles, number restrictions, and nominals.* (Sequoia.)

---

## Scope and honest limitations

- The current production executable is not formally verified end to end.
- The Lean development proves properties of abstract definitions and validates
  a fixed collection of small certificates. It does not cover the complete
  router, all Konclude-derived procedures, the Rust frontend, concurrency,
  resource fallback behavior, or every optimization.
- ORE evidence is empirical. The complete route matrix measures all 592
  ontologies, but successful termination does not itself establish correctness.
  Comparisons use retained Konclude signatures where available, with contested
  and missing gold documented separately.
- No single KM procedure solves the full corpus within the benchmark limits.
  Coverage comes from the union of specialized routes. Some procedures are
  experimental or complete-or-defer only and are excluded from automatic
  routing unless their gate succeeds.
- `KM_ROOT_ORDERED` remains opt-in. It changes the CB derivation system and has
  no current implementation-level Lean certification or complete corpus gate.
- The general regular-role-hierarchy automaton is not implemented. The frontend
  supports transitivity and the role-chain handling documented in the source
  and benchmark records.
- The Protégé plugin exposes TBox classification only. Property and individual
  inference methods return no inferred results.

## OWL frontend

The production frontend is Rust. It accepts OWL functional syntax directly and
uses Horned-OWL adapters for OWL/XML, RDF/XML, and Turtle. Imports are not
downloaded by the CLI; callers must provide a merged ontology. The Protégé
plugin supplies the loaded imports closure explicitly.

## License & citation

BSD-3-Clause (see [LICENSE](LICENSE)). If you use Kobayashi-MaRust, please cite it
via [CITATION.cff](CITATION.cff).

## Acknowledgements

Built in the [Bio-Ontology Research Group](https://github.com/bio-ontology-research-group)
at KAUST. The calculus follows Tena-Cucala, Cuenca Grau and Horrocks and the
Sequoia reasoner. Konclude signatures provide the main ORE comparison, with
HermiT and manual witnesses used only where the retained adjudication records
say so.
