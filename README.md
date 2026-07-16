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
  or require a specialized route, and five corpus cases lack an
  independently adjudicated gold result.
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

The retained complete routing matrix covers all 592 ORE 2015 ontologies and 28
procedures per ontology, for 16,576 measurements at a 240 second timeout and
20 GiB memory cap. The frozen matrix, strict audit, and per-route average,
median, and p95 time and memory are documented in
[`results/benchmarks/2026-07-16-routing-complete592/`](results/benchmarks/2026-07-16-routing-complete592/).

Selected measured rows from that matrix:

| reasoner | solved / 592 | average wall time | median wall time | average peak RSS | median peak RSS |
|---|---:|---:|---:|---:|---:|
| **KM, demonstrated union of all exact routes** | **584** | pending current-route recheck | pending | pending | pending |
| Konclude, 16 threads | 588 | 2.129 s | 0.264 s | 738 MB | 245 MB |
| ELK | 579 | 1.995 s | 0.824 s | 611 MB | 349 MB |
| HermiT | 545 | 13.196 s | 1.851 s | 1,392 MB | 745 MB |

The current `production_all` portfolio was also rerun across the complete
592-entry corpus on IBEX. Array job `49006549` finished all scheduled work and
durably published 590 unique ontology rows. The two absent rows, `3524` and
`15703`, are process-tree/cgroup OOM failures in the benchmark supervisor, not
recorded KM outcomes. Among the 590 durable rows, 580 returned `ok`, eight
timed out, one reached the reasoner memory cap, and one declined an unsupported
DL-safe-rule input. The raw stored-gold audit contains 573 matches; the
adjudicated count is 574 because the only baseline-to-candidate difference,
the named class `daml:Nothing` in `13503`, is explicitly equivalent to
`ObjectComplementOf(owl:Thing)` and therefore must be unsatisfiable. Over the
573 literal stored-gold matches, the candidate averages 4.230 seconds and 615
MB, with medians of 0.268 seconds and 36 MB. These figures describe the single
production route, not the larger all-route union in the headline row.

The paired baseline job `49004275` likewise published 590 unique rows: 574
stored-gold matches, 4.646 seconds average and 623 MB average over those
matches, with medians of 0.267 seconds and 36 MB. Across the 589 directly
comparable ontology rows, the candidate has no genuine correctness change.
Notable wall-time reductions include `7581` (179.4 to 19.8 seconds), `16744`
(120.9 to 95.0 seconds), and `14459` (59.6 to 43.2 seconds). Recovery jobs for
the two missing terminal rows remain a harness-validation task and do not
invalidate the completed long-array measurements.

The KM headline is the union of every retained, valid exact closure, not only
the routes present in one matrix binary. The complete frozen matrix contains
575 exact KM closures. Retained route-specific runs add `10702`, `10908`,
`11745`, `15672`, `6934`, `7499`, `9540`, `9635`, and `3215`, giving 584 exact
matches to authoritative gold. In addition, `2669` and `15516` are
independently adjudicated inconsistent while their stored Konclude signatures
are stale, so KM has 586 demonstrated-correct corpus cases under the
adjudicated-gold accounting described in
[`docs/CONTESTED-GOLD.md`](docs/CONTESTED-GOLD.md).

The time and memory cells are temporarily withheld while the restored routes
are rerun under the current binary, 240 second timeout, and 20 GiB cap.
Publishing the frozen-matrix averages beside the larger cross-run union would
mix different ontology sets. Once the focused recheck finishes, each ontology
will contribute its minimum wall time across exact KM routes and,
independently, its minimum peak memory across exact KM routes.

A completed follow-up `cb_absorb_portfolio16` sweep supplies 547 exact rows and
restores `10908` beyond the frozen matrix, so the current-result route registry
now contains 576 exact ontologies. Its exact-row averages are 10.543 seconds
and 1,189 MB, with medians of 0.374 seconds and 125 MB. Two no-gold tasks
published empty files and one completed result for `11745` disagreed with
gold; none of those are counted. The separate 34-route proof array completed
as Slurm work but emitted only invalid error rows, so it contributes no route
claims.

Individual KM configurations remain available in the complete matrix report.
For example, `cb_plain16` completed 537 ontologies, `ht_bridge` completed 505,
and `elc_cert` completed 467; their separate time and memory distributions are
reported in the linked CSV and JSON. The 575-case matrix union is an oracle
envelope over that matrix's measured configurations. The 582-case headline
also includes retained exact closures from route families omitted or not
faithfully reproduced by that frozen matrix.

KM uses a typed production portfolio rather than one universal procedure.
[`docs/SOLVED-ONTOLOGIES.md`](docs/SOLVED-ONTOLOGIES.md) records the mechanism
used for each ontology requiring special treatment. The main special-treatment
families are exact nominal/ABox reasoning, the Konclude-derived KPSet bridge,
cardinality successors, role-specific saturation successors, EL certification,
DL-safe-rule consistency checks, and source-symbol isolation. The current hard
residual and restoration audit is in
[`docs/HARD-RESIDUAL-AUDIT.md`](docs/HARD-RESIDUAL-AUDIT.md); disputed or
invalid Konclude gold is tracked separately in
[`docs/CONTESTED-GOLD.md`](docs/CONTESTED-GOLD.md).

The root-context ordered-resolution experiment is compiled but remains opt-in
behind `KM_ROOT_ORDERED`. It changes calculus derivations and has no
implementation-level Lean certification. It is not part of the automatic
production route; the obligations in
[`docs/ROOT-ORDERED-RESOLUTION.md`](docs/ROOT-ORDERED-RESOLUTION.md) and the
full-corpus A/B gate remain open.

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
