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

- **Complete all-route ORE matrix.** The fresh source-bound benchmark runs 66
  procedures over all 592 ORE 2015 ontologies: 39,072 isolated measurements at
  240 seconds and 20 GiB per procedure. It includes all public KM routes,
  historically selected environments, optimization stages and ablations, plus
  Konclude, HermiT, ELK, RustDL, and Sequoia.
- **Broad but not universal production coverage.** The latest completed
  automatic sweep has 585 operational completions and 583 exact
  Konclude-signature matches among 592 ontologies. Some ontologies still time
  out, decline, or have contested consistency gold. Automatic 10702 and 12653
  recoveries are in source-bound validation sweeps and are not included in
  those completed totals.
- **Measured routing rather than one universal algorithm.** `km classify`
  profiles each ontology and selects among the CB engine, EL completion, exact
  nominal handling, and gated Konclude-derived completion procedures. The
  route matrix records where each procedure succeeds and where it declines.
- **Standard OWL input.** The CLI accepts OWL functional syntax, OWL/XML,
  RDF/XML, and Turtle. Conversion and imports fail closed instead of silently
  classifying a partial ontology.
- **Protégé Desktop integration.** The 0.3.0 plugin targets Protégé 5.6,
  flattens loaded imports, invokes the native `km` executable, and exposes the
  inferred named-class hierarchy and unsatisfiable classes. The bundle also
  provides an OWL Explanation API 2.0.1 generator/factory and a cancellable
  source-justification panel for Protégé's standard Explain action.
- **Bounded source-axiom explanations.** `km explain` enumerates verified,
  subset-minimal justifications for a named-class subsumption, unsatisfiable
  class, or inconsistency. Schema 2 exposes source OWL axioms, explicit bounds,
  and enumeration status to CLI and OWLAPI clients.
- **Exact incremental EL++, CB, and direct-HT reasoning.** `km incremental`
  retains the completed EL++ relation and role graph for safe additions,
  accepts the full normalised clause fragment completed by the CB worker, and
  offers an explicit hypertableau backend for its validated direct-clause
  fragment. HT additions can resume compatible completion graphs; removals and
  replacements reuse monotonic and dependency-independent probes. Every
  uncertain probe runs fresh before the transaction commits.
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
./target/release/km incremental
./target/release/km explain ontology.ofn subclass \
  http://example.org/A http://example.org/B
```

`km classify` profiles the ontology and selects its measured procedure by
default. `--route NAME` selects any named procedure; `--route manual` preserves
individually supplied `KM_*` options. See [`docs/ROUTING.md`](docs/ROUTING.md)
for the exact expressivity calculation, statistics schema, option bundles, and
decision-tree validation.

`km explain` accepts a self-contained functional-syntax source and returns one
or more source-axiom justifications. Explanation checks are bounded and opt-in,
so the normal classifier carries no provenance overhead. It always uses
automatic production routing; manual and forced matrix routes are rejected.
The Protégé module exposes the same contract through the standard OWL
Explanation API. See
[`docs/EXPLANATIONS.md`](docs/EXPLANATIONS.md) for query syntax, the JSON
schema, minimality semantics, Java configuration, and the exact supported
OWLAPI/Protégé entailment surface.

`km incremental` serves an exact EL++/CB/direct-HT session over JSONL standard
input and output. It consumes normalised clauses, assigns stable ids, and
supports addition, removal, and combined replacement. The default policy
remains EL-first with exact CB fallback; set `"backend":"ht"` on `init` to
select the validated direct HT fragment. Unsupported or incomplete snapshots
are rejected atomically instead of exposing a partial answer.
See [`docs/INCREMENTAL-REASONING.md`](docs/INCREMENTAL-REASONING.md) for the
protocol, Rust API, correctness argument, and current limitations.

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

> **2026-07-23 rerun status:** the merged engine revision
> [`efbcbbc`](https://github.com/bio-ontology-research-group/kobayashi-marust/commit/efbcbbc57193bd5a50b0ee8f07c25114414fc01d)
> restores the two source-bound mechanisms for 9540 and 10621. The frozen
> rerun contract now contains 37 public KM routes and 68 total procedures
> (40,256 limited measurements) in exactly 30 Slurm chunks. The published
> table below remains the completed 66-procedure run until the new IBEX results
> pass exact full-IRI scoring and aggregation; this note is not a 589-coverage
> claim.

The fresh source-bound panel runs 66 procedures on each of all 592 ORE 2015
ontologies, for 39,072 independently limited measurements. Every procedure
receives 240 seconds, 20 GiB summed process-tree RSS, and 16 CPU cores on the
same IBEX CPU model. The frozen KM revision is
`8c731f43b3c8a277f5fd7a25687e35afb4c4045e`.

| procedure | sound yes | complete yes | both yes | `status=ok` | wall mean s | wall median s | peak mean MiB | peak median MiB |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| **KM, preselected current routes** | **583** | **583** | **583** | 583 | 5.0168 | 0.2336 | 643.16 | 37.12 |
| KM, oracle-selected current route | 587 | 587 | 587 | 587 | 3.4696 | 0.1883 | 393.83 | 29.03 |
| **KM, automatic route** | **570** | **570** | **570** | 571 | 5.3000 | 0.2807 | 789.92 | 44.43 |
| Konclude | 589 | 587 | 587 | 589 | 3.2657 | 0.2813 | 558.09 | 76.53 |
| HermiT | 557 | 558 | 557 | 558 | 13.1261 | 1.8868 | 1,330.56 | 714.01 |
| ELK | 578 | 531 | 531 | 592 | 1.7449 | 0.7466 | 505.86 | 234.11 |
| RustDL, complete mode | 547 | 530 | 530 | 551 | 4.9596 | 0.1928 | 299.49 | 49.80 |
| Sequoia, strict mode | 340 | 339 | 339 | 341 | 7.3405 | 2.5371 | 2,197.31 | 536.15 |

The `sound` and `complete` columns are separate empirical judgments about the
named-class taxonomy against the cited full-IRI reference or adjudication.
They are not global proofs about a reasoner. Averages and medians use only
`status=ok` rows, so the table also reports that metric population. The result
package contains all-attempt metrics, including timeouts, memory exits,
unsupported inputs, and errors. Peak memory is MiB even though the retained
field name is `peak_mb`.

The
[main-branch per-ontology route table](https://github.com/bio-ontology-research-group/kobayashi-marust/blob/main/results/benchmarks/2026-07-22-reproduced-route-performance/ontology-route-performance.scoring-v2.tsv)
records every command, environment, source revision, binary and runtime hash,
time, memory, taxonomy hash, correctness field, and evidence locator. The
[main-branch result package](https://github.com/bio-ontology-research-group/kobayashi-marust/tree/main/results/benchmarks/2026-07-22-reproduced-route-performance)
also contains the 66-arm contract, raw and normalized measurements, build and
Slurm receipts, optimization comparisons, and an executable Showboat
verification record.

The authoritative correctness labels are scoring schema v2 in
[`full-panel-results.scoring-v2.tsv.gz`](results/benchmarks/2026-07-22-reproduced-route-performance/full-panel-results.scoring-v2.tsv.gz).
The reasoner measurements are unchanged. Schema v2 repairs two post-processing
errors: shared inconsistency was compared as if two different taxonomy
serializations denoted different answers, and exact same-job full-IRI identity
was ignored for the two ontologies whose local-name projection is
non-injective. The frozen v1 table remains available for provenance, but its
correctness totals are superseded.

### Automatic versus explicit KM routes

Plain `km classify ONTOLOGY` is equivalent to `--route auto`. In the latest
completed, source-bound 592-ontology sweep it produces 585 operational
completions, of which 583 match the retained Konclude full-IRI signatures
exactly. The two other completions are contested consistency cases rather than
accepted exact matches.

The complete 180-task residual route panel found one additional exact explicit
route: `certified_card_proxy_abox` solves `ore_ont_7499.owl` in 87.2187 seconds
at 1029.11 MiB. That route deliberately drops an uncertified ABox and therefore
remains explicit; an exact result on this ontology does not establish a general
automatic-routing certificate.

The current automatic source also selects `nominal_ni_tbox` for
`ore_ont_10702.owl`. Focused IBEX job 49676814 confirms an exact signature in
2.2885 seconds at 21.72 MiB. The complete no-regression sweep is job 49676527,
with dependency-bound audit job 49676902. These pending results are not folded
into the completed 583-match total.

Five ontologies lack a validated answer from any current route: `1194`, `4669`,
`9540`, `10621`, and `10860`. The eight rows previously reported as unknown
(`443`, `3524`, `6720`, `7052`, `8941`, `13912`, `15288`, and `15703`) are
validated by schema v2 without rerunning a reasoner. Route `9540` times out,
and the old `10621` `ht_bridge` recipe is rejected by the frozen current
revision. These are the two accepted historical mechanisms that still need to
be restored in the current binary.

For `4669`, old KM executions terminated but their taxonomies are unsound: 64
named classes claimed unsatisfiable have independent satisfiable witnesses.
Logical completeness of those old taxonomies is unknown. Current KM defers and
returns no taxonomy. Source-built Konclude also fails to solve 4669, timing out
at both 240 seconds and 3,600 seconds without an answer. See the
[Konclude source trace and runtime verification](docs/ORE-4669-KONCLUDE-VERIFICATION.md).
`10860` contains unsupported DL-safe rule atoms and lacks authoritative full
gold; `1194` has no validated route within the standard resource limits.

The earlier 28-procedure matrix remains in
[`results/benchmarks/2026-07-16-routing-complete592/`](results/benchmarks/2026-07-16-routing-complete592/),
and disputed references are documented in
[`docs/CONTESTED-GOLD.md`](docs/CONTESTED-GOLD.md).

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
mvn package   # -> target/kobayashi-marust-protege-0.3.0.jar
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
  inference methods return no inferred results. The native explanation JSON
  protocol is available, but the current plugin has no explanation UI.

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
