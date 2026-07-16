# Kobayashi-MaRust

**A sound disjunctive context reasoner for SROIQ / OWL 2 DL — with machine-checked soundness in Lean 4.**

[![CI](https://github.com/bio-ontology-research-group/kobayashi-marust/actions/workflows/ci.yml/badge.svg)](https://github.com/bio-ontology-research-group/kobayashi-marust/actions/workflows/ci.yml)
[![License: BSD-3-Clause](https://img.shields.io/badge/License-BSD--3--Clause-blue.svg)](LICENSE)
[![Rust](https://img.shields.io/badge/engine-Rust-orange.svg)](engine)
[![Lean 4](https://img.shields.io/badge/proofs-Lean%204-brightgreen.svg)](lean)
[![Proof axioms](https://img.shields.io/badge/proof%20axioms-propext%2C%20Quot.sound-success.svg)](lean)

Kobayashi-MaRust is a consequence-based ("context") reasoner for the description
logic **SROIQ** — the logic behind **OWL 2 DL** — built on the disjunctive
context calculus of Tena-Cucala, Cuenca Grau and Horrocks (the core of the
[Sequoia](https://github.com/andrewdbate/Sequoia) reasoner). What makes it
unusual is *what is proved about it*:

- the **soundness of the calculus** is proved in **Lean 4**, kernel-checked, with
  no `sorry` (axioms: `propext` only); and
- **every verdict the actual compiled reasoner emits is re-checked by the Lean
  kernel, per run**, by an independent verified certificate checker — so a green
  build is a machine-checked guarantee that the reasoner's output is a genuine
  logical consequence, not merely that *some* idealised algorithm is correct.

To our knowledge this combination — a running DL reasoner whose outputs are
kernel-certified against a formally verified calculus — is uncommon among
description-logic reasoners.

> *Why the name?* SROIQ subsumption is a worst-case-intractable test
> (N2ExpTime-complete). Rather than fight the no-win scenario head-on, this line
> of work **changes the conditions of the test**: it compiles the ontology's
> symbolic structure into a tractable arithmetic circuit for differentiable
> weighted model counting. Kobayashi Maru, in Rust.

---

## Highlights

- **Sound on the full disjunctive fragment.** Disjunction (`⊔`), conjunction,
  full negation, existentials/universals, role hierarchy, inverse & symmetric
  roles, **number restrictions** (`≥n R.C`, `≤n R.C`), **nominals** (`{a}`), and
  **transitive roles / role chains** (`R∘S⊑T`). An earlier Horn-only prototype was
  unsound on the disjunction × existential interaction; this calculus is not.
- **Soundness proved in Lean 4** (`resolution_sound`, `derivable_sound`,
  `subsumption_sound`, `unsat_sound`, `paramodulation_sound`).
- **Completeness proved** for the foundational fragments by the four constructions
  the calculus combines (propositional resolution; consequence-based EL; the
  disjunctive-ALC filtration / good-type model; the equality-quotient Herbrand
  model for merging features), plus **blocking termination** and
  **optimised-saturation ≡ ground-resolution**.
- **Per-run verified validation.** A Lean-verified certificate checker
  re-derives and kernel-checks **45 verdicts** from real engine runs — disjunctive
  subsumption, disjointness, number-restriction clashes, paramodulation,
  disjunction-over-a-successor, nested successors `f(g(x))`, and nominals —
  matching the **HermiT** oracle exactly (e.g. `kinship` 21/21).
- **Parallel classification.** Each named concept is classified by an
  independent context saturation, so classification is embarrassingly parallel:
  the engine splits the named concepts across cores (`rayon`) and merges the
  results, producing output **identical** to the sequential run (the verified
  saturation core is unchanged). On a 2300-class ontology this is a ~50×
  speed-up on 16 cores. Set `KM_THREADS=1` to force sequential.
- **Tiny, dependency-light.** The engine is ~1k lines of Rust with only `serde`
  and `rayon`; the proofs are Lean 4 + mathlib.

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

For end-to-end OWL functional-syntax classification, use the multi-call binary:

```sh
./target/release/km classify ontology.ofn
./target/release/km profile ontology.ofn
./target/release/km routes
```

`km classify` profiles the ontology and selects its measured procedure by
default. `--route NAME` selects any named procedure; `--route manual` preserves
individually supplied `KM_*` options. See [`docs/ROUTING.md`](docs/ROUTING.md)
for the exact expressivity calculation, statistics schema, option bundles, and
decision-tree validation.

### 2. Check the proofs

```sh
cd lean
lake exe cache get      # fetch prebuilt mathlib oleans
lake build              # kernel-checks the calculus proofs AND all 45 validation theorems
```

### 3. Reproduce the end-to-end validation

```sh
bash validation/run.sh  # build engine -> re-derive every verdict -> kernel-check
```

This runs the real engine, independently re-derives each reported verdict from
the genuine premises (engine output is **never** assumed as an axiom), and has
the Lean kernel re-check every certificate. A green run prints
`OK: every reasoner verdict above is a kernel-checked theorem.`

---

## What is proved

All Lean theorems are `sorry`-free and reduce to `[propext, Quot.sound]` (the
soundness core needs only `propext`). See [`lean/README.md`](lean/README.md) for
the full account.

| Property | Statement | File |
|---|---|---|
| Calculus soundness | every derived clause is entailed; subsumption/⊥/paramodulation sound | `ContextCalculus/Basic.lean` |
| Completeness — disjunction | refutational completeness of propositional resolution | `CompletenessProp.lean` |
| Completeness — existentials | canonical-model completeness for consequence-based EL | `CompletenessEL.lean` |
| Completeness — disjunction × ∃ | finite filtration / good-type model for disjunctive ALC | `CompletenessContext.lean` |
| Completeness — merging | equality-quotient Herbrand model (`≤n R.C`, nominals, inverses) | `CompletenessEq.lean` |
| Termination | blocking ⇒ finite saturation (König) | `Termination.lean` |
| Saturation ≡ resolution | engine saturation refutes iff ground resolution does | `Equivalence.lean` |
| Verified checker | accepted certificate ⇒ verdict entailed | `Checker.lean`, `CheckerFO.lean`, `CheckerTerm.lean` |

### Per-run validation (45 kernel-checked verdicts)

The `Validation` library turns real engine runs into theorems proved `by decide`:

| input | what it exercises |
|---|---|
| `disj`, `disjoint`, `hierarchy` | disjunctive subsumption, `⊥` clash, class hierarchy |
| `exists` | `∃R` / value restriction (Succ) |
| `numrestr` | number restrictions (`≥2 R.C ⊓ ≤1 R.C ⊑ ⊥`) |
| `paramod` | paramodulation into a literal (superposition) |
| `disjsucc` | disjunction over a successor (only the complete disjunctive engine derives it) |
| `trans_test.ofn` | transitive role, incl. nested successor `A ⊑ D` via `f(g(x))` |
| `kinship.ofn` | all **21** subsumptions, incl. the nominal `Queen ≡ {Elizabeth}` |

The certified verdict set equals the HermiT oracle's on every benchmark.

---

## Repository layout

```
engine/        Rust reasoner (the `kobayashi-marust` binary) + Python tooling
  src/                 calculus, clause/term representation, saturation engine, JSON I/O
  py/                  certificate generators, the .ofn front-end, HermiT adapter
lean/          Lean 4 formalisation
  ContextCalculus/     soundness, completeness, termination, the verified checkers
  Validation/          auto-generated, kernel-checked per-run verdicts
validation/    end-to-end driver (run.sh) + normalised JSON inputs
oracle/        HermiT cross-check (scripts, reference results, ontologies)
examples/      example OWL ontologies (.ofn)
protege/       Protege reasoner plugin (Maven; OSGi bundle)
```

## Protege plugin

`protege/` is a [Protege](https://protege.stanford.edu/) **reasoner plugin**:
Kobayashi-MaRust appears in the *Reasoner* menu and computes the inferred class
hierarchy and unsatisfiable classes. It is a thin OWL API `OWLReasoner` that
serialises the ontology and calls `engine/py/owl_classify.py` (the real moose
normalisation + the Rust engine), then maps the named-class subsumptions back
into Protege.

```sh
cd protege
mvn -DskipTests package   # -> target/kobayashi-marust-protege-0.1.0.jar  (drop into Protege plugins/)
mvn test                  # headless OWL-API tests (disjunction; kinship.ofn vs HermiT)
```

Runtime needs Python 3 + `moose` + the built engine (see `protege/README.md`).

---

## The calculus, briefly

Each named concept `A` seeds a **root context** with core `{A(x)}`; anonymous
successors live in **successor contexts**. Context clauses `Γ → Δ` (a body
conjunction of predicates implying a head disjunction of literals) are derived by
the rules **Core / Hyper / Pred / Succ / Eq / Ineq / Elim**. Every rule is, model-
theoretically, a clausal resolution or paramodulation step — which is exactly
what the Lean soundness proof formalises. Terms are integer-encoded as in Sequoia
(`x=0`, `y=-1`, `z_i=-(i+1)`, `f_i(x)=+i`). The engine uses a *pay-as-you-go*
expansion strategy — **one successor context per function symbol `f`** rather
than the trivial strategy's single shared empty-core context for all anonymous
successors. Both are sound and complete; partitioning per `f` keeps each
existential's successors out of one another's context, which avoids the
shared-context blow-up that the trivial strategy suffers under disjunction
(≈45× faster on a distinct-skolem disjunction×existential stress test, with
byte-identical verdicts).

**References**

- Horrocks, Kutz, Sattler. *The Even More Irresistible SROIQ.* KR 2006.
- Motik, Shearer, Horrocks. *Hypertableau reasoning for description logics.* JAIR 2009.
- Tena-Cucala, Cuenca Grau, Horrocks. *Consequence-based reasoning for description
  logics with disjunction, inverse roles, number restrictions, and nominals.* (Sequoia.)

---

## Scope and honest limitations

- **Soundness is the headline guarantee** (proved + kernel-certified per run).
  Completeness is proved for the foundational fragments above and validated
  empirically against HermiT on the benchmarks. The engine classifies by
  consequence-based *type-elimination* (and uses a *pay-as-you-go* representation:
  one successor context per function symbol). Its strategy completeness is now
  **machine-checked, `sorry`-free**, in `lean/ContextCalculus/CompletenessStrategy.lean`
  (imported by the root module, so it is part of the default certified build):
  `saturate_decides` proves that iterating the elimination operator from the
  consistent candidates converges (in ≤ `|candidates|` rounds) to exactly the
  good types, which decide `A ⊑ B` via `subsumption_complete`. `engine_complete`
  carries this through with **no residual hypothesis**: the engine's pre-elimination
  candidate space, at the type level, is all consistent types `cand` (its disjunctive
  clauses represent that whole space), and `goodFS ⊆ cand` is immediate, so the
  `coverage` hypothesis of the general `engine_decides` is discharged. The single
  remaining gap is then *not* coverage but the **representation refinement**: the
  engine manipulates disjunctive context clauses rather than enumerated types, and
  that its clause saturation computes the same `goodFS` is the disjunctive-saturation
  completeness. That clause engine's soundness is hypothesis-free and kernel-certified
  per run (the checker); its completeness is validated empirically against HermiT
  (byte-identical verdicts). Mechanising clause-level completeness is the remaining
  substantial theorem and is not claimed.
- The per-run certificate search re-derives verdicts by a complete layered method
  (propositional, Horn forward chaining, and a complete disjunctive saturation
  over a term algebra); the disjunctive layer is bounded, so an ontology with very
  many excluded-middle definitions may exceed the bound.
- Still open in the engine: the general regular-role-hierarchy automaton (only
  transitivity and single chains are encoded). The Table-3 nominal rules are
  implemented and certified in `lean/ContextCalculus/Nominals.lean`. The
  pay-as-you-go strategy is implemented (per-`f` successor contexts) and
  its type-level completeness is machine-checked with no residual hypothesis
  (`engine_complete`). The sole remaining obligation is the clause-level
  disjunctive-saturation completeness (the engine works on disjunctive context
  clauses, not enumerated types) — soundness-certified per run and HermiT-validated,
  but not yet mechanised.

## The `.ofn` front-end (optional)

The OWL functional-syntax front-end (`engine/py/frontend.py`) reuses the separate
[`moose`](https://github.com/bio-ontology-research-group) package for SROIQ
normalisation. It is needed **only to regenerate** `.ofn`-sourced certificates;
the engine and all checked-in proofs need no moose. Point to it with
`MOOSE_HOME=/path/to/moose` or place `moose` beside this repository.

## License & citation

BSD-3-Clause (see [LICENSE](LICENSE)). If you use Kobayashi-MaRust, please cite it
via [CITATION.cff](CITATION.cff).

## Acknowledgements

Built in the [Bio-Ontology Research Group](https://github.com/bio-ontology-research-group)
at KAUST. The calculus follows Tena-Cucala, Cuenca Grau and Horrocks and the
Sequoia reasoner; HermiT is used as the validation oracle.
