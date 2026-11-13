# KM 1.6.2 release notes

Released 2026-11-13 from commit f3af7658 (tag `v1.6.2`).

## What changes

KM 1.6.2 proves the frontend of the reference procedures: from the OWL 2
functional syntax text to an answer that is exact under the OWL 2 direct
semantics, for OWL EL and OWL ALC. km's own answers on those inputs can be
checked against it. No theorem of v1.6.0 or v1.6.1 changes; the acceptance
contract is `docs/V1.6.2-ACCEPTANCE.md`.

- **OWL semantics and parser in Lean.** `OWL/Semantics.lean` defines OWL 2
  class expressions, axioms and their direct semantics; `OWL/Parse.lean`
  parses the functional syntax with prefix expansion. On the 499 suite
  inputs of the fragment it reads the same axioms as km's Rust parser.
- **Translations with proofs.** `translateEL` and `translateALC` turn an
  OWL ontology into the normal forms the v1.6.0 reference procedures
  decide, with one fresh name per occurrence of a complex expression
  (polarity definers). `translateEL_correct` and `translateALC_correct`
  show that subsumption between named classes is the same before and
  after.
- **The capstone.** `owlReference_sound`: every answer the OWL reference
  procedure publishes is exact for `OWL.EntailsSub`.
  `owlReference_complete`: on every OWL EL and OWL ALC ontology it
  publishes. Inconsistency and unsatisfiable classes are read from two
  fresh probe names (`inconsistent_iff_entailsSub_fresh`,
  `unsatisfiable_iff_entailsSub_fresh`), and `owlReadout_exact` covers
  what the executable prints.
- **`km-owl-reference`.** The executable of the capstone (output format
  `owl-sparse-v1`, exit codes as `km-el-reference`). It declines ALC
  inputs with more than 16 concept names after translation, because type
  elimination is exponential in that number; this is a decline, never a
  wrong answer.
- **`KM_FRONTEND_CHECK=1`.** `km classify` compares its answer with
  `km-owl-reference` (inconsistency, unsatisfiable classes, subsumptions
  between satisfiable classes). Agreement makes km's answer exact under the
  direct semantics of its input text; disagreement fails closed with exit
  6. Off by default.
- **IRI identity in the Rust parser.** An abbreviated IRI `p:x` and its
  expansion now denote one entity, builtins and datatypes are recognised
  by their expanded IRI, and malformed input gives a parse error (exit 2)
  instead of a panic. Inputs that spell each entity one way give the same
  answer as before.

## Coverage on the suite

With `KM_FRONTEND_CHECK=1` on the 1,781-input checkers-on suite (Ibex):

| outcome | inputs |
|---|---:|
| agreed with the OWL EL reference | 389 |
| agreed with the OWL ALC reference | 2 |
| disagreed | **0** |
| declined: a construct outside `F` | 1,270 |
| declined: in `F`, neither OWL EL nor OWL ALC (the v1.6.3 fragment) | 84 |
| declined: over the ALC budget of 16 concept names | 25 |
| no check: km itself timed out or failed | 11 |

The ALC budget declines have 18 to 829,082 concept names after
translation; the v1.6.3 plan replaces type elimination for that reason.

## Speed and correctness (Ibex, same day)

| | v1.6.2 | v1.5.3 same day | Konclude same day |
|---|---:|---:|---:|
| held-out inputs verified (of 585) | 576 | 560 | 576 |
| mean wall-time ratio against v1.5.3 (bound 1.10) | 0.957 | 1 | |
| median wall-time ratio against v1.5.3 (bound 1.10) | **1.183** | 1 | |
| median wall time on the 573 inputs v1.6.2 and Konclude both verify | 0.244 s | | 0.200 s |

No wrong answer on the held-out half or on the 1,708-input pool (1,686
verified). `KM_FRONTEND_CHECK` is off by default, so these numbers measure
the production routes.

**Exception.** The median clause and the clause "more held-out inputs
than Konclude" are not met in the record run, and the maintainer accepted
the release with both recorded. Three Ibex runs of the same binaries gave
medians 1.142, 1.306 and 1.183; in the record run each chunk ran for both
binaries on the same node, and chunks still ranged from 0.97 to 1.42. On
the workstation, interleaved on 40 median-range inputs, v1.6.2 against
v1.5.3 has a median per-input ratio of 1.002 (0.4 ms) and is level with
v1.6.1. The Konclude tie comes from ore_ont_7557, which timed out at 240 s
in the record run and took 197 s in both earlier runs (577 against 576
there). Details: `docs/V1.6.2-ACCEPTANCE.md`.

## Certification

On Ibex from the tag (`tools/release/v160-ibex/`): PGO build (22 of 22
training answers verified), five Lean gates (653 tests, including the OWL
frontend theorems and `km-owl-reference`; no `sorryAx`), full Rust suite
(95 cargo commands, 3,656 passed, 0 failed), Java plugin (76 tests),
checker step (57 checker tests; checkers-on suite, 0 rejected, 0 answers
changed).

## Not in this release

Checking km's own clause stream (phase B of
`docs/V1.6.2-FRONTEND-PLAN.md`) and reference procedures for inverses,
role hierarchies with ALC constructors, transitivity and role chains move
to v1.6.3 (`docs/V1.6.3-HT-PLAN.md`).

## Assets

`km-v1.6.2-linux-x86_64` (PGO, GLIBC at most 2.34),
`km-v1.6.2-certified-source.tar.gz`, `kobayashi-marust-protege-1.6.2.jar`,
`BENCHMARKS.md`, `build-completion.json` (generated before the exception:
S1 `NOT_MET`, C1 `met`; L1 and R1 show `pending`, their evidence is
`certification-ibex.json`), `certification-ibex.json`, `SHA256SUMS`.

## Records

`docs/V1.6.2-ACCEPTANCE.md`, `results/agents/2026-11-12/v162-rc1-frontend-check/`,
`results/agents/2026-11-13/v162-s1-ws-bench/`, `docs/V1.6.3-HT-PLAN.md`
(next release).
