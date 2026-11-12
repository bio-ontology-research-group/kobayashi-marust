# KM 1.6.2 release notes

Released 2026-11-13 from commit COMMIT (tag `v1.6.2`).

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

FC-TABLE

## Speed and correctness (Ibex, same day)

S1-TABLE

## Certification

CERT-TEXT

## Not in this release

Checking km's own clause stream (phase B of
`docs/V1.6.2-FRONTEND-PLAN.md`) and reference procedures for inverses,
role hierarchies with ALC constructors, transitivity and role chains move
to v1.6.3 (`docs/V1.6.3-HT-PLAN.md`).

## Assets

`km-v1.6.2-linux-x86_64` (PGO, GLIBC at most 2.34),
`km-v1.6.2-certified-source.tar.gz`, `kobayashi-marust-protege-1.6.2.jar`,
`BENCHMARKS.md`, `build-completion.json`, `certification-ibex.json`,
`SHA256SUMS`.
