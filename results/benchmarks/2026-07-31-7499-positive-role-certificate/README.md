# Certified positive-role ABox route for ORE 7499

This directory records the candidate that makes the existing
`certified_card_proxy_abox` route complete-answer-or-defer and gives it the
exact nominal CB fallback. The candidate is not counted in the production
default total until a source-bound IBEX gate and complete 592-ontology sweep
pass.

## Certificate contract

The source profile may propose the route when its first-class cardinality roles
are separated from inverse and non-simple role components. The normalized
worker input then independently checks all of the following before the
cardinality arm can publish a TBox taxonomy:

- the native ABox is complete, nonempty, and contains only positive object-role
  assertions;
- every individual has exactly one normalized positive class assertion;
- no asserted-role closure intersects a first-class number role;
- every normalized clause triggered by the asserted-role closure is a positive,
  range-restricted, two-variable Horn clause;
- disjunction, negative concepts, equality, existential heads, inequality, and
  negative role assertions fail closed;
- the exact cardinality taxonomy says every asserted class is satisfiable;
- concrete role and role-chain closure over the named ABox introduces no public
  class type that was not already entailed by that individual's asserted class.

Internal `__chain__*` and `__trans__*` concepts are treated as normalized
role-automaton state and closed over the concrete ABox graph. The worker queries
those internal concepts for certificate checking, then removes them before the
public classification result is converted back to full IRIs.

If any structural or taxonomy check fails, the cardinality worker produces no
answer. The route now sets `KM_NOMINALS=1`, so its concurrent CB arm retains the
complete singleton and ABox encoding and remains the authoritative fallback.
A source-profile false positive can therefore affect scheduling but cannot
change the answer.

This changes orchestration and result admission, not the CB calculus. It does
not require Lean re-certification.

## Local evidence

The workstation release command was:

```text
/usr/bin/time -v timeout 150s env KM_TIMING=1 \
  target/release/km classify --route certified_card_proxy_abox \
  /tmp/ore_ont_7499.owl
```

Result:

- exit 0;
- 96.84 seconds wall;
- 1,010,812 KiB process-tree peak RSS;
- 4,841 public subclass keys;
- output SHA-256
  `97b34a2790a442c2fe55274359fe1e46ddbc6141d62c255c690743cbc801bff2`;
- byte-identical to the retained exact `7499` output with the same SHA-256.

Repeating the route with `KM_NOMINALS=1` explicitly also exited 0 in 97.14
seconds, used 983,116 KiB peak RSS, and was byte-identical to the retained exact
output.

After making the route automatic and adding the exact nominal fallback, plain
`km classify` exited 0 in 97.25 seconds at 2,330,372 KiB process-tree peak RSS.
Its output remained byte-identical with SHA-256
`97b34a2790a442c2fe55274359fe1e46ddbc6141d62c255c690743cbc801bff2`.

The preserved worker payload completed independently in 53.94 seconds and
21,740 KiB RSS. The Rust certificate accepted its exact taxonomy in 1.69
seconds before the indexed role-chain join was added; the end-to-end indexed
verifier completed between the worker exit at 96.08 seconds and final output at
96.79 seconds.

## Tests

The permanent certificate test covers:

- positive role implication and domain/range consequences;
- an internal transitivity marker followed by a public consequence;
- rejection when the required public taxonomy entailment is absent;
- rejection when an asserted class is unsatisfiable;
- rejection of equality-generating role constraints.

The complete serial release suite passed:

```text
test result: ok. 1827 passed; 0 failed; 8 ignored
```

All CLI and integration test targets also passed with one test thread. A
parallel library run exposed four pre-existing process-global environment races;
each passed alone, and the complete serial run is the authoritative result.

The corrected automatic composition was followed by another complete serial
all-target run: 1,827 library tests and every integration target passed, with 0
failures and 8 ignored library tests.

## First source-bound IBEX gate

Commit `9462131` was archived as
`125101f90a18f66e280976a667ae571c36b4c2b503750fb636bab7ffcb64c7fc`.
Build job `49700575` compiled it on `gpu510-32` in 3m50s, passed the smoke
classification, and published binary SHA-256
`d6ef417e3e2c5bae5a9cac4377c68311c0120d81ee58557759e9c7f086687ddf`.

Focused array `49700588` used a deliberately constrained four-CPU allocation.
Controls 33, 10702, 6934, and 9540 all completed with exact full-IRI matches.
Ontology 7499 timed out at 240.0304 seconds and 659.94 MiB. This was a
scheduling failure: the exact nominal fallback saturated the cpuset while the
serial card worker retained the route's default positive nice value.

The corrected candidate sets `KM_HT_NICE=0` and projects only the card worker's
private clause view back to the TBox. The shared clause file still contains all
ground ABox clauses for the exact CB fallback. This scheduling/view correction
does not change either procedure's derivations. A second source-bound IBEX gate
is required before the production total changes.

## Corrected source-bound IBEX gate

Commit `ebe56bd` was archived as
`108e9996997cfda6109e7bc61dcf7287a219c6263fd3782ab1957439f2e28616`.
Build job `49700800` completed on `gpu510-32` in 3m45s, passed its smoke test,
and published binary SHA-256
`c6f3e01c67421f3ae97c5edadf59a10befea361385dcdd0912dcbb9e762f9317`.

Focused array `49701005` passed all five automatic-route cases with exact
full-IRI matches: 7499, 33, 10702, 6934, and 9540. The 7499 production row was:

- 77.1015 seconds wall;
- 951.91 MiB peak RSS;
- zero missing and zero extra subsumptions;
- zero missing and zero extra unsatisfiable classes;
- full-IRI verdict `match`;
- signature SHA-256
  `f82850c6582131358cd9ecc108888e2131734900cf687d055a7a7c0f4fece17d`.

The complete resumable 592-ontology automatic sweep is array `49701329` under
the same 240-second, 20-GiB reasoner contract. Its results remain pending and
the production headline stays at the completed v16 count until all rows and the
correctness comparison pass.

## Pending production gate

1. Build this exact committed source revision on an IBEX compute node.
2. Run `7499` plus exact controls under the 240-second and 20-GiB production
   limits.
3. Verify full-IRI identity and route selection.
4. Run and audit all 592 default `km classify` inputs.
