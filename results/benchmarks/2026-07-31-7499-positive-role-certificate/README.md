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

## Pending production gate

1. Build this exact committed source revision on an IBEX compute node.
2. Run `7499` plus exact controls under the 240-second and 20-GiB production
   limits.
3. Verify full-IRI identity and route selection.
4. Run and audit all 592 default `km classify` inputs.
