# Streamed flat reachability and inert disjointness

This candidate removes the memory failure that previously excluded ORE868
from the proved direct flat-NF1 route. `GroupedJsonTaxonomy` may now retain the
acyclic NF1 graph rather than its complete transitive closure. JSON
serialization computes and emits one subject's sorted reachable superclasses
at a time, using one generation-stamped visited array. This changes only the
representation and schedule of the already-proved graph closure.

The source recognizer also accepts normalized pairwise disjointness and checks
the executable premise of `flatNF1Disjoint_sub_iff_flatReach`: no named source
may reach both operands. `flatNF1Disjoint_has_model` proves consistency for the
accepted source shape. Active disjointness declines before publication and
uses the unchanged complete route.

Focused tests cover byte-identical streamed JSON, inert acceptance, active
decline, and the existing fail-closed flat grammar. ORE868 is the target;
ORE10689 checks the ordinary flat route and ORE1559 checks whether a second
disjoint source is admitted or safely declined by the semantic inertness test.
Exact retained signatures, route traces, binary identity, and
checkpoints are mandatory before any timing claim.

`audit_functional_sweep.py` counts terminal records separately from their
checkpoint copies and fails closed on missing or non-identical checkpoints,
malformed JSON, duplicate ontology records, incomplete successful profiles,
or a binary-identity mismatch. Use it for progress reports and again before
aggregation; raw `*.json` counts are intentionally not valid progress evidence.

`compare_v1_semantics.py` independently joins terminal rows to the immutable
v1.0.0 ledger and requires byte-identical signature hashes for every pair of
successful classifications. Its final `--require-complete` invocation covers
592/592 rows and reports zero semantic errors. ORE3215 is explicitly not
treated as a completion: its AMD-node timeout still requires the Gold-6248
restoration gate.

Isolated build job `50847002` completed with exit code zero. Its 886-file
source manifest hashes to `32d0f42cc9d7...`; all ten flat-route tests and the
separate streamed-JSON identity test pass in release mode. The installed
binary SHA-256 is `ae629a04cbe37cf3a75e39946125d9a09d66876d07ef1bfceb7cef8a734c35a6`.
Dependent functional array `50847003` is the authoritative first ontology
gate. Residual-shape audit `50847038` completed under
Slurm and found that ORE11395 is another exact source-shape match: 11,232
named NF1 edges, 641,123 existential leaves, and six positive transitivity
axioms. ORE3836 has the same admitted family and already selected `flat_nf1`
exactly in the medium-route control. Dependent array `50847099` checks both
against their retained signatures with the streamed representation. The audit
also confirms that ORE6233 contains 176,043 class assertions; it must decline
this route and is handled only by the separately proved ABox-elision gate.

`50847099_0` confirms the newly identified ORE11395 case: it selects
`flat_nf1`, matches retained full-IRI signature `5f730ffc22a0...`, and records
1.7176 seconds with 113.29 MiB peak RSS. The retained v0.2.36 ELC record is
22.5575 seconds and 1,304.96 MiB, a functional reduction of 20.8399 seconds
and 1,191.67 MiB. This run uses the pinned streamed binary and a terminal
checkpoint.

`50847099_1` also confirms ORE3836 with the streamed representation: exact
signature `203f79d8a6f...`, 2.9739 seconds, and 19.30 MiB peak RSS. Its retained
ELC record is 12.9114 seconds and 1,813.54 MiB, yielding another 9.9375 seconds
and 1,794.24 MiB of functional savings. Both newly audited shape matches are
therefore complete and exact.

The decisive ORE868 record `50847003_0` passes every functional gate. It
selects `flat_nf1`, matches retained signature `be6be6663ffd...`, and completes
in 4.8241 seconds with 268.96 MiB process-tree peak RSS. The retained v0.2.36
ELC record is 29.4332 seconds and 1,642.41 MiB, so the streamed route saves
24.6091 seconds and 1,373.45 MiB. It is also below the 12.6636-second fastest
external wall target and the 5,871.01-MiB fastest external memory target for
this ontology. The record is checkpointed and identifies the pinned candidate
binary.

Because the functional evidence is decisively positive, order-balanced,
same-node Gold-6248 array `50847199` compares immutable v1 and the pinned
candidate twice each on ORE868, ORE11395, and ORE3836. It is the binding
performance gate; the unconstrained rows establish exactness and effect size
but not release-quality timing.

Supplemental Gold array `50847292` adds the same two order-balanced ORE1559
pairs discovered by the completed functional panel.

The ordinary flat control ORE10689 also passes with the streamed graph:
4.6777 seconds, 269.05 MiB, route `flat_nf1`, and exact retained signature
`be6be6663ffd...`. The retained ELC row is 30.7278 seconds and 1,642.46 MiB.
Streaming therefore preserves the established direct-route speed while
reducing this functional record by roughly 131 MiB relative to the earlier
materialized direct implementation.

ORE1559's two disjoint pairs also pass the inertness condition, so
`50847003_2` safely selects `flat_nf1` rather than declining. It matches exact
signature `a1ad6c7eedab...` in 3.8132 seconds at 74.55 MiB. The retained ELC
record is 25.8006 seconds and 2,644.40 MiB, adding 21.9874 seconds and 2,569.85
MiB of functional savings. This also beats the fastest external wall and
memory targets for ORE1559, 18.8857 seconds and 3,884.16 MiB. The complete
five-ontology functional panel is exact and checkpointed throughout.

Full hardware-unconstrained validation uses the pinned combined candidate on
all 592 ORE inputs. It uses the established strict per-ontology harness,
terminal checkpoints, exact retained-gold comparisons, and automatic route
capture. This sweep can reject semantic or aggregate regressions early; it
cannot replace the final Gold-6248 release measurement.

The first submission, array `50847252`, was cancelled after its first thirteen tasks failed
before classification. The inherited release template correctly detected a
missing ontology list and non-Gold CPU models; it produced zero result rows.
The replacement copies the complete retained harness, removes only the CPU
model restriction for this explicitly functional sweep, and must pass a
single-task smoke before tasks 1–591 are submitted.

Smoke job `50847322` completed ORE33 and passed all release-harness checks. It
used binary `ae629a04cbe37cf3...`, selected `production_all`, produced a terminal
checkpoint byte-identical to its result record, and matched the retained
Konclude signature with zero missing or extra subsumptions and no consistency
mismatch. Its route profile is complete. The measured record is 0.2508 seconds
and 33.98 MiB on an Intel Xeon Gold 6248 node. After this smoke gate passed,
array `50847358` submitted tasks 1–591 with a 40-task concurrency cap.

The strict auditor reports 592 distinct terminal/checkpoint pairs with zero
integrity errors: 590 are `status=ok`, ORE1194 is `status=error`, and
ORE3215 timed out on an AMD EPYC 7702 node. Of the successful rows, 587 match
retained full-IRI gold, ORE2669 and ORE15516 have their expected independently
adjudicated consistency mismatches with Konclude, and ORE10860 has no usable
Konclude gold.
ORE1194 is the sole non-success in the immutable v1.0.0 baseline as well: both
select `nominals` and terminate near the 18-GiB worker limit. ORE3215 is a
hardware-dependent performance result rather than a semantic difference and
must be restored by its Gold-6248 release gate. The final correctness audit
must preserve all 591 empirically correct v1.0.0 answers; any additional
semantic failure rejects the candidate.

A census of retained source profiles found seven further large pure
named-subclass inputs in the same proved flat fragment as ORE10689: ORE3524,
8486, 9674, 11739, 13355, 14459, and 16008. Their eight immutable v1 rows total
165.6318 wall-seconds. Targeted array `50847519` fast-tracks their exact route
and signature checks; the full array will resume from any resulting terminal
checkpoints.
