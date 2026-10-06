# Exact relation indexes for finite-model verification

The SWRL worker diagnostic 53328863 completed both 3726 and 7278 with independent
taxonomy and consistency agreement. Both runs took about 102 seconds. The
worker traces show two tableau expansions, no search branches, a 283-element
live interpretation, and 10,258 converted clauses. Progress snapshots exposed
the long converted-clause verification phase.

The verifier previously scanned a role's entire live edge relation whenever a
partial universal assignment constrained either endpoint. The candidate builds
immutable indexes over exactly those live edges: outgoing and incoming
neighbours, source and target projections, and the diagonal. Bound endpoints
select adjacency indexes; unbound endpoints select projections; a repeated
variable selects the diagonal. An absent role or endpoint yields the empty set.

This preserves the exact permitted node set for each role premise. The
intersection with the other premises and the sorted unary domain is unchanged,
as are recursive enumeration, budget charging, head evaluation, and all source
checks. No rule, clause, model obligation, or verification step is dropped.
The change affects neither calculus derivations nor reasoning schedules.

The focused suite passed 15 tests. The new index test checks all 512 directed
three-node relations against the original scan, with both endpoint directions,
bound and unbound neighbours, self-edges, absent roles, and missing nodes. The
existing exhaustive two-object interpretation test independently checks full
verifier results for positive/negative classes, roles, equality, and existential
heads and premises. All four certification gates passed without `sorryAx`
against the pinned candidate source. All 624 source hashes and the four gate
log hashes were rechecked after completion.

The paired diagnostic uses the original ontologies, the certified-source
baseline binary, and the candidate binary, with two repetitions in reversed
order. Limits remain 240 seconds, 20 GiB, and one CPU. Completed answers require
independent audit.

Job 53329150 completed all eight measurements and all eight answers passed
independent consistency and taxonomy checks:

| Ontology | Baseline seconds, repetitions 1 / 2 | Indexed seconds, repetitions 1 / 2 |
|---|---:|---:|
| 3726 | 104.957 / 103.340 | 18.199 / 19.130 |
| 7278 | 102.656 / 101.664 | 18.010 / 17.966 |

This is about an 82% end-to-end reduction on both diagnosed cases. Full-corpus
job 53329459 now tests the pinned binary over all 1,920 unchanged inputs with
the existing admission, limits, and independent auditing. Its inventory binds
the completed certification receipt. This two-case result does not satisfy
the v1.5.0 release conditions, and no release is approved.
