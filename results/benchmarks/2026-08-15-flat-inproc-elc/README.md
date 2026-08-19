# Small flat exact-EL in-process handoff

This cumulative candidate starts from the unreleased, semantically clean V3
KPSet label-cache candidate (`ff9c458`) and adds commit `657ce32`. Exact-EL
ontologies under 4 MiB whose logical content is a role- and constructor-free
class hierarchy now call the same ELC implementation in process. The previous
path serialized the frontend clauses, forked the ELC worker, parsed its output,
and then mapped the same taxonomy. Larger flat hierarchies retain the process
boundary that limits allocator high-water during public-output mapping.

The change affects process isolation and serialization only. It does not alter
EL completion rules, routing semantics, the derived fixpoint, or output mapping.
The focused route-gate test passes. The complete serial release suite passes
1,990 library tests with eight ignored tests and all integration tests,
including the issue #3 pigeonhole regression. A parallel test-suite run exposed
an existing environment-variable race in one frontend unit test; the isolated
test and the authoritative serial suite both pass.

## Focused panel

Binary SHA-256:
`632d42cb9a1ac47d9479e37b596a357ca22e9c18222dfb332136192dcb2f5e24`.
IBEX job `50516137` ran 13 eligible median-band ontologies in three alternating
baseline/candidate pairs on exclusive Intel Xeon Gold 6248 nodes. The baseline
uses `KM_NO_INPROC_ELC=1`; the candidate uses the new default handoff. All 39
pairs are byte-identical.

| Metric | Subprocess baseline | In-process candidate | Change |
|---|---:|---:|---:|
| Mean wall (s) | 0.18385 | 0.13128 | -28.59% |
| Median wall (s) | 0.19 | 0.14 | -26.32% |
| Mean peak RSS (MiB) | 28.063 | 28.242 | +0.179 |
| Median peak RSS (MiB) | 29.562 | 29.918 | +0.355 |

## Strict cumulative sweep

Strict sweep `50516163` used the standard 240-second, 20-GiB ORE contract,
one pinned binary hash, Intel Xeon Gold 6248 nodes, atomic terminal rows,
profiles, checkpoints, route traces, and collision-safe full-IRI checks. It
contains exactly 592 unique results, profiles, and checkpoints and no temporary
files. Comparison with v0.2.26 found zero differences in status, verdict,
consistency, selected route, or signature. Both sweeps report 591 successful
classifications and the same sole fail-closed error.

| Metric | v0.2.26 | Cumulative candidate | Change | Improved? |
|---|---:|---:|---:|:---:|
| Mean wall (s) | 3.607746 | 3.587480 | -0.020266 | yes |
| Median wall (s) | 0.1839 | 0.1859 | +0.0020 | no |
| Mean peak RSS (MiB) | 436.3724 | 435.8093 | -0.5630 | yes |
| Median peak RSS (MiB) | 36.16 | 35.54 | -0.62 | yes |

The cumulative candidate improves three metrics but misses median wall by two
milliseconds, so it was not released. `audit-vs-v0.2.26.json` contains the
strict report. The next cumulative experiment routes a four-ontology,
source-certified EL terminology family that currently takes `production_all`
through exact ELC; the family includes ORE10806 near the corpus median and
ORE868 in the expensive tail.

## Intersection-only EL route panel

IBEX job `50516820` compared the cumulative automatic route with explicit exact
ELC on all four source-certified intersection-only terminologies. Two
opposite-order pairs per ontology produced byte-identical public JSON in every
arm. The result also agrees with the retained gold signatures from the strict
sweep.

| Ontology | Automatic wall (s) | Exact ELC wall (s) | Automatic RSS (MiB) | Exact ELC RSS (MiB) |
|---|---:|---:|---:|---:|
| ORE10806 | 0.205 | 0.160 | 35.39 | 26.60 |
| ORE9590 | 0.240 | 0.185 | 39.67 | 30.29 |
| ORE13664 | 1.320 | 0.600 | 123.19 | 73.10 |
| ORE868 | 42.130 | 35.885 | 2,103.11 | 1,642.23 |

The source certificate permits only subclass/equivalence axioms and named
intersections, with no ABox, RBox, object/data property, disjunction, complement,
existential, universal, cardinality, nominal, or datatype constructor. This is
an exact OWL EL fragment; the ELC worker additionally validates the normalized
clauses before publishing.

Strict cumulative sweep `50516916`, binary
`519a892f87f27da0396a8278ae8a81effc7e646f7e42f59d015370e9d26c39bb`,
contains 592 validated rows, profiles, and checkpoints. The four expected route
changes are `production_all` to `elc`; status, verdict, consistency, and every
signature remain identical to v0.2.26.

| Metric | v0.2.26 | Intersection-route candidate | Change | Improved? |
|---|---:|---:|---:|:---:|
| Mean wall (s) | 3.607746 | 3.594156 | -0.013589 | yes |
| Median wall (s) | 0.1839 | 0.1870 | +0.0031 | no |
| Mean peak RSS (MiB) | 436.3724 | 433.3922 | -2.9802 | yes |
| Median peak RSS (MiB) | 36.16 | 36.16 | 0.00 | no |

This candidate was not released. The strict process-tree measurement exposed
the remaining issue: ORE10806 and ORE9590 still used a subprocess ELC handoff,
so their parent and child RSS overlapped. Commit `8a65944` extends the existing
typed in-process handoff only to sub-4-MiB, role-free intersection hierarchies.
The larger ORE13664 and ORE868 controls retain subprocess isolation.

## Small intersection in-process handoff and release gate

Commit `8a65944` keeps typed ELC in process for the two sub-4-MiB intersection
terminologies, ORE10806 and ORE9590. A strict process-tree pair reduced their
wall times from 0.1905 to 0.1592 seconds and from 0.2169 to 0.1584 seconds. Peak
RSS fell from 47.55 to 28.36 MiB and from 48.16 to 31.93 MiB. Both signatures
were identical. ORE13664 and ORE868 retain subprocess isolation.

Independent strict sweep `50517606` contains 592 terminal results, profiles,
and checkpoints, with no temporary files. It reports zero semantic differences
from v0.2.26 and the same four expected route changes. Independent scheduling
improved mean wall and both memory metrics but moved median wall from 0.1839 to
0.1873 seconds, so it was not sufficient by itself as a release gate.

Paired sweep `50518274` then ran v0.2.26 and the candidate sequentially for all
592 ontologies on the same exclusive Intel Xeon Gold 6248 nodes, alternating
arm order by task index. Both arms contain exactly 592 results and checkpoints,
use the pinned binary hashes, and leave no temporary files. Both report 591
successful classifications and the same sole fail-closed error. Every status,
verdict, consistency result, and signature is identical.

| Metric | v0.2.26 paired | v0.2.27 candidate | Change | Improved? |
|---|---:|---:|---:|:---:|
| Mean wall (s) | 3.650193 | 3.586135 | -0.064059 | yes |
| Median wall (s) | 0.1893 | 0.1848 | -0.0045 | yes |
| Mean peak RSS (MiB) | 436.0197 | 433.2820 | -2.7377 | yes |
| Median peak RSS (MiB) | 35.85 | 35.04 | -0.81 | yes |

`audit-paired-vs-v0.2.26.json` is the release-gate report.
`audit-intersection-inproc-independent-vs-v0.2.26.json` records the independent
sweep. No Lean re-certification is required because these changes reuse
representations and alter route scheduling and process boundaries, not the CB
calculus or its fixpoint.
