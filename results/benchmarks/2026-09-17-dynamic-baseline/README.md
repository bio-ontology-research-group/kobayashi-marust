# v1.4.1/v1.4.2 dynamic reasoning benchmarks (in progress)

Baseline is the unchanged published v1.4.0 (`c10e22f`). The protocol and harness
are in [benchmarks/dynamic-v1.4](../../../benchmarks/dynamic-v1.4/).
This directory preserves baseline pilots, controls, frozen main-run provenance,
and the certification evidence for the candidate fixes. Main comparisons are
in progress; pilot timings are not final release results.

## Current evaluation

Both benchmarks follow literature recorded before implementation in the
[methodology](../../../benchmarks/dynamic-v1.4/METHODOLOGY.md).
The original incremental main array is `51982318`, with pure-DL supplemental
array `51982375`; their audits are `51982323` and `51982376`. Justification
main arrays are `51982389` and `51982752`, with audits `51982402` and `51982764`.
These runs retain the released baseline and peer runtimes. Final versioned KM
runs use separate artifacts and preserve the same inputs and repetitions.

A syntactic audit corrected the original inventory's DL labels: TO and uberon
contain SWRL rules. They remain extension stress cases in the denominator.
The pure-DL panel is mfomd, zfa and mro; the EL panel is mmo, hao and vto.
Justification query preparation failures remain explicit, including MRO's
600-second preparation timeout. No replacement was selected using KM success.

The controls exposed two related ABox errors. Experimental candidate controls
and the 592-ontology regression passed, followed by the Lean routing gate.
See [fix evidence](../2026-09-17-dynamic-fixes/README.md),
[certification receipt](abox-lean-certification.json), and
[proof boundaries](../../../lean/ATOMIC-ABOX-PUBLICATION.md).
All four native certification gates have now passed; their
[receipt](v141-native-gates-source-manifest.json) records the exact excluded
test names and source hashes. Final comparative measurements and artifact-bound
regression checks remain separate release requirements.

## Incremental pilot, Slurm 51981055

Two six-state histories: independent synthetic EL chains with ten axiom
exchanges per update; frozen Alzheimer's Disease Ontology with one exchange.
KM, HermiT, JFact, Openllet, ELK and Whelk; retained/session and fresh arms.
22/24 arms completed. All 22 completed arms have six signatures matching
HermiT; each revision has a different taxonomy. Both Whelk session arms
failed at revision 1 due to a harness OWLAPI 4/5 collection-overload ABI
mismatch. This was fixed in the next harness version with per-axiom
`applyChange`. The two failed runs are preserved, not counted as success.

KM's first chain update reported `el_delta`, reused fixpoint true and 1,087
retained states. ADO's first update reported `exact_rebuild`, reused fixpoint
false and zero retained states. A retained backend object alone does not
establish incremental inference. ADO is not the EL profile, so this pilot's
ELK agreement does not establish broader supported-fragment coverage.

Original pilot artifacts remain in:
`/ibex/scratch/hohndor/km/dynamic-benchmark-20260917/`.
Local full pilot copy:
`.work/artifacts/dynamic-benchmark-20260917/` in the top-level checkout.
Selected audit and provenance are preserved in `pilot/` here.

## Main incremental preparation

Panel is selected without KM timings by `select_incremental_panel.py`:
EL mmo/hao/vto; other DL mfomd/to/uberon. All source hashes are frozen.
18 histories, 250 updates each, at change sizes 1, 10 and 100.
Preparation array: 51981134, remote `incremental-main/inputs/`.
Driver build: 51981168, remote `incremental-driver-v2/`.
Six-state, 30-comparator-pair panel check: array 51981169, dependent on
successful preparation and driver build. Includes 60 retained/fresh arms.
This check must pass or produce diagnosed failures before main repetitions.
Main timing runner adds process-tree memory monitoring, state deadlines,
partial-result checkpoints, compressed signatures and warm runtime rebuilds.

## Remaining release requirements

Complete the real-ontology comparisons and independent audits over every frozen
case and repetition. Report correctness and coverage alongside timing, keep
warmups out of measured summaries, and preserve unsupported, incorrect and
resource-limited outcomes. Incremental comparison requires complete canonical
taxonomies; justification comparison requires source membership, entailment
and one-deletion minimality for every returned support.

Artifact-bound ORE regression and all four native certification gates have
passed for both candidate versions, with source hashes retained in their
receipts. The general Rust suites and versioned Protégé validation also pass.
Retain these bindings in the tagged releases. Publish v1.4.1 for incremental evaluation and v1.4.2 for justification
only after the corresponding complete evidence and comparison reports exist.
Neither release has been published by this work.

## Early complete-case validation

The first declared MMO query's STAR-module case completed all six repetitions
at bounds 1, 10 and 100 across baseline peers and final KM. Its isolated
[review](justification-early-case-review/review-validation.json) independently
verified 234/234 extraction attempts, including 195 measured attempts, with no
source-binding or semantic disagreements. Warmups are excluded from timing
pairs, and unknown enumeration remains distinct from completion. This is a
bounded protocol check; it does not establish overall benchmark performance.

The completed `mmo-n10` incremental case also passes its isolated
[audit](incremental-completed-mmo-n10/parent-verification.json): all 24 histories
(six repetitions of KM session, KM fresh, HermiT fresh and JFact fresh) contain
all 251 states. The full canonical taxonomy digest vectors agree across every
arm and repetition, and all 251 state digests differ from one another. Snapshot
hashes were revalidated before the audit. This is one real case, not completion
of the full incremental comparison matrix.

The [timing review](incremental-completed-mmo-n10/timing-review.json) excludes
warmup and uses five measured repetitions. Median whole-history wall time is
17.87 s for KM session, 15.57 s for KM fresh, 52.60 s for HermiT fresh and
49.29 s for JFact fresh. All 1,250 measured KM updates report real `el_delta`
fixpoint reuse, but the session is slower than rebuilding on this case. The
median update retains 265 states and invalidates 5,092. Whole-history time
includes interface and canonicalization costs; internal Java and KM intervals
are not directly interchangeable. This finding motivates diagnosis, not an
overall ranking or a change to the frozen benchmark protocol.

## Common-driver correction and final comparison selection

The shared Java subprocess reader could close stdout before a KM or Konclude
worker finished writing its JSON response. The exact patch drains stdout
before parsing. Full common-driver cohorts are rerun for baseline/final KM
and for Konclude, with original results retained. See the
[Konclude correction evidence](justification-konclude-stream-v4/README.md)
and [combined report submission](justification-konclude-stream-v4/comparison-submission.json).
The final justification comparison must include both corrections; earlier
KM-only reports are intermediate. A corrected failure cannot be replaced
by an original success. All independent audits must finish before publication.
