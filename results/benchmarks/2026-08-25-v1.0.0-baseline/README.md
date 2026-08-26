# KM v1.0.0 performance baseline

This directory records the fresh automatic-route baseline for the immutable
`v1.0.0` release commit `ef9e9893dcfa8794be630afd47b34ceca86c1c2f`.

- Binary SHA-256:
  `3f313fe954e2fc779364a4999ba1d0ee6118aaeef0e1bf6e1cbc49ed7a196087`
- Native build job: `50836494`, completed in 4 minutes 53 seconds
- Full resumable sweep: array job `50836659`
- Tail-first debug resume: array job `50836856`, cancelled while still pending
  after Slurm estimated a 22:10 start but the complete array was scheduled for
  10:34. It produced no rows and consumed no compute allocation.
- Contract: 592 ORE 2015 ontologies, 240 seconds, 20 GiB process-tree RSS
- Hardware: exclusive Intel Xeon Gold 6248 nodes, 16 allocated CPUs
- Route: automatic `km classify`
- Correctness: full-IRI signatures and retained independent adjudications

The Slurm runner validates the ontology list, binary identity, CPU model,
terminal checkpoint, route trace, and collision-sensitive fingerprints. It is
resumable only when an existing result/profile pair passes all validation.

The resulting measurements establish the optimization baseline for v1.1.0.
They do not reuse the older v0.2.36 performance numbers attributed to binary
`bbef8d7efbc6...`.

## External gates

[`derive_external_targets.py`](derive_external_targets.py) accepts only
successful answers marked empirically sound and complete in the frozen
all-reasoner panel. It writes:

- [`external-aggregate-targets.json`](external-aggregate-targets.json), the
  aggregate v1.1 comparison values; and
- [`external-per-ontology-targets.tsv`](external-per-ontology-targets.tsv), the
  strict fastest-wall and lowest-memory target for each v1.2 comparison.

The source panel SHA-256 is
`e2bba1ee660f714b85da1e8db16da4251a59729af2c2de01b3008738c77ebf56`.
It provides a valid external target for 589 ontologies. Konclude sets 434 wall
targets and ELK sets 155; Konclude sets 493 memory targets and ELK sets 96.
The three ontologies without a correct external completion need an explicit
adjudicated comparison policy and cannot silently be treated as victories.

[`audit_per_ontology_candidate.py`](audit_per_ontology_candidate.py) applies
those exclusive wall and memory targets to a completed 592-row KM sweep. It
reports the exact wall-only, memory-only, neither, and simultaneous-win sets.
It cannot pass the all-592 v1.2 gate while any ontology lacks a correct
external reference; those cases remain visible as `unadjudicated` until an
explicit comparison policy and evidence are recorded.

On correct completions, the binding aggregate v1.1 wall target is ELK's
1.520774-second mean. The binding memory mean is ELK's 493.327 MiB, while
Konclude sets the 0.2814-second median-wall and 76.87-MiB median-memory targets.

[`audit_release_candidate.py`](audit_release_candidate.py) is the fail-closed
v1.1 release gate. It requires all 592 byte-identical terminal/checkpoint pairs
from the pinned candidate binary on Gold 6248 CPUs, preservation of every
successful v1 status/signature, independently proved signatures for recovered
v1 non-successes, 591 successes plus the established fail-closed ORE1194 error,
complete route/performance evidence, and strictly lower mean and median wall
and peak memory than every external arm. Missing rows, temporary files,
hardware mixing, or an equality at any aggregate boundary rejects release.

## Completed v1.0.0 sweep

Array `50839937` completed all 592 terminal rows with matching checkpoint and
profile records and no temporary files. The strict partial auditor reports 590
successful classifications, 587 retained exact-gold matches, mean/median wall
5.135733/0.160100 seconds, and mean/median peak RSS 456.784/35.315 MiB. The two
non-successes are the established fail-closed ORE1194 error and an ORE3215
timeout. ORE3215 is a v1 conversion-overhead regression rather than lost
reasoning coverage; the v1.1 candidate repair is tracked in the certification
overhead ledger. v1.0.0 therefore satisfies the aggregate memory boundary but
does not satisfy the binding ELK mean-wall boundary.

[`v1.0.0-sweep-ledger.tsv`](v1.0.0-sweep-ledger.tsv) is the 592-row status,
signature, route, and resource ledger exported from this sweep; its SHA-256 is
`ea72e6fe51a10e82...`. The release auditor now distinguishes preservation from
proved recovery: every successful v1 row must retain status and signature, and
a v1 timeout or error may become successful only when the independent v0.2.36
recovery ledger supplies the same successful signature. Running the revised
auditor against v1.0.0 itself correctly rejects release with exactly three
errors: 590 rather than 591 successes and mean wall above ELK and Konclude.

## Retained v0.2.36 optimization profile

The complete 1,184-row paired release sweep `50554161` remains available at
`/ibex/scratch/hohndor/km/v036-large-clean-20260815/full-pair`. Script
[`derive_v036_profile.py`](derive_v036_profile.py) extracts the 592 candidate
rows, verifies ontology uniqueness, and joins them to the frozen external
targets. The resulting
[`v0.2.36-per-ontology.tsv`](v0.2.36-per-ontology.tsv) and
[`v0.2.36-profile-summary.json`](v0.2.36-profile-summary.json) are the targeting
ledger while the fresh v1.0.0 sweep runs.

Across 591 successful classifications, v0.2.36 uses 1,913.8077 wall seconds.
ELC contributes 863.7179 seconds and `production_all` contributes 516.7193
seconds. Against the fastest correct external result for each comparable
ontology, KM wins wall on 387/589, memory on 463/589, and both on 375/589. The
summed positive wall gap is 1,094.0733 seconds. These per-ontology targets are
the v1.2 gates; the separate v1.1 aggregate gate remains ELK's 1.520774-second
mean over its correct completions.
