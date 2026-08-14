# v0.2.20 frontend handoff benchmark

This directory records the evidence for the v0.2.20 automatic-route release.
The tested implementation is commit `eb11fc2`. The strict candidate binary was
`a18fa4026561768dfc50df93904ba44ef98bfd525d0be9c4b165f4fede3b89a7`.
All end-to-end measurements used exclusive Intel Xeon Gold 6248 nodes, a
240-second timeout, and a 20-GiB process-tree memory cap.

## Change

The automatic frontend now:

- runs inputs smaller than 4 MiB in process, avoiding a frontend subprocess;
- passes exact in-process EL clauses directly into completion without writing
  an unused JSON handoff;
- avoids cloning the owned named-class set on atomic EL and CB mechanisms; and
- admits three measured 300–600 MiB exact-EL inputs to the in-process path only
  after a fail-closed source scan excludes inverse, symmetric, and transitive
  object-property axioms that require the established isolated route.

These changes affect process boundaries, serialization, allocation lifetime,
and scheduling only. They do not alter calculus rules, ordering, redundancy,
or the derived fixpoint.

## Focused validation

The 2–4 MiB panel was Slurm job `50472992`. Its 57 ontology IDs each ran three
alternating control/candidate pairs. All 57 outputs were byte-identical. Median
wall fell from 0.28 to 0.26 seconds, median peak RSS from 42,156 to 39,088 KiB,
mean wall from 0.47895 to 0.43386 seconds, and mean peak RSS from 167,108 to
162,357 KiB. The submitted array initially contained one extra index; the
out-of-range task failed before selecting or running an ontology. The archived
script corrects the range and adds an explicit bounds check.

Separate giant, sparse-EL, ABox, subprocess-fallback, and median-band panels
verified byte-identical outputs and the handoff gates. Earlier strict candidates
that retained the 2 MiB threshold missed the frozen median-wall gate and were
rejected without release.

## Strict sweep

Strict sweep `50473463` produced exactly 592 result rows, 592 profiles, and 592
completion markers, with no harness-validation failures. The binary hash,
CPU model, selected route, checkpoint, terminal status, and collision-sensitive
full-IRI fingerprints were checked per task.

Relative to v0.2.19 sweep `50466143`:

| metric | v0.2.19 | v0.2.20 candidate | change |
|---|---:|---:|---:|
| mean wall, s | 4.004608 | 3.954087 | -1.26% |
| median wall, s | 0.2159 | 0.1910 | -11.53% |
| mean peak RSS, MiB | 449.847 | 443.371 | -1.44% |
| median peak RSS, MiB | 38.66 | 36.43 | -5.77% |

Coverage and adjudication are unchanged: 591 successful classifications, 588
gold matches, two established consistency mismatches, one independently
adjudicated no-gold result, and ORE1194 as the sole fail-closed error. The
comparator reports zero behavior regressions.

## Files

- `automatic-results.tsv`: all 592 strict rows
- `summary.json`: strict aggregate and binary identity
- `comparison-v0.2.19.json`: frozen release comparison
- `ibex_inproc_4m_band_pair.sbatch`: corrected 2–4 MiB paired panel
- `ibex_combined2_sweep.sbatch`: strict sweep harness used for the final run
- remaining `ibex_*.sbatch` files: focused gates and rejected-candidate sweeps

The complete serial Rust release suite passed, including all 1,987 library
tests, integration tests, doc tests, and the issue #3 pigeonhole regression.
