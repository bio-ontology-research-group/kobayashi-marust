# Compact taxonomy relation IDs

Commit `9ee269e` stores grouped JSON taxonomy subjects and superclasses as
`u32` IDs into one lexicographically ordered full-IRI dictionary. This replaces
one cloned `Arc<str>` per retained relation while preserving aliases,
duplicates, and exact JSON order. Reasoning, routing, the public allocating API,
and `--lines` are unchanged.

## Validation

- Complete release suite: 1,951 library tests passed, eight ignored, with all
  binary, integration, and documentation tests passing.
- End-to-end JSON and `--lines` output was byte-identical to the preceding
  implementation on EL, disjunctive, and nominal/cardinality examples.
- Source archive SHA-256:
  `d6f075d272c660943102ee03e034394abccae729ad653307f45c5a6ae767de58`.
- IBEX build job `50038917` produced binary SHA-256
  `be326fe76e9cbe52d574ad8d5f3c037ae3db9f9fd3d25b498a1f90492534a6dd`.

## Alternating ORE9674 pair

Job `50038918` ran three alternating repetitions against the source-bound
`abe2759` binary on an exclusive Intel Xeon Gold 6248 node. Every output had
SHA-256
`152cdf0863750e3c94ac3faeb1764fe31a52935db73069bb48a5a8b6d2cd9184`.

| Arm | Wall seconds | Peak KiB |
|---|---:|---:|
| `abe2759` baseline 1 | 42.22 | 2,223,144 |
| `9ee269e` candidate 1 | 41.50 | 2,228,124 |
| `abe2759` baseline 2 | 41.97 | 2,228,796 |
| `9ee269e` candidate 2 | 41.52 | 2,228,136 |
| `abe2759` baseline 3 | 42.41 | 2,229,372 |
| `9ee269e` candidate 3 | 41.62 | 2,228,752 |
| **Baseline mean** | **42.200** | **2,227,104** |
| **Candidate mean** | **41.547** | **2,228,337** |

Mean wall improved by 0.653 seconds, or 1.55%. Mean peak RSS changed by
+1,233 KiB (+0.06%), which is measurement-neutral. The smaller relation
representation therefore improves integer sorting and traversal but does not
lower this process's peak high-water mark.

The scripts in this directory reproduce the exact source build and paired run.
The complete 592-ontology production sweep is stored at
`/ibex/scratch/hohndor/km/release-9ee269e-auto-20260804`. Sanity job `50048451`
and production arrays `50048480` and `50048481` used the expected binary.
The strict audit verified all 592 terminal rows, checkpoints, profiles,
production route traces, task-to-ontology identities, completion logs, and
collision-sensitive full-IRI fingerprints, with no temporary artifacts. It
found zero route or semantic differences from the accepted `abe2759` sweep.
Coverage remained 591/592: 591 successful rows and the existing ORE1194 error.
Verdicts remained 588 matches, the established consistency disagreements on
ORE2669 and ORE15516, one no-gold row (ORE10860), and ORE1194's error.

Across the 591 paired successful rows, mean wall increased from 5.8196 to
6.0082 seconds (3.24%) and median wall increased from 0.2495 to 0.2523 seconds
(1.12%). Mean peak RSS increased from 820.36 to 823.32 MiB (0.36%), while the
median fell from 43.04 to 42.13 MiB (2.11%). These independently scheduled
corpus runs are noisier than the alternating source-isolated pair, so they do
not establish a corpus-wide speed improvement. The complete result table is
[`automatic-results.tsv`](automatic-results.tsv).

An initial submission used a copied sweep script whose hard-coded root still
named `229ad77`. Its tasks only recognized that sweep's existing rows as
complete and produced zero `9ee269e` results. Jobs `50040968` and `50040969`
were cancelled. The corrected
[`ibex_sweep_9ee269e.sbatch`](ibex_sweep_9ee269e.sbatch) hard-pins the candidate
root and binary SHA-256, checks binary identity in resumed rows and newly
produced rows, and writes Slurm output beneath the candidate root. This makes a
wrong-root fast finish fail before it can be accepted.
