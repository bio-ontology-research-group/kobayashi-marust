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
The complete 592-ontology production sweep is staged at
`/ibex/scratch/hohndor/km/release-9ee269e-auto-20260804`. Sanity job `50040967`
depends on both `abe2759` arrays; production arrays `50040968` and `50040969`
depend on that sanity gate. The staged binary hash matches the paired candidate
exactly.
