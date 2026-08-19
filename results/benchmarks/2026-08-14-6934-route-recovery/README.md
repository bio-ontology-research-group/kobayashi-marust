# Isolated complete ground-clause route for ORE6934

This directory records the v0.2.26 automatic-route release evidence.

- Candidate logic commit: `85f3423`
- Candidate binary SHA-256:
  `4d8d81378d565d6b5d0b33b8fe352d2e6aa076b7c82a0c196bb58bc167401071`
- Strict IBEX sweep jobs: `50503499`, `50503695`, and `50503696`
- Hardware: Intel Xeon Gold 6248
- Contract: 240-second timeout and 20-GiB memory cap
- Integrity: 592 unique terminal results and profiles, 592 checkpoints, no
  temporary files, exact task indices 0–591, and one verified binary hash
- Automatic-results SHA-256:
  `38bde359ab9593f1bee73ab36fbf30cd57e9c57ca71372ff44f3a1895847182b`

The automatic route reports 591 successful classifications and ORE1194 as the
sole fail-closed error. Full comparison with v0.2.25 finds zero differences in
status, verdict, consistency, or output signature. ORE6934 is the only route
change, from `nominal_ni_abox` to `ht_general`.

| metric | v0.2.25 | candidate | change |
|---|---:|---:|---:|
| mean wall, seconds | 3.722682 | 3.607746 | -3.087% |
| median wall, seconds | 0.1860 | 0.1839 | -1.129% |
| mean peak RSS, MiB | 440.8062 | 436.3724 | -1.006% |
| median peak RSS, MiB | 36.04 | 36.16 | +0.12 MiB |

ORE6934 itself falls from 68.9191 seconds and 2,948.33 MiB to 0.1565 seconds
and 44.02 MiB while retaining signature
`5e60a794400802833a9d5785abb6320b7b13d702e48a4c810462bad6c1fc931e`.

`automatic-results.tsv` contains every terminal row, `summary.json` contains
the strict aggregate, and `comparison-v0.2.25.json` records the behavioral,
route, and resource comparison. `aggregate_strict.py` enforces the integrity
contract. The included Slurm scripts reproduce the retained-binary check,
bisect diagnostics, compatible IBEX build, targeted automatic run, route
profile audit, and checkpointed full sweep.

No Lean re-certification applies. The change does not add a calculus rule or
alter any derived clause. It isolates the existing complete ground-clause
worker from specialist state and changes automatic scheduling for one stored
source profile.
