# Certified EL typed handoff

This directory records the v0.2.23 automatic-route release evidence.

- Candidate binary SHA-256:
  `13b4d406aaddb4b94d1d9f9740cfd5839df851193d049bd76f911a3f1ab84e30`
- Strict IBEX sweep: Slurm job `50494584`
- Hardware: Intel Xeon Gold 6248
- Contract: 240-second timeout and 20-GiB memory cap
- Integrity: 592 results, 592 profiles, and 592 checkpoints
- Automatic-results SHA-256:
  `a98844c16a6aa02fc07041913098ab07aa719880ca50d9478f128691f9aa67af`

The sweep reports 591 successful classifications and ORE1194 as the sole
fail-closed error. Comparison with v0.2.22 finds zero status, consistency,
signature, or coverage regressions.

| metric | v0.2.22 | candidate | change |
|---|---:|---:|---:|
| mean wall, seconds | 3.846692 | 3.783516 | -1.642% |
| median wall, seconds | 0.1885 | 0.1885 | 0.000% |
| mean peak RSS, MiB | 441.1139 | 441.4595 | +0.078% |
| median peak RSS, MiB | 35.73 | 36.47 | +2.071% |

Three alternating same-node pairs on ORE8737 reduced mean wall from 96.743 to
80.223 seconds. A separate ORE16744 pair reduced wall from 73.233 to 63.438
seconds. Every focused output was byte-identical and matched gold. Focused
process-tree peak differences were below 0.2%; the independent full sweeps show
the small RSS variation reported above.

`automatic-results.tsv` contains every terminal row, `summary.json` contains
the strict aggregate, and `comparison-v0.2.22.json` records the behavioral and
resource comparison. The `focused-v1` and `focused-v2` directories retain the
controlled giant-route rows. The first attempted focused run used a
workstation-built binary and failed before routing because the IBEX node lacked
GLIBC 2.39; that run was canceled and excluded. All accepted measurements use
the IBEX-built binary named above.

No Lean re-certification is needed. The change removes serialization and
subprocess boundaries around the same typed clauses and completion function;
it does not alter reasoning rules, ordering, redundancy, or derived results.
