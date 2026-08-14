# EL typed-input handoff and one-shot allocation release

This directory records the v0.2.19 performance gate. The candidate combines
four fixpoint-preserving implementation changes:

- preprocess role-chain additions without cloning the complete TBox and move
  the retained clause set into a right-sized allocation;
- release the one-shot CB worker's converted source-clause arena after engine
  preparation and query construction;
- select eight workers for one large plain-TBox profile and one worker for a
  medium SHI profile, without changing the selected reasoning mechanism; and
- pass the frontend's typed clause vector directly to in-process EL completion
  when the selected route is `elc`, avoiding a JSON read and parse. Other
  routes drop that vector inside the frontend and retain the established
  serialized handoff.

No rule, ordering, redundancy criterion, or derived fixpoint changes.

## Focused gate

IBEX array `50466117` compared v0.2.18's exact candidate baseline with binary
`6b4dbd165382f19ec666520cb226b46058b77a3bc83ccc9f7a779f8b2f0eb9e1` on ten
ontologies, with five alternating same-node repeats per arm. All 50 output
pairs are byte-identical. Across all 100 measurements, mean wall falls from
0.1812 to 0.1774 seconds and mean peak RSS from 30,223.6 to 29,292.2 KiB. The
three `elc` inputs retain 18–20 ms wall savings and 1.8–3.7 MiB RSS savings;
the seven `production_all` controls remain at baseline-scale noise.

Raw panel logs are in [`evidence/panel/`](evidence/panel/). Build job
`50466050` and its exact binary hash are retained in
[`evidence/build/`](evidence/build/).

## Strict 592-ontology gate

IBEX array `50466143` ran all 592 ORE ontologies under the 240-second, 20-GiB,
16-core contract on Intel Xeon Gold 6248 nodes. The audit records:

- 592 terminal rows, profiles, and checkpoints;
- 591 successful classifications and ORE1194 as the unchanged fail-closed
  error;
- 588 exact signature matches, two established consistency mismatches, one
  independently adjudicated no-gold result, and one error;
- one exact binary identity, one array-job identity, no missing route traces,
  and zero status, verdict, signature, consistency, or coverage differences
  from v0.2.18.

Metrics over the 591 successful rows:

| metric | v0.2.18 | candidate | change |
|---|---:|---:|---:|
| mean wall | 4.14838 s | 4.00461 s | -3.47% |
| median wall | 0.2192 s | 0.2159 s | -1.51% |
| mean peak RSS | 450.251 MiB | 449.847 MiB | -0.09% |
| median peak RSS | 39.04 MiB | 38.66 MiB | -0.97% |

[`strict-audit.json`](strict-audit.json) contains the machine-readable audit.
[`automatic-results.tsv`](automatic-results.tsv) contains every terminal row,
and [`ibex_elc_typed_route_drop_sweep.sbatch`](ibex_elc_typed_route_drop_sweep.sbatch)
is the resumable, identity-checking sweep harness.

## Local regression gate

The final source passed the complete serial release suite: 1,984 library tests
and every integration test, including `tests/issue_3_soundness.rs`. The issue
#3 nominal-enumeration/pigeonhole inconsistency remains detected.
