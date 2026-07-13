# ore_ont_3215 closure and regression sweep

Status: complete. This directory records the production IBEX proof and the
592-ontology regression sweep for the Konclude KPSet phase-barrier port that
closes `ore_ont_3215`.

The final binary was built on `ws` with Rust 1.85 in the Bullseye container. It
requires at most GLIBC 2.29 and has SHA-256
`87ee76f1713e498fa7367832b00090663d0f8d3e02e7d296e275d7d1323c37c4`.
The release suite passes 1,468 tests, with zero failures and 7 ignored tests.

## Production closure

The first code-complete bridge binary proved the logical fix but exposed an
orchestrator scheduling boundary:

| IBEX run | Ambient `KM_THREADS` | Result | Wall | Peak RSS |
|---|---:|---|---:|---:|
| 48789800, diagnostic | 16 | timeout | 241 s | 3,532,620 KB |
| 48790038, quiet | 16 | timeout | 240 s | 3,543,944 KB |
| 48790049, quiet control | 2 | exact match | 137 s | 5,348,648 KB |

The bridge's 18,323 KPSet model jobs are currently synchronous. The speculative
CB fallback used the other 15 cores and starved the serial bridge on memory
bandwidth. The production scheduler now detects a faithful bridge with at least
50,000 active classes and limits only its concurrent CB fallback to one thread.
All smaller bridge races retain their prior reservation. This is scheduling
only; neither reasoner nor the winner/fallback rule changes.

Final binary job 48790271 was invoked with the normal `KM_THREADS=16`, applied
the structural cap automatically, and matched gold in 129 seconds at 5,351,252
KB. The full-sweep task matched again in 120 seconds at 5,357,524 KB. Both have
zero extra and zero missing pairs.

## Full-sweep result

IBEX array job 48790295 ran all 592 ORE ontologies, one per task, with a
240-second reasoner cap, 20 GB Slurm memory, and the same trigger-absorption
flags as the preceding plan-15 feature sweep.

| Metric | Plan-15 baseline | 3215 closure |
|---|---:|---:|
| ok | 569 | 574 |
| timeout | 23 | 18 |
| exact Konclude match | 499 | 508 |
| incomplete | 50 | 51 |
| unsound | 10 | 4 |
| both-disagree | 2 | 2 |
| inconsistent | 6 | 6 |
| no gold | 2 | 3 |

No gold-matching ontology regressed. Nine ontologies changed to exact match:
11315, 12414, 3215, 4054, 4755, 7127, 7581, 8068, and 8864. The classifier
fixes remove the prior false positives on 11315, 12414, 4054, 4755, 7127, and
8068, and the 21 missing pairs on 8864. The remaining both-disagree result on
11745 also improves from 25,170 extra / 3,685 missing to 15,350 extra / 1,213
missing. Timing recoveries let 4669, 7581, 9663, and 9724 finish; only 7581 is
gold-exact among the three ontologies that have gold.

`aggregate.json` is the machine-readable comparison with the immediately
preceding feature sweep. Its SHA-256 is
`455832ed73cd87d8cd995462172dda65345e614ce07b2b5821dfba4471fd1498`.

## Controlled changed-ontology A/B

IBEX job 48790909 reran the nine changed correctness cases with the preceding
plan-15 binary and the final 3215 binary under identical flags. All nine pairs
completed. The final binary changes 3215 from timeout to exact match, changes
six unsound results and one incomplete result to exact matches, and reduces
11745 from 25,170 extra / 3,685 missing to 15,350 extra / 1,213 missing. There
are zero exact-match regressions. `ab-summary.json` records the result and has
SHA-256 `29447a0554894297a686c7a71f4819182a66f7139f0db143ff10525f2d178743`.

## Reproduction

- `ibex_3215_smoke.sbatch` runs the production `km classify` path for 3215 with
  a 240-second reasoner cap, 20 GB Slurm memory, and direct Konclude-gold
  comparison.
- `ibex_3215_fullsweep.sbatch` runs the same feature configuration over the
  complete 592-ontology ORE corpus, one ontology per array task.
- `aggregate_ibex_3215.py` compares every result with the immediately preceding
  plan-15 feature sweep in `plan15_7914_closure/final_res`.
- `ibex_3215_changed_ab.sbatch` repeats the nine changed correctness cases with
  the previous and final binaries under identical flags.
