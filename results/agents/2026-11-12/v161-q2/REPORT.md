# v1.6.1 Q2: forced reference stage on the checkers-on suite (Ibex)

Rows: 1781 of 1781 v1.6.0 inputs; missing rows: 0.

| measure | v1.6.0 | v1.6.1 |
|---|---:|---:|
| published, all inputs | 410 | 628 |
| published, recognised (of 592) | 378 | 575 |

- Lost (published in v1.6.0, not now): 0
- Gained: 218
- Digest mismatches (forced vs unforced, both ok): 0
- Published while the unforced run failed (no digest to compare): 0

## Misses among the recognised inputs, by cause

| cause | inputs |
|---|---:|
| not recognised | 14 |
| km timeout (300 s) | 3 |

## Recognised inputs whose v1.6.0 recognition status was accepted but the stage declines as not recognised

- `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-checkers-on-suite/engine/tests/fixtures/realization/inconsistent.ofn`: declined: not recognised: not in pure EL/ALC clause-stream fragment
- `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_13233.owl`: declined: not recognised: not in pure EL/ALC clause-stream fragment
- `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_13937.owl`: declined: not recognised: not in pure EL/ALC clause-stream fragment
- `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_1579.owl`: declined: not recognised: not in pure EL/ALC clause-stream fragment
- `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_253.owl`: declined: not recognised: not in pure EL/ALC clause-stream fragment
- `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_3377.owl`: declined: not recognised: not in pure EL/ALC clause-stream fragment
- `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_3884.owl`: declined: not recognised: not in pure EL/ALC clause-stream fragment
- `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_3910.owl`: declined: not recognised: not in pure EL/ALC clause-stream fragment
- `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_5295.owl`: declined: not recognised: not in pure EL/ALC clause-stream fragment
- `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_5596.owl`: declined: not recognised: not in pure EL/ALC clause-stream fragment
- `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_6722.owl`: declined: not recognised: not in pure EL/ALC clause-stream fragment
- `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_7188.owl`: declined: not recognised: not in pure EL/ALC clause-stream fragment
- `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_7226.owl`: declined: not recognised: not in pure EL/ALC clause-stream fragment
- `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_7455.owl`: declined: not recognised: not in pure EL/ALC clause-stream fragment

## Phase timing of the inputs that hit the stage budget

Phases that finished before the kill (ms); the phase after the last one listed was running at the budget.

| input | phases |
|---|---|
| `ore_ont_14042.owl` | - |
| `ore_ont_14101.owl` | - |
| `ore_ont_16744.owl` | - |
| `ore_ont_8737.owl` | - |
| `ore_ont_954.owl` | - |

Last completed phase before the budget: none 5

## Published inputs: phase totals

- total: 3791.1 s
- closure: 2972.2 s
- readout: 287.7 s
- json: 248.8 s
- source: 158.4 s
- read: 38.6 s
- output: 35.0 s
- recognise: 27.3 s
- alc-reference: 0.3 s
- alc-precheck: 0.0 s
- alc-recognise: 0.0 s
