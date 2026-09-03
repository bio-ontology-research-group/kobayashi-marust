# ORE 9096 automatic-route boundary confirmation

The integrated v1.4 sweep left ORE 9096 just above its strict memory target in
a single observation: 0.1114 seconds and 42.32 MiB versus external targets of
0.1292 seconds and 40.18 MiB. Because both margins are small, IBEX array
`51256553` repeated the current automatic route ten times and compared it with
ten runs under `MALLOC_ARENA_MAX=1`.

The experiment used the production binary built for the compact nominal
scheduling confirmation, SHA-256
`6fa5a55f78b4b7017ca31eb3ddac6ae64e2066604b5f6259dabbf7b56c0e9b53`,
on Intel Xeon Gold 6248 nodes with 16 allocated CPUs. Every run returned
`status=ok`, selected the `nominals` route, matched the retained Konclude gold
signature, and produced signature SHA-256
`f3b5d8340ae8952054a204146b16e5e82818390360e61cd62831da4c24b7867f`.

| arm | correct runs | median wall (s) | wall range (s) | median peak RSS (MiB) | RSS range (MiB) |
|---|---:|---:|---:|---:|---:|
| automatic | 10/10 | **0.1123** | 0.1094--0.1143 | **39.36** | 38.42--40.90 |
| `MALLOC_ARENA_MAX=1` | 10/10 | 0.24565 | 0.2339--0.3241 | 37.79 | 37.17--39.36 |
| external target | - | 0.1292 | - | 40.18 | - |

The unmodified automatic route strictly beats both external targets on its
ten-run median. The allocator arm lowers memory slightly but fails the wall
target and is rejected. ORE 9096 therefore raises the evidence-composite
strict score from 515/589 to **516/589**, leaving 73 comparable residuals. No
code or routing change is required.

The 20 results, 20 checkpoints, and 20 scheduler logs are archived under
`.work/artifacts/v14-9096-boundary/`. Its verified `SHA256SUMS` manifest covers
all 60 files.
