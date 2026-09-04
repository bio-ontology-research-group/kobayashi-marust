# v1.4 post-partition production-CB residual panel

IBEX array `51332996` ran the exact post-partition development source three
times on each of the 25 production-CB residuals. The source archive has
SHA-256 `2df7f7b2065964e59cf74e82e3cc6d079a8c82fd9c2277b16a7a3cfedf5a8ef5`:
commit `2701e339b3fdea81e2c1bf1e977b88e686160033` plus working-diff SHA-256
`3be845bbb0bce711427e49482e0d646b92457413a49dc534dbf690da58a36faf`.
Native IBEX build job `51332926` produced binary SHA-256
`09bf5aaadf24630eb37b673a9bbd40536d6335836ca2c429e987a58cd672e8b6`.

All 75 tasks returned `status=ok`, matched their retained gold signature,
recorded the pinned binary hash and route trace, wrote a checkpoint, and ended
with `TASK_COMPLETE`. The three-run median comparison closes none of the 25
residuals. Therefore the partitioned minimum-head index remains an accepted
general memory improvement, but it does not by itself increase the
authoritative `525/589` strict joint score.

ORE 11316 is the closest result: its 0.2196-second median is below the
0.2201-second target, but its 59.18-MiB median remains above the 42.43-MiB
target. ORE 14312 remains below its memory target but 18.1% above its wall
target on the repeated panel. The larger CB cases require improvements beyond
the posting partition.

A follow-up exact-current route panel, IBEX array `51334469`, repeated
`production_all`, `production_all1`, and `tab_race` three times on ORE 11316.
All nine runs completed, matched gold, and passed the same receipt checks.
`tab_race` is a strict joint win at median 0.1435 seconds and 35.70 MiB.
This result does not rely on the tableau answer: the route's tableau grace is
30 seconds, while CB finishes in under 0.15 seconds, so the tableau worker is
never spawned. The result identifies a useful plain-CB schedule that bypasses
the production portfolio overhead. It is not yet counted in the composite
until that schedule has a source-profile gate and corpus-wide regression
evidence. Reducing the absorbed production route to one worker did not recover
the case: `production_all1` was slower and retained essentially the same peak.

Raw results, checkpoints, logs, source archive, scripts, and build receipt are
retained under
`/ibex/scratch/hohndor/km/v14-partition-current-cb25-20260904/`; the local
working mirror is `.work/artifacts/v14-partition-current-cb25/`.

