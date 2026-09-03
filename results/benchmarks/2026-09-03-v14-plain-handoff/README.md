# Plain-clause handoff experiment

This experiment tested whether the production CB portfolio should construct
the unabsorbed clause set during its first frontend pass instead of invoking
the frontend again for the plain probe. The candidate was commit `1dbe146`
on `agent/v14-round2-handoff`. It was not merged.

IBEX build job `51253874` validated and deployed binary SHA-256
`5816baaf37a9144eb8f5ffc0d29afc2fb8cdc40a23cbba67801725de7afcd433`
from source archive SHA-256
`ceb9d9c8cfa6fb76088338f0d7dc347320980fae73658f9c39c275d71934fdf5`.
Array `51254110` ran all 36 production-CB residuals under two automatic-route
arms, three repetitions per arm: the candidate handoff and the historical
second frontend invocation (`KM_NO_PLAIN_HANDOFF=1`). All 216 runs returned
`status=ok`, matched their gold signatures, and produced 216 result files, 216
checkpoints, and 216 `TASK_COMPLETE` markers.

The broad handoff is rejected. It creates no new strict time-and-memory win
against the per-ontology baseline targets. It improves several small cases,
but retains a second normalized clause set during the frontend and causes
unacceptable peak-memory regressions on larger or differently routed inputs:

| ontology | handoff / legacy wall | handoff / legacy peak |
|---|---:|---:|
| 7914 | 1.078 | 3.268 |
| 8347 | 0.852 | 1.437 |
| 7956 | 1.018 | 1.390 |
| 15491 | 1.045 | 1.293 |

The apparent 10123 wall change (0.4357 s to 0.3514 s) is not attributable to
the handoff. Follow-up phase array `51254440` ran five repetitions per arm with
`KM_TIMING=1`; every run reported `absorption withheld nothing, plain probe
skipped`. Both arms therefore executed the same code path, and the difference
is run-to-run noise. The experiment provides no measured strict recovery.

A future implementation may reuse withheld clauses only after a fail-closed
source/profile gate or reconstruct them without retaining a second
post-processed clause set. The present broad implementation must not be
enabled by default.

The complete raw evidence is retained at
`.work/artifacts/v14-plain-handoff/panel-evidence.tar.gz`, SHA-256
`4d35d58cfff19ef2b0387fa40791a2315a426c598b876416fcf6f84704794f87`.
