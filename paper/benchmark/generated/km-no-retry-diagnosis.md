# KM v1.3 current-corpus internal-cap diagnosis

The repaired OBO sweep first exposed five terminal records whose stderr was
only `worker engine exited -1:`: CDAO, CHMO, CL, DPO, and ECTO.  The completed
189-row ledger identifies twelve instances: CDAO, CHMO, CL, DPO, ECTO, ENVO,
HANCESTRO, OHD, ONS, and PCL are OWL 2 DL but non-EL; MIAPA and OVAE are outside
OWL 2 DL.  The records belong to native array job `51028377` and bind the tested
KM binary:

`cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d`.

This is a default-routing limitation, not a runner or Slurm failure. The v1.3
source-feature policy injects `KM_NO_RETRY=1` for the selected route. When its
central engine reaches `KM_CENTRAL_TIME_CAP` or the internal parallel-memory
cap, the worker is killed by signal and no single-threaded adaptive retry is
started. Rust maps the signal-only exit status to `-1`, and the supervisor
returns exit code 1. The benchmark runner therefore records an honest `error`.

The behavior was reproduced locally with the exact tested binary and CDAO
source SHA-256
`318d0ed4d393a3917726edfd16c1544d8ab9da9cec5e368529a51bba63f1f2a2`.
Reducing `KM_CENTRAL_TIME_CAP` to three seconds reproduced the exit after three
seconds. A worker-wrapper probe observed one engine spawn with
`KM_NO_RETRY=1` and no fallback spawn. Disabling the central strategy and
running the legacy single-threaded mechanism instead remained active until the
independent 15-second diagnostic timeout, which distinguishes the route policy
from a parser or immediate worker crash.

These diagnostics do not alter the benchmark environment. The paper evaluates
the shipped automatic route, so all twelve ontologies remain default-route
failures.  The final count comes from the manifest-complete, profile-aware,
stderr-digest-bound ledger in `km-terminal-causes.tsv`; its summary SHA-256 is
`da9bb783eebaa3a5121c2ec99df0df20608a4e645965a1c6dd421446b0c230a7`.
