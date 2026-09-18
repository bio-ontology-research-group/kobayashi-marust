# MFOMD worker-limit diagnosis

Diagnostic job 51993463 completed with exit 0 using the measured v1.4.2 binary
and the unchanged mfomd q000 module source. Four runs changed only the internal
central worker limit to 1, 2, 1 and 2 seconds. They failed after 1.047, 2.054,
1.051 and 2.060 seconds respectively, each with the same outer exit 1 and
`classification oracle: worker engine exited -1` as the measured failures.
These are diagnostic runs, not replacement benchmark observations.

The worker watchdog in engine_run.rs records timed_out when killing at its
deadline and maps a signal exit to code -1. The atomic CB wrapper in
orchestrate/mod.rs forwards the nonzero code as a generic worker error, without
forwarding that timeout flag. The diagnostic establishes this failure mechanism
for q000 module. The other MFOMD errors have the same message and observed
240-second boundary (plus Java overhead in the common arm), consistent with
the same mechanism; their original logs do not directly expose the kill cause.

Keep all original raw statuses as errors. Do not relabel all -1 exits as
timeouts: memory kills and other signals can also produce that code. Report
this diagnosed internal-limit behavior separately. The frozen harness uses
600 seconds per extraction and KM_CENTRAL_TIME_CAP=240 per central-worker
invocation, for both native and common-driver arms. No configuration or KM
source change was adopted.
