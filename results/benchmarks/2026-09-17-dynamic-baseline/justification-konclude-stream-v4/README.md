# Konclude common-driver stream correction

The Java common driver used by KM and Konclude could close a worker stdout
pipe after the first JSON object, before its trailing newline. Konclude samples
show a valid response followed by Python `BrokenPipeError`. The existing
stream-v4 patch drains the pipe to EOF before parsing.

All 300 frozen Konclude-common tasks are rerun at bounds 1, 10 and 100,
including every repetition and warmup. This produces 900 attempts, of which
750 are measured. Original outcomes remain archived. Separate unsupported-input
errors remain failures; the correction does not recategorize them.

Stage 51996783 failed because the probe omitted the required compatibility
library path. Replacement stage 51997023 completed successfully with that
path and fresh output directories. Positive and negative HAO/ZFA probes, the
pinned-Jackson stream regression and the independent MMO support audit passed.
[Stage evidence](stage-evidence.json) records retrieved files and hashes.

[Submission](submission.json) records the two benchmark arrays and dependent
audits. The [capacity observation](scheduling-capacity.json) supported caps
of 64 and 16. These later runs share cluster resources; their times are not
interchangeable with the original rotated multi-arm measurements.

The [combined-report receipt](comparison-submission.json) binds the corrected
reporter and configuration. Initial binding validation exposed legacy tasks
whose arms are implicit. The replacement validator uses the frozen runner's
exact arm expansion, with a regression test. All six KM/Konclude correction
cohorts now pass [binding validation](binding-validation.json).
The comparison selects whole cohorts by original panel and arm, rejects
overlapping replacements, and never falls back to original failed or missing
corrected attempts. Reports generated before the Konclude correction are
intermediate artifacts. The combined report still awaits all ten audits.
