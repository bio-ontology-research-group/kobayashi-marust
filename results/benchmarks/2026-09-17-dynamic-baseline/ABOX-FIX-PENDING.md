# Historical diagnosis: source ABox inconsistency publication

This records the initial diagnosis before restored access and validation. The
candidate subsequently passed experimental controls, all four certification
gates and the v1.4.1 592-ontology regression. See the current
[fix evidence](../2026-09-17-dynamic-fixes/README.md). The notes below are retained
as historical evidence, including invalid diagnostic commands and interrupted
checks; they do not describe current execution access or release readiness.

Controls audit jobs 51981218 and 51981232 found that two asserted disjoint
classes on one individual yield `consistent: true` through `incremental-source`.
HermiT and JFact fresh results and the analytic expectation are inconsistent.
The same result occurs on initial load and on update, so this is not solely
an invalidation bug.

Diagnostic job 51981233 repeats the source with prefixed, full URN and full
HTTP names. All source-session responses report consistency. The full-HTTP
frontend output explicitly contains `abox_inconsistent: true`. Its normalized
clauses contain the disjointness but the source precheck's global verdict is
separate metadata. `map_incremental_result` previously used only worker
inconsistency and unsatisfiable asserted classes, losing that metadata.
The diagnostic's ordinary classify command accidentally used `--format json`,
which specifies an input syntax and is invalid. Those classify outputs are
not evidence. The script now uses the correct command and a new output path;
that corrected rerun has not been submitted.

Candidate: preserve `frontend.abox_inconsistent` in the source response's
consistency conjunction, clearing taxonomy rows on that global source clash,
as already done for an unsatisfiable asserted class. No saturation rule changes.
Regression covers fresh inconsistent load, consistent-to-inconsistent update
and restoration of the initial consistent classification.

Required before accepting:

1. Run the new regression against baseline and candidate; compare the source
   session to ordinary classification and independent reference results.
2. Run source incremental/nominal/rule, ELC/HT/CB incremental and explanation
   regressions. Check side-metadata edits and restoration, not just initial load.
3. Only after experimental success, certify the changed publication boundary
   in Lean, including exact-source evidence and any required additional theorem.
   Running an unrelated proof target is insufficient.
4. Run the candidate through the affected controls and real histories, then
   full ORE correctness/regression and final release gates.

The local baseline-test compilation was interrupted by the execution-environment
change: its handle is gone and no cargo/rustc process was visible afterward.
The log has compiler warnings but no test result, so it proves neither pass nor
failure. Subsequent commands face restricted network access (IBEX DNS failure)
and a failed 20-GiB disk preflight. No heavy check or Lean certification has
been started under those failing gates.
