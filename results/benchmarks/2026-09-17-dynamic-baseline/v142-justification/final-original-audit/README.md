# Final original-panel KM audit

Array 51984134 and audit 51984145 completed with exit 0. All 240 frozen tasks
have matching task, source and driver receipts and completion markers. The
parent verified all 1,440 unique planned attempts and normalized support counts.

Excluding 240 warmups, the 1,200 measured attempts contain 825 independently
correct results, 270 timeouts and 105 errors. Completed supports pass the
independent entailment, source-subset and deletion-minimality checks. No audit
integrity errors or duplicate logical supports were reported. Execution
completion does not mean every extraction succeeded.

The errors require further diagnosis before final reporting. HAO q002 module
common-driver attempts show a valid KM response followed by a broken pipe.
The Java adapter passes the live stdout stream to Jackson readTree, which
closes it after parsing an object before the producer necessarily finishes
writing its trailing data. This adapter defect must be reproduced and fixed
in an isolated harness revision, preserving these original attempts.
MFOMD native and common-driver errors report worker engine exit -1; the
underlying signal or cause is not established by that message.

The sampled process-tree RSS can miss short-lived processes; observed zero
samples are not evidence of zero memory consumption. Native/common and full/
module measurements remain separate. Comparator audits remain pending.
