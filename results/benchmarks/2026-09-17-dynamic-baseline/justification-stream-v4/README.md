# Common-driver stdout correction

Staging job 51992710 completed successfully. The pinned Jackson regression
reproduces the old premature stream close and validates draining stdout before
parsing. Both baseline and final KM pass positive and negative HAO q002 module
probes and an independently validated one-support MMO extraction.

Earlier staging jobs 51992703 and 51992705 failed due to Python API compatibility
and an omitted auditor copy respectively. Their outputs remain remote. The
successful revision creates fresh roots; it does not overwrite either attempt.
No measurement from a failed staging attempt enters the main comparison.

The submission receipt identifies four corrected main arrays and dependent
audits, covering all 600 original task manifests with the single km-common arm:
1,800 attempts including 300 warmups. Limits, repetitions, input hashes and KM
binaries remain unchanged. Task receipts bind their prior manifest hashes.
The capacity snapshot supports at most 64 concurrent main tasks.

Both corrected supplementary audits are complete: see audit-baseline-pure-dl
and audit-final-pure-dl. Each has 75 correct and 75 timeout measured attempts.
The corrected original-panel outcomes and audits remain pending. The old
comparison remains archived; integration must preserve distinct harness
revisions and the timing caveats documented in METHODOLOGY.md.
