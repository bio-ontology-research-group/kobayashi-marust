# Final KM incremental audit

This cohort covers eight ontologies with update sizes 1, 10 and 100, each with
251 states, one warmup and five measured repetitions. Both KM session and fresh
arms use the final v1.4.1 candidate. Peer comparisons belong to the combined
incremental report; this audit establishes coverage and KM self-agreement only.

All 288 attempts have terminal measurements: 144 completed, 72 errors and
72 timeouts. Excluding warmups leaves 240 attempts: 120 completed, 60 errors
and 60 timeouts. MMO, HAO, VTO and ZFA completed all measured histories.
MFOMD and TO ended with errors; Uberon and MRO timed out. Failures remain in
the benchmark denominator.

The 60 measured error logs are retained in `error-driver-logs.tar.gz`, with
per-file hashes and final diagnostics in `error-driver-log-review.json`.
All 30 TO errors report `DL-safe rule contains a complex class atom` during
initialization. All 30 MFOMD errors report `worker engine exited -1` (15 fresh
initializations and 15 session replacements). That exit code does not by itself
identify the underlying cause, so these attempts retain their recorded error
status. These logs exclude warmups.

Session and fresh digests agree on all 19,626 jointly available states,
including warmups. There are 72 fully agreeing history pairs including warmups.
Self-agreement does not establish agreement with an independent reasoner or
correctness of states that did not complete.

- `main-audit.json.gz` and `main-audit.md.gz` record audit job 51983839 after
  benchmark array 51983825 completed.
- `parent-structural-review.json` records coverage, limits and self-comparison.
  Run `python3 review-structure.py` to check these claims against the archive.
- `provenance.tar.gz` retains 56 files: the panel, deployment receipt, six
  driver sources and 24 pairs of input manifests and checksum lists.
  `parent-provenance-review.json` records their match to all 288 measurement
  source/manifest receipts and all 6,024 independently verified input hashes.
- `parent-payload-verification.json`, `verify-payloads.py` and the job
  52021312 log bind all 6,024 compressed input files and the candidate runtime
  to measurement receipts. They also check manifests, panel, deployment and
  driver-source associations. The verifier requires the remote input paths.

The earlier structural receipt marks payload verification as pending. The later
payload receipt closes that check; neither receipt asserts independent peer
correctness. Canonical digest evidence follows the frozen benchmark method:
full sorted IRI taxonomies, consistency and unsatisfiability are hashed; pilot
full outputs validate canonicalization, and disagreements require targeted
full-output diagnosis.

Uncompressed audit SHA-256:
`e7bd1b642fe11b00545f1f36d50384e7ecfed609a1e050480d553f8e2eb8316d`.
Candidate runtime SHA-256:
`680d9002583468e7c68115bf67cb60b89e420339db4c6aa22b5ca802206c8629`.
