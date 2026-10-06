# Typical-case latency diagnosis

The partial finite-role-index sweep had a median of about 0.390 seconds.
The three closest recorded verified cases were 236 (0.390297 seconds), 11896
(0.390593 seconds) and 3250 (0.390168 seconds). They were selected for bounded
workstation phase traces, without changing their source files. This is not a
representative performance panel or a replacement for the full corpus.

All three local answers independently agree with retained full-DL references.
The probes use the pinned instrumented binary, one CPU, a 30-second deadline
and 20 GiB. Their host and diagnostic output differ from the full benchmark,
so the local wall times must not be used as a speedup comparison.

| Ontology | Local wall (s) | First conformance check (s) | Later engine-block endpoint (s) | Route |
|---|---:|---:|---:|---|
| 236 | 0.431 | 0.240 | 0.11 | EL |
| 11896 | 0.240 | 0.137 | 0.05 | EL |
| 3250 | 0.244 | 0.002 | 0.23 | Certified cardinality/nominals |

The later endpoint is measured from the orchestrator's own timer, after the
initial conformance check. It is not a separate additive phase duration.
Exact-source cache hits make repeated conformance calls cheap, but do not
avoid the first check. Conformance dominates the two EL examples; the third
case spends its time in reasoning. This gives a measured reason to inspect
validation costs when pursuing the median-runtime target.

`check_source_uncached` currently performs literal validation, grammar
validation, prefix extraction, role restrictions, anonymous-individual
restrictions, entity checks and datatype checks in sequence. The aggregate
trace does not identify which check dominates. Any optimization must preserve
all checks, refusal explanations and admission outcomes on the frozen corpus.
Removing validation or caching a different source is not an optimization of
this contract.

The runner, exact selected-input manifest and diagnostic answer receipts are
retained. These findings do not satisfy either release target. The next useful
measurement separates the first conformance call's subphases while the v2
slow-case analysis job resolves the independent mean-runtime bottleneck.
