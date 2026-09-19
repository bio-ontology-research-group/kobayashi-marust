# Extended 1,920-input completion work

The target is complete classification of every original input, with soundness,
completeness and Lean certification. The v1.4.3 panel completes 1,829 inputs;
79 deadlines, two resource failures and ten syntax declines remain. Increased
resources and experiments do not themselves establish correct completion.

## Resource policy

`KM_RESOURCE_WORKER_MEM_GB` supplies a positive finite RSS limit in GiB for
CB workers and the HT racer. Unlike route-specific `KM_PAR_MEM_GB` and
`KM_HT_MEM_GB`, it survives automatic route normalization and fallback.
Without the explicit resource setting the historical defaults remain intact.
An invalid value emits a warning and retains the route defaults.

This is a per-worker watchdog threshold, not an aggregate reservation. Concurrent
workers, the frontend, output buffers and supervisor also consume memory. Keep
an external Slurm allocation/process-group cap and leave headroom for those
processes. The current investigation stays within the user's 256 GB / six-hour
maximum per ontology. Short diagnostic limits precede larger allocations.

The change affects when a worker is interrupted. It changes neither source
normalization, calculus rules, fragment admission nor acceptance of a completed
answer. Exhaustion still returns failure; it never licenses partial taxonomy
publication. Existing source publication theorems apply to the same accepted
worker results. Exact-source certification gates and experimental semantic
checks remain mandatory before promoting the change. Validation is pending.

## Remaining semantic support

The source inventory includes inverse-role chains, datatype SWRL rules and
SQWRL query built-ins. Inverse roles must survive both clause normalization and
typed RBox metadata. Rule handling requires a stated semantics and a proved
conservative projection or complete implementation; deleting unsupported rules
is not a solution. The source inventory and failed attempts remain evidence.

The [SWRLAPI SQWRL semantics](https://github.com/protegeproject/swrlapi/wiki/SQWRL#semantics-of-sqwrl)
describes query operators as observers that cannot write results back into the
ontology. This suggests a conservative classification projection for rules
whose entire head consists of recognized query operators. It does not justify
ignoring arbitrary SWRL built-ins or mixed logical heads. Initial lexical
inventory finds 94 candidate query-only heads among 95 rules in input 15753;
a structural check and Lean model-preservation proof are still required.
