# ORE 1194 virtual upper-model closure

This experiment represents reciprocal inverse roles only in the
certificate-repair upper model. It leaves the sound EL lower bound unchanged.
The gate admits only reciprocal bridge pairs, rejects virtual roles consumed by
role chains or other residual clauses, and fails closed if certification does
not finish. The prototype is preserved at commit `a7b14af` on branch
`codex/1194-compressed-virtual`; none of it is enabled in production.

## Input and focused tests

- Clause payload: `/tmp/1194.clauses.json`, 1,062,240 clauses, 257 MB JSON.
- Certificate mode: `KM_ELC_CERT=2`.
- Prototype gate: `KM_ELC_CERT_VIRTUAL_BRIDGES=1`.
- Limit: 240 seconds; every run below emitted zero bytes unless a complete
  certificate was available.
- The three focused release tests passed: edge-before-propagation,
  propagation-before-edge, and reciprocal/fail-closed bridge-plan admission.

The 1194 plan admitted 12 directed reciprocal bridge rules and discharged only
their 12 residual bridge clauses. It retained the other 190 residual clauses.

## Results

| Candidate | Binary SHA-256 prefix | Wall | Peak RSS | Output | Result |
|---|---|---:|---:|---:|---|
| Compressed virtual-event queue | `cba040ed` | 240.77 s | 16.13 GiB | 0 B | timeout |
| In-place initial virtual scan, FIFO repair closure | `bd070374` | 240.43 s | 17.35 GiB | 0 B | timeout |
| In-place scan, LIFO repair closure | `9ea56aa6` | 240.30 s | 7.39 GiB | 0 B | timeout |
| Concurrent fresh lower/upper closures | `623f73eb` | 240.15 s | 3.62 GiB | 0 B | timeout |
| LIFO plus dormant-event suppression | `89317a3e` | 240.29 s | 7.41 GiB | 0 B | timeout |

The LIFO change materially reduced memory, but a 600-second diagnostic still
did not finish the upper closure. It peaked at 9.21 GiB and emitted zero bytes.
The concurrent formulation suffered memory-bandwidth contention: at the
240-second cutoff even the lower closure had not completed.

## Work-volume profile

The measurement-only `KM_ELC_PROFILE_PROGRESS=1` build (`342cc257`) reports one
line per ten million work items. The lower EL fixpoint processed about 120
million items and drained its queue. In the certificate upper model, the run
processed another 70 million items by the cutoff while its queue grew to
18,444,440 entries:

```text
KM_ELC_PROFILE_PROGRESS sub_items=43118482 edge_items=26881517 queue=18444440
```

The reciprocal inverse closure adds labels; those labels activate existential
rules; the resulting physical edges create more inverse consequences. The
remaining cost is therefore genuine closure volume rather than initial virtual
edge allocation, state cloning, or dormant worklist events.

## Decision

Reject all candidates as an ORE route. They preserve the fail-closed output
contract but do not close 1194 under 240 seconds. The verified automatic result
remains 591/592. A productive next design must avoid item-at-a-time expansion
of the upper inverse/existential closure, for example through a bulk relational
NF3/NF4 fixpoint or a query-directed certificate that proves all reported
classification pairs without materialising the full upper canonical model.
