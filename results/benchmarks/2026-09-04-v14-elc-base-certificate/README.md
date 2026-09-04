# Copy-free clean EL certificate

`repair_certify` previously deep-copied the completed EL state before checking
whether that unchanged state already satisfied every residual clause. The
candidate performs that same full residual-clause round over the base state
first. A clean round is the existing first pass's `Pristine` outcome and can
return immediately without allocating the fork.

If the base is not a model, the candidate hands the enumeration index built by
that round to the first repair pass. The fork starts with the same labels,
edges, and edge epoch and an empty journal. A focused structural test verifies
that refreshing the handed-off index produces exactly the same buckets and
bucket order as a fresh build over the fork. End-to-end tests cover both the
clean shortcut and repair after a failed base check.

This optimization changes no EL completion rule, residual clause, repair
choice, model criterion, or fallback. It therefore preserves the same exact,
fail-closed result contract and does not change the certified calculus.

## IBEX evidence

Build job 51335650 consumed the isolated candidate at commit
`1e83fe0fd9670c46f9cd12ff4cec8bab8ccb2de1` and produced binary SHA-256
`03e9177dc76cd2e052a99291a564f7b283cad933b8d87327a8e781f7c17fe5d3`.
Array 51335651 tested eleven affected ontologies five times each. It produced
55 results, 55 checkpoints, and 55 completion markers. All 55 runs returned
`ok`, matched retained gold, and selected the expected automatic route.

For ORE 14312, the five-run medians were:

| Measure | KM median | Best correct external target | Strict win |
|---|---:|---:|---:|
| Wall time | 1.3680 s | 1.4472 s | yes |
| Peak process-tree RSS | 201.58 MiB | 279.24 MiB | yes |

The affected panel also included ORE 3414, 457, 15491, 7956, 9020, 2397,
10032, 7127, 16444, and 9724. Their signatures remained exact. A combined
source archive containing this optimization and the ORE 11316 routing change
has SHA-256
`a62fb8701e3a9988788f430fbb0d4cacab011b3cfe7a25e0d4b861f41bb49e9c`.
Build job 51336953 and panel 51336954 passed the independent integration gate:
all ten results and checkpoints were exact. The combined five-run medians were
1.3823 seconds and 201.38 MiB for ORE 14312, and 0.1934 seconds and 36.64 MiB
for ORE 11316.

Full automatic-route array 51337157 then produced exactly 592 results, 592
checkpoints, and 592 completion markers. All 592 status values are `ok`, and
every status and signature SHA-256 is identical to the preceding accepted
sweep. The retained result archive has SHA-256
`4a88e5cc6712472341bd77ccb6168e36fbacb03d0c00f75212af5686955adf67`.
The one-shot sweep was strictly faster on 510/589 comparable inputs, lower in
peak memory on 529/589, and won both measures on 498/589. Its mean and median
wall times were 1.4613 and 0.1144 seconds; mean and median peak RSS were 207.55
and 23.58 MiB.
The ORE 14312 recovery therefore raises the evidence-composite strict joint
score from 526/589 to 527/589, leaving 62 comparable residuals.
