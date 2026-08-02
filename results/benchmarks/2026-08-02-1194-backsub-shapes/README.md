# ORE 1194 backward-subsumption shape profile

This instrumentation-only run refines the earlier `add_clause` profile by
counting the shapes and candidate volume of every backward-subsumption call.
It uses the exact production CB path with two threads and a 225-second central
cap. The run failed closed, as expected, after 234.7436 seconds at 12,903.75
MiB. It did not publish a taxonomy and does not change the standing 591/592
coverage result.

## Provenance

- Instrumentation commit: `d6a28b2`
- Source archive SHA-256:
  `c091d0791e5780646120799a821636776138c40f5863a24d63c3c95d6f4cb0e1`
- IBEX build job `49854048`, with `BUILD_COMPLETE`
- Binary SHA-256:
  `eae9f09b78f2c8f5027e580ff3b036e407aca4ea038269d46c25d714e58f3678`
- Profile job `49854075`, with checkpoint and `TASK_COMPLETE`
- Immutable root:
  `/ibex/scratch/hohndor/km/profile-d6a28b2-backsub-shapes-20260802`

The explicit route was exact CB with `KM_THREADS=2`, `KM_NOMINALS=1`,
`KM_ABSORB=0`, `KM_KEEP_CHAIN_AXIOMS=1`, `KM_COMP_IND_BITS=15`, and all
portfolio/race/retry paths disabled.

## Final 600,000-iteration checkpoint

| measurement | value |
|---|---:|
| backward-subsumption calls | 3,650,589 |
| calls with an empty head | 0 |
| calls with an empty body | 3,650,589 |
| posting candidates visited | 21,716,431 |
| exact strengthening checks | 976,023 |
| clauses removed | 776,522 |
| backward-subsumption time | 75,268.7 ms |
| forward-subsumption time | 44,861.7 ms |
| total `add_clause` time | 127,613.4 ms |
| Hyper time | 25,153.5 ms |

Every call had an empty body and a non-empty head. Consequently, an active
body-atom posting cannot reduce this workload. The selected rarest head posting
averaged only 5.95 candidates per call, and only 0.21 clauses were removed per
call. The generic candidate `Vec` and removal `HashSet` therefore perform
millions of heap allocations around very small collections. This evidence
selects direct posting iteration plus an inline small removal buffer as the next
exact, schedule-preserving candidate. It changes neither the strengthening
predicate nor the calculus.
