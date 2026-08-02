# ORE 1194 newest-first CB work-off probe

This probe tested whether queue order caused the late Hyper/subsumption storm
seen in the profiled two-thread nominal route. It is a negative result. The
candidate is not integrated.

## Rationale

The `644e57c` profile reached one context with roughly 10 million Hyper
conclusions, 689,000 admitted clauses, 186,000 back-subsumption removals, and a
small pending queue. A plausible schedule-only optimization was to work off
newly admitted strengtheners before older pending clauses, allowing the normal
work-off forward-subsumption check to discard stale clauses sooner.

Detached candidate `6553f37050b9c07957fe014d1ced7f1315dc58eb` added the opt-in
`KM_TODO_LIFO=1` policy. It inserted every newly admitted context clause at the
front of the existing deque. It did not change inference rules, ordering,
subsumption, or the saturation fixpoint. The candidate also retained the
previously measured two-thread nominal schedule and 225-second central cap so
the experiment could reach the profiled tail within the resource contract.

## Validation

- Focused release engine tests: 41 passed, 0 failed.
- Focused release routing tests: 24 passed, 0 failed.
- FIFO and LIFO classifications were byte-identical on all five shipped OFN
  example ontologies.
- Source archive SHA-256:
  `d9e84eaf1f57b2cba32ba9c740d9e5851c68fb0fa561f4cc29acae33027d710f`.
- IBEX build job: `49849002`, with `BUILD_COMPLETE` marker.
- IBEX binary SHA-256:
  `4fef6945dea392d0d672dc04ffd53686405803605654cc9a42f920c21e032507`.

## ORE 1194 production gate

IBEX job `49850227`, array index 33, ran on an Intel Xeon Gold 6248 compute
node through the resumable production runner. The runner recorded an exact
terminal checkpoint, selected route `nominals`, explicit environment
`KM_ROUTE=auto` and `KM_TODO_LIFO=1`, and emitted `TASK_COMPLETE`.

| schedule | status | wall seconds | peak MiB | termination |
|---|---:|---:|---:|---|
| FIFO, `644e57c` | error | 234.5824 | 12909.99 | central time cap |
| newest-first, `6553f37` | error | 234.3745 | 12910.38 | central time cap |

The 0.2079-second wall reduction and 0.39-MiB memory increase are noise. The
candidate produced no taxonomy and did not reduce the saturation tail enough
to pass the 240-second contract. It is rejected, so no 592-ontology sweep is
warranted.

The result narrows the bottleneck: merely processing the newest strengthening
clause first does not prevent the local Hyper family from generating and
admitting the same large antichain. The next candidate should reduce duplicate
or subsumed conclusions before `add_clause`, or exploit structure in the
dominant Hyper family, instead of changing deque order.
