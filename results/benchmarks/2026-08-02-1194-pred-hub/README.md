# Exact Pred-hub compression gate on ORE 1194

Claude Opus commit `2c8692f` grouped predecessor edges only when their pushed
predicate sets were exactly equal, converted each Pred payload once per sender,
pool entry, and edge label, and retained the original edge-major send order. A
frozen copy of the uncompressed fanout scan compared the complete send sequence
and covered-check count, while receiver-side reference mode re-derived every
payload at arrival.

Twelve focused release tests passed. A 90-second run over the real 1194 clause
set with `KM_PRED_REF_CHECK=1` produced no reference assertion failure. The
unbiased gate then used the same one-worker, no-query, 245-second contract as
the preceding candidates.

| candidate | wall | peak RSS | result |
|---|---:|---:|---|
| `1ef8ee1` | 245.17 s | 2,470,112 KiB | timeout, no output |
| Pred-hub compression (`2c8692f`) | 245.16 s | 2,482,448 KiB | timeout, no output |

The implementation passed its exactness checks but produced no measurable
wall improvement and added about 12 MiB peak RSS. It was therefore not
integrated into `main` and did not receive a full 592-ontology sweep.
