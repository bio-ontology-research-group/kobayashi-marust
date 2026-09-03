# Wide-role EL context-parallel routing

This experiment extends the automatic context-parallel EL schedule to one
additional source-feature family.  The common gate still requires an exact,
ABox-free EL terminology.  The added family is bounded to 150,000--200,000
logical axioms, 60,000--75,000 classes, 90,000--100,000 existential
restrictions, 20--32 object properties, no role chains, and at most 40 MiB of
source.  Projection over all 592 retained profiles admits exactly one new
ontology, ORE 7567, and admits no ontology outside the bare `elc` route.

The change is scheduling-only.  It changes the firing order of the same finite
monotone EL rule set and therefore preserves the least fixpoint.  Existing
cross-worker tests and the corpus confirmation below establish byte-identical
output; no CB-calculus rule, ordering, or redundancy criterion changed, so no
Lean re-certification is due.

IBEX build job `51254739` built integrated source commit `4968149` and produced
binary SHA-256
`8a5d73d43fcabffa0631cf561360f23f1b20b74c918b074a842045b0e0603587`.
Confirmation array `51254778` compared the preceding automatic binary with the
integrated automatic route for ten repetitions per arm on Intel Xeon Gold 6248
nodes.  The array produced exactly 20 results, 20 checkpoints, 20 scheduler
outputs, and 20 completion markers.  Every result returned `status=ok`, used
route `elc`, matched the retained gold signature, and all repetitions shared
one signature.

| arm | median wall (s) | median peak RSS (MiB) |
|---|---:|---:|
| preceding automatic route | 1.90205 | 237.755 |
| integrated automatic route | **1.7043** | **277.515** |
| best external target | 2.0761 | 764.39 |

The integrated route is 10.4% faster than the preceding route.  Its memory
increase remains 2.75 times below the external target.  ORE 7567 therefore
becomes a strict win on both measures, raising the current evidence-composite
score from 513/589 to **514/589** and reducing the residual set from 76 to 75.

The complete source and raw-job evidence is archived at
`.work/artifacts/v14-elc-wide-role/complete-evidence.tar.gz`, SHA-256
`0a68546e13e43a822831f3a8f02dfd43ba2f6b391885f46dacd57e8cc1c1bb17`.
The source-only archive has SHA-256
`03a38088ba12f327f8029777b439076c43486840ff4cf3420b7f8d6bea497b68`.
