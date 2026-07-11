# KPSet, disjunct extraction, successor extension, and role automata

This run implements and validates the four production paths identified by the
remaining-five comparison with Konclude:

- saturation-seeded KPSet predecessor ordering, persistent classification
  state, possible-subsumption maps, pseudo-model prechecks, and completion
  message analysis;
- saturation disjunct common-concept initialization and incremental extraction;
- deterministic predecessor restriction collection and resolved saturation
  successor-extension/cache lookup;
- retained source RBox data and Konclude's role-chain automata preprocessing in
  the production bridge.

## 7914 reduction and Konclude comparison

The first sound-gated implementation still produced 30 extra and five missing
subsumptions on `7914`. Disabling saturation and its cache produced the same
30/5 result, locating the remaining defect in production completion/RBox
construction rather than the new saturation heuristics. An earlier experiment
that allowed classification-message analyzer decisions produced 516 extra and
five missing subsumptions; those decisions were therefore rejected and remain
diagnostic only.

Konclude's full taxonomy (Slurm job `48599118`) showed that all 30 extras came
from three concepts which Konclude classifies equivalent to `owl:Nothing`. The
five missing edges are direct taxonomy edges in Konclude:

```
UBERON_0003071 <= UBERON_0010312
UBERON_0005087 <= UBERON_0004121
UBERON_0009078 <= UBERON_0010314
UBERON_0010092 <= UBERON_0010314
UBERON_0010096 <= UBERON_0010314
```

`ddmin_7914.py` reduced the `0005087 <= 0004121` proof to 17 logical
axioms. The proof uses an inverse role pair, a transitive role, both
`p o r <= r` and `r o p <= r`, and recursive recognition at a chain-reachable
node. Konclude and HermiT derive the pair on the reduced module; KM did not
until the production RBox fixes below.

## Production defects fixed

The comparison exposed five concrete deviations from Konclude:

1. The Rust frontend extracted role chains and transitivity but omitted the
   RBox records from `FrontendResult`, the worker JSON protocol, and the
   `cb_to_ht` bridge call. The records now survive the complete pipeline.
2. The raw role-chain detectors reordered the two body roles but checked the
   head against the unreordered endpoints. Chain and transitivity recognition
   now use the oriented endpoints.
3. Konclude seeds every indirect-super-role list with the role itself and also
   retains direct super-role links. The bridge now does both before computing
   strict transitive closure.
4. The automata preprocessor allocated new concept tags from the arena length.
   The bridge has reserved tag ranges, so this could collide with existing
   concepts. Allocation now starts after the largest existing tag, matching
   Konclude's `getNextConceptID()` behavior.
5. Konclude's signed role representation implicitly supplies the inverse of a
   chain. Because KM represents inverse roles as separate objects, it now
   explicitly materializes `R2^- o R1^- <= S^-` for every
   `R1 o R2 <= S`, including inverse transitivity.
6. Preserving the RBox exposed stale routing fences. Symmetric-role metadata is
   now compiled as Konclude's self-inverse role, while the bridge admits the
   legacy `inverse+number(SHIQ)` and `inverse-functional` markers whose full
   semantics are already present in the normalized equality/role clauses. All
   other unsupported fences still reject the bridge.

The reduced 7914 production probe now reports both `pairwise=true` and
`readoff_has=true`. A permanent non-ignored regression test covers this
inverse-chain recognition core.

## Validation

Source was built and tested on `ws`. The complete Rust suite passes:
**1,441 passed, 0 failed, 7 ignored**. Focused coverage includes KPSet
root-first ordering, read-off/classification-message coupling, disjunct
common-concept intersection, successor extension/cache resolution, RBox JSON
retention, oriented role-chain materialization, inverse-chain construction,
the minimized 7914 recognition proof, symmetric-role RBox compilation, and
bridge-only handling of legacy fast-tableau fences.

The four cases unaffected by the final inverse-functional routing change used
build job `48604926` (SHA-256 `4da15917197e216d1bd74e07be8ca9a04f6f7707d6c98a4cb2078da4aca4c495`)
as jobs `48605307`/`48605308`. `9724` used final build job `48606237`
(SHA-256 `21895fd4c3d1dfef5775d3355ac35bccb5234c135b7be42bf9f7e0f4fe3c91d4`)
as job `48606699`. Each task used 8 CPUs and 64 GB, a 28-minute process
timeout, a 10-minute saturation budget, and output comparison against stored
Konclude signatures. The bridge watchdog was explicitly raised to 58 GB; an
earlier attempt accidentally left its 12 GB default in place and measured only
the fallback engines, so it was discarded.

| ontology | status | Konclude comparison | wall | peak RSS |
|---|---|---:|---:|---:|
| 3215 | timeout | not run | 28:00.07 | 2.13 GB parent* |
| 7914 | timeout | not run | 28:00.01 | 25.19 GB parent* |
| 9663 | timeout | not run | 28:00.06 | 39.67 GB parent* |
| 9724 | timeout | not run | 28:00.02 | 10.87 GB parent* |
| 14817 | timeout | not run | 28:00.04 | 1.35 GB parent* |

`*` `/usr/bin/time` records the orchestrator parent rather than the complete
process tree. Slurm observed substantially higher task memory, including about
61.6 GB for `3215`; these figures are retained only as the script's raw metric.

## Outcome

**Zero of the remaining five ontologies is solved under the 28-minute
benchmark.** All five now enter the production Konclude bridge and report zero
unsupported source axioms, so the result is no longer explained by missing
RBox transport or routing. Every case exhausted the 10-minute saturation budget
and discarded that pass. Final round-zero classification progress was:

| ontology | subjects reached | deferred subjects |
|---|---:|---:|
| 3215 | 1 / 54,973 | 0 |
| 7914 | 769 / 17,680 | 77 |
| 9663 | 9,537 / 58,192 | 72 |
| 9724 | 193 / 23,136 | 128 |
| 14817 | 47,041 / 58,364 | 60 |

The minimized 7914 proof is fixed, but the full ontology repeatedly spends
roughly 10--17 seconds on read-off or pair probes that stop and defer. The next
work is therefore not another role-chain semantic patch: it is retaining useful
saturation results at budget expiry and matching Konclude's cheap KPSet
candidate pruning/cache reuse so those hard subjects do not restart expensive
completion probes.
