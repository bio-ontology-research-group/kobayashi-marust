# Cardinality-aware partition assignment and a rotated residual scan

> Read [`PROVENANCE.md`](PROVENANCE.md) first. This report is retained verbatim
> from the 2026-08-01 experimental binary, which is not an ancestor of the
> current branch. Only the cardinality half of it landed; the rotated-scan rows
> measure a change that did not.

Two changes to the certified-EL repair search, plus the measurement that says
what now stops ORE 1194. The search improvements are real and are kept. The
1194 gate still fails, and the reason has moved: the repair search is no longer
the binding cost.

All runs are local single-ontology diagnostics on `leechuck-office` under
`systemd-run --user --scope -p MemoryMax=20G -p MemorySwapMax=0`, the production
240 s / 20 GiB contract. No corpus sweep and no IBEX compute was used.

## Inputs

- Ontology `/tmp/ore_ont_1194.owl`, SHA-256
  `72082c4ce0e5008589256eba0aa50957c04d294ff1e065b18cf014cc59b870e2`.
- Frontend clause payload SHA-256
  `5c0fdb40e5252e1d3092127bbe77c4cba74abf9da27041767f5c2959c2bc7da0`, byte
  identical to the payload used by the 2026-08-01 negative-result run, so the
  rows below compare directly against it.
- Binaries in `input.sha256`.

## What changed

**Cardinality-aware partition assignment.** The residual holds an exhaustive
disjoint partition between a `≤n R.C` definer and a `≥m R.C` definer, so every
element takes a side. The certificate model keeps one canonical node per skolem
function, shared across every source element, so a `≥n` distinctness clause
`G(x) ∧ f_i(x) ≈ f_j(x) → ⊥` pins two fixed nodes apart for the whole model.
Identifying them to satisfy an at-most bound at one node makes that clause false
at every node carrying the guard.

The search now reads both shapes off the compiled residual and uses them two
ways. When an at-most bound is violated it picks an identification the model may
actually make, preferring one that does not clash, instead of taking the first
pair the clause enumerates. When a covering disjunction offers a side that a
qualified at-most bound makes locally unsatisfiable at that node, that side
drops out of the preferred choice tier. Neither is a ban: if nothing else
survives, the choice is still taken and the model is still validated in full.
A violated at-most bound whose every identification is pinned apart is now
charged to the choice that made the node over-full, at the point of detection,
rather than surfacing as a `⊥` several closure rounds later where the blame no
longer reaches it.

**Rotated residual scan.** A round that fills its violation cap on one clause
has verified every clause before it and learned nothing about the clauses after
it. Restarting the next cycle at clause 0 re-verified that clean prefix against
the whole model every round. The scan now resumes at the clause that filled the
cap and wraps around. A cycle still visits every clause, so the accepting
verdict is unchanged.

Neither change touches `cert_round`'s checking, the EL completion rules, or the
acceptance criterion. A pass model is still accepted only when a full cycle
finds every residual clause satisfied under the quotient, the base-satisfiable
named witnesses still have to survive, and the per-subject intersection
criterion is unchanged.

## Search trajectory on 1194

| | conflicts | restarts | rounds reached | scan per round | peak RSS |
| --- | --- | --- | --- | --- | --- |
| previous HEAD | 7 | 7 | 9, re-derived each restart | 1.7 s rising to 12.4 s | 5,439,932 KiB |
| partition assignment only | 0 | 0 | 23, one monotone pass | 1.7 s rising to 12.5 s | 5,594,140 KiB |
| plus rotated scan | 0 | 0 | 23, one monotone pass | 1.65 s to 1.83 s | 10,675,524 KiB |

The previous HEAD reached round 9, conflicted on a forced-distinct witness pair,
banned one `(node, clause, disjunct)` triple, and restarted, re-deriving rounds
1 through 9 with identical violation counts at about 16 s per restart. Seven
restarts fit in the budget and none of them learned anything transferable.

The partition assignment removes that loop outright: zero conflicts, zero
restarts, one monotone pass. The rotated scan then cuts the per-round scan from
12.4 s to about 1.8 s, a factor of about 7, with `from_clause` advancing
0, 120, 127, 145, 152, 165 as each clause family is cleared. Total scan time
across the run falls from 126.6 s to 39.2 s.

`card_demoted` is 0 on 1194. The partition-side demotion never fires here: the
at-most bounds have bound 2, so a node over the bound carries at least three
qualifying successors and some pair among them is free to merge. What removes
the conflicts on this ontology is the identification-legality filter, not the
side demotion. Both are kept, and the synthetic tests cover each separately.

## Where the 240 s actually goes

Instrumenting the phases accounts for the whole budget on the final binary
(`gate-final-240s.log`, and `check-mode-baseline.log` for the first row):

| phase | wall | note |
| --- | --- | --- |
| parse, normalise, EL saturation, residual compile | 96.2 s | `KM_ELC_CERT=1` reaches its first check at 96.19 s / 3,289,536 KiB |
| fork of the saturated structure | 1.8 s | 78,367,893 subsumptions over 43,891,310 edges |
| repair rounds 1 to 22 | 42.3 s | 2,197,601 repairs, 17 merges, 6 clause families cleared |
| round 23 | 100.5 s, incomplete | scan finished in 1.65 s; the apply and re-close did not finish |

Round 23 collects 80,646 violations of a clause family the earlier rounds never
reached, applies them, and re-closes. It was still inside that closure when the
240 s wall arrived. This is the model-scale wall the 2026-08-01 negative result
identified: repairing a role bridge mirrors the role graph, and each mirrored
edge fires qualified existential eliminations across a 45M-edge structure.

So the repair search is no longer what stops 1194. Its scan costs 1.8 s per
round and its whole round loop costs 42.3 s of the 240 s. The budget is spent on
96.2 s of base saturation that has to happen before any certificate work, and on
one EL re-closure after mirroring a role bridge.

## Batch size

The violation cap is a batch size, not part of the acceptance test: whatever a
cycle leaves unvisited the next cycle finds, and a model is accepted only after
a full cycle reports nothing. `KM_ELC_VIOL_CAP` exposes it for measurement and
defaults to the unchanged 100,000.

Raising it to 1,000,000 reaches 1,997,333 repairs at 9.7 s into the pass, where
the default cap needs 42.3 s for 2,197,601 repairs, so the repair loop runs
about 4.6 times faster. It does not change the outcome: 240.81 s, 13,144,196
KiB, no taxonomy, because the same round-23 closure follows. Peak RSS rises with
the cap, so the default stays at 100,000.

A cap far below the available work spends a round per handful of repairs and can
exhaust the 64-round budget before the model closes. That declines, which is
fail-closed; it never produces a different answer. A test pins exactly that: over
caps 1, 16, 64 and 100,000, every batch size that certifies produces the same
taxonomy, the same residue and the same consistency verdict.

## Gate result

| run | budget | terminal status | wall | peak RSS | output bytes | taxonomy |
| --- | --- | --- | --- | --- | --- | --- |
| `KM_ELC_CERT=repair`, gate binary | 240 s / 20 GiB | 124, killed on timeout | 240.68 s | 11,404,928 KiB | 0 | none |
| `KM_ELC_CERT=repair`, cap 1,000,000 | 240 s / 20 GiB | 124, killed on timeout | 240.81 s | 13,144,196 KiB | 0 | none |
| `km classify`, automatic route | 240 s / 20 GiB | 1, `worker engine exited -1` | 30.73 s | 18,954,648 KiB | 0 | none |
| `KM_ELC_CERT=repair`, cost probe | 900 s / 20 GiB | stopped, still in round 23 | over 850 s | | 0 | none |

Trajectory of the gate run: 22 rounds completed, the last at t=42.4 s into the
pass, **0 conflicts and 0 restarts**, then round 23 consumed the remainder
without completing. The output file is 0 bytes and does not parse as JSON, so
there is no taxonomy, complete or partial.

The 900 s row is a cost probe for the inverse-bridge closure, not a gate, and it
is not a closure of any kind: it completes the same 22 rounds and then stays
inside round 23 for more than 850 s without producing a taxonomy. The gate is
the 240 s row.

1194 is not closed. Peak RSS stays inside the 20 GiB cap on the certificate
runs, unlike the 2026-08-01 reverted experiment which reached 25,035,308 KiB on
an extended budget; that experiment also added a per-clause violation cap, which
is not part of this change.

The automatic route is unaffected either way. Running `km classify` on 1194 with
`KM_ELC_DEBUG=1` emits zero `KM_ELC_CERT` lines: the route is `nominals`, whose
settings include `KM_NO_ELC=1`, and `Config::elc` reads that variable, so the
certified-EL worker and the certified-elc portfolio racer never start. The
production row is the CB engine reaching the 20 GiB ceiling at 30.73 s and
returning no taxonomy, on a route this change does not touch.

## Controls

Release suite on the gate binary's source: **1,883 passed, 0 failed, 8
intentional ignores**, across the library and every integration target, run
serially with `--test-threads=1`. That is the 1,873 of the previous commit plus
the 10 tests added here. Build and suite both returned rc=0 with zero `^error`
lines.

Per-source witness projection, reported by the certificate at startup and
analysed in [`PER-SOURCE-WITNESS.md`](PER-SOURCE-WITNESS.md): 499,902 alive
nodes, 78,367,893 subsumptions, 43,891,310 edges, average label 156. A full
unravelling would need 43,891,310 new nodes carrying 6,847,044,360 projected
facts, which is out of reach of the 20 GiB cap by about two orders of magnitude.
The selective variant over the 36 pinned witnesses needs 148 new nodes and
23,088 facts, which is affordable but addresses a 148-instance phenomenon that
the identification-legality filter already handles at zero conflicts. Neither
was implemented.

| ontology | route | result |
| --- | --- | --- |
| `10702` | automatic | exact match to Konclude gold, 2.58 s, 12,696 KiB |
| `12653` | automatic | exact match to Konclude gold, 0.15 s, 32,000 KiB |
| `1034` | automatic | consistent, 0 subsumptions, 0 unsatisfiable, matching the stored gate row |
| `2237` | automatic | consistent, 0 subsumptions, 0 unsatisfiable, matching the stored gate row |
| `7499` | automatic | consistent, 36,145 subsumptions, 97.05 s, 2,371,644 KiB |
| `12653` | forced `KM_ELC_CERT=repair` | partial certificate, 170 subjects answered, 21 unresolved |
| `10702` | forced `KM_ELC_CERT=repair` | declines, exit 3, no output |

The two forced rows exercise the changed code directly and show both of its
exits: a partial certificate that hands its residue to the context engine, and
an outright decline. The 7499 row is within measurement noise of the 86.74 s /
2,409.59 MiB recorded in the residual audit for that route on a quieter host.

## Files

- `gate-final-240s.log`: the gate on the final binary, with per-phase timings.
- `gate-cardinality-only-240s.log`: partition assignment before the rotated scan.
- `gate-cap1m-240s.log`: the same gate at `KM_ELC_VIOL_CAP=1000000`.
- `check-mode-baseline.log`: `KM_ELC_CERT=1`, isolating parse and saturation.
- `production-route-240s.log`: `km classify`, showing no certificate worker runs.
- `residual-index-dump.log`: per-index residual families, with each cover
  disjunct annotated by what asserting it would activate.
- `input.sha256`: ontology, clause payload and binary hashes.

## Proof obligations

No Lean re-certification. The Lean formalisation covers the CB disjunctive
context calculus, which is not involved here. What changed is which repair step
the certificate search tries first and where its scan begins, inside a procedure
whose acceptance predicate is untouched.

1. The EL completion rules, the residual compilation and `cert_round`'s checking
   are unchanged, so a pass model satisfies exactly the same condition as before.
2. Acceptance still requires a full cycle over every residual clause reporting
   no violation, the survival of every base-satisfiable named witness, and the
   unchanged per-subject intersection criterion. Nothing added here discharges a
   residual clause.
3. The pinned-apart relation is used only to order and filter candidate repair
   steps. A pair wrongly called pinned only costs the search a merge it could
   have made; the model it builds instead is still validated in full. A pinned
   pair the recogniser misses leaves the search exactly as it was.
4. Scan rotation visits every clause in a cycle, so the `clean` verdict is
   independent of the start offset. A test asserts that directly, over every
   start offset, for both a violated and a satisfied residual.
5. The violation cap bounds one batch, not what is checked. Splitting the same
   repairs across more batches reaches the same fixpoint, and a test asserts the
   accepted taxonomy, residue and consistency verdict agree across batch sizes.
6. The round, restart and refinement budgets are unchanged, so the search
   terminates exactly as it did.

## What this does not do

It does not close 1194, and it does not make the certified-EL route reachable on
1194. Closing it needs the 96.2 s base saturation and the role-bridge closure
addressed, and then a routing change, since the automatic route excludes the
certificate worker. The repair-search work here is finished: its scan is 1.8 s
per round and its conflict count is zero.
