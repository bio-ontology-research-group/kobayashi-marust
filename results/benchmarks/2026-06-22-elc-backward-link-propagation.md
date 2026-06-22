# 2026-06-22 — `elc` ELK backward-link propagation + parse-tree discard

Point-in-time snapshot after porting ELK's core EL++ saturation optimisation
(backward-link propagation) and ELK's parse-tree discard into `elc`. Commit
`387b511` on `payg-strategy`. Both changes are **result-identical** to the prior
binary (proven, not approximated): 113 cargo tests pass; 8737 + 16744 byte-clean
vs gold.

## Full-corpus panel (ORE 2015 scored, n=587)

IBEX job `47711101`, base arm = `km classify` production path, 240 s / 20 GB,
gold = Konclude (`ore_canon`). Aggregated from `abl_res/base__c*.jsonl`.

| measure | value |
|---|---|
| ok | **565** |
| timeout | 20 |
| memout | 2 |
| gold_match | **565** |
| unsound | **0** |
| incomplete | **0** |
| unsat_unsound | 0 |
| unsat_incomplete | 0 |
| wall_s avg / median / max | 4.67 / **0.41** / 225.1 |
| peak_mb avg / median / max | 938.6 / **112.1** / 18704.7 |

Fully clean (565 / 0 / 0 / 0), no regression vs the prior 565-ok baseline. The
20 timeouts + 2 memouts are the unchanged hard residual (the live ∀+⊔ disjunction
family + CB-engine blow-ups); they run on the CB/HT path, untouched by the `elc`
work.

## `elc` before/after on the EL giants (the changed path)

Standalone `elc` classify phase on cached clause sets, and full `km classify`
peak RSS. "before" = commit `f0331bb` (filler-label indexing); "after" = `387b511`.

| ont | classify before | classify after | peak RSS before | peak RSS after |
|---|---|---|---|---|
| 8737 | 63 s | **22.4 s** | 9.7 GB | **5.5 GB** (−43%) |
| 16744 | ~48 s | ~38 s | 8.5 GB | **5.6 GB** |

`KM_ELC_PROFILE` on 8737: Edge-rule hashmap lookups **4.33 B → 23 M** (one
`prop.get` per edge instead of `role_supers(r) × nf4_label[d]` probes). The
remaining 4.06 B `add_sub` join-firings are confluence cost that ELK's join
(`SubsumerBackwardLinkRule` × `SubsumerPropagationRule`) pays identically.

The large EL-routed onts now sit at a tight ~5 GB ceiling — the signature of the
parse-tree discard capping saturation memory:

```
868   45.1s 5205MB    10689 44.0s 5207MB    8486  42.4s 4859MB
11745 42.1s 5432MB    9674  36.1s 5208MB    7409  33.8s 4702MB
8737  46.3s 5426MB    16744 38.2s 5666MB
```

(The 12–18 GB onts — 9024, 5303, 9635, 12141, 4205 — are the CB/HT disjunction
path, not `elc`.)

## What was tried and rejected

- **Propagation-Set dedup** (ELK stores propagations in a Set): measured <0.5%
  bucket duplication on 8737, so the `contains` guard only added cost. Reverted.
- **ArrayHashSet small-set subsumers / role-partitioned backward links / dual
  composed-decomposed store**: assessed marginal (giants have large subsumer sets
  where FxHashSet wins; the NF4 sub-side is already cheap) or N/A to `elc`'s
  edge-based design, and high-risk on the central `sub_super` structure. Skipped.

## Open: memory vs ELK/Konclude

`elc` peak on 8737 is now 5.5 GB; ELK classifies the EL giants in far less. Next
step is a head-to-head ELK/Konclude memory comparison to find the remaining gap
(candidate: the FxHashSet-per-context subsumer store, and the `String`-keyed
frontend clause encoding that forces the parse-tree allocation in the first place).
