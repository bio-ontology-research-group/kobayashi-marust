# 2026-06-25 — fast-Ht full-corpus sweep with the ≥n recognition rule

Point-in-time snapshot. Gold = Konclude (587 ORE 2015 onts). See `README.md` and
`docs/CONTESTED-GOLD.md` for the gold rule.

## What was measured

The **standalone fast hypertableau** (`tableau_cli` `KM_HT=1`) FORCED onto every
routable ontology, carrying the newly ported **≥n recognition rule** (mixed
concept+Eq head, commit `3002f2c`) + the self-loop matching fix (`592cf27`).

- Config: `KM_HT=1 KM_HT_FORCE=1 KM_HT_QMERGE=1`, `HT_TIMEOUT=240`, build of HEAD
  `3002f2c` on IBEX (job 47783564; binaries from build job 47783535).
- Driver: `harness/ht_runone.py` (ofn → cb_to_ht → `tableau_cli KM_HT=1`, mapped +
  canonicalised the same way gold was made, compared to `gold/konclude__*.sig.gz`).
- `ht_runone`'s `routable` guard (`dropped==0 ∧ ¬fenced ∧ ¬inverse`) means only the
  no-inverse fragment reaches the Ht, so `KM_HT_FORCE` is sound here. This is a
  STANDALONE-Ht measurement, not the production hybrid (which routes the residue
  to CB/elc); the timeouts / transitive-incompleteness below are where the Ht
  alone is weaker than the hybrid, not where the reasoner ships.

## Result (584 of 587 produced a line; 3 giants no line / wrap_fail)

| metric | value |
|---|---|
| status `ok` | 509 |
| `gold: MATCH` | **503** |
| `gold: DIFF` | 12 |
| `DIFF_consistency` | 6 |
| timeout (240 s) | 63 |
| wrap_fail (harness) | 6 |
| MATCH wall_s | median **0.12**, mean 10.85, max 240.3 |
| MATCH peak_mb | median **10.4**, mean 83.2, max 2759.7 |

Sound-vs-complete split of the 12 `gold: DIFF`:
- **unsound = `15516`, `2669` only** — both are KNOWN CONTESTED GOLD (Konclude gold
  is wrong; HermiT + KM are right — `docs/CONTESTED-GOLD.md`). NO new unsoundness
  from the recognition rule.
- **incomplete-only = `1016`, `10702`, `11623`, `7216`** — the known transitive-role
  / live-disjunction-family gaps (mode-1 subset blocking is incomplete on
  transitive roles; the sweep forces the Ht onto those too).
- `DIFF_consistency = 13912, 15288, 443, 6720, 7052, 8941` — `8941` + `13912` are
  also known contested gold; the rest are consistency-verdict differences on the
  transitive / disjunction fragment.

## The recognition rule's specific reach (cardinality fragment)

99 number/cardinality (`has_number`) onts routed to the fast Ht; **80 gold-MATCH**,
85 ran ok. Before `3002f2c` every mixed concept+Eq head bailed `unsupported`, so the
fast Ht returned None and `run_json` fell through to the (documented-unsound) legacy
Tableau. The whole cardinality fragment is now handled by the SOUND fast Ht.

## Standing-goal targets

| ont | before | now | wall_s | peak_mb |
|---|---|---|---|---|
| **10908** | false-UNSAT (legacy fallback) | **gold-MATCH** | 36.5 | 4.5 |
| **15672** | timeout / family | **gold-MATCH** | 3.0 | 14.8 |
| 10621 | timeout | timeout (244 385 clauses — pure scale) | — | — |

10908 (SHOQ: number + nominal, NO inverse — inverse was never the blocker) and
15672 are finalised. 10621 remains a throughput problem (separate from this rule).

Raw per-ont JSON: `2026-06-25-ht-recognition-sweep.jsonl`.
