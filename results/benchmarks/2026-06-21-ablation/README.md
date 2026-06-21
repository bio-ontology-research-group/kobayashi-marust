# Per-feature ablation sweep — ORE 2015 — 2026-06-21

Goal: turn every KM feature ON individually across the full scored corpus,
measure (time, mem, sound, complete), find what moves the lever, then combine
winners and rerun until the best config **per ontology** (not on average) is
known.

- Corpus: 587 scored onts (those with a Konclude gold `.sig.gz` AND a corpus
  `.owl`). Gold = Konclude. Timeout 240 s, memcap 20 GB, `KM_PAR_MEM_GB=18`,
  `KM_THREADS=16`. Binary = HEAD `7437965` rebuilt on IBEX.
- Baseline = `km classify` with all features at their **defaults** (NOT the
  tuned production config), so each lever's contribution shows as a clean delta.
- Each arm = baseline + one `KM_*` delta. Harness in `results/ablation/`
  (`feat_ablate.sbatch`, `sig_cmp.py`, `ablate_agg.py`).
- "clean" = status `ok` AND km sig byte-equal to gold (split into UNSOUND =
  km-extra subsumptions, INCOMPLETE = gold-extra). 0 unsound is the hard floor.

## Round 1 — 32 single-feature arms (IBEX job 47693697)

Full panel: `round1_panel.txt`. Per-ont oracle: `round1_portfolio.json`.
Raw per-(arm,ont) records: `round1_jsonl.tgz`.

### Headline

| arm | clean | Δ vs base | unsound | incomplete | note |
|---|---|---|---|---|---|
| **absorbpf** (`KM_ABSORB_PORTFOLIO`) | **569** | **+4** | 0 | 0 | dominant lever; recovers 6212,10908,15491,16444; 0 regress |
| base (all defaults) | 565 | — | 0 | 0 | matches known production baseline |
| elcforce / seqorder / noearlyunsat / noshare / nodatatypes | 566 | +1 | 0 | 0 | each only recovers 15491 (easy) |
| orderedall | 540 | −25 | 0 | +24 incmp | forcing total order globally = harmful |
| nominals | 491 | −74 | 0 | — | forcing nominals globally = catastrophic (routed feature) |
| htblock3 (pairwise) | 561 | −4 | 0 | — | under-folds canaries 12141/5303/9024 (known risk) |
| htqo | 563 | −2 | 2 | 2 | QO produces wrong taxonomy → confirms QO dead-end |
| htracemode | 561 | +1/−5 | 0 | +4 | HT speed-race loses onts needing full CB time |

### Levers that move coverage

- **`KM_ABSORB_PORTFOLIO` is strictly dominant**: it recovers ALL FOUR onts any
  single arm recovers (6212, 10908, 15491, 16444), with zero unsound, zero
  incomplete, zero regressions. Single-arm portfolio coverage = 569 = absorbpf.
  → Promote (default-on or always-in-portfolio).
- Every other "+1" arm only recovers 15491, which absorbpf already gets.

### Time / memory (over the 453 onts clean in every arm)

- base avg/median wall = 2.01 / 0.43 s; absorbpf = 2.49 / 0.37 s (slightly
  higher avg from the sequential plain-then-absorbed probe, but lower median).
- `nohtrace` is the fastest (1.68 avg) — the HT fallback racer costs ~0.3 s avg
  spawn overhead even when unused — but loses 4 onts that need HT (12141, 5303,
  9024, 9635). Pure speed-vs-coverage tradeoff → per-ont routing.
- `noelcpf` slashes memory (median 16 vs 60 MB; the certified-elc racer runs a
  parallel attempt) but loses 5 onts (11460, 2397, 4604, 7246). Same tradeoff.
- Forcing `seqorder` everywhere is slower (2.94 avg) than the auto-router in
  base — auto-routing is correct; do not force globally.

### Regressions / unsound (kept OFF or routed)

`orderedall` (+24 incomplete), `nominals` (−74), `htblock3`/`htqo`/`htracemode`
/`split`/`corecap4`/`nocentral` all net-negative when forced globally. `htqo`
and `nochaindom` are the only arms that introduce **unsound** — both stay off.

### The hard residual — 18 onts clean by NO arm

`10621 10702 12653 14817 15516 15803 1603 2669 3215 541 6934 7499 7581 7914
9540 9663 9724 15672`

- disjunction family (CB-only): 10702, 1603, 12653, 9540, 15672, 6934
- contested gold (HermiT-proven gold bugs, unreachable by design): 2669, 15516
- memory / throughput bombs: 9663, 9724, 7581, 7914, 7499, ...
- These need algorithmic work (ordered resolution / memory reduction), not flags.

→ Round 2 (job 47699271): combine absorbpf with targeted deltas; see round2.
