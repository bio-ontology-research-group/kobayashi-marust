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

→ Round 2 (job 47699271): combine absorbpf with targeted deltas; see below.

## Round 2 — 12 absorbpf-based combination arms (IBEX job 47699271)

New base = `absorbpf` (`KM_ABSORB_PORTFOLIO`+`KM_ABSORB`). Each arm = absorbpf +
one combination delta. Panel: `round2_panel.txt`.

| arm | clean | Δ vs a_base | note |
|---|---|---|---|
| a_base (absorbpf) | 569 | — | |
| a_httrig / a_tabrace / a_elc_tab | 569 | 0 | coverage-neutral, no regress, no recovery |
| a_htrace_stack | 569 ok | +4 incomplete | HT speed-race still makes 12009/15098/6817/7216 incomplete |
| a_elcforce / a_seqorder / a_kitchsink | 568 | −1 | lose 15491 |
| a_corecap8 / a_nocentral | 564/565 | −5 | |
| a_nohtrace | 564 | −5 | fastest (median 0.37s) but loses the 4 HT-dependent onts (5303,9024,12141,9635) |
| a_split | 561 | −9 | |

**No combination beats absorbpf alone.** Merged portfolio across all 44 arms
(round1 ∪ round2, `merged_portfolio.json`) = **569/587**. Recovered over the
true 565 base = exactly the 4 absorbpf onts. The flag-space ceiling is 569.

### Best config per ontology (the deliverable)

For coverage, the per-ont oracle collapses to one config: **absorbpf everywhere**
gives 569, the maximum, and is within noise of optimal on time/mem. The 4
recovered onts each *require* the absorb portfolio (`6212`,`10908` only absorbpf;
`16444` also via nocentral/nohtrace; `15491` via many). The speed-optimal arm
`a_nohtrace` cannot be used globally because the 4 HT-dependent onts
(5303/9024/12141/9635) need the HT fallback racer that it disables. So there is
no useful per-ont split beyond "absorbpf, HT racer on" — a single config.

## Verdict + action

1. **Promote `KM_ABSORB_PORTFOLIO` to default-ON** (it was opt-in in the
   `km classify` orchestrator). Done in `config.rs` (default on; opt out with
   `KM_NO_ABSORB_PORTFOLIO`). Strictly dominant: 565 → 569, 0 unsound, 0
   incomplete, 0 regressions, sequential probe (no memory doubling).
2. **Flag ceiling = 569/587.** The 18 unreachable onts need real work, not
   flags:
   - disjunction family (CB-only): 10702, 1603, 12653, 9540, 15672, 6934 —
     ordered-resolution / case-splitting in root contexts.
   - memory/throughput bombs: 9663, 9724, 7581, 7914, 7499, 10621, 14817,
     15803, 3215, 541 — interning / arena memory reduction.
   - contested gold (unreachable by design, HermiT-proven gold bugs): 2669,
     15516.
3. Levers to keep OFF/routed (confirmed harmful when forced global): orderedall,
   nominals, htblock3 (pairwise), htqo, htracemode, split, corecap, nocentral.

## Round 3 — greedy combinations + the time/mem Pareto (IBEX job 47700083)

9 combination arms anchored on absorbpf, in one batch (so avg/median time/mem
are directly comparable). Panel `round3_panel.txt`; per-ont best config
`round3_peront_bestconfig.txt`.

| config | clean | wall avg | wall med | mem avg | mem med |
|---|---|---|---|---|---|
| absorb (default) | 568 | 3.06 | 0.43 | 769 | 100 |
| htspeed | 569 | 2.92 | 0.44 | 765 | 90 |
| noelc | 562 | ~3 | 0.30 | ~400 | ~30 |
| nohtrace | 564 | ~2.5 | 0.37 | ~360 | 58 |
| lean (no HT, no elc) | 561 | 3.12 | 0.29 | 395 | 25 |
| lowmem (no elc, no central) | 560 | 3.92 | 0.30 | 292 | 22 |
| leanmax (no HT, no elc, no central) | 553 | 3.82 | 0.30 | 286 | 22 |

### The big time/mem finding (structurally predictable)

**The default over-provisions parallel racers.** Median memory drops ~4-5x
(100 -> 22 MB) and median wall ~30% (0.43 -> 0.29 s) under lean, same answers.
Per ontology the effect is far larger: **230 onts have a memory saving > 80 MB
AND > 25%**, several multi-GB (`5519` 6.1 GB->886 MB, `9498` 6.4->1.2 GB,
`3560` 6.4 GB->892 MB). **Almost all 230 are pure EL** (`d_nonEL = 0`,
no union/all/inverse/nominal/card) -- medium-large EL onts where the parallel
`elc`-portfolio + central CB + HT racer balloon peak RSS, when plain `elc`/lean
CB answers in 20-500 MB.

The dominant memory levers are **`elc`-portfolio and `central`**, NOT the HT
racer (nice'd + bounded; wins memory on only 7 onts, time on 5).

Blanket-lean loses coverage (561/553), so the win is a **router**:

| structural signature | route | effect |
|---|---|---|
| `d_nonEL ~ 0`, not huge | lean (no elc-pf, no HT racer) | 4-10x mem, ~30% time, same result |
| `d_nonEL ~ 0`, huge (>~150k ax) | certified-`elc` | the 11460/2397/4604/7246 case |
| `d_union>0` & no inverse/nominal | HT racer on, drop central | HT solves; central CB attempt is doomed (5303: 18 GB->156 MB) |
| inverse/nominal/card present | full CB (central on) | the heavy path; central needed for 1016/11623/11745/6682/7127/7956/9944 |

One feature (`d_nonEL`) drives almost all of it; `central` is needed for a
small enumerable set. Net: ~569 coverage AND median memory cut ~4-5x.

