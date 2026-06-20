# ore_ont_5303 — the live ∀+⊔ disjunction family, attempt history

This is the running log of every attempt to make KM classify **ore_ont_5303**
sound + complete in budget. 5303 is the canonical HT-fragment member of the
"live ∀ + ⊔ disjunction family" (`10702, 1603, 12653, 9540, 15672, 6934` are the
others, but they carry inverse / nominals / cardinality, so KM's hypertableau is
unsound on them — they are CB-only; 5303 is **ALC(H)**, the only one KM's HT can
soundly attempt).

Keep this current. Each entry: what was tried, the result, why it failed (or how
far it got). The point is to never re-run a falsified lever.

## The ontology

- `~/ore2015/pool_sample/files/ore_ont_5303.owl` (41 KB, OWL functional syntax),
  the `chemtop` chemistry ontology. **94 named classes = 94 satisfiability
  queries.** All 94 are satisfiable (no unsat concept; the ont is consistent).
- Gold (Konclude): 238 subsumptions. `gold/konclude__ore_ont_5303.owl.sig.gz`.
- cb_to_ht TInput (`tin5303.json`): **clauses=937, dropped=0, fenced=0,
  nominals=0, inverse=false, number=false, queries=94.** Fully inside the
  cache-tableau / Ht ALC(H) fragment (dropped=0) — the old "withheld by the
  transitive-role guard / 0 composition clauses" claim is **stale**.
- Structure: 868 clauses, 33 disjunctive heads = **17 global ⊤-disjunctions**
  (inherent `⊤ ⊑ A ⊔ B`, all-positive disjuncts — nothing to absorb) + 16
  triggered; 26 binary + 7 ternary. Several global disjunctions are **exclusive**
  (`⊤ ⊑ A ⊔ B` paired with `A ⊓ B ⊑ ⊥`), e.g. Peptide ⊔ NucleicAcid,
  Hydrocarbon ⊔ Carbohydrate.

## HermiT ground truth (the target)

Trace `HermitBlockingCore` over all 94 classes (job 47676952, 2026-06-20):

- HermiT classifies the **whole ontology in 940 ms**, **134 SAT tests**, **17341
  total backtracks** (~129 per test). Every concept is `saturations=1`.
- HermiT does **not** fold to ~3 nodes (an earlier belief — wrong). Its hardest
  concepts are the DNA/RNA chain family (ChromosomalDNA, EntireDNAMolecule,
  the mRNA/rRNA/tRNA group): **~690-node models with ~668 blocked** (~97% blocked,
  ~22 expanding). The fold is real, but the model is big and each step is cheap.
- **So 5303 is not algorithmically hard for HermiT.** The KM gap is an
  efficiency gap, not a missing-mechanism gap.

KM on the same hard concept (qi=12, internal concept idx 31): with EAGER +
subset blocking, **6779 backtracks, 1516 nodes, 217 s** ≈ 32 ms per backtrack vs
HermiT's ~1 ms.

## What works / partially works

| Lever (flag) | Effect on 5303 | Sound? | Status |
|---|---|---|---|
| `KM_HT_EAGER` | fire ⊤-disjunctions only on UNBLOCKED nodes; folds depth, reaches **qi=93/94** standalone | yes | foundational, the best sound lever before NEGTRIED |
| `KM_HT_NEGTRIED` | HermiT startNextChoice: after a disjunct clashes, assert ¬D_di so siblings unit-propagate. **concept 31: 217 s → 7.2 s (~30×)**, reaches qi=93/94 | yes | **CURRENT BREAKTHROUGH** (2026-06-20); total still > 280 s sequential — aggregate shaving + parallelism pending |

EAGER + subset blocking, when it does run, is **incomplete by 1**
(`CarbonHydrogenSubstructure ⊑ Hydrocarbon`) — the transitive-role subset-blocking
gap. Whether pairwise blocking (mode 3) closes this, or it is a genuinely missing
composition clause, is being disambiguated by the canon_cmp matrix.

## What was falsified (do not re-run)

### Conflict learning — DEAD in all forms
- **node-uid-keyed** (`KM_HT_LEARN`): 100% inert — search byte-identical to no
  learning. No-goods key on (node, uid, lit); every branch recreates nodes with
  fresh uids, so each no-good is discarded stale before it can refire.
- **NOSTALE upper bound** (`KM_HT_LEARN_NOSTALE`, unsound diagnostic): the
  theoretical ceiling of any conflict-learning scheme — cuts backtracks only ~7%
  and goes *deeper*, never converges.
- **label-signature-keyed** (`KM_HT_LBLCACHE`): fires correctly but **hit rate
  ~0.08%** (≈150 fires vs ≈200k conflicts). Sig-keyed no-goods almost never recur.
- Root cause: 5303's conflicts are **tiny (avg card 5.5, 2–7 levels)** and
  structurally **near-unique** — there is nothing recurring to learn. The DEPSTATS
  profile (avg_card=5.5 at avg_depth=1244, backjump_gap=0 on all samples) is
  textbook CDCL, but the conflicts don't repeat, so learning has no purchase.

### QuasiOrderClassification (`KM_HT_QO`)
- QO tally on 5303: queries=94, dead=3, **suff=0**, insuff=91 (open med=17,
  max=18). Lazy-saturation determinism gives zero shortcut — every concept needs
  branching. Corpus-wide a strict −2 regression (9024 + 12141 clean → incomplete).
  Gated OFF.

### Cache-tableau path (`KM_TAB_CACHE` / `KM_TAB_CONV` / `TYPECACHE` / `SUBCACHE`)
- Has *working* label-keyed learning (135k–863k no-good hits, stable keys) and
  bounded depth (66–308) and Luby restarts — and **still cannot finish**.
- It gets stuck on the **global consistency check** (`sat_seed([])`): 65k–109k
  distinct (label, imposed) seeds, never reaches the per-concept queries. With
  `KM_TAB_ASSUME_CONSISTENT` it times out on the *first* per-concept witness.
- Reason: per-label decomposition **fragments** the one consistency model into
  tens of thousands of (label × parent-imposed-∀) seeds. **Model-sharing (Ht)
  beats label-caching here.** Hybrid cache-CDCL per-concept is DEAD for 5303.

### SATFOLD — model folding by SAT-superset completion — RIGHT ATTACK, UNSOUND
- Idea: record positive cores of completed clash-free model nodes; before
  branching, if a node's label ⊆ a cached core, complete it to that core so its
  disjunctions are satisfied without branching.
- **It makes 5303 TERMINATE — the first mechanism ever to do so** (standalone
  RC=0). So model folding is a viable attack on termination.
- But it is **UNSOUND**: v1 unsound=10, v2 (positive cores + disjointness guard)
  unsound=22. Root cause (proved with `satfold_diff.py`): the wrong-subsumption
  pairs are all **wrong exclusive-disjunct picks** — Carbohydrate/Glucose/Hexose/…
  ⊑ Hydrocarbon, AminoAcidSequence/BioMolecularSequence ⊑ NucleicAcid, where the
  truth is ⊑ Peptide. Folding commits a node to a cached core that resolved an
  exclusive disjunction (Peptide ⊔ NucleicAcid) the **wrong** way. At fold time
  the node has not yet derived the forcing fact (it is disjunctive / non-Horn,
  not propagated), so the subset+disjointness check passes and the wrong pick is
  locally clash-free → nothing ever catches it.
- **Why HermiT/Konclude don't hit this**: they use cached / pseudo models for
  **refutation only** (prove a non-subsumption), never to **commit** a disjunct
  choice. Sound folding must distinguish forced completions from choice
  completions; the subset check cannot. ABANDONED.

### Other gated, inert mechanisms (built, 111 tests pass, no effect on 5303)
- `KM_HT_SATCACHE` (persistent SAT core-sig pool): zero effect — model already
  folded; bottleneck is branching, not size.
- `KM_HT_WITREUSE` (pseudo-model witness reuse): fires but reuses only the cheap
  concepts; the ~13 expensive witnesses aren't in earlier models.
- `KM_HT_PHASE` (label-keyed phase saving): warm-starts disjunct choices; on its
  own did not crack it (being re-tested combined with NEGTRIED+ORD).
- `KM_HT_BLOCK=3` (pairwise blocking): O(n) hashed, complete under transitive
  roles, but folds **less** than subset → bigger model → timed out alone
  (matrix combo B). Useful for the +1 completeness corner, not for speed.
- `KM_HT_BLOCKSKIP`: collapses depth but explodes shallow backtracks (374k thrash).
- `KM_HT_RESTART`: thrashes (135+ restarts).
- `KM_HT_TRIGABS` (trigger-keyed binary absorption): only the 16 *triggered*
  disjunctions absorb; the 17 *positive* global ⊤-disjunctions (the killers)
  cannot. Combos C/D timed out.
- `KM_HT_HARVEST` (common-disjunct hoisting, M3): made sound per-disjunct
  (commit 5072749, recovered 4205) but did not crack 5303 (combo D timed out).

## SOLVED (2026-06-20)

The HermiT trace reframed the problem: 5303's gap is **search efficiency**, not a
missing structural mechanism. KM has the full DPLL toolbox (dependency-directed
backjumping, VSIDS activity ordering, `negtried` startNextChoice, phase-saving)
but it was **all OFF by default**.

**Winning combo (matrix job 47677091, combo I):**

```
KM_HT_EAGER=1 KM_HT_NEGTRIED=1 KM_HT_ORD=2 KM_HT_PHASE=1
→ RC=0, wall=207 s, CLEAN=True, km_n=238 gold_n=238, unsound=0 incomplete=0
→ concept 31: 217 s → 2.98 s
```

This is the **first ever sound + complete classification of 5303.** The +1
completeness gap (`CarbonHydrogenSubstructure ⊑ Hydrocarbon`) **vanished**
(incomplete=0) under this search config — no frontend / pairwise-blocking fix
needed.

**The levers only work combined** — each alone times out:
- `EAGER` — fire ⊤-disjunctions only on unblocked nodes (model fold).
- `KM_HT_NEGTRIED` — HermiT startNextChoice: assert ¬D_di after a disjunct
  clashes so siblings unit-propagate (the single biggest lever, 217 s → 7 s).
- `KM_HT_ORD=2` — most-failing-first disjunct ordering (VSIDS activity).
- `KM_HT_PHASE` — phase-saving warm-start from the consistency model's choices.

(G = EAGER+NEGTRIED, H = +ORD2, J = +PHASE all individually RC=124; only
I = all four together completes.)

207 s is under the 240 s budget but tight. **`KM_HT_PAR=N`** (new parallel
`Ht::classify`: per-worker `Ht` via `Ht::new` + `thread::scope` over the 94
Phase-1 SAT tests and the Phase-2 confirms; set-identical, fixpoint-preserving,
no Lean re-cert) gives margin (expected 207 s → ~60 s on 4–8 threads).

### Speed chase (target: single-digit seconds; HermiT ≈ 0.94s)

Sound+complete throughout (238/238, unsound=0, incomplete=0):

| Step | Wall | Note |
|---|---|---|
| combo I (ORD=2) | 207s | first completion |
| **ORD=1** (least-failing-first) | 123s | concept 31: 5650 → **41 backtracks** (beats HermiT) |
| + **inverted-index blocking** (default) | **41s** | per-step O(n²)→~O(n·label); result-identical |
| + parallel `KM_HT_PAR=4` (dynamic) | **18s** | work-stealing; flatlines past 4 threads |
| + `KM_HT_PAR=16` | **17s** | bounded by the single longest per-phase SAT test |

Production search combo: **`KM_HT_EAGER=1 KM_HT_NEGTRIED=1 KM_HT_ORD=1`** (fast
blocking is the default; `KM_HT_PAR=N` optional for parallelism).

Dead ends in the speed chase:
- `KM_HT_BLOCK=0/2/3` (the existing O(n) blocking modes): fold too little for
  5303 → time out (mode 0) / OOM-abort in parallel. Only subset (mode 1) folds
  enough, so the win was making *subset* O(n) via the inverted index.
- `KM_HT_CONTRA` determinism: ~3% only — ORD=1 already cut branching to 41
  backtracks, so there is nothing left for absorption to remove. The floor is
  model *construction*, not search.

Remaining gap to single digits: parallel flatlines at ~17s = the longest single
SAT test per phase. Candidate lever = **incremental blocking** (the inverted
index is O(n·label) per call but rebuilt O(n) times per model ⇒ O(n²·label);
maintaining it across `process_obligations` calls would amortize to ~O(n)).
Profiling (job 47678181) to confirm blocking dominates before building it.

### Remaining work to land it
1. ✓ `KM_HT_PAR` parallel path validated CLEAN (17s @ 16 threads).
2. Wire the winning flags ON for the HT fallback path + full corpus regression —
   **must not regress the emelim canaries** 9024 / 12141 / 541 / 11460 / 15491 /
   4604 / 9635 (HT-recovered today). Note: single-threaded 41s already clears the
   240s budget, so coverage does not depend on parallelism.
3. Test whether the same combo cracks the HT-routable family siblings.

## Reusable diagnostics (on IBEX `/ibex/scratch/hohndor/km/`)

- `tin5303.json` — the dumped cb_to_ht TInput; run any flag combo standalone with
  `km tableau < tin5303.json` (no rebuild, no orchestrator). `KM_DUMP_TIN=<path>`
  in `race.rs spawn_ht` regenerates it.
- `canon_cmp.py <subs> <gold.sig.gz>` — canonicalizes via `ore_canon` and prints
  `CLEAN / km_n / gold_n / unsound / incomplete`.
- `satfold_diff.py` — prints the specific unsound (km-only) and incomplete
  (gold-only) subsumption pairs.
- `HermitBlockingCore.java` — per-concept HermiT model fold (total/blocked/active
  node counts + ms). `HermitTrace` — overall CountingMonitor (tests, backtracks,
  nodes). `sb_hermit_trace.sh <ont>` launcher.
- Flag-matrix sbatch templates: `mtx5303.sh` (model-shaping), `mtx5303b.sh`
  (search discipline, with `KM_HT_STATS=1`).
