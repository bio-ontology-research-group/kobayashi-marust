# Throughput / disjunction giants — handoff for a fresh session

2026-06-27. Session summary + the exact next steps to finish the remaining
hard ORE-2015 ontologies. Read this first, then `MEMORY.md` →
`project_km_giants_taxonomy`.

## Wins committed this session (branch `payg-strategy`)

- **`c677301` — closes ore_ont_7499.** The residue-complete worker
  (`qo_residue_complete`) was a bare `Ht::new` that bailed `unsupported` on a
  single `≤n` Eq-head clause (the `apply_head` Eq arm is gated on `ext.number`,
  hypertableau.rs:1424). Fix = `w.force_number=true; w.force_qmerge=true` on the
  worker so Eq-heads route to `push_card`/`branch_merge`. Validated 0/0 vs
  Konclude gold (closure 39424==39424). Config: `KM_HT_QO_SPLIT` +
  `KM_HT_QO_RESIDUE_COMPLETE` + `RESIDUE_CAP=10000` + `EAGER/NEGTRIED/ORD` +
  `BLOCK=5`.
- **`8a3fd93` — elc-NF1 fast path + disjunction-route enablement (both gated,
  172 tests pass, result-identical).**
  - `KM_HT_QO_FASTIMPL`: index simple Horn `C(x)→D(x)` clauses (83% of a near-EL
    ont) as `C→[D…]` and apply with direct `add_lit`, bypassing the
    `fire_concept_clause` sigma-alloc + `apply_head` machinery (the 5.1M-call
    hot path). Speeds the concept half of the QO saturation.
  - QO global-forward disjunction route: `quasi_order_classify` (hypertableau.rs
    :9528) deferred ALL non-inverse onts in certify mode; relaxed under
    `KM_HT_QO_RESIDUE_COMPLETE` so pure-disjunction onts (3215) reach the lazy
    global-forward + residue-complete path. Plus the engage-guard that seeds
    parked disjunctions (not only cardinality) into the residue affected-set.

## The giant taxonomy (clause-census ground truth)

Always run `ofn <ont>.owl` and count disjunctions FIRST (the atom key is
`kind`, not `type`). Partial saturation-counter ratios mislead.

1. **THROUGHPUT near-EL: 14817, 9663, 7914.** SRIQ (inverse + cardinality, no
   nominals), so they can NOT use the fast `elc` and fall to the slower QO Ht.
   14817 = 272558 clauses, only 143 disjunctions; 83% of clauses are single-atom
   `C(x)→D(x)`. The QO saturation is a **lit↔edge fixpoint**: the lit loop
   (fire_concept_clause) and the edge loop (fire_role_clause / ∀-range
   propagation over 800k+ edges) are BOTH large and feed each other.
2. **DISJUNCTION family: 3215, 541, 12653.** 3215 = SHI, 18323 disjunctions, no
   inverse bridge. Falls to naive O(n²) TR without the routing fix; with the fix
   it enters QO but hits the same saturation-throughput wall (seeds 54973
   concepts).
3. **Eq-head residue: 7499 — DONE.**

## How Konclude solves the throughput giants (measured, `-v`, single-thread)

Binary: `unimatrix01:~/bench/reasoners/Konclude-v0.7.0-1138-.../Binaries/Konclude
classification -w1 -v -i <ont> -o /tmp/x.owl`.

| ont   | expr | parse | preprocess | **precompute** | **classify** | total |
|-------|------|-------|-----------|----------------|--------------|-------|
| 14817 | SRIQ | 1.0s  | 1.0s      | **3.0s**       | **23.3s**    | 28.8s |
| 9663  | SRIQ | 0.9s  | 1.6s      | **6.2s**       | **2.4s**     | 11.6s |
| 7914  | SRIQ | 0.8s  | 0.7s      | **1.8s**       | **0.5s**     | 4.1s  |
| 3215  | SHI  | 0.8s  | 2.2s      | **35.8s**      | **76.7s**    | 116s  |

Konclude = **two phases**: (1) a fast **precompute** that builds ONE
canonical/consistency model (one saturation, NOT one-per-concept), 1.8–6.2s even
for the giants; (2) per-concept **classify** against that pseudo-model with
deterministic-subsumer + pseudo-model pruning (only survivors get a real tableau
test).

## The precise gap (the 60–100× to close)

- Konclude precomputes 14817 in **3.0s**; KM's QO saturation **doesn't finish in
  200s**.
- Structural difference: Konclude's precompute is ONE consistency model; KM's QO
  global-forward **seeds all ~58k named concepts** into one giant saturation
  (the 54973/58364-node seed in the trace) — bigger AND slower per step. KM's
  per-concept path (`classify_parallel`) hits the same wall (each per-concept
  saturation is slow × 58k).
- Per-step speed: Konclude fires concepts by binary-operator descriptor dispatch
  (watched-trigger parking keyed by concept tag, NO clause-body re-scan, NO
  substitution, freelist-pooled descriptors —
  `CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`,
  `CReapplyConceptSaturationLabelSet.cpp`). KM re-checks the full clause body on
  every trigger arrival and allocates per call. `fastimpl` removes this for the
  single-atom case; the edge/role half does NOT have it yet.

## Next steps (in priority order) for the fresh session

1. **Speed the QO Ht edge half** — port `elc`'s clone-free NF4 role/∀-range
   propagation into the QO saturation edge loop (`drain_work` edge loop ~line
   4073 / `fire_role_clause`). This is the other half of the lit↔edge fixpoint
   and where most of the remaining 60× lives. `elc` (`elcomplete.rs`) already
   does this fast; the QO Ht does not. (`fastimpl` did the concept half.)
2. **One-model precompute** — restructure the QO classify to build ONE
   consistency model (like Konclude's 3s precompute) instead of seeding all 58k
   concepts, then classify per-concept against it. KM has the pieces
   (`classify_parallel` for per-concept, the QO saturation for the model) but not
   assembled the Konclude two-phase way.
3. Re-test 14817/9663/7914 with `KM_HT_QO_FASTIMPL=1` + the edge-half speedup;
   then 3215/541/12653. Validate each vs Konclude gold
   (`unimatrix01:~/bench/ore_out/konclude__ore_ont_<id>.sig.gz`, transitive-close
   both sides — see the cmp script note below).

## Reproduction notes / gotchas

- **Build on ws only** (`~/km-frontend/kobayashi-marust/engine`,
  `rsync -a engine/src/ ws:.../engine/src/ && ssh ws 'cargo build --release'`).
  NEVER build/run on the laptop. Clean ws km orphans by PID after each session.
- **perf is UNAVAILABLE on ws** (`perf_event_paranoid=3`, not installed) — use
  application counters (the DBG_* atomics pattern) instead.
- To engage the QO global-forward path the HT worker needs **`KM_HT_QO=1`**
  (tableau.rs:4577) — without it the worker runs naive TR `classify`. This cost
  hours of confusion; set it explicitly.
- Gold comparison: KM emits closure, HermiT `-c` emits reduced — transitive-close
  BOTH sides + strip to local names (the `kind` atom key; KM `__` suffixes).
  Konclude is NOT gold where it errors/times-out (see
  `feedback_konclude_not_gold` — KM's correct answer counts as solved).
- Probe files on `ws:/tmp/o{7499,9663,7914,3215,14817}.owl`; Konclude phase logs
  `unimatrix01:/tmp/kg_<id>.log`; gold `/tmp/gold{7499,9663}.sig`.

## Status vs gold (do not regress)

Baseline before this session: 573 ok / 0 unsound. 7499 now closes via the gated
residue config. The committed `fastimpl` + disjunction route are gated OFF in the
production path, so production routing is unchanged until the edge-half speedup
lands and a full sweep validates them default-on.
