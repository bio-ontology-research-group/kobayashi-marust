# Throughput timeout family — Konclude trace + precise bottleneck (2026-06-24)

Target: the ORE "throughput / context-explosion" timeouts
10908/14817/10621/7499/7914/3215/9663/9724/15672. Goal: classify them sound +
complete in time, matching Konclude. This note records the Konclude trace, the
structural profile, the empirical bottleneck, and the implementation plan. It is
the diagnosis behind the gated `KM_HT_QO_CARD` infrastructure.

## Structural profile (frontend `KM_DUMP_TIN` + clause analysis + Konclude expressiveness)

| ont | clauses | nom | inv(bridge) | number | disj_heads | maxw | Konclude expr | konclude | KM(base) |
|-----|--------:|----:|:-----------:|:------:|----------:|-----:|---------------|---------:|---------:|
| 9724  | 139634 | 0  | yes | yes | 0    | 0 | SHIF     | 5 s / 457090   | 20 GB timeout |
| 7914  | 68012  | 0  | yes | yes | 14   | 4 | SRIQ     | 2.7 s / 141517 | 18.5 GB timeout |
| 9663  | 302772 | 0  | yes | yes | 18   | 4 | SRIQ     | 8.2 s / 725040 | 19.6 GB timeout |
| 14817 | 272558 | 0  | yes | yes | 97   | 4 | SRIQ     | 18.6 s / 1.18M | 3.5 GB timeout |
| 7499  | 20154  | 0  | yes | yes | 252  | 8 | SRIQ     | 3.7 s / 39424  | 18.5 GB timeout |
| 10621 | (28 MB)| yes| yes | yes | -    | - | SOIF(D)  | 17 s / 70827   | timeout |
| 10908 | 1665   | 18 | yes | yes | 25   | 9 | SROIQ    | 0.28 s / 6001  | 18.5 GB timeout |
| 15672 | 922    | 3  | yes | yes | 10   | 2 | SHOIN    | 0.18 s / 142   | 18.5 GB timeout |
| 3215  | 458165 | 0  | yes | no  | 18323| 2 | SHI      | 147 s / 3.9M   | timeout (disjunction-family) |

Three tracks: **near-Horn SRIQ/SHIF** (9724/7914/9663/14817/7499 — no nominal, no
datatype; the prime target), **nominal/datatype** (10908 SROIQ, 10621 SOIF(D),
15672 SHOIN), and **disjunction-family** (3215, 18 323 disj heads — belongs with
10702/1603, not here). Every member has S (transitive) or R (complex role
inclusions) and inverse-via-bridges; none is transitivity-free.

## How Konclude scales (verified against a fresh clone, `~/Public/software/Konclude`)

One non-branching deterministic saturation decides ~95 % of concepts; a complete
tableau runs only on the residue. Four levers (file:line in KONCLUDE-STUDY.md):
A) one shared node per (concept,polarity), existentials reuse it — graph is
O(#concepts); B) monotone de-duplicated label, each concept-rule fires once per
node; C) `∀` propagates BACKWARD over recorded role links, never forward over
enumerated successors — and transitive `∀` via `∀R.C ⊑ ∀R.∀R.C` (no edge
closure); D) `≤` records a cardinality bound (node marked INSUFFICIENT and
deferred to tableau only when it cannot resolve deterministically); disjunctions
parked + common-disjunct hoisted. On 9724: 15 s saturation → "sufficiently
saturated" → 0.6 s classification, ~zero tableau tests.

## The empirical bottleneck in KM's QoSat (per-concept saturation, `hypertableau.rs`)

Confirmed by tracing (`KM_HT_TRACE`) on 9724:

1. **At-most / functional (`F`/`Q`) produces Eq-heads.** The QoSat `apply_head`
   bailed the WHOLE pass `unsupported` on the first Eq atom (was
   `hypertableau.rs` ~3664). Fixed under `KM_HT_QO_CARD`: mark the anchor node
   INSUFFICIENT and continue (Konclude's deferral), so the pass completes.
2. **Inverse is pervasive and load-bearing.** Keeping inverse bridges, the global
   saturation generates 2.5 M reversed edges and 66 M containment-check misses
   (`kp_miss`), vs 7581 where `kp_miss=0`. The per-node CLEAN split (study P2,
   wired into `qo_classify_kpset` / `qo_classify_global_fwd` under
   `KM_HT_QO_CARD`) recovers only **2815 / 23136 (12 %)** concepts — 88 % are in
   the bidirectional closure of an insufficient node.
3. **So the global pass never certifies → falls to the per-concept path:** ~23 k
   separate single-seed saturations → ~299 M cumulative edge pops → 300 s
   timeout. The per-concept fallback is O(#queries × per-sat) and cannot scale to
   58 k-query onts; Konclude issues zero per-concept work for clean concepts.

Root cause: KM defers cardinality and (effectively) inverse to a per-concept /
complete-tableau path, which is fine when the residue is a small tail (7581:
`kp_miss=0`, residue ≈ 0) but collapses when `≤`+inverse are pervasive (the whole
near-Horn SRIQ family), because the residue becomes ~the whole ontology.

## Per-node CLEAN% measured across the family (KM_HT_QO_CARD, pending-aware)

The per-node split emits the saturated answer for concepts whose self-node cannot
forward-reach any deferred node (cardinality Eq / critical-∀ / inverse-miss /
parked-disjunction anchor). Measured CLEAN fraction of named query concepts:

| ont | clean / queries | residue | hard core | verdict |
|-----|-----------------|--------:|-----------|---------|
| 7914 | 10509 / 17680 (59 %) | 7171 | pending=67, insuff=173, kp_miss=855 | best, still 41 % residue |
| 9724 | 2815 / 23136 (12 %)  | 20321 | inv_edges=2.5M, kp_miss=66M | pervasive inverse |
| 7499 | 1 / 5109 (0.02 %)    | 5108  | pending=7606 disjunctions | pervasive disjunction |
| 9663 / 14817 | global saturation does not complete in 400 s | — | 58–60 k concepts | does not scale |

So the clean emit alone solves NONE: even 7914's hard core (a few hundred nodes)
has a reverse-reach closure covering 41 % of concepts because the graph is
well-connected; its clean subsumptions are 62529 of the 141517 gold. Completing
the residue needs a cardinality+inverse+disjunction-complete method on the
residue (the gap below), or the residue must first be shrunk by handling inverse
and cardinality IN the saturation. Complete-HT + full search discipline
(`KM_HT_FORCE`+`KM_HT_NUMBER`+`INCRBLOCK2`+`INCROBLIG`+`EAGER`+`SATFOLD`) on the
smallest member 7499 also TIMES OUT (600 s, 18.5 GB). The bare QO branching
classifier (Phase 1 residue-SAT + Phase 2 bounded subsumption via
`qo_residue_test`, reached by `KM_HT_QO` without `_PC`/`_KPSET`) on 7914 TIMES OUT
(600 s, 18.8 GB) — its 7171 insufficient concepts each trigger a branching residue
test. **Every classification path KM has — CB, complete HT (+search), QoSat
per-concept, QoSat kpset+card-split, QoSat branching — fails on the most tractable
member within 600 s. No existing flag or combination classifies any of the 9.**
The bottleneck is structural (the deferred core is not a tail), so only the
in-pass re-architecture below can close this family.

## Plan (the real fix — a global-saturation re-architecture, like the 7581 QoSat work)

To classify these in one pass like Konclude, the GLOBAL saturation must handle
`≤` and inverse SOUNDLY in-pass instead of deferring them:

- **P1 — backward-∀ inverse (lever C).** Stop materialising inverse as bridge
  edges; record `∀r⁻.C` and propagate it backward over the existing forward
  r-edges. Removes the 2.5 M reversed edges + 66 M misses; most concepts become
  CLEAN. (INVCOMPOSE was a partial, clause-level approximation; this is the
  saturation-level rule.)
- **P2 — cardinality bound + deterministic merge (lever D).** Record per-role
  `≤n` bounds on the shared node; when a node is forced over the bound, merge
  deterministically (the complete HT already has `merge_into`, `hypertableau.rs`
  ~1021) or mark INSUFFICIENT only then — not on every Eq-head.
- **P3 — keep the per-node CLEAN split + residue verify** (`KM_HT_QO_CARD`,
  already wired): once P1/P2 shrink the residue to a real tail, emit CLEAN
  concepts from the single pass and verify the small residue with the complete
  HT (cardinality-aware via `merge_into`).

P1/P2 change what the saturation derives → Lean re-cert of the affected rules
(the QoSat soundness obligations), as with the original CB calculus. This is the
same class of effort as the 7581 QoSat re-architecture and is multi-session.

## What landed this session (sound, gated, no default change)

`KM_HT_QO_CARD` (default off): Eq-heads mark the anchor INSUFFICIENT and continue
instead of bailing; critical-∀ writes record their node insufficient; the
per-node CLEAN split is wired into `qo_classify_kpset` and
`qo_classify_global_fwd` (emit CLEAN concepts when the residue is empty). Inert
unless the flag is set; measured 12 % CLEAN on 9724 (residue too large to recover
without P1/P2). The corpus sweep (job 47760983, 587 onts × 12 configs, 600 s)
confirms the only lever that recovers throughput onts today is `KM_HT_QO_ROUTER`
(+2: 7581, 16444 — both gold-exact); no flag cracks the SRIQ family.
