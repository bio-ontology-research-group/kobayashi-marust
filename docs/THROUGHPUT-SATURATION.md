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


## Single-thread CB (KM_THREADS=1) — bounds memory, still times out (the decisive split)

Tested single-thread CB on all 9 (job 47766702, 600 s, 28 GB cap). EVERY ont times
out, but peak RSS is now BOUNDED: 15672=22.5 MB, 7914=533 MB, 7499=2.1 GB,
9663=2.1 GB, 14817=4.8 GB, 10621=5.6 GB, 3215=4.5 GB, 9724=8.2 GB, 10908=18.5 GB.
So the parallel 18-20 GB blowups were a thread-memory-multiplication artifact, NOT
the cause of failure — single-thread fits in memory and STILL does not converge in
600 s. This splits the family cleanly:
- **15672 (22 MB!), 10908, 3215** — pure SEARCH non-convergence at tiny/bounded
  memory: the live-∀+⊔ / nominal DISJUNCTION-FAMILY problem (cf 5303/10702),
  not throughput. Needs Konclude-grade search convergence, not saturation scale.
- **7499/7914/9724/9663/14817/10621** — near-Horn SRIQ throughput: the in-pass
  saturation re-architecture (P1/P2).

Six distinct sound/complete paths now exhausted on this family — CB(parallel),
CB(single-thread), complete-HT(+search), QoSat per-concept, QoSat kpset+card-split,
QoSat branching — all time out. The reuse space is empirically closed.

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

## Session 2 (2026-06-24, cont.) — the precise blocker is residue completion, not the saturation

Experiment discipline: cap at 150 s (Konclude does these in <30 s; a correct path
is fast, a 590 s finish is a blowup). Findings:

- The GLOBAL saturation completes fast on 7914/9724 (it printed pending/insuff
  counts). The blowup is the RESIDUE COMPLETION: both the per-concept verify funnel
  and the bare QO branching classifier (`qo_residue_test`) RE-SATURATE per residue
  concept → 19 GB / timeout on 7914's 7171 residue. Konclude instead builds the
  model ONCE and branches only the small open core in place (study P4: satisfiable-
  expander + completion-graph reuse). **That model-reuse is the port needed** — KM's
  residue path is per-concept, not model-reuse.
- Inverse-consumer breakdown (INVCOMPOSE-DIAG): 7499 bad=0/27 bridges/485 single
  consumers (blocked by 7606 disjunctions); 7914 bad=0/14 bridges/12 pairs (2 are
  one-directional)/9465 single consumers, 0 multi — fully prop-shape; 9724 630 bad
  roles in 674 multi-role/chain consumers → 2.5 M reversed edges.
- LANDED: `KM_HT_QO_INVONEWAY` (gated, default off) — one-directional bridge
  composition (a consequent role produced only by its bridge and only single-role-
  consumed fires its consumers over the forward source edge swapped; bridge dropped,
  no reversed edge). Sound (resolvents). Covers 7914's 2 one-way bridges. Does NOT
  by itself solve 7914 (its 19 GB is residue completion, not its ~24 k inv_edges).

The two concrete ports remaining (both in `hypertableau.rs`, no Lean until the end):
1. **Residue model-reuse** — classify residue concepts by branching the open
   disjunctions on the ALREADY-BUILT global shared model + reading subsumers, instead
   of re-saturating per concept (`qo_classify_*` + `qo_fixpoint`/`qo_branch_dfs`).
   Closes the few-disjunction members (7914: 67; 9663: 18; 14817: 97).
2. **In-pass inverse for chain consumers** — compose the inverse into the 674
   multi-role consumers (9724) so its 2.5 M reversed edges vanish; 9724 is pure Horn
   (0 disjunctions) so after that it is a clean deterministic saturation.
The disjunction-heavy members (7499: 7606, 3215: 18 323, 15672/10908 nominal+disj)
are the disjunction-family search-convergence problem, tracked separately.

## Session 3 (2026-06-24): both ports built+tested — the real blocker is ∀ pollution

Both ports from the previous session are implemented, gated, and pass the 131-test
suite:
- **Port #2 `KM_HT_QO_INVCHAIN`** (in `compose_inverse`): composes a purely-virtual
  inverse role (single bridge source, not otherwise produced) away even inside a
  multi-role/chain body, dropping the bridge so no reversed edge is materialised.
- **Port #1 `KM_HT_QO_RESIDUE`** (in `qo_classify_kpset`): completes the affected
  (residue) concepts on the already-built shared model — one global completion to
  harvest candidate extras + per-subtree `A⊓¬B` verify (checkpoint/rollback, no
  rebuild). Gated SOUND to the pure-disjunction case; `residue_tainted` defers any
  concept whose verify touches a deferred-insufficient (∀/cardinality) node.

### Measured structure (KPSET+CARD+INVCHAIN, IBEX)
| ont  | concepts | clean | residue | pending(⊔) | insuff_nodes | qo_insuff | inv_edges |
|------|----------|-------|---------|------------|--------------|-----------|-----------|
| 9724 | 23136    | 2815  | 20321   | 0 (Horn)   | 34012        | true      | 2.43 M    |
| 7914 | 17680    | 10509 | 7171    | 67         | 173          | true      | 23 869    |

INVCHAIN composes 395 bridge roles on 9724, 2 on 7914 — but the dominant cost is
NOT inverse-chain edges or disjunction residue. It is **∀-shared-filler pollution**
(`qo_insufficient`, the `apply_head` critical-ALL case): a `∀R.C` write lands on a
filler shared across sources, so the shared-node label over-approximates. On 9724
that is 34012/37251 nodes; on 7914 only 173 nodes but still enough to set
`qo_insufficient` and block the sound residue gate.

### The fast lazy arm works; the complete arm is too slow (isolated, `km tableau` on a dumped TInput)
- **7914 fast QO pass**: 55 s / **512 MB**, correctly emits the 10509 clean
  concepts. With `KM_HT_QO_RESIDUE_FORCE` (gate bypassed, taint suppressed) it runs
  to completion but emits **190539 subs vs gold 141517** (~49 k spurious from the
  affected concepts' polluted forward labels), and the polluted global model has no
  clash-free completion (`phase1 sat=false`). So the force result is unsound — as
  expected; the pollution is real.
- **Complete HT classify** (the sound, non-shared-filler, per-concept path) on all
  17680 concepts **TIMES OUT at 150 s** (277 MB), even with `KM_HT_PAR=8 +
  KM_HT_HORNFAST + KM_HT_WITREUSE` (412 % CPU). The per-concept tableau builds
  (inverse + cardinality + blocking) are individually expensive and there are too
  many of them.

### Conclusion: neither requested port solves the family alone
The blocker is a pincer: the fast lazy pass is UNSOUND on these onts (∀ pollution),
and the sound complete pass is TOO SLOW (per-concept SAT count). Pruning the
over-approximation cheaply is not possible from the lazy side (cheap pseudo-model
merge refutes non-subsumptions, i.e. the lower-bound direction; the pollution is an
upper-bound error). The genuine lever is **Konclude lever C**: make the single
shared saturation SOUND for `∀` by using the completion-graph semantics
(non-shared / pairwise-blocked successors) instead of shared role-keyed fillers.
Then `qo_insufficient` never fires, clean% → ~100 %, and the one pass classifies
directly. KM already has the completion graph + blocking inside `Ht.classify`, but
runs it per-concept; lever C means running it ONCE as the shared model. That is a
saturation re-architecture (`saturate_global` / `ensure_filler` / `apply_head`),
the next port — larger than #1/#2 and not requested by name, but it is what the
data demands.

### Hybrid ruled out; QO speed is fine — the sole blocker is ∀-pollution soundness
Tested the clean-bulk + complete-residue hybrid (KM_HT_QO_DUMP_AFFECTED → restrict
queries → complete HT on affected only):
- 300 affected concepts: 11 s. **1000 affected: TIMEOUT (>150 s).** Non-linear — a
  HANDFUL of affected concepts are pathologically explosive under full per-concept
  SAT (the live-disjunction search problem, cf. 5303). So routing the residue to the
  complete tableau does NOT work: a few hard concepts blow the budget.
- BUT the QO branching pass itself classified ALL of 7914 (all 67 disjunctions) in
  **55 s** — QO handles the disjunctions fine; it is FASTER and better-behaved than
  full HT per-concept search here. Its only defect is the ∀-shared-filler
  over-approximation (190539 vs 141517).

So the lever is unambiguous: **make QO's `∀` handling SOUND** (so its fast single
pass is also correct), NOT route to per-concept SAT. Two scopes:
- GLOBAL (lever C): non-shared / pairwise-blocked successors in `saturate_global`.
- RESIDUE-LOCAL: fresh non-shared fillers only inside `qo_residue_test`'s subtree
  branch (bounded, per affected concept), so the verify decides `A⊓¬B` soundly
  without reproducing the shared-filler pollution. Smaller scope than global lever C
  and leverages QO's measured speed; the most tractable sound fix. Still a real
  change to the filler/saturation machinery (and eventual Lean re-cert), not a flag.

### Complete HT also times out on 9724 (cardinality) — every existing path exhausted
9724 reports `inverse=false (bridges) number=true` — it has cardinality, so its
per-concept models are not deterministic either. Complete HT classify (HORNFAST,
PAR=8, WITREUSE) on its 23136 concepts TIMES OUT at 150 s (318 MB). Combined with
the 7914 results, EVERY path over existing machinery + ports #1/#2 fails within
150 s for the two most tractable members: CB (OOM 19 GB), QO-sound (defers),
QO-force (unsound, 190539 vs 141517), complete-HT-all (timeout), and the
clean-bulk + complete-residue hybrid (timeout on a few explosive concepts). The
family genuinely needs NEW sound algorithmic capability — sound fast `∀`
(non-shared/blocked successors), in-saturation cardinality bound+merge, AND
disjunction search-convergence — i.e. the SHIQ-completion saturation re-architecture
(project_km_shiq_ht Phase 3), not the two named ports. Confirmed by exhaustive
measurement, not assumed.
