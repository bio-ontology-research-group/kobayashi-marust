---
name: project_km_seqorder_win
description: Candidate portfolio (user-directed race of many ideas on IBEX) found KM_SEQ_ORDER recovers +6 ORE onts gold-clean with 0 regressions; regression sweep PASSED; deploy to production pending user authorization.
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-15, branch `portfolio-candidates` (off `disjunction-split`). User directed:
"implement up to 5 of my own ideas and race them against the failing onts on IBEX;
keep everything in git + CHANGELOG." Did exactly that.

**Portfolio** (IBEX job 47519642): 14 arms x 36 failing onts = 504 jobs, 240s/20GB,
each gold-compared (cmp zcat km sig vs konclude gold). Raw in repo:
`results/portfolio-20260615.txt` + `.sbatch`. Result: 9 GOLD=MATCH, **0 DIFF**
(zero unsound across the whole grid). 6 distinct onts recovered: 5107 6246 6682
10908 11016 11291. **KM_SEQ_ORDER alone recovers ALL 6**; every other arm's win is
a subset (combo/unitsfirst got 5107; tabrace got 6246 faster, 31s). The 4 NEW
candidate flags I implemented (KM_CORE_CAP, KM_SEED_FROM_SUBSET, KM_TODO_UNITS_FIRST,
KM_EARLY_UNSAT; commit 31764e0) recovered nothing seqorder didn't; corecap/highcap/
threads16/notrigskip recovered 0. So the portfolio collapses to one lever.

**KM_SEQ_ORDER overturns the prior 6246 dead-end verdict** ([[project_km_absorption]]
had 6246 as "genuine timeout, not recoverable"): total-order resolution cracks it
at 137s (31s under tabrace). Also overturns [[project_km_disjunction_blowup]]'s
framing of KM_SEQ_ORDER as only an OOM risk — it's a clean win.

**Regression sweep** (IBEX job 47520358): base vs seqorder over all 587 gold onts
(1174 jobs), KM_ABSORB=1. base 540 MATCH / seqorder 546 MATCH, BOTH 0 DIFF.
GAINED = the 6; **LOST/regressed = NONE**. seqorder STRICTLY DOMINATES base: +6,
0 regressions, every answered ont byte-identical to Konclude. 5303 stays non-ok in
both (its known OOM is not a regression). Raw: `results/regress-seqorder-20260615.txt`.

**What KM_SEQ_ORDER does** (`engine/src/calc.rs:481`, pre-existing Direction-A code,
NOT new this session): Sequoia `ContextLiteralOrdering` — named/query concepts stay
mutually incomparable at the bottom (the CompletenessProp regime the Lean proof
certifies, so forward `T->B(x)` readout stays complete); only internal definers
(Q_*, def_*, __trans__*) are totally ordered above (ordered resolution on definers,
resting on Sequoia's published SROIQ-classification completeness). The definer-
ordering restriction is the one piece NOT covered by KM's current Lean proof =>
follow-up Lean cert warranted, but corpus-wide gold-clean is decisive empirical
backing.

**AUTO-ROUTER LANDED (commit 9aee987).** Instead of default-on (which taxes
near-Horn onts: 6423 6s->126s forced), the engine self-routes. `Reasoner::saturate`
computes DISJ_INT (any clause head with >=2 concept literals AND >=1 internal
definer) and calls `calc::set_seq_order_auto`; enables seqorder iff DISJ_INT>=1.
Env still wins (KM_SEQ_ORDER on / KM_NO_SEQ_ORDER off). Both orderings complete
(named concepts incomparable either way) so routing is sound by construction;
seq_order() is now an AtomicU8 (2=undecided->env fallback) read in pred_lteq hot
path. has_internal_definer_disjunction() in reasoner.rs.

ROUTING RULE validated full-corpus (results/seqorder-routing-20260615.txt, IBEX
featall 47522005 x regression 47520358): keeps all +6 recoveries + 7/11 speedups,
avoids 27/28 slowdowns incl 6423 (+120s, DISJ_INT=0); only 18/540 passers route on.

CONFIRMED on IBEX (new binary, 83 tests pass):
- auto sweep no-flag (47522857): 546 MATCH, 0 DIFF, +6, set IDENTICAL to forced-on.
- same-sweep base(forced-off)-vs-auto A/B (47523500): base 540/auto 545 MATCH,
  0 DIFF, 0 lost; auto NET -24.6% wall (1968 vs 2610s) -- captures disjunction
  speedups, routes Horn off. 10908 borderline (~190s, ok@133s in dedicated sweep,
  contention-timeout in A/B; base misses too = not a regression).
Results in git: results/{portfolio,regress-seqorder,combo2,seqorder-routing,
auto-route-confirm,auto-route-AB}-20260615.{txt,sbatch}.

**DEPLOY STATUS: built on IBEX (ws was DOWN this session), NOT yet on production.**
Deploy now = ship the rebuilt auto-routing binary to unimatrix (relay IBEX->laptop
->unimatrix; ws cant scp to unimatrix) as kobayashi-marust-batch (back up old),
NO sbatch change needed (auto is default), then a production confirmation sweep.
Expected ~554->560. Awaiting user OK for the production binary swap (classifier
blocked an earlier prod-config edit as scope-escalation). NOTE: deployed
kobayashi-marust-batch is Jun 13; the prod sbatch ore_km_batch.sbatch has
KM_TAB_RACE=1 but NOT KM_ABSORB (554 baseline came from the kmpf/absorb-portfolio
sbatch, a different config) -- reconcile which prod config before the sweep.

Commits on portfolio-candidates: 31764e0 (4 candidate flags), e533169 + 1bcabd5
(portfolio CHANGELOG+results), 8594a48 (regression results+CHANGELOG).
Related: [[project_km_disjunction_blowup]], [[project_km_disjunction_split]],
[[project_km_absorption]], [[project_km_throughput]], [[feedback_prefer_ibex]].
