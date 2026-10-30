CB inverse/TOP completeness fix (branch fix/v155-cb-inverse-top), 2026-10-29

Binaries (scratch, not committed): km.before = 4f2b29aa, km.fix1 = b674d38d,
km.fix2 = ea161e57, km.final = fdc94ac2. km.fix2 and km.final differ by a
comment. Design notes: docs/CB-COMPLETENESS-FIXES.md.

Causes
1. engine.rs attach_shared_base / seed_worked_off: clauses of the shared
   facts+TBox closure never entered the per-context r-Succ pool, so a parent
   label such as D(y) from TOP <= D was never offered to successors.
   Fixed in b674d38d. Every CB-route wrong answer in both seed sets came
   from this cause (each is right with KM_NO_SHARE=1 on km.before).
2. engine.rs retained_insert_boundary: a retained CB insertion that adds
   the first backward-role clause kept rsucc=false. Fixed in ea161e57
   (RSuccActivation boundary -> exact rebuild). Reproducer:
   minimal/retained_rsucc_activation.* (km incremental session).
3. konclude_ht/bridge.rs Builder::atmost_q / atmost / atleast_q (fixed in
   d4d8dfd1, follow-up task): the source-TBox bridge built <=0 R.C as a
   CCATMOST with parameter 0. The ported saturation's critical at-most test
   counts only linked successors, so a predecessor over the inverse role was
   never counted and D stayed satisfiable on fresh seed 1241
   (minimal/bridge_inverse_atmost0_unsat.ofn). Konclude's builder emits
   forall R.not C instead; the bridge now does the same (and builds >=1 R.C
   as exists R.C). See docs/HYBRID-CB-HT.md section 8.

Files
  counts.tsv            outcome counts per run (seeds/*.txt)
  seeds/s700_*          700 ALCHIQ seeds 1-700 (agent-assets sq/ + bridge/seeds,
                        gold bridge/gold), 60 s cap, 8 workers
  seeds/f300_*          fresh gen_alc.py seeds 1000-1299, HermiT gold from
                        agent-assets oracle/, 60 s cap, 8 workers
  eval.py               harness (adapted from 2026-10-28/bridge/eval.py)
  ddmin.py              one-axiom-removal minimiser used for seed 1241
  corpus.sh, corpus_compare.tsv
                        auto-route corpus spot check, km.before vs km.final
  test_results.txt      cargo test result lines
  minimal/              reproducers not covered by engine fixtures

ERR in the seed files is a 60 s timeout (no answer), not a wrong answer.

Seed outcomes (WRONG = differs from HermiT; ERR = 60 s timeout)
  700 seeds, cb_plain1: before 674 ok / 2 WRONG / 22 ERR; final 676 ok /
                        0 WRONG / 22 ERR (fix1: 674 ok / 0 WRONG / 24 ERR)
  700 seeds, auto:      before 695 ok / 0 WRONG / 3 ERR; final the same
  fresh 300, cb_plain1: before 290 ok / 3 WRONG / 7 ERR; fix2 294 ok /
                        0 WRONG / 6 ERR
  fresh 300, auto:      before 296 ok / 1 WRONG / 3 ERR; fix2 the same
                        (seed 1241, the ht_bridge miss above)
  2 hermit-error seeds in the 700 set have no gold.
Pure-CB cost: seeds 169, 241, 483 answer correctly before the fix in
  1.4 s / 0.02 s / 14 s and take >150 s / 49 s / 141 s after it on cb_plain1;
  km.before with KM_NO_SHARE=1 on seed 169 also exceeds 100 s, so the cost
  is that of the specified r-Succ product. Seeds 147 and 241 sit near the
  60 s cap and flip between ok and ERR across runs.
Corpus: all 10 ontologies byte-identical sorted SUB/UNSAT on auto.

Bridge follow-up (2026-10-29, second task)
Binaries: km.pick = 75cf7844 (this branch plus cherry-picks 6735a788 and
c1f5a235, before the bridge fix), km.br1 = d4d8dfd1 (bridge fix).
Diagnosis on km.pick, minimal/bridge_inverse_atmost0_unsat.ofn:
  auto, ht_bridge, production_all (source TBox): D <= Q3, no UNSAT D
  same routes with KM_NO_SOURCE_TBOX=1 (clause translation): UNSAT D
  ht_bridge with KM_HT_NO_SATURATION=1: UNSAT D (the miss is in saturation)
Harness: eval.py now separates DECLINE (ht_bridge exit 3, "bridge defer"),
TIMEOUT (60 s), and ENV (thread-spawn EAGAIN or allocation failure on the
shared host, which ran near its commit limit). ENV seeds are retried up to
three times, and recheck.sh reruns any that remain one at a time; after the
recheck no ENV or ERR remains. Files: bridge-seeds/, bridge-counts.tsv.

  set / route          km.pick                          km.br1
  700  auto            695 ok, 0 wrong, 3 timeout       695 ok, 0 wrong, 3 timeout
  700  ht_bridge       654 ok, 0 wrong, 43 declined,    654 ok, 0 wrong, 43 declined,
                       1 timeout                        1 timeout
  300  auto            296 ok, 1 wrong (1241), 3 t/o    297 ok, 0 wrong, 3 timeout
  300  ht_bridge       278 ok, 1 wrong (1241), 18 decl, 279 ok, 0 wrong, 18 declined,
                       3 timeout                        3 timeout
  (700 set: 2 seeds without HermiT gold.) Per seed, km.pick and km.br1
  differ only on 1241.
Corpus (auto, bridge-corpus_compare.tsv): all 10 sorted SUB/UNSAT outputs
  identical between km.pick and km.br1 and identical to km.before. The host
  was loaded; repeated pairs (bridge-corpus_repeat_timings.txt) show
  15803 117-161 s vs 116-140 s and 6682 31-33 s vs 31-34 s (no change), and
  850 9 s vs 2.2 s on both repeats (faster after the fix).

At-most predecessor probes (2026-10-29, third task)
20 probes with HermiT gold (engine/tests/fixtures/bridge_atmost_predecessor/):
<=1 and <=2, qualified and unqualified, forward and inverse, through a
sub-role and through InverseObjectProperties, plus satisfiable controls. Run
with km at d4d8dfd1 on six configurations (atmost-predecessor/probe_results.txt):
  ht_bridge (source TBox), auto, cb_plain1: 20/20 agree with HermiT
  ht_bridge + KM_HT_NO_SATURATION=1: 19/20 (inv_atmost1_q_pred misses
      D <= F; K unsatisfiable is found)
  ht_bridge + KM_NO_SOURCE_TBOX=1: 12/20; misses every <=2 case that needs
      the predecessor counted (8 probes, listed in the test)
  ht_bridge + KM_NO_SOURCE_TBOX=1 + KM_HT_NO_SATURATION=1: 19/20 (the same
      D <= F miss)
The clause-translation <=2 misses disappear without saturation and do not
occur without a predecessor (succ_only_* probes), so they come from the
saturation pre-pass under the clause encoding. Identifying the __inv__ role
with the native inverse object did not change them (tried, reverted).
Neither failing configuration is an automatic route. No code changed.
