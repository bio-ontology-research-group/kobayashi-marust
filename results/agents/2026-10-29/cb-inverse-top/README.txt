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
Open (not CB, not in this worktree's scope): the ht_bridge route misses
   D unsatisfiable on minimal/bridge_inverse_atmost0_unsat.ofn (fresh seed
   1241); cb_plain1 and default1 answer it. auto routes it to the bridge.

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
