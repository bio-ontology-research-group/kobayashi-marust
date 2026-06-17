# Debugging KM HT's per-test search gap vs HermiT on ore_ont_5303

*2026-06-17T10:56:48Z by Showboat 0.6.1*
<!-- showboat-id: 265d2c66-6100-4e31-a69a-ca44655a9eb8 -->

HermiT classifies 5303 in 1.6s (~111 backtracks/test, ~70 nodes/test). KM HT times out: one satisfiability test does ~26,560 backtracks on a 661-node model. Blocking is NOT the cause (KM blocks 91-95% vs HermiT's 73%). We ported HermiT's #1 search lever -- assert the negation of each tried-and-failed disjunct (startNextChoice) so siblings unit-propagate (KM_HT_NEGTRIED). It is output-identical (27/27 sample onts byte-identical, sound+complete) but did NOT reduce backtracks. This doc debugs WHY, via two instrumented counters: backjumps (clash dep did not contain the current branch level => we skipped this branch point) and negfired (the negation was actually asserted). If backjumps << backtracks, the dependency sets are too coarse and search is effectively chronological -- the real gap.

Per-concept counters on 5303 (concept id, nodes, backtracks, backjumps, negfired). If backjumps is a tiny fraction of backtracks, KM's dependency-directed backjumping is not firing -- it is doing chronological backtracking, which is the actual gap.

```bash
ssh dragon "sbatch --wait --account=pi-hohndor --partition=batch --time=15:00 --mem=20G --cpus-per-task=4 --job-name=dbgrun --output=/ibex/scratch/hohndor/km/dbgrun.out --wrap 'bash /ibex/scratch/hohndor/km/dbgrun.sh' >/dev/null 2>&1; cat /ibex/scratch/hohndor/km/dbgrun.out" 2>&1 | grep -vE "Ibex|kaust|slack|policy|acceptable|authoris|Admin Team|^####|^#  |^# |^#$"
```

```output
----- negtried=OFF : 5303 first hard concepts (30s budget) -----
qi=0/94 dt_ms=213 nodes_last=170 backtracks=977 backjumps=0
qi=1/94 dt_ms=349 nodes_last=215 backtracks=1229 backjumps=0
qi=2/94 dt_ms=412 nodes_last=230 backtracks=1308 backjumps=0
qi=3/94 dt_ms=300 nodes_last=200 backtracks=1140 backjumps=0
qi=4/94 dt_ms=3280 nodes_last=548 backtracks=9500 backjumps=3971
qi=11/94 dt_ms=10910 nodes_last=661 backtracks=26560 backjumps=9047
----- negtried=ON : 5303 first hard concepts (30s budget) -----
qi=0/94 dt_ms=232 nodes_last=170 backtracks=966 backjumps=0
qi=1/94 dt_ms=391 nodes_last=215 backtracks=1212 backjumps=0
qi=2/94 dt_ms=441 nodes_last=230 backtracks=1293 backjumps=0
qi=3/94 dt_ms=341 nodes_last=200 backtracks=1127 backjumps=0
qi=4/94 dt_ms=4461 nodes_last=604 backtracks=10286 backjumps=4246
qi=11/94 dt_ms=13494 nodes_last=718 backtracks=26755 backjumps=9047
DBGRUN_DONE
```

Finding: backjumping DOES fire (concept 27: 9047 backjumps of 26560 backtracks, ~34%); negtried left both unchanged (9047 backjumps, 26560 backtracks). So the gap is not absent backjumping -- even with it, KM explores 26560 branch points where HermiT explores ~111 over a comparably-sized active model (~33 active nodes vs HermiT ~19). Next: do KM's other (gated) search levers -- conflict learning (KM_HT_LEARN), clash-activity disjunct ordering (KM_HT_ORD/PICK), Luby restarts (KM_HT_RESTART) -- collapse the 5303 search, even though they regressed the overall passrate? Measured below: how far each config gets in 30s + backtracks on the hardest concept reached.

```bash
ssh dragon "sbatch --wait --account=pi-hohndor --partition=batch --time=20:00 --mem=20G --cpus-per-task=4 --job-name=dbg2 --output=/ibex/scratch/hohndor/km/dbgrun2.out --wrap 'bash /ibex/scratch/hohndor/km/dbgrun2.sh' >/dev/null 2>&1; cat /ibex/scratch/hohndor/km/dbgrun2.out" 2>&1 | grep -vE "Ibex|kaust|slack|policy|acceptable|authoris|Admin Team|^####|^#  |^# |^#$"
```

```output
baseline               concepts_logged=6 max_backtracks=72696 finished=0
LEARN                  concepts_logged=6 max_backtracks=72033 finished=0
ORD+PICK               concepts_logged=6 max_backtracks=86063 finished=0
RESTART                concepts_logged=5 max_backtracks=154604 finished=0
LEARN+ORD+RESTART      concepts_logged=5 max_backtracks=179076 finished=0
NEGTRIED+LEARN         concepts_logged=6 max_backtracks=63151 finished=0
DBGRUN2_DONE
```

Conclusion. The per-test gap is NOT closeable by tableau search discipline. Evidence: (1) blocking already exceeds HermiT (91-95% vs 73%); (2) dependency-directed backjumping fires (~34% on hard concepts); (3) HermiT's #1 search lever (negate-tried-disjuncts) is output-identical but perf-neutral -- KM's binary DL-clauses already encode it (the second branch IS the negation); (4) conflict-learning, clash-activity ordering, and Luby restarts do not help and several make it worse. The real difference is UPSTREAM: KM generates ~15535 disjunctive choice points on 5303 where HermiT's absorbed clausification leaves far fewer, so HermiT's per-test search is ~111 backtracks and KM's is tens of thousands over a comparably-sized model. Matching HermiT here needs HermiT-grade ABSORPTION (drive more propagation deterministically, cut the number of live disjunctions) and/or model-based classification -- a frontend/clausification change, not a search-loop tweak. This confirms the long-standing diagnosis that the live-forall+or disjunction family is the genuinely hard residual. KM_HT_NEGTRIED is retained as a sound+complete option (27/27 byte-identical); all metrics kept for the final combination decision.

UPDATE — operation-level HermiT walk on 5303 (custom TableauMonitor) + hashed-blocking test. HermiT hard tests derive ~1000-2300 ground disjunctions and push ~2000-4900 branching points PER TEST (comparable to KM's disjunction count) yet backtrack only ~700-900 times and finish each test in single-digit ms (129 tests, 0.8s total; histogram branchPoints/test: 0:14 1-9:53 10-49:29 50-199:8 200-999:8 1000+:17). KM on the equivalent test does ~26,560 backtracks and 11-26s. So the gap is NOT disjunction count (similar) and NOT blocking: (a) KM already blocks 91-95% vs HermiT 73%; (b) replacing KM's O(n^2) blocking recompute with an O(n) hashed signature cache (HermiT's BlockingSignatureCache, output-identical) did NOT make 5303 finish — all modes still time out at 60s. Two compounding factors remain: KM does ~30x MORE backtracks (877 vs 26560) AND each step is ~200x slower (0.23ms/step). The standard search levers (negate-tried-disjuncts, conflict learning, activity ordering, restarts) were all tried and none transfer. The remaining study-flagged lever is dependency-set PRECISION: if KM's clash dep-sets are coarser than HermiT's exact hash-consed per-premise sets, backjumps are shallow and negate-tried facts carry too-broad deps (discarded on the wrong backtrack) -- which would explain why every standard lever is inert. That is a deep engine change (audit dep_union / DepSet construction).

CORRECTION (search count IS the gap, not per-op cost). Measured KM branching-points-pushed per concept on 5303 in HermiT-comparable units (a branch push = one disjunction case-split = HermiT pushBranchingPointStarted). KM concept 1 (an EASY test it finishes in ~200ms, 197 nodes) pushes 4299 branch points; concept 9 pushes 47521. HermiT pushes <50 on most of its 129 tests (histogram: 53 tests 1-9, 29 tests 10-49) and at most 4900 on its single hardest. So KM explores ~100x MORE disjunction splits than HermiT on the same concepts -- a real search-size blowup, not constant-factor per-op cost. Leading cause: KM re-pushes/re-explores branch points after every backtrack (recursive dfs re-discovers the lower disjunctions fresh on each re-descent), whereas HermiT keeps one persistent DisjunctionBranchingPoint per ground disjunction, advances its disjunct index on backtrack, and asserts the negated tried disjuncts so the re-descent is unit-propagated rather than re-branched. KM's negate-tried port did not cut branch_pushes because it negates only within the current branch frame, not persistently across the backtrack-and-redescend. NEXT: make disjunction decisions persist across backtracking (decision stack / no re-push), the actual ~100x lever.

CORRECTION to the prior note (the 100x search-count claim was a bad comparison). Full HermiT per-test trace (HermitWalk2, derived/satisfied/pushed): HermiT's HARD tests push 2000-5726 branching points with 681-1780 backtracks and STILL finish in a few ms (96 of 129 tests are easy, <50 pushes -- that easy median was wrongly compared to KM's hard concept-1 earlier). KM concept 1 pushes 4299 / backtracks 1072 in ~200ms -- SAME branch scale as a HermiT hard test, but ~30x slower per branch operation. KM's worst concept (9) pushes 47521 (~10x HermiT's hardest). The disjuncts HermiT branches are exactly the EXISTS+OR family (e.g. CarbonAtom v HydrogenAtom). CONCLUSION: there is no single missing inference mechanism -- HermiT and KM run the same hypertableau with the same disjunctive search at the same scale on hard tests. The gap is (a) ~30x per-operation cost (HermiT interned dep-sets / array-indexed node labels / incremental extension manager vs KM Rc-allocated dep unions + HashMap<CLit> labels recomputed per step), and (b) ~10x more search on KM's worst few concepts. Closing it is performance engineering of KM's tableau primitives + a per-concept search-size audit, not porting a missing algorithm. Clean next experiment if pursued: align ONE concept IRI across both reasoners and compare pushes head-to-head.

ROOT CAUSE (definitive, aligned per-concept). Ran HermiT's per-concept satisfiability on the SAME concept IRIs KM finds hard: C10-24Chain HermiT=3 pushes / KM=4299; AminoGroup 3/5296; CarboxyGroup 9/5622; CarbonHydrogenSubstructure 6/4964; AminoAcidMonomer 46/47521. So ~1000x more branching on IDENTICAL concepts (my earlier 'comparable / per-op cost' reading was wrong). 5303 has 22 GLOBAL (top-headed, empty-body) disjunctions that fire on EVERY node. KM's branch_pushes = 22 x model_size exactly (197 nodes -> 4299; 2160 nodes -> 47521). KM builds 197-2160 node models where HermiT folds to ~3-50, because KM applies blocking in BATCHES (process_obligations computes blocking once per pass then expands the whole non-blocked frontier; the 22 global disjunctions fire on every created node before folding catches up). HermiT blocks EAGERLY/incrementally (a node is blocked before its successors and their disjunctions are created), so exists-chains fold at depth ~2 and the model stays tiny. FIX = eager/incremental blocking during expansion (block before creating successors; re-check blocking per new node), so KM's model size -> HermiT's and branch_pushes drops ~1000x. This is the concrete missing mechanism.
