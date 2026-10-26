---
name: project_km_cb_scaling
description: "KM ORE scaling: root-cause of 40 failures + fixes landed -> 555 ok (frontend streaming-parse fix recovered giant 15059); residual is engine-bound. Repo moved to ~/Public/software/kobayashi-marust"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3e94cd1a-f3b7-4c1c-a08d-39c076fa2104
---

Diagnosis of KM's 40 remaining ORE failures (2026-06-09, user: "fix the CB engine
to work with the remaining ontologies"). 21 timeout + 19 memout; gap to Konclude 587.

**Two root causes, both confirmed empirically on ws:**

1. **Within-ontology parallelism is self-defeating under a memcap.** `reasoner.rs`
   `saturate()` splits named queries into `available_parallelism` (64 on
   unimatrix) chunks, each a full `Engine` (`build_engine()` clones clauses0) that
   **re-derives all shared successor contexts**. On existential-heavy onts this
   multiplies the dominant cost by thread count. Measured on 2397 (ALCH, 49k
   clauses): 1 thread = 9GB/138s **SUCCESS**, 8 thr = 40GB, 16 thr = 84GB, 64 thr
   = 20GB **MEMOUT @ 9s**. Single-threaded shares successor contexts (one engine,
   get_or_create dedups) → does the work once. Fix: parallelize ACROSS ontologies
   (the Slurm harness already does), set `KM_THREADS=1`. BUT this alone recovers
   ~0-1 onts: it converts memout→timeout because the onts are TIME-bound, not
   memory-bound. Single-threaded slashes memory (5303: 6.7GB→334MB, 541:
   5.9GB→682MB) but still >240s.

2. **Hyper rule cartesian-product blowup on number restrictions (the real
   time-killer).** Profiled 13912 (ALUIN(D), 1486 ax) which spins 240s at only
   **5.5MB** (flat memory = all resolvents subsumed). Added KM_PROF instrumentation
   to engine.rs (per-rule `CART_COMBOS=[hyper,pred_local,pred_from_neighbor]`,
   gated; `bump_cart` currently UNGATED — must gate/remove before real build).
   Result: blowup is **entirely in Hyper** (`[738171,0,455]` and climbing). A `≤n
   R.C` clause normalises to `R(x,y1)..R(x,yk) ∧ C(y1).. → ⊔ yi≈yj` (many neighbour
   body atoms); each `R(x,yi)` matches every successor predicate → `(#succ)^k`
   resolvents, nearly all immediately subsumed. Classic known-hard CB number-
   restriction case. Fix needs symmetry/subsumption-aware enumeration in the
   Lean-verified Hyper rule (risky; number completeness subtle).

**Key infra finding: the benchmark never uses the tableau.** `route.py` is a
working hybrid router (CB vs hypertableau) — design in docs/HYBRID-TABLEAU.md —
that sends live-`∀+⊔` / inverse / nominal / number onts to the validated tableau
(`tableau_cli` via cb_to_ht.py; fragment ALC+H+SH/SHI+SHQ+SHO/SHOQ). But
`ore_runone.py --reasoner km` calls `owl_classify.py` (CB-only, elc-vs-engine),
so the ~12 disjunction-blowup onts are fed to the engine known to explode on them.
`tableau_cli` is NOT deployed to ~/bench/km/.

**Failure taxonomy (40):** disjunction-blowup ALC/S/SH/ALCHI/ALCI (~12, tableau's
job); number F/N/Q (~15, Hyper surgery or tableau SHQ); role-chain SRI/SRIF (~8,
hard); giants 3M-axiom 450-550MB (~4, size, neither path).

**FIXES LANDED (payg-strategy, 2026-06-09 eve):**
- Hyper backtracking join (commit 2c67c61): `hyper_join()` replaces full
  cartesian product; 738k→59k combos on 13912; sound (kmjoin agg vs gold: 0
  both-disagree, unsound/incomplete ⊆ baseline). All cargo tests pass.
- Adaptive threading (commits 6798758,b199d3d): `owl_classify._run_engine_adaptive`
  runs parallel under an RSS watchdog (KM_PAR_MEM_GB=18) killing only the engine
  child, retries single-threaded on overflow. Blanket KM_THREADS=1 was
  NET-NEGATIVE (−12 speed regressions vs +1..4 memout recoveries); adaptive keeps
  parallel speed AND recovers memory-bound onts. Validated on 2397 (parallel
  kill@18GB → ST retry → ok in 137s). ore_runone forces KM_THREADS=16 (first
  attempt uses it). CHANGELOG.md in repo tracks everything.

**TABLEAU IS A DEAD END for these onts:** route.py validation — tableau FAILS
(5303 errored) or HANGS (timeout 200s; found 6h runaway tableau_cli procs).
Validated on small synthetic only, not real ORE. Do not pursue.

**KEY: Sequoia (same calculus!) solves 16/40 KM failures** (1016 11460 11623
15059 16444 16744 2397 4205 4604 5303 6212 7127 7581 7956 8737 9944 — incl giants
+ disjunction + role-chain + number). So KM's blowup is IMPLEMENTATION
inefficiency, not calculus limit — real headroom to match Sequoia. Konclude
36/40, ELK 39/40 (ELK likely incomplete, ignores non-EL axioms). Giants:
KM frontend alone peaks 20-24GB on 450-550MB onts (memout before engine starts);
Sequoia's OWLAPI frontend is more compact.

**FINAL RESULT (2026-06-10): ORE 551 -> 554 ok (+3, 0 regressions), SOUND.**
Recovered 2397 (fully correct), 9944 + 9724 (sound-but-CB-incomplete on
number/inverse). vs gold: unsound unchanged at 8 (pre-existing nominal/number
under-detected-unsat: 15288 15516 2669 443 6720 7052 7901 8941), both-disagree=0,
no agree->fail regression. 4 commits pushed to payg-strategy (2c67c61 Hyper join,
6798758+b199d3d adaptive retry, 06d91d0 batched propagation). CHANGELOG.md has the
full table. Winning binary = kobayashi-marust-batch (now also = par-cur on
unimatrix ~/bench/km/); config = job 5265 (ore_km_batch.sbatch: KM_PAR_MEM_GB=18,
no KM_THREADS, adaptive owl_classify.py deployed to ~/bench/km/py/).
- Batched propagation (06d91d0): message loop drains whole batch, saturates each
  target, propagates each touched ctx ONCE/round (was per-message). ~1.5x faster,
  fixpoint-preserving. Recovered 9724.

**FRONTEND FIX (2026-06-10 PM): ORE 554 -> 555 ok, SOUND, 0 regressions.**
The 3M-axiom giants (8737 15059 16744) memouted IN THE FRONTEND at ~20GB before
the reasoner started. Fixed NOT by JSON u32-interning but by making `ofn` stream:
(1) zero-copy lazy tokeniser, tokens = &str slices not Vec<String> (sexpr.rs);
(2) for_each_ontology_child streams each axiom subtree + drops it, never holds
the whole AST, and the rbox/declared side-scans re-stream instead of deep-cloning
onto_nodes (parse.rs); (3) DLClause body/head = sorted-dedup Vec<Atom> not
BTreeSet<Atom> (over-allocates per clause), Ontology axioms behind Rc
(clauses.rs/syntax.rs). Frontend peak **19.2GB -> 3.6GB** on 8737 (45s->20s).
Output BYTE-IDENTICAL to old frontend across whole corpus + all 3 giants
(jobs 5295/5297). **Recovered 15059 (memout->ok, 52s/5GB, AGREES with gold).**
8737/16744 now reach the engine (not EL-safe, inverse roles) -> engine-timeout at
240s/18.5GB = engine-scaling residual, NOT frontend. Commits ac153ef (frontend)
+ 2701255 (gitignore CLAUDE.md), pushed to payg-strategy. Full sweep job 5299:
km 555 ok / 32 timeout / 4 memout; vs gold agree=530 incomplete=17 unsound=8
both-disagree=0 (UNCHANGED soundness; the +1 ok = 15059 which agrees). km now
LOWEST median peak mem of all reasoners (45.9MB; konclude 65, sequoia 536).
The 4 memouts now (10781 15491 16444 6682) are CB-ENGINE ~20GB blowups, not
frontend. Streaming ofn deployed as canonical ~/bench/km/ofn (old = ofn.btreeset.bak).

**REPO MOVED (2026-06-10): kobayashi-marust -> ~/Public/software/kobayashi-marust**
(was ~/Documents/papers/neuro-symbolic-independence/kobayashi-marust). Standalone
repo, clean move. Wrote a full local CLAUDE.md (git-IGNORED — repo remote is
PUBLIC, CLAUDE.md has internal host IPs/paths) with all continuation instructions
(build->ws, bench->unimatrix, hosts, architecture, current state, residual). User
will RESTART from the new folder. ws clone still at ~/km-frontend/kobayashi-marust.

**RESIDUAL (engine-bound, needs LARGE efforts; frontend is now DONE):** (a) live-∀+⊔
disjunction message-traffic explosion — Sequoia (same calculus) solves via mature
redundancy/ordering; (b) giants 8737/16744 now ENGINE-time-bound (inverse+size CB
blowup), and 4 CB-engine ~20GB memouts (10781 15491 16444 6682); (c) role-chain
propagation volume. Constant-factor speedups won't crack these.

**Benchmarks:** kmbatch FINAL=job 5299 (555 ok; status map saved
~/bench/ore_jobs/status_kmbatch_5299.json). Prior 5265=554. kmad=5235.
5199=blanket-ST (net-neg, donot use). ofn diff jobs 5295/5297 (byte-identical).
See [[project_km_hybrid_tableau]], [[project_km_nominals_routing]],
[[project_km_correctness_audit]], [[project_km_rust_elc]], [[project_km_rust_frontend]],
[[feedback_no_heavy_laptop]].
