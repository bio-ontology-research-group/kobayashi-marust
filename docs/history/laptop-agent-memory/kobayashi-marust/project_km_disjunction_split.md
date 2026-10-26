---
name: project_km_disjunction_split
description: "Direction B (disjunction case-splitting, KM_SPLIT) increment 1 LANDED on branch disjunction-split (1e5506a), gated default OFF, sound+complete. Recovers 0 of the disjunction timeout family — their nondeterminism is at the successor/conditional level, needs structural splitting (increment 2 = DPLL(CB) decision trail, multi-session). Direction B converges with Direction C (split+learning = caching tableau). Build host = unimatrix ~/km-build (ws DOWN)."
metadata:
  type: project
  originSessionId: 4530cb60-f93c-475f-b077-f611d49979db
---

**2026-06-13 — Direction B (disjunction splitting), user-directed: "do B then A,
then full benchmark, then analyze whether C is worth doing."** Design:
`docs/DISJUNCTION-SPLITTING.md`. Branch `disjunction-split` (off payg-strategy),
pushed to origin.

**Increment 1 LANDED (`1e5506a`, gated `KM_SPLIT`, default OFF, SOUND+COMPLETE).**
Semantic case splitting instead of unrestricted resolution on incomparable
disjunctions. `classify_assume(query, assume)` + `read_closure` (engine.rs) run a
branch's tame ORDERED closure on a FRESH engine (isolation) and read ClosureFacts
(forced units / residual concept-on-x fact-disjunctions = split points / ⊥).
`split_recurse` + `saturate_split` (reasoner.rs): branch on a fact-disjunction,
intersect forced units over open branches, query unsat iff all branches close.
Per-thread `BRANCH_ORDERED` total-order (calc.rs) — branches ordered (tame),
FALLBACK unordered (complete), because ordered-alone is incomplete
([[project_km_perf_pivot]] KM_ORDERED_ALL verdict). KEY BUG FOUND+FIXED: first
A/B had split_mode coupled to ordered globally → 5107 "solved" was the INCOMPLETE
ordered fallback finishing fast with WRONG answers; the thread-local fix made the
fallback complete (5107 then correctly times out).

**Conservative completeness guard** (read_closure scans ALL contexts): set
`foreign` → fall back to complete default engine whenever any context has a
disjunction that is NOT a query-context body-empty concept-on-x fact-disjunction
(conditional / role / equality / successor-context disjunction). Guarantees
SOUND+COMPLETE on every ont; recovered fragment = queries whose only
nondeterminism is concept disjunctions on x over Horn successors.

**Validation (66+16 tests + A/B vs default engine):** 14/14 byte-identical on
finishable small onts; **13383 IDENTICAL with 368/368 queries split-classified, 0
fallback** (splitting itself correct on a real named-disjunction ont, not just
fallback). **Benchmark recovery = 0**: the live-∀+⊔ timeout family (5107, 5303,
12698, 2313, 12141, 10702, 9540, 1603 ...) puts nondeterminism at the SUCCESSOR
level (`A⊑∀R.(C⊔D)`, `A⊑∃R.⊤` → C⊔D in the successor context), which increment 1
does not split → falls back (complete-engine timeout) or per-branch closure times
out. See [[project_km_disjunction_blowup]].

**Increment 2 LANDED (`d57e30d`, gated KM_SPLIT, SOUND).** Structural splitting:
generalised from query-root fact-disjunctions to disjunctions in ANY context,
keyed by core. `branch_decisions: HashMap<core, [assumed disjunct iris]>` seeded
as `⊤→d(x)` facts when a context with that core is created (cores deterministic
given decisions → same successor context + same seed across fresh-engine-per-
branch runs). This is how a disjunct is assumed in a SUCCESSOR context (the
live-∀+⊔ structure `A⊑∀R.(C⊔D)`). SOUNDNESS guard `chain_unique_contexts`: split
only contexts reachable from a root by SINGLE successor edges — central strategy
MERGES by core, so ≥2 incoming edges = successors that could pick disjuncts
independently, shared split would force agreement (UNSOUND). Non-chain-unique /
role / eq / non-central disjunctions → foreign → fall back to complete default.
Validation: 66+16 tests; **14/14 A/B identical; 13383 identical; SOUND**.
**Recovery still 0**: split now ENGAGES on successor disjunctions (5303/5107/
12698/2313 split instead of immediately falling back) but the branch search
**does NOT converge in time without conflict-driven learning** — all family onts
time out mid-split (rc=124).

**Increment 3 LANDED (`079da53`, gated, SOUND, but recovers 0 — the MEASURED
CEILING).** Built a UNIT-PROPAGATION mode: Hyper resolvent builder (under
branch_ordered) suppresses resolvents combining ≥2 derived disjunctions (the
fact×fact multiplication) → per-context closure stays tame; splitting recovers
suppressed derivations. Sound (14/14 A/B; 13383 identical full-split/0 fallback).
Recovery still 0. Node-rate + fixpoint instrumentation (5303/5107/12698/2313/
10702) shows WHY — two failure modes fatal to LAZY splitting (saturate-to-
fixpoint THEN split): (1) 5303/5107/12698/10702 — the per-query closure (saturate
+ MESSAGE FIXPOINT) never completes (<100 split nodes, no progress in 40s); the
blow-up is computing the closure ITSELF, before any disjunction is exposed.
(2) 2313 — split loop completes but all 1688 queries FALL BACK (disjunctions in
non-chain-unique contexts; soundness guard refuses) → complete engine times out.

**ARCHITECTURAL CONCLUSION:** lazy splitting over the MONOTONE CB engine cannot
recover this family. Recovery needs splitting INTERLEAVED with saturation (decide
BEFORE the closure explodes) + backtrack — which fights the append-only arena
(no cheap retraction). **REFINED task #27 / C verdict (FLIPPED):** earlier leaned
"build the trail into the CB engine (C-by-integration)"; the measurement shows
interleave+retract is what a TABLEAU is built for and what the monotone CB engine
is built to AVOID. So a DEDICATED/standalone caching tableau (Direction C, routed
as a sub-solver) is now the CLEANER path for this family — NOT a CB-engine
retrofit — provided tableau_cli is brought to benchmark grade (currently errors/
hangs on real ORE inputs). Direction A layers on once splitting converges (moot
until the tableau exists). Lean-cert task #23 still pending (for whichever
recovery path).

**Lever 2 (KM_PAR_SAT) earlier this session:** built per user override, COMMITTED
fb117df on branch lever2-parsat (pushed), gated default OFF, confirmed INERT
(message fixpoint near-sequential, batches size 0-2). See [[project_km_perf_pivot]].

**DIRECTION C AUDIT DONE (2026-06-13, commit 069ef90).** Pipeline EXISTS:
`engine/py/route.py` (hybrid router) + `engine/py/cb_to_ht.py` (CB DL-clauses →
tableau TInput converter, with fragment fencing) + `engine/src/tableau.rs`
(hypertableau, 2006 lines, DFS+checkpoint/rollback, DepSet dep-tracking, subset/
pairwise/equality blocking, nominals o-rule) + `oracle/validate_ht.py`. tableau
TInput format = UN-Skolemized (∃-atoms `e`), different from engine's `{clauses}`;
cb_to_ht bridges. Disjunction-family audit (route.py pipeline, build host):
- **5107** (in-frag, live=1, 24 NOMINALS), **5303** (in-frag, clean ALC, live=13,
  no inv/num/nom): tableau **TIMES OUT**. CORRECTED DIAGNOSIS (commit a8053e1):
  an earlier "classification overhead" read was a subprocess STDERR-CAPTURE
  ARTIFACT (capture_output pipe drains only after exit → partial stderr lost on
  timeout-kill; redirect stderr to a FILE to see truth). Real blocker: on 5303
  the tableau never gets past `consistent([])` — "classify START" prints,
  "consistent([])=" never does. A SINGLE model build doesn't complete →
  classification caching (told subsumers / pseudo-model merging) is the WRONG
  LAYER (sits above a non-completing model build). Blocker = MODEL CONSTRUCTION:
  horn_saturate is a NAIVE non-incremental fixpoint (re-scans all ~884 clauses
  every iteration) with NO concept→node index (scans all nodes per unbound
  concept atom); a single saturation pass is the cost (<200 horn iters, <100k
  nodes, <200k expands — so matching-bound, not node/branch explosion). CORRECT
  target = semi-naive + indexed saturation (port CB engine's hyper_join/indexing
  to the tableau). Whether it recovers 5303 depends on model size (diagnostic
  PENDING — unimatrix went unreachable mid-measurement 2026-06-13 ~13:55).
- **12698/2313/10702/12141** OUT OF FRAGMENT (cb_to_ht fences): complex-domain/
  range (2313,12141 — cheapest to lift; 12141 is then clean ALC live=13 → same
  classify-overhead wall as 5303), inverse+number SHIQ / inverse-functional /
  nominal+inverse SHOIQ / role-chain / symmetric-role (12698,10702 — hard).
**DIRECTION C IMPLEMENTATION (no-good learning) LANDED + MEASURED (commit
16ec50b).** Built CDCL-style no-good (conflict-clause) learning in the tableau's
non-careful expand_inc (SearchState: per-level Concept decisions, learn conflict-
DepSet literals as no-goods, prune branches re-asserting them). SOUND on non-
careful path (stable node ids), 16 tableau tests pass, gated KM_TAB_NOLEARN.
MEASURED on 5303: learning FIRES + HITS (2218 learned, 730 hits @60k tries) but
INSUFFICIENT — ~1% hit rate, decision depth dl=8610. The search is DEEP not WIDE:
building 5303's ~1840-node model takes ~8600 sequential disjunction decisions;
no-goods over NODE-INSTANCE (node,lit) literals don't generalize across distinct
deep nodes. EFFECTIVE form = LABEL-BASED unsat caching (cache "concept-set L
unsat", generalizes across nodes — FaCT++/Konclude technique), which needs a
per-node-SUBTREE recursive sat check, NOT the global-DFS expand_inc. That subtree
restructure + label caching is the next (larger) architectural step. So EVEN
Direction C's caching, done right, needs an architectural change — the 4th layer
where the fix needs a bigger change. Family remains research-grade hard on every
KM approach; KM stays sound+complete on all it finishes (37 failures = timeout/
memout, 0 wrong).

**DIRECTION C: LABEL-CACHING (GLOBAL-CACHING) TABLEAU — FULL REWRITE LANDED +
VALIDATED, recovers 0 of the family (commit 8ebc7db, `KM_TAB_CACHE`, gated OFF).**
User-directed "full fix, rewrite the tableau". Rewrote the non-careful (ALCH, no
inverse/number/nominals) path from one global DFS over a shared completion graph
into a label-keyed global-caching procedure (Goré–Nguyen): in ALCH a node's
satisfiability depends ONLY on its concept label → (un)sat verdicts cache across
every node + every classify query (the generalisation node-INSTANCE no-goods of
16ec50b could not capture). Design in `tableau.rs`: TWO LEVELS — per-node
propositional DPLL (transient, UNcached, so the 2^k partial-assignment space never
enters the cache) + cached ∃-successor SEED satisfiability (`CKey` = base concepts
+ imposed clauses). `∃r.C ⊑ D` clauses (`r(x,y)∧C(y)→D(x)`, 82 in 5303)
internalised to `D ⊔ ∀r.¬C` via synthetic MARKER concepts (id past real concepts)
carrying a `Uni` that pushes ¬C to r-successors when chosen. SOUND cycle handling
WITHOUT an SCC pass: UNSAT always cached (unsat under optimistic blocking ⇒ unsat
in every context); SAT cached only when the witness used no on-stack blocking
(`used==false`, a genuine finite model). Eager ∃-pruning (check each obligation's
successor at every DPLL level — sound: partial node-set ⇒ fewer universals ⇒
partial-unsat stays unsat) + subset blocking over the ancestor stack (sound GFP
for ALCH, Dickson-bounded) + semi-naive INDEXED `close()` (Horn fires only clauses
a new literal triggers; ~50× over naive scan). `build_cprog` fences (→ fall back to
complete `expand_inc`) on any clause outside the recognised shapes; entered only
when `!careful()`.

VALIDATED: 16 tableau tests pass via cache path; 5 real ALCH ORE onts
(11949/9509/10309/13503/2485) cached classification SET-IDENTICAL to validated
`expand_inc` (132/81/6/113/1 subs); no regression (66+16 tests). RECOVERY OF THE
LIVE-∀+⊔ FAMILY = 0 (honest negative): 5303 builds a >1000-deep ∃-chain of
incomparable labels → subset blocking rarely fires → same deep-model wall that
makes 5303 a TIMEOUT FOR `expand_inc` ITSELF. The ⊤ node alone has 120
disjunctions; eager pruning tames the width partly, depth×width not. On 3 other
ALCH onts (8937/1420/4856) the cached path is SLOWER than the global DFS
(deep-recursion + eager re-check) → NOT a strict win → stays gated OFF. 4th
approach to hit this family's wall (CB resolution → CB splitting → tableau
no-good learning → caching tableau). Closing it needs the full production stack:
dependency-directed BACKJUMPING + LABEL-based learning INSIDE the per-node DPLL
(my `local_search` is naive chronological — strictly worse than `expand_inc` per
node), smarter blocking. Multi-session engineering, not an algorithmic gap.
Build: unimatrix `~/km-build`; tin via `MOOSE_HOME=~/sroiq-rerun/pkg/moose
python3 /tmp/mktin.py <ont>`; A/B `tableau_cli` with/without `KM_TAB_CACHE`.

**CDCL IN THE CACHING TABLEAU: backjumping + label-based learning LANDED +
VALIDATED, 5303 still times out (commit 2ac84f1, KM_TAB_CACHE).** User-directed
"add dependency-directed backjumping + label-based learning inside the per-node
DPLL". `local_search` now tracks a SOURCE-LITERAL reason (seed-base + disjunction
decisions) per derived literal in `cdep`, on a TRAIL (undo in place — the first cut
cloned set+cdep per branch = O(set²), which stalled everything). Conflicts (clash /
⊥ / unsat ∃-successor / fired no-good) carry that reason; disjunct whose conflict
omits it → BACKJUMP past the disjunction; all-disjuncts-fail → LEARN
`guard ∪ ⋃(conf_i\{d_i})`. No-goods over CONCEPT LITERALS (not node instances) →
one prunes EVERY node whose label ⊇ it (the cross-node generalisation 16ec50b's
node-instance form lacked); watched by smallest literal (`ng_watch`). Learning
gated to imposed-free nodes (node-independent derivation) for soundness. SOUND BUG
FOUND+FIXED via the A/B: a clashing literal returned from `close_dep` BEFORE being
trailed leaked into sibling branches → spurious unsat → unsound EXTRA subsumptions
on 9509/10309; fix = trail every insert BEFORE the clash check. VALIDATED: 16
tableau tests + 5 real ALCH onts (11949/9509/10309/13503/2485) set-identical to
`expand_inc`; 66+16 green. MEASURED on 5303: learning FIRES HARD (134 no-goods,
~9.7k prune hits) but STILL TIMES OUT — search backtracks through an exponential
per-node region pinned at ∃-depth ~226 that learning prunes but doesn't eliminate;
smaller no-goods (KM_TAB_LEARN_MAX=64 default) generalise BETTER than large
(learn_max=400 → 34 no-goods, far fewer hits). 5th technique to the same wall;
production-stack pieces all in place + sound, family not closed within budget.

**C VERDICT (measured):** Direction C is a LARGE TWO-AXIS project — (1) tableau
classification scalability (pseudo-model caching / told subsumers — gates ALL
in-frag onts), (2) fragment extension. NEITHER a quick win. The live-disjunction
family is research-grade hard for BOTH CB (Direction B increments 1-3) AND the
current tableau. No recovery landed; honest negative result on both fronts.

Build: ws DOWN → unimatrix `~/km-build/engine`, `nice ~/.cargo/bin/cargo build
--release`; binaries `~/km-build/engine/target/release/{kobayashi-marust,ofn,elc}`
on NFS (reachable from compute nodes). A/B harness scripts in /tmp + ~/bench.

## UPDATE (2026-06-14): cache path optimised — RECOVERS ore_ont_2313 (gold-exact), C verdict revised UP

The "5th technique hit the wall" verdict above was PESSIMISTIC. Four more sound,
gated cache-path optimisations (commits dbb474a, 8231873 on branch
`disjunction-split`) recovered family members. Profiled 5303 on the cache path
(KM_TAB_CACHE) and found the real wall is NOT exponential — depth grows ~linearly
(33→45→58→70→84→96 over dpll 20k→1M) then plateaus; the costs were (a) learning
DISABLED at imposed nodes, (b) blocking-SAT seeds recomputed (cache stuck ~200 vs
100k+ seed-evals), (c) eager ∃-check rebuilding ~59 successors every DPLL step.

LANDED (all sound, validated set-identical to expand_inc on 19 in-frag onts, 0
wrong / 0 panics):
1. **Taint-aware learning** (dbb474a, the key lever): per-literal taint in
   close_dep; learn globally iff conflict derivation is UNTAINTED (no imposed
   clause used), replacing the `key.imposed.is_empty()` gate. Enables learning at
   the deep imposed ∃-chain nodes. Breaks 5303's hard-stop at depth 96 → 144.
2. **Pseudo-model caching** (8231873): `used:bool` → `block_level:usize` (min
   stack level any subtree-blocking relied on; blocked() returns DEEPEST ancestor).
   Self-contained (block_level >= own level → finite cyclic model → cache
   permanently) + CONDITIONAL (blocked-on-ancestor-i → cache in `cond` map valid
   while level i on stack, purged on its pop; `cond_at[i]` parallel to stack).
   This is the lever that recovered onts.
3. **Incremental eager ∃-check** (KM_TAB_EAGER, default on): skip the rescan on
   DPLL steps adding no trigger literal (trigger = node_exists-body or uni-xbody
   lit); per-role uni index. ~1.77x throughput.
4. **Disjunct ordering** (KM_TAB_ORD, default 0=program order): MEASURED program
   order BEATS the vacuous-marker-first "shallow bias" on 5303 (depth 363 vs 96).

RESULTS: **ore_ont_2313 RECOVERED** — finishes on the cache path with 13967
subsumptions BYTE-IDENTICAL to Konclude gold (verified). Also recovers 2066, 5089
(previously cache-path timeouts). 5303 now ~3x faster (8M dpll/280s, depth 483)
but STILL times out — search accelerates+deepens but oscillates, doesn't converge;
1603, 12141 also still time out. So: family PARTIALLY closed (2313 + others), not
fully. The residue is Konclude-grade search control (the oscillation), not a
missing soundness/completeness mechanism — all the production-stack pieces
(backjumping, taint-learning, pseudo-model caching, ordering) are in place + sound.

Tooling: `engine/py/tab_emit.py` (ofn→cb_to_ht→TInput JSON for standalone
cache-path tuning); TInputs cached on unimatrix `~/tabwork/`. Cache-path is a
SPECIALIST for the live-disjunction family — slower than expand_inc on ordinary
onts (4/26 A/B timeouts where expand_inc finishes) → reach it by ROUTING, not as a
blanket replacement. NEXT: turn oscillation into convergence (better decision
heuristic / restart strategy) to close 5303; then wire a router (live-disjunction
+ in-frag → cache path) into owl_classify.

## UPDATE (2026-06-15): SUBSUMPTION SAT CACHE (KM_TAB_SUBCACHE) — bounds DEPTH, residual wall is WIDTH (commit ccc798e, gated OFF)

User: "continue optimizing the tableau to recover more." 7th technique. NEW lever
not in the chain above: SAT is DOWNWARD-CLOSED in (base, imposed) — a
self-contained model for a MORE-constrained node also models any node with
base ⊆ and imposed ⊆ (Horn closure monotone; dropped universals/∃-obls already
satisfied). So a seed subsumed by an UNCONDITIONALLY-SAT anchor is SAT w/o search.
Distinct from the existing EXACT-key SAT cache (`self.cache`) + subset UNSAT
no-goods. In tableau.rs CacheRun: anchors = search-proven `bl>=my_level` keys,
indexed by every base literal (`sat_watch`); `subsumed_sat` scans the seed's
first-base-literal anchor list (cap KM_TAB_SUBCACHE_SCAN=512) for a base+imposed
superset via subset_sorted. Pure redundancy → no Lean re-cert.

SOUND (IBEX job 47535073): subcache on vs off BYTE-IDENTICAL on 4 oracles the
tableau solves gold-clean — 9635/2313(13967 subs)/2066/5089 — same cons/unsat/subs
through full CONV + multi-query classify. Build + 67+16 tests green. Tooling:
results/{tab_portfolio,tab_subcheck,tab_probe}.py + .sbatch on IBEX; new binary in
SEPARATE target dir `engine/target-sub/` (don't clobber the running portfolio's
`engine/target/release/tableau_cli`).

MEASURED (KM_TAB_STATS, 300s, off→SUB): 5303 depth 579→403 (PLATEAUS), restarts
1654→912 (stabilises); 12141 depth 830→722; 9024 794→873 (neutral). So subcache
BOUNDS the deep-∃-chain explosion (the depth-axis wall the prior 6 techniques hit
— 5303's depth-483 oscillation). **BUT recovers 0 ORE onts**: with depth bounded,
the residual wall is WIDTH — seeds/cache grow unbounded, dpll/branches grow
~linearly, because the ∀+⊔ axioms (`A⊑∀R.(C⊔D)`) make exponentially many
INCOMPARABLE successor labels subsumption can't prune. SAME incomparability core as
the CB engine's pred_lteq ([[project_km_disjunction_blowup]] — KM_ORDERED_ALL also
fails because covering facts keep width). ALSO MEASURED: portfolio of 10 EXISTING
configs (base/ord1/ord2/plain/vsids/restart_aggr/restart_lazy/bignog/noeager/
staticluby) × 6 small targets (5303 9024 12141 1603 541 12653) = 60/60 TIMEOUT at
200s (IBEX 47534771). Targets categorised (results/tab_diag): CLEAN small =
5303/9024/12141; FEAT(number,no-nom, tableau-eligible) small = 1603/541/12653;
big-volume CLEAN (NOT search, throughput/context) = 11460/3215/4604/7246(0 disj,
pure Horn!)/15491.

**VERDICT:** depth axis is now handled (subcache); the family's true blocker is
DISJUNCTIVE WIDTH (incomparable-label explosion), unprunable by subsumption on
BOTH the tableau and CB engine. Closing it needs a width-control mechanism
(Konclude/HermiT-grade: semantic branching + global label subsumption + heavy
absorption), a major build, NOT a cache/heuristic tweak. 9635 remains the only
tableau-route recovery (FEAT number, committed db712ff; re-sweep 559 ok/0 DIFF).

## UPDATE (2026-06-15 cont.): SEMANTIC BRANCHING (KM_TAB_SEMBR) — sound, 0 recovery; width wall CONFIRMED from the width side (commit bcaf5a1, gated OFF)

User-directed 8th technique (AskUserQuestion: "try semantic branching"). n-ary
DPLL semantic split in local_search: once a relevant disjunct d is refuted, assert
¬d (entailed: context∧d unsat ⟹ context⟹¬d) for the remaining siblings on a
node_trail; cdep[¬d]=conf\{d} (source lits, so ¬d is TRANSPARENT in later conflict
analysis since conf\{d}⟹¬d → even backjump stays sound); tainted iff d's
refutation was node-specific; undone on node failure, kept on success (part of
model). SOUND: KM_TAB_SEMBR and KM_TAB_SEMBR+SUBCACHE both BYTE-IDENTICAL to
baseline on all 4 oracles (9635/2313/2066/5089) incl. 13967-sub 2313; 67+16 tests
green (IBEX 47539137).

RECOVERY = 0. Trajectory (240s) on 5303/9024/12141: none converge under SEMBR or
SEMBR+SUBCACHE, and seeds/cache (the WIDTH proxy = #distinct successor labels) are
UNCHANGED. ROOT CAUSE confirmed from the width side: the family's C⊔D successor
disjunctions are COVERING disjunctions whose disjuncts are EACH INDEPENDENTLY
CONSISTENT → asserting ¬C just forces D (what search explores anyway), NO
cross-disjunction clash for semantic branching to exploit. Models are genuinely
WIDE (exp-many distinct, consistent, incomparable successor types). DEFINITIVE: 8
techniques deep (CB ordered-res → CB splitting x3 → tableau node-instance learning
→ caching tableau → backjumping+taint-learning+pseudo-model cache → subsumption SAT
cache → semantic branching), the ∀+⊔ family does NOT converge in ANY KM approach
within the 240s cap; KM stays sound+complete on all it finishes. The wall is
genuine model WIDTH (same incomparability core as CB pred_lteq), not a missing
heuristic. Recovering it = a major Konclude/HermiT-grade build (global structural
node-type caching / told-subsumers / lazy-unfolding absorption), not a tweak.

CAVEAT (recorded): cache-tableau per-RUN search path is NON-DETERMINISTIC (Rust
HashSet randomised seed → order_disj/obligations iteration order differs per
process). Soundness unaffected (results byte-identical, oracle-confirmed); only
single-run depth/dpll deltas between separate processes are partly variance → the
ROBUST signal is binary converge/not. Tooling: results/{tab_portfolio,tab_portfolio2,
tab_subcheck,tab_probe,tab_diag}.py + .sbatch; sembr_eval.sbatch; new binary in
engine/target-sub/ (don't clobber a running portfolio's target/release/tableau_cli).
Gated levers KM_TAB_SUBCACHE (ccc798e, bounds depth) + KM_TAB_SEMBR (bcaf5a1) both
sound, off by default, inert on production.

## UPDATE (2026-06-15 cont.): KONCLUDE/HERMIT-GRADE STACK (typecache + told + lazy) — all sound, 0 recovery; full ORE run done (commit ddb637a)

User-directed (verbatim): implement global structural node-type caching +
told-subsumers + lazy-unfolding absorption, EACH independently, pipeline
(implement→launch IBEX→next), don't stop until all implemented + a full ORE run
launched with them; no Lean yet. DONE, all 3 gated:
- KM_TAB_TYPECACHE: 2nd cache keyed on the Horn-CLOSED type (curv)+imposed (vs the
  pre-close CKey) → collapses distinct seeds closing to the same type. Uncond only.
- KM_TAB_TOLD: told_closure() reads A⊑B off unary node_horn (body[A+],head B+) +
  ⊤⊑T (horn_empty), transitive over all concepts, emits named pairs; classify
  records them WITHOUT sat-test (subset of model candidates → result unchanged).
- KM_TAB_LAZY: in build_cprog, push_node_clause! moves NEGATIVE head lits of a
  disjunction into the body guard → ¬A∨B becomes Horn A→B (no branch), ¬A∨¬B a
  clash, ¬A∨B∨C the guarded A→B∨C (lazy). Logically identical clause.

SOUND: each individually BYTE-IDENTICAL to baseline on all 4 oracles (9635/2313/
2066/5089) incl. 13967-sub 2313; 67+16 tests green (IBEX 47539770/795/820).
INDIVIDUAL CONVERGENCE = 0: each alone leaves all 6 small targets (5303/9024/12141/
1603/541/12653) TIMEOUT@240s. COMBINED full 584-ont ORE sweep with ALL FIVE tableau
flags (typecache+told+lazy+subcache+sembr), prod config, gold-compared (job
47539854): **559 ok / 24 timeout / 1 memout, gold 559 MATCH / 0 DIFF** — IDENTICAL
failing set to the 559-baseline (9663 just shifted timeout↔memout = run variance;
9663 is a CB-engine ont, 302k clauses > KM_TAB_MAX_CLAUSES=20000 so the tableau
isn't even spawned). So the full stack is SOUND + gold-clean + 0 additional ORE
recovery.

DEFINITIVE (now 10 techniques): the ∀+⊔ family is NOT closable by tableau search
technique in this caching architecture. TWO structural reasons: (1) the SMALL ∀+⊔
onts have genuinely WIDE models (exp-many incomparable consistent successor types)
that none of typecache/told/lazy/subcache/sembr prune — covering disjunctions, no
clash to exploit; (2) the LARGE failing onts (3215/4604/7246/11460/9663/9724/14817/
15803...) exceed KM_TAB_MAX_CLAUSES=20000 so the tableau is never spawned — they
are CB-engine THROUGHPUT/MEMORY problems ([[project_km_throughput]] /
[[project_km_memory_reduction]]), not tableau-addressable. KM stays sound+complete
on all it finishes (0 wrong, every sweep). Beating Konclude here needs either
CB-engine scaling (memory/indexing for the big onts) or a non-model-constructing
approach for the wide small onts — NOT more tableau heuristics. 9635 remains the
only tableau-route ORE recovery this whole arc (db712ff). All 5 tableau flags
committed gated-OFF (ccc798e/bcaf5a1/ddb637a); zero production risk.
