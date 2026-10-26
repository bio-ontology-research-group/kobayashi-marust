---
name: project_km_el_routing
description: EL fast-path routing fixes the KM transitivity timeout blow-up; correctness fixes for the 18 incomplete + naming-collision unsound onts; goal = match Konclude ORE coverage
metadata: 
  node_type: memory
  type: project
  originSessionId: 3e94cd1a-f3b7-4c1c-a08d-39c076fa2104
---

Goal set 2026-06-08: make KM match Konclude's ORE 2015 coverage (587/590 ok),
optimising time+mem too. Building on [[project_km_ore_rerun_cur]]. Branch
`payg-strategy`. Big multi-front effort; progress so far below.

## Correctness fixes (committed + pushed, validated vs Konclude gold)
- **Isolated declared classes** (commit 2d2e7d7): the CB engine only classifies
  concepts reaching its signature (`named_queries`), so a class declared but in
  no axiom never gets `⊤ ⊑ B`. Fix: `ofn_to_clauses` appends a tautological
  self-clause `A(x)→A(x)` per absent declared class. Sound, calculus/Lean
  unchanged. Fixed the bulk of the RELAPPROXC "incomplete" onts.
- **Output local-name collapse** (2d2e7d7): `short()` disambiguates distinct
  IRIs sharing a fragment (3978 fix) but output must collapse to bare local name
  to match the gold convention (`ore_canon.localname`); else the `__tag` suffix
  is a spurious miss+extra. Added `frontend.local_name` reverse-map. Fixed
  triple-`LineString` onts (1420, 14826).
- **is_internal false-positive** (commit after): real classes named `Q_minus`/
  `Q_plus` (symbols.owl) were dropped by the prefix heuristic. Fix:
  `frontend.is_named_iri` (in the short registry) ⇒ never internal. Fixed 15098.
- Result: 16/18 "incomplete" now exact vs gold. Remaining: 10362 (5 missing,
  needs inverse-role completeness), 16461 (1, qualified number), 5404 (50,
  ALEHI), 9904 (datatype). UNSOUND set: 3978 clean; 6720 gold is EMPTY
  (konclude error, KM's 997 likely right); 5940/8135 small miss+extra on
  `_hasValue__` surrogate classes; rest are datatype (now fenced).

## THE BIG LEVER: EL routing (commit "Route EL++ ontologies...")
189 of 269 KM timeouts are **OWL 2 EL profile**. Root cause: the disjunctive
context engine's transitivity encoding (`__trans__r__C` propagation concepts)
generates unbounded redundant Pred/Succ message traffic. Diagnosed with
KM_TRACE: on ore_ont_11497 (105 classes) context count stabilises (~210) but
`msgs_pending` grows unbounded with `max_body_len=1` — an algorithmic-efficiency
blow-up in the message fixpoint, NOT context explosion or growing clauses.
Removing the 3 TransitiveObjectProperty axioms ⇒ instant.

**Fix = `engine/py/el_route.py`**: maps the frontend's normalised DL-clauses
onto EL++ normal forms NF1–NF7. If *every* clause maps (ontology is EL++),
`owl_classify` classifies with `moose.elpp.completion` (ELK-style O(n³)
told-subsumer saturation — discharges the `__trans` NF4 rules efficiently, no
successor trees, no messages). Any non-EL shape (disjunctive head, eq/number
atoms, nominal `ind` terms) ⇒ `to_nf` bails ⇒ context-engine fallback.
Conservative + sound. IMPORTANT: NF TOP symbol is `"⊤"` not `"owl:Thing"` (else
`⊤⊑C` facts silently dropped).

Validated: 11497 240s→7s exact; 16351 top-axiom exact; **13/13** sampled EL
timeouts (≤38k axioms) CLEAN vs gold in 0.1–13.7s; all 23 oracle fixtures
byte-identical (EL fixtures now go through completion).

Routing refinement (commit "EL routing: race…"): completion-always REGRESSED
some large *flat* EL onts (context engine was faster: 8579/16684 ok→timeout).
Fix: transitive onts (moose `__trans__` concepts) → completion only (context
engine reliably diverges); other EL onts → **race** the context-engine binary
vs completion (two subprocesses, threaded communicate(), take first valid, kill
loser). No regression either way.

## Completion O(subs*edges)→O(in-degree) optimization (moose repo, branch
sroiq-forall-introduction, commit 42877bd)
moose's Python completion timed out on large EL onts (16558: 3679 classes
>200s) because three rules (NF4 back-trigger, R⊥-backward, NF7-symmetric)
rescanned the WHOLE edge set per derivation. Added a predecessor index
`in_edges[target]={(parent,role)}` in `saturate`. Pure perf, identical results
(7 completion unit tests pass, 23 fixtures byte-identical). Effect: 16558
>200s→0.28s; 8634 timeout→2.75s (395548 subs); 8579/16684 timeout→<0.5s — ALL
exact vs Konclude gold. This removes the large-EL tail; no Rust ELK needed for
the ORE sizes. Deployed to cluster `~/sroiq-rerun/pkg/moose/elpp/completion.py`.

## RESULTS (sweep 4966, then 4996 with chain/conjunction routing)
KM coverage **214 → 515+ ok / 591** (Konclude 587). KM is the **lowest-memory**
(median 20.4 MB) and **2nd-fastest** (median 0.347s) reasoner on the common-118
subset. Correctness vs gold: 515 compared, 484 agree, 17 incomplete, 10 unsound,
4 both-disagree.

Critical late fixes (all committed payg-strategy):
- **Harness pipe deadlock** (oracle/ore/ore_runone.py): KM stdout via PIPE was
  read only after the monitor loop; large EL successes (8634: 395548 subs ≈10MB)
  filled the 64KB buffer, KM blocked, killed at timeout. Concurrent reader
  thread now drains stdout. THIS was masking every large-output success.
- **el_route ⊤/⊥-as-subject filter**: completion emitted ⊤⊑X (from ⊤⊑C axioms)
  as spurious extra → 8 pure-EL onts falsely "unsound". Fixed.
- **rbox_el_safe gate**: moose folds only role hierarchy/domain/range/trans into
  clauses; inverse/symmetric/functional are context-engine triggers absent from
  clauses, so completion is unsound on them (5404 ALEHI +11 extra). Route to
  completion only if rbox ⊆ {subrole,domain,range} ∪ {fenced role-chain}.
- **role-chain → completion is sound** (dropping a composition axiom only
  removes consequences; never extra). Allowed; gains ALER onts (935 exact, 412
  sound but misses 28 chain subs). **n-ary conjunction** decomposed to binary
  NF2 (__conj__ aux) since moose emits k>2 conjuncts.

Residual 10 unsound = 6720 (gold EMPTY, konclude error, KM likely right) + 9
complex SROIQ(D) (SHIF/ALCHOIQ/ALEHOIN/SHN/SHIN: datatype+number+nominal+inverse
— context-engine approximation on full SROIQ, the research frontier, NOT a
regression; datatype abstraction itself is provably sound). 17 incomplete are
mostly SHOIN(D) (full datatype+number+nominal).

## 2026-06-09 session: sound config + soundness fix + gap characterized
- **Final sound-config sweep (5008): KM 516/591 ok**, 44 timeout, 31 memout,
  unsound 14 (=10 pure + 4 both-disagree), incomplete 16; **lowest median mem
  (20.3 MB), 2nd-fastest (0.369 s common-115)**. Chain-routing revert (commit
  2810ff8) confirmed sound; 7868 now correctly times out (was unsound +1110).
- **short() IRI-mangling soundness fix (commit 016a206)**: `owl_classify.short`
  did an extra `.rsplit("/")` on local_name's output, truncating fragments that
  contain '/' or an embedded IRI after '#'. Gold (ore_canon.localname) keeps the
  whole post-'#' fragment. This made FALSE unsound flags (NOT reasoning errors):
  ore_ont_14499 `…#C2/C3_facet_joint`→`C3_facet_joint` (extra=46); 8135/5940
  `_hasValue__http://…/SWO_0000023` surrogate→`SWO_0000023` (extra=8). Fix:
  `short()` returns `local_name(n)` unchanged (== _short_base == gold convention).
  Re-classified vs gold: 8135/12831/5940→AGREE, 14499 unsound→sound(incomplete 2);
  3978 (disambiguation) + 10056 unchanged AGREE. Re-sweep job 5038 measures the
  benchmark-wide unsound drop (likely several more false-unsound fixed).
- **Tableau lever = 0 ORE onts** (empirically). Of the 7 small live-disjunction
  timeouts, 6 are FENCED out of the built tableau fragment (SHIQ/SHOIQ:
  inverse+number+nominal+chain — cb_to_ht handles only ALCQ+RBox) and route to
  CB; 1 (5303, SH) is in-fragment but the tableau HANGS (non-termination on
  transitive-role blocking, 230s@18MB). route.py now has the EL fast path wired
  as single entry (commit 016a206) but switching the benchmark to it gains 0, so
  benchmark stays on owl_classify.py. 541/1603 are ALSO konclude timeouts (no gold).
- **Rust-frontend lever is nuanced** (profile on 935, 39k clauses): parse 2.7s +
  normalise 2.9s + tojson 2.2s + augment 0.8s = 8.5s; no single stage dominates,
  so a parser-only port saves ~⅓. BUT 935 still TIMES OUT — it's el_safe=False so
  the CB ENGINE blows up on size, not the frontend. So size-bound splits: huge
  onts (200k–1M clauses, parse>240s e.g. 3215/1194) = frontend-bound (Rust
  frontend helps); medium onts (935 39k) = ENGINE-bound (need CB scaling). Rust
  frontend is necessary-but-not-sufficient for huge onts (engine must also scale
  to 1M clauses). User chose Rust frontend (2026-06-09) AND wants hypertableau too
  (BOTH, eventually). normalisation.py=786L, owl_loader=453L → multi-day port.

## Remaining gap to 587 (the hard frontier)
~43 disjunction onts (ALC/S/SH+ — context-engine disjunction blow-up, the core
research problem) + a few huge horn onts (3M axioms, Python frontend/completion
too slow) + ~4 inverse onts + the SROIQ(D) unsound/incomplete. These need the
sound+complete SROIQ procedure (the whole moose→SROIQ extension) — not quick
fixes.

## Status / next
- Full KM re-sweep submitted: **Slurm job 4885** (`~/bench/ore_km_cur2.sbatch`,
  30-chunk array → `ore_out_kmcur2` / `res_kmcur2_*`), with EL routing + all
  correctness fixes. Measures new coverage. Reuse Konclude/HermiT/etc.
- Deployed to cluster `~/bench/km/py/`: frontend.py, owl_classify.py, el_route.py.
- Remaining buckets to 587: large-EL tail (~30, need fast Rust EL), non-EL
  disjunction timeouts (~80, e.g. 5303 SH — context-engine disjunction blow-up),
  memout (54, size), datatypes (50, `is_unsupported` fenced — design pending).
- Datatype plan (task #34): data domain/range = Horn (like object); the hard
  part is datatype satisfiability (facets, disjoint ranges) for soundness.
  Pragmatic subset likely covers most ORE datatype onts.
