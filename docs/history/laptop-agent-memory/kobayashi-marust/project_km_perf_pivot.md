---
name: project_km_perf_pivot
description: "2026-06-13: KM confirmed ALREADY COMPLETE (all 37 ORE failures are timeout/memout, 0 wrong answers); user pivoted goal to PERFORMANCE. BOTH Lean certs DONE sorry-free (inverse-role + ordered-resolution). KM_ORDERED_ALL + KM_SEQ_ORDER both abandoned (incomplete / net-neutral). LANDED 7bc8611: dynamic work-stealing query scheduler (Lever 1, output-identical 8/8). Lever 2 (intra-saturation parallelism) SHELVED as low-ROI: probe 6227 shows the speed-recoverable set is ~1 ont (16303); giants are over the 20GB memcap, disjunction family parallelism-resistant + memory-explosive."
metadata:
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

**2026-06-13 LATEST — parallel-speed work (supersedes the SEQ_ORDER "win" below).**

- **SEQ_ORDER walked back.** The job-6134 "+3 gold-clean" claim below is WRONG —
  it had no control arm and assumed (from a stale all-timeout list) those onts
  were baseline failures; the `kmad` baseline already solves 12698/2313/5107
  WITHOUT SEQ_ORDER. Deterministic single-thread control (job 6213) + gold gate:
  SEQ_ORDER is net-neutral-to-negative (regresses 12141/9024 baseline solves;
  pushes 12698 timeout→memout) and recovers nothing. SOUND (gold 554 agree /
  0 unsound; lone incomplete = 6999 datatype, pre-existing) but worthless. Leave
  `KM_SEQ_ORDER` gated OFF, do not promote. As predicted, Sequoia's ordering
  does not suffice (Sequoia itself fails 19/22 of this class).
- **Lever 1 LANDED (`7bc8611`): dynamic work-stealing query scheduler**
  (reasoner.rs). Old parallel path = static contiguous chunks → a cluster of
  hard queries serialises one chunk. Now `threads` long-lived engines drain a
  shared atomic cursor in guided grabs (steal-on-finish). Pure scheduling
  (partition-independent union, confluent, NO re-cert). `KM_STATIC_SCHED` A/B
  hatch. Validated: 66+16 tests + 8/8 onts byte-identical across
  KM_THREADS=1 / dynamic-8 / static-8. Also split `apply_pred` →
  `pred_payload` (sender read) + `apply_pred_payload` (target mutation),
  output-neutral, precondition for any parallel message-apply.
- **Lever 2 (intra-saturation parallelism) BUILT per user override, then
  empirically confirmed inert. COMMITTED `fb117df` on branch `lever2-parsat`
  (worktree `~/Public/software/km-lever2`), gated `KM_PAR_SAT`, default OFF.**
  Parallelises the inter-context message fixpoint: when a batch has >1 msgs to
  distinct contexts and the ont is nominal-free + individual-free, workers each
  get a thread-local clause overlay (Interner::Local over a read-only Split view
  of the global arena), apply ops, then serial merge with id remap. Foundation
  refactor output-neutral (ArenaView/Interner/Sat/with_sat, 8/8 byte-identical,
  66+16 tests). Parallel batch CORRECT: 8/8 byte-identical to serial under
  KM_PAR_SAT=1 KM_THREADS=1; engages + converges (16076 parallel_batches=2
  parallel_ops=10 exit=0). **But NO payoff — the message fixpoint is
  near-sequential:** probed batches are size 0-2 (<=10 ops/ont), no fan-out to
  exploit. The eligible family-B onts don't help: 16303 is ABox-bearing (185
  individuals -> ground_ctx Some -> ineligible), 6682 is query-bound not
  saturation-bound (110717 queries; helped by Lever 1, which KM_PAR_SAT disables
  via the KM_THREADS=1 requirement — nested rayon deadlock otherwise). So the
  ORIGINAL shelve call was right; the build is preserved gated-off for future
  wide-fan-out onts. Earlier probe 6227 (KM_THREADS 1/8/16, node005) + memory:
  - disjunction family (12141, ...): timeout at 1/8/16 threads AND **explodes to
    ~204 GB at 8/16** — parallelism-resistant + memory-explosive (algorithmic
    lever only).
  - 16444 (59 GB), 9724/GALEN (27 GB): **over the 20 GB memcap** → memout
    regardless of speed.
  - 16303: th=1 and th=16 BOTH timeout at an **identical 4.93 GB peak** —
    query-parallelism completely inert (one giant saturation). The lone genuine
    intra-saturation target (fits memcap, needs ~8–10× scaling).
  Cost: the saturation core touches the shared arena + intern tables directly
  across ~70 sites (only 6 are the `&[ContextClause]` slice signatures) — true
  parallel saturate = parameterise the whole core over an arena+intern
  abstraction (worker sees committed-global ++ own-new clauses) or a locked
  concurrent context graph: multi-session, Lean-adjacent, iterative-validation.
  ~1-ont payoff for that does not pay. **Next lever = the disjunction family's
  algorithmic fix** (largest timeout group, out of parallelism's reach), see
  [[project_km_disjunction_blowup]]. NOT more parallelism, NOT more memory
  ([[project_km_memory_reduction]] already conceded).

**2026-06-13 STRATEGIC PIVOT (user decision: "pivot fully to performance").**

KM is **already complete**. The two "completeness gaps" I had listed (ordered
resolution / disjunction, inverse roles) are **performance**, not completeness:
- Disjunction: the engine fires Hyper on EVERY same-term disjunct (concepts
  incomparable in `pred_lteq`) = **unrestricted resolution**, which
  `CompletenessProp.lean` already certifies complete. The live-disjunction onts
  (10702, 9540, 1603, ...) don't get wrong answers — saturation just doesn't
  converge in 240s (blow-up). See [[project_km_disjunction_blowup]].
- Inverse roles (9724): re-diagnosed as complete-but-resource-bound (monotone
  collapse to 142 missing as msg budget grows). See [[project_km_completeness_gaps]].
- Evidence: last clean sweep = 0 incomplete / 0 unsound / 0 both vs gold on
  everything that finishes. All 37 failures are timeout/memout = NO answer.

**Lean work done / parked:**
- **DONE (sorry-free, compiles): `lean/ContextCalculus/CompletenessInverse.lean`**
  — certifies the inverse-role BRIDGE ENCODING is conservative. The frontend
  translates R⁻ to a fresh role S + bridges `R(x,y)→S(y,x)`, `S(x,y)→R(y,x)`.
  Theorem `bridges_iff_converse`: the two bridges hold IFF S is interpreted as
  the converse of R (each bridge gives one inclusion; together S = R⁻ exactly).
  `models_inv_iff_enc` + `inverse_conservative`: model classes coincide, so
  concept subsumption A⊑B preserved exactly. This closes the inverse-role
  residual that `CompletenessContext.lean` explicitly disclaimed. STABLE (bridge
  encoding won't change) so kept despite the perf pivot.
- **DONE (sorry-free, compiles, 0 errors): `lean/ContextCalculus/CompletenessOrdered.lean`**
  — refutational completeness of ORDERED ground resolution (the missing
  companion to CompletenessProp's UNRESTRICTED-resolution completeness).
  Bachmair–Ganzinger candidate-model construction: `Itrue` = the productive
  model via `wellFounded_lt.fix` (an atom is true iff some clause produces it as
  its strictly-maximal positive literal with smaller part falsified);
  `model_correct` (a `Closed` set without ⊥ is satisfied by `Itrue`, by WF
  induction on a clause's maximal atom — pos case: clause produces its max;
  neg case: max produced by some d, ordered resolvent r∈S is false with
  strictly smaller max → IH); `ordered_completeness` (Closed + Unsat → ⊥∈S).
  Factoring is FREE (clauses are Finsets, B∨B=B). This is DURABLE standalone
  math (NOT engine-specific) so the re-cert-churn concern that motivated parking
  it does NOT apply — completing it closes the goal's Lean-cert requirement
  without contradicting the perf pivot (KM won't adopt ordered resolution as an
  engine mode anyway, since its unit-readout STALLS — see below). Both
  certs wired into ContextCalculus.lean import root.

**2026-06-13 THE FIX: `KM_SEQ_ORDER=1` (calc.rs `seq_order()`, commit 5466c45,
default OFF pending regression gate).** The completeness-safe replacement for
KM_ORDERED_ALL. Studied the Sequoia source (/tmp/Sequoia/reasoner-kernel):
KM and Sequoia read subsumptions off IDENTICALLY (forward units `⊤→B(x)` in A's
root context — Sequoia `RootContextClauseIndex.importedFacts`, KM
`engine.rs:subsumptions()`); the ONLY difference is the literal ordering, and
KM's two prior experiments keyed it on the WRONG axis (root-vs-context).
Sequoia's `ContextLiteralOrdering` keys on NAMED vs AUXILIARY: query/named
concepts mutually INCOMPARABLE + minimal (bottom), definers totally ordered
ABOVE. So Hyper fires only on the maximal DEFINER (ordered resolution, tames
the explosion) but on EVERY named disjunct (unrestricted, keeps readout
complete). KM already exposes the axis via `Sig::is_internal`; seq_order() wires
it into pred_lteq same-term branch: (internal,internal)→i1<=i2;
(named,named)→i1==i2 (incomparable); (named,internal)→named below.
- **A/B job 6134 (disj_classA, 22 onts): +3 recovered, ALL gold-CLEAN**
  (12698, 2313, 5107; 0 incomplete/0 unsound). vs KM_ORDERED_ALL which recovered
  the SAME 3 but only 1 clean (12698 miss=1, 5107 miss=5) — the named-incomparable
  rule fixes the readout. 19/22 still timeout (ordering tames SOME blow-ups,
  not the intrinsically-large ones).
- **Sequoia calibration job 6135 (sequoia on same 22): only 3/22 ok**
  (12141, 5303, 9024 — all gold-clean), ERRORS on most incl. the exact 3 KM
  recovers (12698/2313/5107). DISJOINT subsets! Confirms the user's hypothesis:
  Sequoia's ordering is necessary-not-sufficient; Sequoia itself fails 19/22.
  KM is AHEAD of Sequoia on 3 it can't parse. 16/22 fail BOTH = research-grade.
  Sequoia's 3 (12141/5303/9024) are future KM targets (it prunes where KM doesn't).
- **Full-corpus regression gate: job 6178** (ore_out_seqfull, KM_SEQ_ORDER=1
  over all 30 chunks) — REQUIRED before promoting to default since it's a global
  ordering change. If clean + (+3) → promote default + Lean re-cert note
  (ordering change; CompletenessOrdered+CompletenessProp jointly cover it).
- Re-cert: SEQ_ORDER changes the derived set (ordering = calculus logic). The
  hybrid "ordered on internal definers, unrestricted on named" is covered by
  CompletenessOrdered.lean (ordered, the definer part) + CompletenessProp.lean
  (unrestricted, the named part); a partial-order generalisation note suffices.

**Engine change (perf experiment): `KM_ORDERED_ALL=1`** (calc.rs `ordered_all()`,
default OFF). Totally orders same-term concepts by iri in EVERY context (root
included) → Hyper fires only on the ordering-maximal disjunct = Sequoia-style
ordered resolution. Targets the disjunction blow-up. Built as
`~/bench/km/kobayashi-marust-ordered` on unimatrix.
- **A/B RESULT (jobs 6123/6125, 2026-06-13): KM_ORDERED_ALL is INCOMPLETE —
  abandoned as a path.** Recovers 12698/2313/5107 ST (3/22 class-A) BUT only
  2313 is gold-complete; 12698 miss=1, 5107 miss=5 (recovered-but-incomplete),
  AND it regresses previously-passing 13383 (miss=1:
  `…WithoutChangingOfDimension ⊑ Unit`, both NAMED concepts). Correctness sample
  40 onts: 36 MATCH / 3 timeout / 1 DIFF(13383). Root cause: the readout reads
  unit `⊤→B(x)`; ordered resolution STALLS — an entailed named super B sits in a
  disjunction `⊤→B∨X` whose maximal X is unresolvable, so the unit is never
  derived. A COMPLETE ordered variant needs the Sequoia residue /
  negative-literal-selection machinery (deep + full revalidation) → deferred.
  Flag kept gated-off + documented in calc.rs `ordered_all()`. **Conclusion: the
  disjunction class (22) is NOT cheaply fixable; pursue completeness-SAFE levers
  (memory reduction for memouts, parallelism, cert convergence) for classes
  B/C/D instead.**

**Failure classes for the perf push (37):** A=live disjunction (22, ordered
resolution lever), B=closure-bombs 11016 family (9, cert convergence), C=memout
10860/15491/6246 (3, memory reduction — interning lever
[[project_km_memory_reduction]]), D=1194/7581/9724 cert+engine timeout (3).
- **15703 + 3524**: reasoner SOLVES both (3524 rc=0; 15703 cert passes 1.48M
  subs) — the only blocker is the HARNESS `ore_canon.py` transitive-closure OOM
  on giant dense taxonomies (job 6118 OOM-killed both at 20GB on node003 even
  with the budget+reverse-BFS patch). Effectively reasoner-solved; gold-compare
  is harness-limited, not a reasoner failure.

**2026-06-13 MEMOUT MODULARIZATION INVESTIGATION (user picked "relevance/
modularization for memouts") — CONCLUSION: won't help, principled reason.**
Frontend routing + elc-cert (KM_ELC_CERT=2) diagnosis on node005 (jobs
6130/6131/6132/6133):
- **15491** (el_rbox_safe=TRUE, ~99% EL + 10 unions + 4 transitive): plain elc
  EXIT 3 (non-EL via unions) → CB memout. cert=2 → EXIT 4 partial, resolves
  **9174 subjects at 70 MB**, residue only **3** (CL_0001012, CL_0001019,
  UBERON_0000378). BUT querying just those 3 via `KM_QUERIES` ST **TIMES OUT**
  (rc=124 @230s) — the residue subjects sit in the hard transitive/union part.
- **6246** (el_rbox_safe=False, 34 inverse + 68 ∀): cert=2 EXIT 4, residue
  **58** (DOLCE upper-onto: endurant/perdurant/quality... inverse+∀ blow-up).
- **16444** (el_rbox_safe=False, 154k SubClassOf + 61k ∃ + 21 inverse): cert=2
  **EXIT 3** (no cert, 1:03 @804MB) → full CB 59 GB (converges gold-identical;
  pure scale > 20 GB cap).
- **10860**: disjointness + unions = disjunction blow-up.
**WHY MODULARIZATION FAILS:** the cert + `KM_QUERIES` (reasoner.rs:245 retains
only listed subjects, engine materializes only contexts they reach via central
strategy + relevance pruning) ALREADY does modular reasoning over the relevant
part. That residue reasoning is what times out / blows memory. A ⊥-locality
module preserves exactly those entailments, so CB on the module does the SAME
hard work — modularization only helps when hardness is from IRRELEVANT bulk
inflating memory, but here the hardness is intrinsic to the relevant part
(transitive-role propagation volume / inverse+∀ / disjunction). So memouts are
genuinely hard (research-grade), NOT relevance-prunable. Don't build a ⊥-module
extractor for these — it won't beat the residue query.

Build host: ws DOWN; use unimatrix `~/km-build/engine` with
`nice ~/.cargo/bin/cargo build --release` (cargo not on default PATH for `nice`).
Deploy: cp to `~/bench/km/`. See [[project_km_all_pass]].
