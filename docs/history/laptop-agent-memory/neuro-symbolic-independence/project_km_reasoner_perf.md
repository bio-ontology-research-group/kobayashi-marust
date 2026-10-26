---
name: project_km_reasoner_perf
description: "KM reasoner (kobayashi-marust) perf audit — real bottleneck is the trivial expansion strategy's shared-successor blowup, not hyper/subsumption"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3e94cd1a-f3b7-4c1c-a08d-39c076fa2104
---

Deep perf audit of the KM reasoner (`kobayashi-marust/engine`, the Kobayashi-MaRust
SROIQ context reasoner used by the sroiq-nesy paper; paper cites the embedded
`sroiq-nesy/rust-context-reasoner`, same code).

UPDATE 2026-06-06 (ORE perf root-cause, profiled): KM baseline (audit-fixed
binary) on ORE = 213 ok / 300 timeout / 55 err / 24 memout. **KM is at HermiT's
level** (HermiT 239 ok / 352 timeout; both lose to Konclude 587, ELK 590). KM
timeouts are LARGE onts (median 13k axioms); HermiT also fails on 297/300 of them.
KM is FASTEST when it completes (0.38s median). Profiled smallest unique choke
ore_ont_541 (255 ax SRIF, 92 ∀ × 34 ⊔ × 16 inv × trans): ONE empty-core successor
context balloons to 6500+ clauses, msg queue never drains (>70k). Tested+REVERTED
two fixes: (a) eager expansion strategy (core=K1) -> WORSE (431 ctx vs 92, fat ctx
still 5359 clauses w/ 1-concept core); (b) Elim is NOT the bottleneck -- fat ctx is
only 4% subsumed-by-other (98% antichain), genuine ~4000-clause disjunctive+
successor closure (73% fn-term clauses). KEPT: work-off-time fwd-subsumption
re-check (back_subsume never scanned todo; commit e0f6e34) cut live redundancy
4%->1.9%, sound+re-certified, but doesn't fix any timeout. CONCLUSION: blowup is
irreducible disjunctive saturation; matching Konclude needs real CB optimization
(ordering heuristics, semantic/composite redundancy beyond syntactic subsumption,
caching), NOT expansion-strategy or Elim tweaks. See [[project_km_sroiq_program]].

UPDATE 2026-06-06 (ordering + composite-redundancy levers, trace-driven, both
NEGATIVE on the hard cases): goal was Konclude-competitiveness. Probed ore_ont_541
fat ctx (one empty-core per-f successor, 7351 clauses @60k pops; head-width hist
peaks at unit=4355, ⊥=311, tail to width-9; 72% fn-term). (1) **Subsumption
resolution** (contextual literal cutting, the main composite-redundancy candidate
beyond subset-subsumption): implemented forward SR behind env SROIQ_SUBRES + a
cutter_index; FOUND+FIXED a soundness bug (criterion must require the cut atom
A∉head(D), else a tautology cutter A→A "resolves" to C itself and fabricates
spurious subsumptions — caught because forall_intro/kinship gave unsound C⊑B). The
apparent "541 terminates with SR" was PURELY that unsoundness (tautology self-cuts
killed concepts). With the CORRECT condition, the cuttable ceiling on 541 is only
~10% AND is 100% central-concept disjuncts (fn-concept=0, role=0) — SR provably
CANNOT touch the fn-term disjunctions that are 72% of the blowup. On the stress
test SR is verdict-identical with ZERO speedup (N=15 21.2s→21.4s). Reason: SR
removes DEAD disjuncts; the timeout cases are hard precisely because their
disjunctions are LIVE (excluded-middle Q_i∨NQ_i, neither branch impossible).
(2) **Given-clause ordering** (FIFO→smallest-first, env SROIQ_SMALLFIRST): 541 and
stress N=25 still TIMEOUT; final saturated set is ~98% antichain so order can't
shrink it. BOTH named cheap levers are dead on live-disjunction onts. CONCLUSION:
KM's timeouts are irreducible LIVE disjunctive saturation; pure-CB clause-level
optimisation (redundancy/ordering) cannot match Konclude here — Konclude wins by
tableau model-exploration + dependency-directed backjumping + caching (explores ONE
model, not ALL consequences). Path to Konclude on these = hybrid CB+tableau
(major) OR context-level redundancy/blocking (targets the DISTINCT stress-test
CONTEXT explosion, not 541's single-ctx CLAUSE explosion — untested). All probes
were env-gated; engine reverted to HEAD (default path unchanged, 6/6 tests). Full
experimental diff saved: kobayashi-marust/notes/subres-ordering-diag.patch (SR with
soundness fix + cutter_index + diag_dump + smallfirst). ORE ∀-fix re-run: 0
subsumptions recovered + 0 unsat changed on 212 both-ok onts, net-zero timeout shift
(1 each way) — the ∀-fix is a proven completeness GUARANTEE, not an ORE-score mover.

UPDATE 2026-06-06b (CONTEXT-LEVEL BLOCKING probed, also NEGATIVE; true mechanism
found): added a context census (env SROIQ_CENSUS+SROIQ_POPCAP, saved
notes/context-census.patch). 541 @40k pops: 91 contexts but ONE fat (5511 cl),
median 162; 24% subset-blockable BUT those are the SMALL contexts — the dominant
fat context is not blockable, so blocking saves ~nothing on wall-clock. stress N=25
@40k pops: 79 contexts ~evenly ~800 cl each (median 809), only 3% subset-blockable,
0 exact duplicates. So context blocking (subsumption/dedup of contexts) is NOT the
lever for either. TRUE MECHANISM (census-revealed): the ∀-introduction emits
DISJUNCTIVE empty-body facts (excluded-middle →Q_i∨NQ_i): stress25 has 25, 541 has
10. init_context seeds ALL empty-body facts into EVERY context (audit M2), so every
context independently re-saturates the same GLOBAL disjunctive closure → 53 root
contexts × ~800 cl = duplicated WORK, not duplicated contexts. The principled fix is
SHARING the core-independent (empty-body) saturation across contexts (compute the ⊤
empty-core closure once, import it) — sound (empty-body clauses are globally valid)
but with a real completeness subtlety (core×global interactions must still fire; can't
just dump the closure into worked_off), so it's a substantial change needing a new
Lean completeness argument, NOT a quick prototype. This is the Sequoia-thesis
"module/closure sharing" research problem. NET across all cheap levers (subsumption
resolution, ordering, context blocking): all measured-negative on KM's live-disjunction
timeouts; remaining levers are all MAJOR (hybrid CB+tableau, or global-closure sharing
with new proofs). KM stays at HermiT's level; the Konclude gap on these onts is
architectural.

UPDATE 2026-06-06c (GLOBAL-CLOSURE SHARING built+measured, NEGATIVE — closes the
pure-CB avenue): implemented the user-chosen lever properly (env SROIQ_SHAREGLOBAL,
saved notes/closure-sharing.patch): compute the empty-body fact closure ONCE in the
⊤ context (root ordering) + once for successor ordering (g_succ), pre-load it into
every query-root and every successor's worked_off (pre-fired) so they only do
core-specific saturation. SOUND + VERDICT-IDENTICAL (examples + stress all SAME,
6/6 tests both modes) — the design is correct (core×fact and core+fact+fact still
fire when the core/pushed clause is worked off). But ZERO speedup: stress N=15
21.4s→21.5s, N=25 still TIMEOUT, 541 still TIMEOUT. SIZES diagnostic (env
SROIQ_SIZES) revealed WHY: stress N=15 = 49 contexts, the cost is 16 SUCCESSOR
contexts EACH ~1788 clauses (roots are small); WITH sharing the successors STILL
grow to ~1788 each (total_wo 49748→49794 unchanged) because each successor's 1788
clauses are DERIVED FROM its own distinct pushed predicate ND_i (the ¬B_i witness),
NOT from the shared empty-body closure (g_succ is small, not in top-8 sizes). So
there is NO large shared sub-closure to amortise — each context does GENUINELY
DISTINCT disjunctive work. DEFINITIVE CONCLUSION across ALL pure-CB levers tried
(subsumption resolution, ordering, context blocking, closure sharing): every one is
verdict-correct but gives no speedup on KM's live-disjunction timeouts, because the
work is irreducibly per-context core-specific disjunctive saturation with no
redundancy/sharing to exploit. The Konclude gap on these onts is ARCHITECTURAL —
only hybrid CB+tableau (model exploration + dependency-directed backjumping +
caching, exploring ONE model not ALL consequences) can close it. Patches saved for
reuse: notes/{subres-ordering-diag,context-census,closure-sharing}.patch (all
env-gated diagnostics + the sound subsumption-resolution fix). Engine at HEAD.

UPDATE 2026-06-07 (SEMI-NAIVE INTER-CONTEXT PROPAGATION — POSITIVE, 11–32× on
real ORE, output byte-identical). This is a DIFFERENT lever from the 06-06c
global-closure sharing (which was negative): that targeted clause-level redundancy
on LIVE-DISJUNCTION stress tests; this targets the algorithmic complexity of the
inter-context message loop on EXISTENTIAL-RICH REAL ontologies. Instrumented the
engine (env KM_STATS counters: propagate/pred_checks/succ_scans/hyper_calls/saturate)
and profiled the slow real ORE ontologies. Smoking gun on ore_ont_10162 (1418 cl,
585 roots, 137 succ ctx): pred_checks=**95.3M** vs hyper_calls=60k — i.e. the
`propagate()` Pred section re-scanned the FULL `worked_off × all predecessor edges`
on every one of its ~41k calls (10160: 122.7M). Root cause: a `(clause,edge)`
covered-check `c.body ⊆ pushed[edge]` was redone every propagate even though it can
only flip fail→pass when `pushed[edge]` GAINS a predicate. FIX (engine.rs, semi-naive):
(1) append-only per-context `pred_pool` (Pred-eligible worked-off clauses: function-free,
predicate-only head) + `pred_hwm`; a back-subsumed pool entry is left in place — still
sound to push since it stays context-entailed — which keeps the high-water mark stable
despite `worked_off` reshuffling under back_subsume; (2) per-edge `edge_seen` pushed-length
watermark → only re-check `(old clause × edge)` when that edge's pushed-set grew, and
`(new clause × all edges)`; (3) same pool+hwm for the Succ scan. `pushed_pred`/`pushed_succ`
still dedup actual sends, so the message SET is preserved. RESULT: pred_checks 95.3M→1.33M
(72×), succ_scans 5.5M→42k; saturate count UNCHANGED (saturation work byte-identical, only
the wasteful rescan removed). VALIDATION: 30/30 unit tests; 13 ORE ontologies byte-identical
to pre-change binary; all 15 HermiT fixtures identical (3 inverse cases = pre-existing CB
incompleteness recovered by the tableau, verified identical on the git-HEAD baseline, NOT
introduced). Server A/B on ws (56 cores, orig git-HEAD vs optimized, all subsumption sets
IDENT): single-thread 10162 **25.5s→0.8s (31.8×)**, 10123 18.9→1.4 (13.5×), 10160 20.4→1.8
(11.3×), 10133/10134/10146 3–4×, already-fast onts ~1× (no regression). ore_ont_10008 (96k cl,
269k subs) 190s→5.0s with th=16. Full ws large-ontology A/B (th=56, 400s cap, all completing pairs IDENT): 10068
(45k cl/380k subs) 88.9→20.2s, 10032 (159k/993k) 162.8→42.7s, 10016 (285k/**1.0M subs**)
36.4→23.8s, 10161 (**730k cl**/678k) 35.2→31.7s, 10006 7.0→2.1, 10008 7.9→2.2;
INFEASIBLE→FEASIBLE (orig TO, opt completes): 10073 (565k subs) →92.8s, 10136 (846k) →161.3s,
1017 →11.3s, 10053 →57.5s. CAVEAT/SCOPE: this does NOT rescue LIVE-DISJUNCTION CB-blowup
onts — 1016, 10175, 10248, 10125, **full 10140 (380k cl, 142k-concept SHQ)**, 1012 (1.8M cl)
all still TO at th=56/400s for BOTH engines — those are the tableau's job, exactly as 06-06c
concluded; the propagation fix is orthogonal and complementary. (10140's number machinery is
HermiT-validated on slices per [[project_km_hybrid_tableau]] M2; only whole-ontology scale is the wall.)
Instrumentation (KM_STATS) left in (env-gated, ~no overhead). NOT yet committed; the parallel
rayon path (Reasoner chunks) composes with the fix and was re-validated IDENT at th=8/16/56.

**Key empirical finding (corrects the static audit):** on a disjunction×existential
stress workload, the original audit's predicted hot path (`hyper`'s `worked_off`
linear scan) is NOT the wall-clock bottleneck. Profiling (env `SROIQ_PROF`, dev-only
counters) showed: only ~5.5k clause-pops take ~5s (≈850µs/pop). The **trivial
expansion strategy** dumps every successor into one shared context (empty core),
which blew up to 1014 clauses (20% of all derived) and is re-saturated/re-propagated
on every inter-context message. That shared-successor blowup dominates.

**Tier-1 logic-preserving optimizations implemented (all byte-identical, tests pass):**
add_clause de-clone; head-predicate index (`head_concept_index`/`head_role_index`)
for hyper/pred partner lookup; subsumption index (`head_lit_index` + `empty_head_wo`)
for forward/back subsumption; per-context `dirty` flag so `propagate` skips no-op
scans (cut propagate calls 20k→4.5k). These reduce constants but give ~no speedup on
the disjunction-heavy workload because the strategy, not these, is the wall.

**Tier-2 DONE (pay-as-you-go strategy):** replaced the trivial single-shared-successor
strategy with **one successor context per function symbol `f`** (`successor_for` in
engine.rs; field `successor_ctxs: HashMap<Term,usize>`, created outside `core_index`).
Result: ~45× faster on a distinct-skolem disjunction×existential stress test
(N=15: 253.7s → 5.65s), verdicts byte-identical to the trivial strategy, HermiT-oracle
validation unchanged (kinship 21/21, trans 2/2, chain 1/1, 0 unsound/0 missing on all 6
ontologies), 6/6 unit tests, and `lake build Validation` re-certified GREEN (soundness
auto-checked per run by the certificate checker). Synced to the paper crate
`sroiq-nesy/rust-context-reasoner/src/engine.rs` (was byte-identical to KM HEAD; net
change is engine.rs ONLY).

**Lean completeness proof — DISCHARGED, sorry-free (2026-06-04).** Rewrote
`kobayashi-marust/lean/ContextCalculus/CompletenessStrategy.lean`: replaced the two
sorries (perF_sound/perF_complete) with a faithful model of the engine's
consequence-based TYPE-ELIMINATION saturation, fully proved. Chain: `good_iff`
(fixpoint eq an elimination round checks) → `goodFS_selfReal`+`selfReal_subset_goodFS`
(good types = GREATEST self-realising set = gfp of operator `step`) → `step_goodFS`
(good types are a step-fixpoint) → `exists_fixed`+`saturate_fixed` (iterating step from
consistent candidates CONVERGES in ≤|candidates| rounds, strictly shrinking finite
chain) → `mem_saturate_iff_good` (computed fixpoint = good types) → `saturate_decides`
(strategy decides A⊑B, via `subsumption_complete`). NOW IMPORTED by root
`ContextCalculus.lean` → part of default build; full module builds 0 sorry/0 error on
server `ws` (~/km-lean, toolchain v4.30.0-rc2, mathlib cache warm; build loop = rsync
lean→ws then `~/.elan/bin/lake build ContextCalculus`). Residual = OPERATIONAL
refinement only (abstract `step` ↔ Rust per-f data structures; verdict-identity to
trivial strategy is empirical, soundness kernel-certified per run). Commit e9ef4b1.
**Engine-lazy bridge added (commit 6b29840):** `engine_decides` — the engine doesn't
enumerate all 2^|C| types, it materialises a finite candidate set U lazily; iterating
elimination `step` from U converges (≤|U| rounds) to exactly the good types and decides
A⊑B, under ONE explicit residual hypothesis `coverage : goodFS O ⊆ U` (+ U consistent,
trivial). This PINS the whole remaining operational gap to that single named property
(lazy-completeness of per-f expansion); everything else machine-checked. Supporting
lemmas iter_subset/goodFS_subset_iter/iter_fixed/elim_eq_good all sorry-free. Both
saturate_decides + engine_decides axioms = [propext, Classical.choice, Quot.sound]; full
ContextCalculus module 0 sorry/0 error. lean/README+README updated. Soundness remains
hypothesis-free (kernel-certified per run by CheckerTerm.certifies_subsumptionT).
**coverage DISCHARGED (commit c75038a):** `engine_complete` + `coverage_of_seeds` —
instantiating engine_decides at U=cand O (all consistent types) discharges the
`coverage : goodFS⊆U` hypothesis via goodFS_subset_cand (good→consistent). engine_complete
is DEFEQ to saturate_decides (∀t∈saturate ≡ ∀t,t∈saturate→). HONEST SCOPE CORRECTION:
discharging coverage showed it was never the binding residual — the type-level decision
procedure is fully verified hypothesis-free. The ONE genuine remaining gap is the
type↔CLAUSE representation refinement: the Rust engine manipulates disjunctive context
CLAUSES (compact rep of the type space), not enumerated types; that its clause saturation
computes the same goodFS = disjunctive-saturation completeness at the clause level = the
real (substantial, multi-week) remaining theorem, NOT yet mechanised. Mitigation: clause
engine soundness is hypothesis-free per-run kernel-certified (CheckerTerm); completeness
is HermiT-validated (byte-identical verdicts, identical to trivial strategy). Do NOT claim
the Rust binary is fully verified complete — only the type-level spec is.

**Repo workflow:** active development is on the standalone GitHub repo
`bio-ontology-research-group/kobayashi-marust` (this is where the Tier-1/Tier-2 work
landed: branch `payg-strategy`, PR #2). The main repo's `sroiq-nesy/rust-context-reasoner`
is a VENDORED MIRROR, untracked-by-design (0 tracked files, not gitignored), kept only
so the sroiq-nesy paper can reference the engine by path; do NOT develop there. Future:
replace it with a git submodule/subtree of the upstream KM repo. A prominent upstream
note was added to `sroiq-nesy/rust-context-reasoner/README.md`. To re-sync, copy
`engine/src/engine.rs` from upstream (that's the only file that diverges).

NOTE: the validation/run.sh regen marks `lean/Validation/{Kinship,Transtest}.lean` as
modified — that's pre-existing moose-frontend concept-renumbering drift, NOT a verdict
change; restore with `git checkout HEAD --` after running. Validate with moose venv:
`MOOSE_HOME=.../moose ../moose/.venv/bin/python oracle/validate.py`.
**CLAUSE-LEVEL COMPLETENESS PARTLY MECHANISED (commits 3ad9c12..4cc0e2e, file
lean/ContextCalculus/CompletenessClause.lean, imported in root, full module 0 sorry/0 error):**
Transported PropRes.completeness (propositional resolution completeness, over its separate PClause
type) onto the engine's OWN Basic.Derivable over Clause Lit, via clause map toP (lists->finsets,
commutes with resolution: toP_resolvent) + step-for-step `lift`. Results: `completeness` (Derivable
refutes any propositionally-unsat finite clause set); decidability TRIO `subsumption_refut_iff`
(O⊨A⊑B iff engine refutes A⊓¬B), `entails_refut_iff` (arbitrary ground-clause entailment),
`consistent_iff`; `model_existence` (propositional) + `herbrand_model_existence` (first-order
Basic.TermModel, equality-free fragment, since TermModel.eval uses real equality). This is the
DISJUNCTION/resolution direction (Core/Hyper/Pred/Elim) at the engine clause level = the stated
"disjunctive-saturation completeness" residual. STILL OPEN: the Succ term-generation (existential)
direction fused with disjunction into one first-order theorem (Herbrand/compactness WITH function
symbols) — genuinely multi-week, NOT faked. Lean build loop: rsync lean/->ws:~/km-lean, then
`~/.elan/bin/lake build ContextCalculus[.<Mod>]` (mathlib cache warm on ws, ~4s incremental). NEVER
commit sorries. README/lean-README have a CompletenessClause section.
See [[project_km_reasoner_benchmark]] [[project_disjunctive_context_calculus]] [[project_sroiq_nesy_submission]].
