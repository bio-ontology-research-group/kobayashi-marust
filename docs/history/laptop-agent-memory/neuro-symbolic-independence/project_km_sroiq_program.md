---
name: project_km_sroiq_program
description: "KM -> full sound+complete SROIQ(D) reasoner program (Konclude competitor, pure CB); P1 = in-fragment completeness; #1 bug = forall-introduction"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3e94cd1a-f3b7-4c1c-a08d-39c076fa2104
---

GOAL (user, 2026-06-05): make the KM Rust reasoner a full competitor to Konclude
in Rust for speed; FIRST fix the calculus to be ACCURATE + sound + complete SROIQ.
Architecture decision: **pure consequence-based as far as it goes** (Tena-Cucala
ALCHOIQ calculus + role automata), hybrid deferred. Start order: **P1 in-fragment
completeness** first.

BENCHMARK STANDING (ORE DL+EL, fixed engine): KM WINS memory (~22MB median vs
Konclude 64, HermiT 189, ELK 200, Sequoia 536); speed competitive (KM 0.47s median
vs Konclude 0.60); COVERAGE weakest (185 timeout / 32 error / 15 memout). Correctness
diagnosis: KM essentially SOUND (EXTRA=0 on in-fragment cases); the "10 unsound" = 5
datatypes(D) + 4 gold-noise(HermiT!=Konclude) + 1 ALEH+ to-verify.

THREE correctness gap categories (data-driven):
1. **In-fragment completeness holes** (ALEH/SH/SHIN/ALCHQ miss subsumptions, EXTRA=0)
   — the serious one. P1.
2. **Datatypes (D)** — 32 errors are ALL frontend ValueError on DataMax/Exact/
   HasValue; + the 5 unsound. No datatype support. Need reject-then-implement.
3. **Nominals/ObjectHasValue (O)** — frontend ValueError on ObjectHasValue; ABox-
   grounded reduction incomplete for merges. Need Table-3 rules.

**P1 #1 BUG FIXED + CERTIFIED (2026-06-05): forall-introduction.** Root cause was
NOT the engine — the normaliser (moose/sroiq/normalisation.py Forall case, ~L379)
had a "first cut" comment that SKIPPED the introduction clause entirely (docstring
L252 lied). FIX: emit `→ Q(x) ∨ ∃R.¬D(x)` by reusing `q()` (reifies ¬D via Not
pattern + ∃ Skolem). Now derives ∀-monotonicity, X⊑B for named B≡∀R.D, ∀r.⊥⊑∀r.C.
Reproducers t3/t4/t5 + battery (fa_mono/indep/unsat/vac) all semantically correct;
HermiT oracle 0 unsound/0 missing (kinship 21/21).
- **PERF GUARD (essential):** unconditional introduction blows up super-linearly
  (N=15 univ-equiv classes = 2.6s, N=40 = minutes) because the empty-body `→Q∨E`
  disjunction is seeded into EVERY context, each spawning a successor. Added a
  POLARITY PRE-PASS (`mark_polarity`/`needs_forall_intro`): emit introduction ONLY
  for ∀R.D occurring at NEGATIVE polarity (subclass pos) or in an equivalence;
  purely-positive `A⊑∀r.C` (the common pattern) gets propagation only -> no blowup.
- **CERTGEN FIX (engine/py/certgen_term.py):** the Lean certificate search
  (derive_full) reported forall_intro UNCOVERED due to a FALSE FIXPOINT: MAX_PROP_STEPS
  counted redundant (already-in-D) resolutions, exhausting budget before productive
  ones. Fixed: count budget on ADDED clauses only + added ordered positive
  hyperresolution (electrons resolve on their MAXIMAL/deepest-term head literal,
  `maximal_head()`) mirroring the engine's max-head selection. All 10 validation
  cases certified (0 uncovered); `lake build Validation` green; new ForallIntro.lean
  kernel-checks A⊑B; full `lake build` green, 0 sorries. moose 75/75, cargo 6/6.
- **LAZY ENCODING done (canonical, Table 1 of tena-cucala 2018):** switched the
  introduction from eager `→Q∨q(∃R.¬D)` (which emits an unneeded ∃-recogniser +
  decomposes ¬D -> cascade) to the complement form `¬Q ⊑ ∃R.¬D`: NQ,ND fresh;
  `→Q∨NQ`, `Q∧NQ→⊥`, `NQ→R(x,f(x))`, `NQ→ND(f(x))`, `ND∧D→⊥`. No recogniser, no ¬D
  decomposition. Built the successor lazily (Succ only in NQ branch). Cut the
  constant ~2.3x (stress N=15 2.64s->1.13s) but did NOT remove the exponential.
- **RESIDUAL EXPONENTIAL = expansion-strategy problem, NOT encoding.** Stress
  (B_i≡∀r.(C_i⊔C_{i+1}), i=1..N): N=20 3.6s, N=25 10s, N=30 24s, N=40 >90s. Cause:
  N excluded-middle splits `→Q_i∨NQ_i` seeded in EVERY context combine into 2^N
  residual disjunctions in one shared context. The fix is the **pay-as-you-go /
  safeCentral expansion strategy** (README "still open"): give each universal's
  reasoning its own core-keyed context so splits don't combine. Substantial engine
  effort; the named pure-CB architecture step. Real ORE impact (timeouts) unmeasured
  on this build -> benchmark-regress before/after safeCentral.
  CURRENT STATE (all re-validated+re-certified green): correctness COMPLETE for
  ∀-intro; polarity guard removes blowup for positive-only ∀ (common case);
  exponential only on many NAMED univ-equivalence classes. **Cost is actually
  HIGH-DEGREE POLYNOMIAL (~N^4-5), NOT exponential** (measured: N=3 50ctx/1357cl,
  N=12 206ctx/45k cl; ctx~O(N^2), time~O(N^4-5)); stress test is adversarially dense.
  **EAGER STRATEGY (core=K1) CONTRAINDICATED for this case** (verified): all
  non-root successor contexts have EMPTY core because univ-intro successors are
  CONDITIONALLY defined (ND_i is a disjunct in the predecessor -> K1=∅), so eager
  would MERGE them into one shared empty-core ctx = trivial-strategy combination,
  WORSE than the current per-function separation. The O(N^2)-context blowup is the
  Pred/Succ message cross-product among per-function successors, not solvable by
  eager. Right next step = either (a) measure real-ORE impact (only poly, likely
  fine on real onts), or (b) deeper diagnosis of the per-function successor
  interaction. Engine NOT modified. Files: moose
  normalisation.py (Forall ¬Q encoding + mark_polarity + normalise pre-pass),
  km certgen_term.py (maximal_head + budget), examples/ontologies/forall_intro.ofn,
  lean/Validation/ForallIntro.lean + Validation.lean + run.sh. NOT committed yet.

REPRO HARNESS: cd kobayashi-marust; KM_ENGINE=engine/target/release/kobayashi-marust
PYTHONPATH=engine/py:../moose ../moose/.venv/bin/python engine/py/owl_classify.py
/tmp/t3.ofn  (outputs {"subsumptions":[[sub,sup]...]}). Test .ofn files in /tmp/t3-7.

DISCIPLINE for the program: never silently approximate (fragment guard); soundness
per-run via the Lean-verified checker (consider Rust port for self-cert); completeness
via ladder + HermiT oracle + ORE benchmark CI. Ladder: P1 in-frag completeness ->
P2 accuracy guard + checker -> P3 role automata (R/S) -> P4 nominals (Table-3) ->
P5 datatypes (D) -> P6 perf/robustness.
See [[project_km_audit]] [[project_km_reasoner_perf]] [[project_disjunctive_context_calculus]].
