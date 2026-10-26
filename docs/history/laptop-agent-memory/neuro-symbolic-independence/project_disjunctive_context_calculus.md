---
name: project_disjunctive_context_calculus
description: Validated Rust + Lean implementation of the Tena-Cucala/Sequoia disjunctive context calculus for the SROIQ-NeSy paper
metadata: 
  node_type: memory
  type: project
  originSessionId: 8013a140-9c7d-4310-a78e-c7c6c789bcd4
---

The disjunction soundness bug (spurious ⊤⊑⊥ on kinship) that forced an earlier
retraction is **fixed**: replaced the Horn-only context reasoner with a faithful
port of the **Tena-Cucala / Cuenca Grau / Horrocks disjunctive context calculus**
(the Sequoia reasoner's core).

Artifacts (all under `sroiq-nesy/`):
- `rust-context-reasoner/src/{calc,clause,engine,reasoner}.rs` — the engine
  (Core/Hyper/Pred/Succ/Eq/Ineq/Elim; trivial expansion strategy; terms
  x=0,y=-1,z_i=-(i+1),f=+i exactly as Sequoia). 5 unit tests pass.
- `lean/ContextCalculus/Basic.lean` — soundness PROVED in Lean 4 (resolution_sound,
  derivable_sound, subsumption_sound, unsat_sound, paramodulation_sound); only
  axiom is `propext`, no `sorry`. `lake build` green.
- `oracle/` — HermiT validation oracle (`run_oracle.sh`, `validate.py`, `results/`).
- Sequoia source guide cloned at `/tmp/Sequoia` (github.com/andrewdbate/Sequoia).
- Primary spec: `papers/dl/tena-cucala-*` and the ALCHOIQ 2018 paper (Tables 2 & 3).

Validation vs HermiT (sound everywhere — **0 unsound, 0 spurious unsat**, now
also **complete** on every benchmark): disjunction 0/0, kinship_chain 0/0,
kinship **21/21**, factor_test (≥3⊓≤2 unsat), trans_test (A⊑D), chain_test
(A⊑D) — all match HermiT exactly. pizza terminates (slow, trivial strategy).

The three previously-dropped features are now IMPLEMENTED + validated:
- **Factor** rule in the engine (`engine.rs::factor`) + body-equality handling
  in the parser (a body `a≈b` becomes a head `a≉b`); fixes number-restriction
  clashes. Also fixed Eq dispatch so equality/inequality clash is order-independent.
- **Nominals**: sound ABox-grounded reduction `{o}⊑C` from each `C(o)`
  (`py/preprocess.py::nominal_clauses`); closes kinship's 4 `Queen⊑*`.
- **Transitivity + role chains**: reachability/automaton encoding
  (`py/preprocess.py::transitivity_clauses`, `chain_clauses`) — `R∘R⊑R` and
  `R∘S⊑T` into central-form clauses.

Still open (honestly): the **general regular-role-hierarchy automaton** (only
single chains/transitivity), the **full Table-3 nominal rules** (merge cases
beyond ABox-grounded), and the `safeCentral` pay-as-you-go strategy (pizza slow).

**Completeness in Lean** — proved for the TWO foundational directions, both
sorry-free:
- `CompletenessProp.lean` — refutational completeness of propositional resolution
  (`PropRes.completeness : Unsat S → Derivable S ⊥`), disjunction direction; DP
  conditioning + lifting lemmas; axioms [propext,Classical.choice,Quot.sound].
- `CompletenessEL.lean` — first-order completeness of consequence-based EL via a
  canonical model with existential witnesses (`EL.completeness`, `canon_models`,
  `EL.sub_sound`); the existential/Succ-Pred direction; **axiom-free** (no axioms
  at all). The closure Sub/Edge = engine's Core/Hyper/Succ/Pred on Horn EL.
mathlib added to sroiq-nesy/lean (CompletenessEL needs no mathlib; Prop does).

**Disjunction × existential interaction now CLOSED for ALC** (new file
`CompletenessContext.lean`, sorry-free, axioms [propext,Classical.choice,Quot.sound]):
the genuinely open case (disjunctive ontology has no least model so the EL
least-model construction breaks; the propositional theorem has no witnesses).
Built as the **finite filtration / good-type model** the context calculus
actually computes: a *type* = Finset of concept names (a propositional model of
the GCIs; disjunction = which disjunct the type chose); `compat` edge (∀ forward,
∃r.d⊑c back); `Good t` = t lies in a self-realising Finset of types (every forced
existential has a witnessing edge inside) = a context surviving saturation;
type-elimination IS saturation. Theorems: `canon_models` (canonical interp over
good types models O — the Herbrand construction, NO assumed Herbrand lemma unlike
moose), `sat_iff_good` (concept satisfiable over all models ⟺ in some good type;
forward = filtration collapsing any model to the finite good-type set),
`subsumption_complete` (O⊨A⊑B ⟺ every good type with A has B), `unsat_iff_no_good`.
This is MORE than moose's ALC (infinite Lindenbaum/Zorn types, not the finite
computed structure) and more than our EL (Horn least model).

**Merging features now BUILT** (new file `CompletenessEq.lean`, sorry-free, axioms
[propext,Classical.choice,Quot.sound]): the **equality-quotient Herbrand model**.
The engine grounds a saturated/blocked context structure to ground clauses over
atoms con/rol/eqa; the model = congruence quotient `T/≈π` of a propositional
model π of the grounding G (x≈πy := π(eqa x y)). Theorems: `congruenceModel_models`
(quotient of any π⊨G is a genuine FO model of O including FUNCTIONAL roles ≤1,
NOMINALS as singletons, INVERSE roles, role hierarchy, on top of disjunctive ALC),
`respectsEq_of_grounds` (congruence DERIVED from the eq-axioms in G, not assumed),
`herbrand_complete` (clash-free G [¬ propositional Derivable ⊥] ⟹ O has a model;
model existence reused from `PropRes.completeness`, NO assumed Herbrand lemma).
Merging = the quotient; functionality = binary eq clause; nominal {o} = con a x→eqa x o;
inverse = role-atom clauses. `Grounds G O wit` is a precise structure listing the
ground instances G must contain (eq axioms + every instantiation over the blocked
Herbrand universe).

BOTH previously-open pieces now MECHANIZED (sorry-free): (1) general ≤n R.C
(`OClause.atMost`, `atMostBody`/`atMostHead`, pigeonhole over (n+1)-tuples of the
Factor distinctness clauses → quotient collapses any n+1 successors to ≤n classes);
(2) concrete grounder `ground` + `grounds_ground` proving it satisfies `Grounds`
(eqAxiomSet ∪ per-clause instance images over finite vocab+universe), so Grounds is
REALISED by a verified function, not assumed. Capstone `herbrand_complete_ground`:
finite vocab+Herbrand universe + clash-free concrete grounding ⟹ O has a model,
covering disjunction+∃+∀+role hierarchy+inverse+nominals+≤n. NO assumed Herbrand
lemma, NO assumed grounding. Genuinely MORE than prior moose Lean (whose
`TenaCucalaCompleteness` is proved FALSE and whose context completeness ASSUMES
`CompositeRefutationLemma`/`herb_models_O`).

ENGINE-FAITHFULNESS layer now ALSO mechanized (two new files, sorry-free, axioms
[propext,Classical.choice,Quot.sound]):
- `Termination.lean` — BLOCKING TERMINATION. Cores = Finset CN (Fintype via Fintype CN);
  blocking = distinct cores on a branch (BlockedBranch = List.Nodup). Theorems:
  `branch_depth_bound`/`context_branch_bound` (length ≤ 2^|CN| via List.Nodup.length_le_card
  + Fintype.card_finset), `no_infinite_branch` (not_injective_infinite_finite),
  `reachable_finite` (subset of List.finite_length_le), `blockedUniverse` + Fintype
  instance → discharges CompletenessEq's [Fintype T] premise. König argument.
- `Equivalence.lean` — OPTIMIZED SATURATION ≡ GROUND RESOLUTION. `derivable_bot_iff_unsat`
  (PropRes Derivable ⊥ ↔ Unsat, via derivable_sound + PropRes.completeness). `Saturation S N`
  structure = sound (N⊆derivable) + resolution-closed + S⊆N = faithful model of engine output.
  `saturation_refutes_iff_derivable` (⊥∈N ↔ Derivable ⊥), `saturation_refutes_iff_unsat`,
  `engine_agrees_ground` (engine saturation of grounding refutes ⟺ ground resolution ⟺ unsat;
  non-refutation ⟹ genuine model via herbrand_complete). Models the COMPLETE (trivial-strategy,
  full-closure) saturation — finite since ground atoms finite.

ACTUAL-REASONER VALIDATION (verified certificate checking): `Checker.lean`
(`checkCert`/`checkCert_sound`: a resolution certificate over the genuine premises,
acceptance ⟹ `entailed`, reusing `resolution_sound`; `certifies_subsumption`,
`certifies_unsat`). `rust-context-reasoner/py/certgen.py` runs the REAL engine binary,
re-derives each reported verdict from premises by resolution (engine output NEVER an
axiom), emits `lean/Validation/*.lean` proved `by decide` (KERNEL-checked, #print axioms
= [propext] only, NO native_decide, NO sorry). Driver `validation/run.sh`; lakefile has a
`Validation` lean_lib in defaultTargets. TWO verified checkers: `Checker.lean` (propositional resolution) + `CheckerFO.lean`
(FIRST-ORDER: FModel with fn:Nat→D→D for successors; validFO; sound universal
instantiation `inst_valid` via subst lemma `evalL_litσ` for f-free clauses, plus
σ=[] path for the Skolem premises; `certifies_subsumptionFO`/`certifies_unsatFO`).
certgen_fo.py (term coding: x=0, f(x)=+index, neighbours/inds negative; generates
premise INSTANCES at successor terms then BFS resolution). certgen_fo.py PRUNES the cert to the derivation DAG (else `decide` hits maxRecDepth;
also set_option maxRecDepth 8000). Validated 20 verdicts on real engine runs,
kernel-checked `by decide` ([propext,Quot.sound]): disj (A⊑D,B⊑D,C⊑D — disjunctive
case old Horn reasoner got WRONG), disjoint (A⊑⊥), hierarchy (12 kinship-style),
exists (A⊑D via ∃R/value-restriction=SUCC, B⊑C), numrestr (A⊑⊥ via ≥2 R.C ⊓ ≤1 R.C
clash = Eq/Factor NUMBER RESTRICTIONS). Coverage = resolution (Core/Hyper/Pred/Elim)
+ Succ (existentials) + Eq/Factor (number restrictions: in the engine's encoding the
witness equality is an OPAQUE clause atom — derived in a head, consumed in the
distinctness clause body — so the clash is plain resolution+instantiation, NO
superposition rule needed). Nominals/inverse roles reduce to resolution clauses
(covered class). Both former residuals now CLOSED:
(a) PARAMODULATION INTO A LITERAL (superposition): added to CheckerFO
(`evalL_rewriteLit`, `paraResolvent`/`paraResolvent_sound`, JustifFO `.para`);
certgen_fo generates `.para` (restricted to unit-eq facts to bound search);
validated `paramod` benchmark A⊑D (functional role rewrites C(f2)→C(f1)),
kernel-checked [propext,Quot.sound].
(b) .ofn FRONT-END (not bypassed): wrote `py/frontend.py` — an OWL
functional-syntax parser producing moose's sx.Ontology AST, reusing moose's REAL
`normalise`+`augment` (NO pyhornedowl needed; only the parser is local). Roles:
plain→short str, inverse→sx.InverseRole(str); And/Or via mkAnd/mkOr (frozenset);
RoleChain tuple. Bug fixed: comment-strip must not touch `#` inside <IRIs> (handle
comments in tokenizer regex AFTER the IRI rule). certgen_fo accepts .ofn (runs
frontend) and filters normalisation-internal concepts (Q_*, __trans__/__chain__/
__nom__). Front-end VERIFIED correct: engine verdicts match HermiT oracle after
internal-filtering. .ofn-sourced kernel-checked validations: trans_test.ofn→B⊑D,
kinship.ofn→11 subs incl NOMINAL Queen⊑Royal/Queen⊑Female.
certgen_fo two-phase search: resolution-only first (fast for propositional), then
with instances (needed for Succ/Eq). 33 verdicts total kernel-checked.

NESTED-SUCCESSOR RESIDUAL NOW CLOSED (was: CheckerFO's one-level f_k(x)): new
`CheckerTerm.lean` (sorry-free, axioms [propext,Quot.sound]) replaces the Int term
code with a genuine TERM ALGEBRA `FTerm` (var i | app f t), so f(g(x)) is
first-class. Reuses Basic's GENERIC resolution core at Atom:=FLit (resolvent/
resolution_sound/Derivable); adds substitution soundness `inst_valid` (now
UNCONDITIONAL — no clFree, since subst into a term algebra always commutes with
eval), subterm paramodulation `paraResolvent_sound`/`evalL_rwL`/`evalT_rwT`, and
checker `certifies_subsumptionT`/`certifies_unsatT`. New generator
`py/certgen_term.py` (term-tree interner recursing into `arg`) re-derives with a
LAYERED, COMPLETE (not Horn-only) pipeline, tried in order:
(a) propositional resolution (fast path);
(b) unit-driven Horn FORWARD CHAINING over the term algebra (instantiate Horn rule
at successor terms its body matches vs ground UNIT consequences; Factor eqs +
forward paramod s→t) — efficient, gets the vast majority;
(c) COMPLETE DISJUNCTIVE SATURATION = ground resolution over matching-driven
instance generation (positive hyperresolution): instantiate rules at successor
terms matching the pool of ground positive consequences (incl. DISJUNCTS), then
resolve rule-instances against consequences carrying residual disjunctions —
handles disjunction AND nested successors TOGETHER. Bounded by MAX_CLAUSES (may
give up on ontologies with many excluded-middle defs; naive hyperres explodes to
~200k clauses on kinship's `→Parent∨Q_9`-style EM clauses, hence layer (b) first).
KEY BUG fixed in (b): must skip when the CONSEQUENCE canon([],head) is already
derived, NOT when the instance is in index (a var-rooted schema IS its own
x:=var0 instance, so `inst in D.index` is always true → never fired).
run.sh + Validation.lean use modules Disj/Disjoint/Hierarchy/Exists/Numrestr/
Paramod/Disjsucc/Transtest/Kinship. 45 verdicts kernel-checked (was 33): incl.
trans_test A⊑D (nested f(g(x))), kinship 21/21 (…⊑Narcissist/Grandparent⊑… chains,
EXACTLY = HermiT oracle's 21, verified set-equal), and NEW `disjsucc` benchmark
A⊑∃R.(B⊔C),∃R.B⊑D,∃R.C⊑D ⊢ A⊑D — disjunction×successor, derived ONLY by layer (c)
(both (a) and (b) return None), proving the engine is complete for the full logic.
CheckerFO/certgen_fo kept (still proven) but superseded by CheckerTerm. Only
remaining boundary: layer (c) is clause-capped (ordered/pay-as-you-go strategy
not re-mechanized); all benchmarks certified within the bound.

Now MECHANIZED end to end: Herbrand construction (sound+complete, all NExpTime features),
blocking termination, saturation≡resolution, AND per-run verified validation of the actual
reasoner's verdicts. ONLY validated-empirically-not-mechanized:
(a) Rust rule applications realise the Saturation spec + Nodup-blocking invariant (per-rule
soundness IS mechanized in Basic.lean; closure = fixpoint); (b) ordered/pay-as-you-go
refinement completeness (classical Bachmair-Ganzinger; we mechanize trivial-strategy);
(c) general regular-role-hierarchy automaton (only transitivity+single chains). Root
ContextCalculus.lean imports all 6 files: Basic, CompletenessProp, CompletenessEL,
CompletenessContext, CompletenessEq, Termination, Equivalence.

Lean completeness now in FOUR stages: PropRes (disjunction) → EL (existential, Horn
least model) → Ctx (disjunctive-ALC filtration/good-type) → Eqv (equality-quotient
Herbrand for merging). Root `ContextCalculus.lean` imports all.

Key non-obvious fix: the normal-form input filter must drop a clause only when a
body **role** lacks a central variable (real role-chain `R(z_i,z_j)`); a body
**concept** on a neighbour var like `C(y)` in `R(x,y)∧C(y)→D(x)` is legal and was
wrongly dropped, which had blocked all existential subsumptions (e.g. the EL
`A⊑∃R.B,B⊑C,∃R.C⊑D ⊢ A⊑D`).

Relates to [[project_sroiq_nesy_submission]].
