# Hybrid Consequence-Based + Hypertableau Reasoning for KM

Status: design + staged build (started 2026-06-06).

## Why

KM is a pure consequence-based (CB) reasoner (Tena-Cucala ALCHOIQ calculus). It
saturates *all* consequences in one pass, which is optimal for Horn/deterministic
ontologies but blows up when disjunctions are *live* (e.g. heavy `∀ + ⊔` creating
excluded-middle splits). Measured: `ore_ont_541` and a `B_i ≡ ∀r.(C_i ⊔ C_{i+1})`
stress test both time out, and every pure-CB lever (subsumption resolution,
given-clause ordering, context blocking, global-closure sharing) is verdict-correct
but gives no speedup, because the work is irreducible *live* disjunctive saturation
with no redundancy to exploit. See `notes/*.patch` and the perf memory.

The fix is architectural: keep CB for the deterministic part, but for the
disjunctive residual **build one model with a hypertableau** (model exploration +
backtracking + blocking) instead of saturating every consequence. This is how
HermiT/Konclude beat CB on these ontologies: explore *one* model, not *all*
consequences.

References (local): `papers/dl/msh09-hypertableau-JAIR.pdf` (the calculus HermiT
implements), `papers/dl/bate-cuenca-grau-motik-2016-extending-CB-SRIQ.pdf` (CB→SRIQ,
the hybrid direction), `papers/dl/tena-cucala-...-2018-CB-ALCHOIQ.pdf` (KM's
calculus). Konclude's own C++ source is NOT public (the GitHub repo ships only
build configs + binaries), so we build from the calculus papers, which is the
right foundation for a clean Rust implementation anyway.

## The hypertableau calculus (implementation spec, condensed from msh09)

Decides consistency of a knowledge base by clausifying to **HT-clauses** and
saturating a **completion graph** (a labelled forest of individuals).

### HT-clause normal form
`U_1 ∧ ... ∧ U_m → V_1 ∨ ... ∨ V_n` (body conj of atoms → head disj of atoms),
over a center variable `x`, branch variables `y_i` (each guarded by a body role
atom `R(x,y_i)`/`R(y_i,x)`), nominal variables `z_j` (guarded by `O_a(z_j)`).
Atoms: literal-concept `B(t)` (`B ∈ {⊤,⊥,A,¬A}`), `≥ n R.B(t)`, role `R(s,t)`,
`ar(R,s,s)` self, equality `s ≈ t` (number restrictions put eq-disjunctions in
the head). KEY: existentials are NOT Skolemized — they stay as `≥ n R.B` head
atoms; successors are created at *runtime* by the ≥-rule (this is what blocking
needs). Antecedents must be path-length-one (normalization guarantees this).

### Completion graph
Root individuals (named + NI-introduced, arbitrary graph) and blockable
individuals (tree successors `s.i`). Labels `L(s)` = atomic concepts on `s`;
`L(s,t)` = atomic roles on edge. Equality `≈` / inequality `≉`. Clash token `⊥`.

### Rules (Table 5, applied to non-indirectly-blocked individuals)
- **Hyp** (only OR-branch): clause `r`, mapping `σ` of its vars to individuals,
  `σ(U_i) ∈ A` for all body atoms, `σ(V_j) ∉ A` for all head atoms ⇒ branch into
  `n` children each adding one `σ(V_j)` (or add `⊥` if `n=0`). Horn (`n≤1`) =
  deterministic, fire eagerly.
- **≥-rule** (deterministic, needs `s` NOT blocked): `≥ n R.B(s)` with no existing
  witnesses ⇒ add `n` fresh distinct successors `t_i` with `R(s,t_i)`, `B(t_i)`,
  pairwise `t_i ≉ t_j`.
- **≈-rule** (merge): `s ≈ t` ⇒ `merge(s→t)` per direction rules (descendant→
  ancestor, blockable→root, non-named→named). Always `prune` before merge.
- **⊥-rule** (clash): `s ≉ s`, or `{A(s), ¬A(s)}` ⇒ add `⊥`.
- **NI-rule** (only if nominals + inverse + number restrictions all present):
  bounds root chains; drop entirely otherwise.

### Blocking (termination): pairwise anywhere blocking
Blockable `s` directly blocked by blockable `t` (`t` not blocked, `t ≺ s`) iff
`L(s)=L(t)`, `L(s')=L(t')` (predecessors) and both edge directions
`L(s,s')=L(t,t')`, `L(s',s)=L(t',t)`. Indirectly blocked = has a blocked
predecessor. Without inverse roles: atomic single blocking `L(s)=L(t)` suffices.

### Decision procedure
Apply rules (precedence: ⊥ > deterministic Hyp > ≈ (NI-gated) > ≥) over a DFS
search tree. Some clash-free complete leaf ⇒ SAT; every branch clashes ⇒ UNSAT.
Subsumption `K ⊨ A ⊑ B` iff `K ∪ {A(a), ¬B(a)}` UNSAT (fresh `a`).
Correctness obligations: Lemma 5 (soundness: every-branch-clash ⇒ unsat),
Lemma 6 (completeness: clash-free leaf ⇒ sat, via unraveling), Lemma 7
(termination via blocking + NI). 2NExpTime.

## Hybrid architecture (target)

Per the Bate-2016 analysis, the right design is **per-context, threshold-triggered**,
not per-candidate-subsumption (which throws away CB's one-pass classification):

1. CB front-end runs normally: Core/Hyper/Pred/Succ saturate the deterministic /
   Horn closure and lay out the context graph. Ontologies with no live disjunction
   never invoke the tableau → pure-CB speed (pay-as-you-go preserved).
2. Track per context `v` the live disjunctive clauses (heads with ≥2 disjuncts
   irreducible by Eq/Factor/order). When the count crosses a threshold (where
   continued Hyper would blow up `S_v`), **freeze** `v` and hand it to the tableau.
3. Tableau receives `core_v` (seed labels) + frozen clause set `S_v` (already
   HT-clauses) + boundary constraints from incident Pred/Succ edges. Returns:
   - UNSAT ⇒ minimal clash core `Γ' → ⊥`, re-internalized as a context clause and
     propagated via existing Pred/Succ.
   - SAT ⇒ branch-invariant atoms `Γ → A` folded back as Horn context clauses (so
     the rest of classification still benefits one-pass).
4. Cache SAT/UNSAT keyed on `(core_v, relevant-clause-subset)` — amortizes over all
   ground terms a context represents. Nominal caveat: root/nominal interaction is
   global (Tena-Cucala `v_r`), so root-touching contexts pass root constraints in
   or are excluded from caching.

### Reuse vs new work
Reuse directly: DL-clause normal form, Hyper rule, Pred/Succ + Su/Pr triggers +
context edges, Eq/Ineq/Factor, Core + expansion strategy, order `≻` + Elim.
Genuinely new: OR-branching/case-splitting over disjunctive clauses; runtime
completion-graph model construction (the proof's model build, made executable);
clash + unsat-core extraction; branch-invariant-atom extraction; the liveness
threshold; blocking for termination; nominal-safe caching.

## Staged build plan

The divergence to resolve up front: KM's moose normaliser pre-Skolemizes `∃`
(`f(x)`), hypertableau wants un-Skolemized `≥ n R.B` with runtime successors. The
tableau layer needs HT-clause input, so either (a) add a HT-clause emit mode to the
moose normaliser, or (b) a thin adapter mapping KM's `f(x)` Skolems to `≥1 R.B`
triggers. Plan uses (a) for faithfulness.

### M1 status (2026-06-07): ALC tableau core DONE + proof-of-value validated

`engine/src/tableau.rs` (+ `bin/tableau_cli.rs`): ALC completion graph, Hyp
(Horn + disjunctive OR-branching, DFS backtracking), ∃-rule (runtime successors),
clash, ancestor subset blocking. JSON driver + classify (O(n²) consistency checks).
7 unit tests + integration on the `B_i ≡ ∀r.(C_i⊔C_{i+1})` stress ontology vs
HermiT (local jar) and the CB engine:

| N | Tableau | HermiT | CB (KM) | verdict = HermiT |
|---|---------|--------|---------|------------------|
| 15 | 0.25s | 1.19s | 3.34s | yes |
| 25 | 1.39s | 1.36s | 38.9s | yes |
| 40 | 9.3s  | 1.9s  | timeout | yes |
| 60 | 42.7s | 3.6s  | timeout | yes |

Thesis validated: the tableau completes where pure CB times out, with verdicts
identical to HermiT at every N. It is slower than HermiT (lacks told-subsumer
classification, indexed matching, incremental/trail backtracking, caching) — the
brute-force O(n²) `A⊓¬B` classification loop and per-step full rescan dominate.
Those optimisations are follow-on; in the hybrid the tableau runs only on frozen
disjunctive *contexts*, not whole ontologies. Generator: `/tmp/gen_stress_ht.py`.

#### Real-ORE batch (40 ontologies, `oracle/validate_ht.py` vs HermiT)
Progression over the 2026-06-07 work (all vs HermiT, 30 s budget):
- pre-fix:        `MATCH=5 MISMATCH=1 OUT-OF-FRAG=0  TIMEOUT=20 CBERR=7` (RBox silently dropped)
- +RBox fix:      `MATCH=4 MISMATCH=0 OUT-OF-FRAG=21 TIMEOUT=8  CBERR=7`
- +transitive SH: `MATCH=4 MISMATCH=0 OUT-OF-FRAG=15 TIMEOUT=14 CBERR=7` (6 onts un-fenced; perf-bound)
- +classify prune:`MATCH=7 MISMATCH=0 OUT-OF-FRAG=15 TIMEOUT=11 CBERR=7`
- +indexed sat:   `MATCH=9 MISMATCH=0 OUT-OF-FRAG=15 TIMEOUT=9  CBERR=7`
- +inverse (SHI): `MATCH=12 MISMATCH=0 OUT-OF-FRAG=13 TIMEOUT=8 CBERR=7` (pairwise blocking)
- +loop-back ∃:   `MATCH=11-12 MISMATCH=0 OUT-OF-FRAG=13 TIMEOUT=8-9 CBERR=7` ← current
  (loop-back fixes inverse non-termination; `ore_ont_1017` non-inverse borderline ~26-40 s
  flips MATCH/TIMEOUT with machine load — task #26. Zero mismatch throughout.)

The MATCHes are exact vs HermiT, several with large subsumption sets:
`ore_ont_10056` (1067), `10133` (985), `10134` (6794, SH transitive), `10146`
(8813, SH transitive), `10160` (7107), `10162` (5474), `10174` (437), `10176`
(106), `10199` (1, former MISMATCH). MISMATCH is 0 (no unsound output ever). The 15
OUT-OF-FRAGMENT are honestly fenced (inverse/symmetric/role-chain/functional/
complex-dom-range). The 9 TIMEOUT are genuinely in-frag (ALC+H+transitive): a few are
borderline (`ore_ont_1017` ≈26 s standalone, over budget only under batch load) and
`ore_ont_10248` is the hard case (67k concepts / 165k clauses). CBERR=7 are datatype
axioms moose's normaliser rejects (DataExactCardinality, ObjectHasValue, …) — a
separate frontend-fragment gap. NB two pre-fix "MATCHes" (10026, 10088) actually
carried inverse/chain and are now correctly fenced.

The batch originally exposed TWO M1-hardening gaps; gap #1 (RBox) is fixed and gap
#2 (perf) is partially addressed:

1. ~~**The CB→HT converter silently drops the RBox.**~~ **FIXED (2026-06-07).**
   moose folds role hierarchy (`r⊑s`), domain, range, inverse, transitivity into
   the CB *engine's* trigger machinery + `augment` step, NOT as concept-clauses, so
   they never reached `cb_to_ht.py`. The fix reads the RBox straight from the parsed
   functional syntax (`frontend.ofn_rbox`, same s-expression parser, no regex) and
   the converter emits the in-fragment axioms as HT-clauses:
   - `r⊑s` → `r(x,y)→s(x,y)` (Horn edge clause).
   - `range(r,C)` → `r(x,y)→C(y)` (Horn; the blocked-node case is covered by the
     blocker's successor copy, so no obligation propagation is needed).
   - `domain(r,D)` → `r(x,y)→D(x)` (backward Horn edge clause — SOUND, it only
     asserts `D` where `r` genuinely has a successor). The blocked-node gap (a node
     carrying an `∃r` obligation the ∃-rule never realises) is recovered by
     **domain-obligation propagation**: every existential clause `Body→∃r.fil`
     additionally emits `Body→D(x)` for `D` in the domain of `r` *or any super-role
     of `r`* (reflexive-transitive `subrole` closure). All Horn, no branching.

   Crucially the *blocking-safe* GCI encoding `domain(r,D) ≡ ⊤⊑D⊔∀r.⊥` was REJECTED:
   it adds a per-node disjunction for every domain role (36 in `ore_ont_10199`),
   giving 2^36 branches per node — it made even a single subsumption check time out.
   The Horn edge clause + obligation propagation is sound, complete, and cheap.

   Out-of-fragment RBox axioms (inverse, symmetric, reflexive, functional, role
   chains, asymmetric/disjoint roles, complex/⊥ domain-range) are returned as
   `("fenced", reason, detail)` records; the converter surfaces them in
   `TInput["fenced"]` and the driver marks the whole ontology OUT-OF-FRAGMENT rather
   than silently dropping a constraint. (M1b will move inverse in-frag.)

   **Transitive roles are NOT fenced (SH fragment, 2026-06-07).** moose's TBox
   normalisation already encodes transitivity losslessly as `__trans__r__C`
   propagation concepts in the concept-clauses (verified: `B(y),r(x,y)→__trans__r__C(x)`
   etc.), which the converter passes through unchanged. Subset blocking is sound for
   SH (transitive + hierarchy, no inverse); an ontology that *also* has inverse/
   symmetric is still fenced by those (SHI needs pairwise blocking). Validated exact
   vs HermiT on committed fixtures: `trans_test` (transitive chain `A⊑D`), `trans_block`
   (blocking-active infinite chain `Inf⊑Win` — needs transitivity *and* blocking),
   `trans_hier` (transitivity through a role hierarchy, exercising the new `r⊑s`
   clause). In the ORE sample this un-fenced 6 ontologies into the in-fragment set.

   Validated: `ore_ont_10199` MISMATCH→MATCH (`Animal⊑Scientist`, exact vs HermiT);
   `ore_ont_10056` MATCH 1067 subs, `10174` 437, `10176` 106 — all exact; committed
   regression fixtures `oracle/ontologies/{rbox_domain,trans_test,trans_block,trans_hier}.ofn`
   (+`results/*.json`). Harness: `oracle/validate_ht.py <dir> --timeout S`. The RBox
   fix is converter-side (engine `tableau.rs` unchanged → Lean calculus cert holds).
2. **Performance (addressed 2026-06-07).** Two compounding, verdict-preserving
   `tableau.rs` changes (perf only, no calculus-logic change; the tableau is
   HermiT-validated — the oracle suite is the regression gate):
   - **classify pruning**: no more brute `O(n²)` `{A,¬B}` sweep — build ONE model of
     each `{A}` and confirm only the named concepts in `M_A`'s root label (a subsumer
     holds in every model, so it cannot be outside `M_A`).
   - **indexed batched saturation** (`saturate`): the old `deterministic_step` returned
     after ONE derived fact, so the outer loop re-scanned all clauses from index 0 per
     fact (≈ `M` full scans for `M` facts). `saturate` now applies ALL Horn
     consequences per pass and loops to fixpoint (Horn fully before each ∃ round, so
     blocking still sees complete labels), and a per-clause **predicate-presence index**
     (`present_lits`/`present_roles` on the graph + `matchable()`) skips any clause whose
     body needs an absent concept-literal or role — the bulk of the clause set early on.

   Effect (full classification, exact vs HermiT): `ore_ont_1017` (1918 concepts / 3522
   clauses) **>90 s timeout → 26 s, 1852 subs**; `ore_ont_10160` **timeout → 13 s, 7107
   subs**. ORE batch MATCH 7 → (see batch table). Verdicts identical on all fixtures and
   prior matches; 20/20 Rust tests pass.

   Remaining: very large ontologies (`ore_ont_10248`, 67k concepts / 165k clauses) still
   exceed budget; the next lever there is true semi-naive (drive matching from the
   newly-added fact rather than re-running `match_body` over a triggered clause), plus
   sharing the TBox deterministic closure across the `n` per-concept checks.

### CB-engine scaling (2026-06-07): semi-naive inter-context propagation

The bulk classifier for in-fragment (EL/SH/SHQ) real ontologies is the **CB engine**
(`engine.rs`, the `kobayashi-marust` binary), not the tableau — the tableau only runs
on the disjunctive residual. Profiling the slow large ORE ontologies (env `KM_STATS`
counters) located the actual wall, and it was NOT the predicted "shared TBox closure":
the ⊤ empty-core context is essentially empty on every real ORE ontology (`top_wo≈0`),
so there is no deterministic backbone to amortise. The real cost was the **inter-context
Pred-pushback loop** in `propagate()`, which re-scanned the full `worked_off × all
predecessor edges` on every call — **95–123 M** redundant covered-checks on
existential-rich ontologies (e.g. `ore_ont_10162`: pred_checks 95.3 M vs 60 k hyper
inferences).

Fix (semi-naive, verdict-preserving): append-only `pred_pool`/`succ_pool` of eligible
worked-off clauses + `pred_hwm`/`succ_hwm` high-water marks, and a per-edge `edge_seen`
pushed-length watermark. A `(clause, edge)` covered-check is re-run only when the clause
is new or the edge's pushed-set grew (the only way a failed check can flip). A
back-subsumed pool entry is left in place — still sound to push since it stays
context-entailed — so the high-water mark survives `worked_off` reshuffling.
`pushed_pred`/`pushed_succ` still dedup sends, so the message **set** is preserved; the
`saturate` count is byte-identical (only the wasted rescan removed).

Effect (A/B original vs optimized on `ws`, 56 cores, all subsumption sets IDENT):
single-thread `ore_ont_10162` **25.5 s → 0.8 s (31.8×)**, `10123` 18.9 → 1.4 (13.5×),
`10160` 20.4 → 1.8 (11.3×), `1017` **>250 s timeout → 11.3 s**, `10053` (12 k clauses,
6 k concepts) timeout → 57.5 s; already-fast ontologies unchanged (no regression).
pred_checks 95.3 M → 1.33 M. Validation: 30/30 Rust tests, 13 ORE byte-identical to the
git-HEAD baseline, 15/15 HermiT fixtures identical. Live-disjunction CB-blowup
ontologies (`10248`, `10125`, `10161`) still time out — those are the tableau's job, not
this fix. Instrumentation is env-gated (`KM_STATS`).

So M1 is a validated classifier on ALC + RBox + SH transitive: exact vs HermiT across
the in-fragment ORE sample, and it beats CB on the stress test.

### M1b status (2026-06-07): inverse roles — SHI, sound; termination caveat

moose does NOT encode inverse in the clauses (unlike `__trans__`); the `InverseObject-
Properties(r,s)` link lives only in the RBox. The converter now reads it (`frontend.
ofn_rbox` → `("inverse",r,s)`) and emits BOTH edge directions as clauses — `r(x,y)→s(y,x)`
and `s(x,y)→r(y,x)` — so the existing role matching navigates inverse with no engine
change for navigation. It also sets `TInput.inverse=true`.

Blocking: subset (ancestor) blocking is UNSOUND with inverse (a blocked node's label
flows back up the tree via the inverse edge), so `tableau.rs` adds **pairwise (double)
blocking**, enabled only when `inverse` is set (otherwise subset blocking is kept, to not
slow the inverse-free majority). A blockable node `s` with parent `p` is blocked by a
blockable strict ancestor `s2` with parent `p2` iff `L(s)=L(s2)`, `L(p)=L(p2)`, and the
edge labels match in both directions (`p↔s` vs `p2↔s2`) — equality + parent + bidirectional
edges, the standard SHI-sound condition.

VALIDATED exact vs HermiT (sound + complete on real inverse KBs): `ore_ont_10026`
(1774 subs, 0.12 s), `ore_ont_10123` (**11516 subs**, 19.9 s); committed fixture
`oracle/ontologies/inv_test.ofn` (`A⊑C` through `∀r⁻`). Non-inverse ontologies are
unaffected (subset blocking, `inverse=false`).

TERMINATION via **loop-back ∃-rule** (2026-06-07): pure equality blocking does NOT
terminate on the `∀r⁻`-over-infinite-generating-chain pattern (`A⊑∃r.A`, `A⊑∀r⁻.D`) —
the backward `∀r⁻` propagation lags one node behind the ∃-frontier, so the frontier never
equals an interior node and blocking never fires. Fix (in the pairwise path only): the
∃-rule is a CHOICE — an `∃r.fil` obligation is first satisfied by **looping back to an
existing ancestor** `t` (`fil ∈ L(t)`, `L(s) ⊆ L(t)`), building a cyclic model, with a
fresh successor as the fallback branch. Trying loop-back first collapses the infinite
chain to a small cyclic model; the fresh-successor fallback keeps the search COMPLETE (no
model pruned) and saturation keeps it SOUND (a loop-back that violates a constraint simply
clashes and is abandoned). `expand` splits: inverse-free KBs keep the fast batched
`saturate` (Horn + deterministic fresh ∃); inverse KBs use `horn_saturate` + disjunction
branch + loop-back ∃ branch. Validated: committed fixture `oracle/ontologies/inv_block.ofn`
(`A⊑∃r.A`, `A⊑∀r⁻.D`) **timeout → 0.00 s, exact vs HermiT**; `ore_ont_10026`/`10123`
unchanged-exact and `10123` even faster (19.9 s → 16.2 s — cyclic < blocked-tree).

### M2 status (2026-06-07): number restrictions — SHQ, sound + complete; nominals fenced

**Qualified number restrictions (`≥n R.C`, `≤n R.C`, functional roles).** Two
encodings, both reusing existing machinery so the only genuinely new tableau
operation is node *merging*:

- `≥n R.C` → **n existentials with pairwise-disjoint slot fillers.** moose emits n
  Skolem witnesses `f_q_0..f_q_{n-1}` plus distinctness constraints
  `q(x) ∧ ≈(fᵢ(x),fⱼ(x)) → ⊥`. The converter reads those distinctness pairs and,
  for each function in a pair, adds a fresh `__slot__f` concept to its filler and
  emits `__slot__fᵢ ⊓ __slot__fⱼ ⊑ ⊥`. The n successors are then ordinary
  existentials that simply cannot be merged (disjoint slots clash), which is
  exactly `≥n` — **no separate inequality relation needed**, the ∃-machinery and
  Horn clash handle it.
- `≤n R.C` and functional → an **`eq` head atom** the tableau discharges by
  *merging* the two nodes. `≤n` is `q(x) ∧ ⋀_{i=0..n}(R(x,yᵢ)∧C(yᵢ)) → ⋁_{i<j}
  ≈(yᵢ,yⱼ)`: a single-`≈` head (n=1, functional) is a forced merge inside
  `horn_saturate`; a multi-`≈` head (n≥2) is a Hyp-rule branch (each branch merges
  a different pair). `≤n` always merges R-successors of a *common* node — siblings
  — so the forest shape is preserved.

Merging is **union-find** (`Graph.repr`): the lower-id node survives, concept
labels + ∃-obligations are unioned onto it, every edge and tree-predecessor
pointing at the dead node is rewritten, and reads canonicalise through `find`.
A merge that unifies disjoint slots / an `A,¬A` pair clashes during the next
saturation and that branch is abandoned (sound); the Hyp-rule tries every pair
(complete).

Blocking: subset blocking is **unsound** with number restrictions (a blocked node
reusing a strictly larger ancestor can leave an at-most unsatisfied under
unravelling), so the `number` flag switches to **equality blocking** (`L(s)=L(t)`),
the standard SHQ-sound condition. `expand` gains a number-only branch (no inverse):
`horn_saturate` incl. deterministic merges → one Hyp branch → else batch-generate
fresh successors → recurse. `number` is set by the converter iff it emits an `eq`
head; `inverse ∧ number` (SHIQ) is fenced (the merge × pairwise-blocking
interaction is not yet validated). Plain functional roles are un-fenced;
inverse-functional stays fenced (it merges predecessors = inverse-flavoured).

VALIDATED exact vs HermiT, 0 MISMATCH:
- 5 Rust unit tests: ≤1 merge-clash unsat / merge-consistent, `≥2 r.C ⊓ ≤1 r.C`
  unsat via slots, `≥2` alone terminating, `≤2`-of-three merge.
- 4 committed `.ofn` fixtures: `card_ge_le_unsat` (≥2⊓≤1), `card_ge_sub` (≥2⊑≥1),
  `card_qual_unsat` (qualified ≤1 clash), `functional_unsat` (functional clash).
- **5 real ALCQ slices of `ore_ont_10140`** (the one pure-SHQ ORE ontology; line
  ranges of the cardinality-dense block 117400–134000): **442 / 867 / 1700 / 3860 /
  3726 subsumptions, all exact.** The full ontology (142 k concepts / 355 k clauses)
  is out of budget — but so is **HermiT** (both time out >400 s); that is the #26
  scaling gap, not a number-restriction bug. A single consistency + 1-concept check
  over the full 355 k-clause TBox runs in 1.1 s, so the merge machinery itself
  scales.

**Nominals (`{a}`) — M2b fenced; superseded by M2c below.** Before M2 the nominal
proxy `__nom__a` flowed through as an *unconstrained* concept name — a silent
incompleteness (the singleton "exactly one instance" constraint was dropped). M2b
fenced any ontology mentioning a `__nom__` concept and parsed
`ObjectHasValue(R a)=∃R.{a}` so those fence cleanly instead of raising. M2c (next
section) replaces the fence with full SHO/SHOQ nominal reasoning.

### M2c status (2026-06-08): nominals — SHO/SHOQ, sound + complete vs HermiT

A nominal `{a}` is a **singleton**: at most one element. The tableau enforces it
with two additions, both reusing the existing union-find merge — no new graph
operation:

- **o-rule (singleton merge).** `apply_nominal_merges`, interleaved in
  `horn_saturate`: for each nominal concept `__nom__a`, any two live nodes that
  both carry it denote the same individual ⇒ merge them (deterministic, no
  branch). A merge that unions conflicting labels (`C`, `¬C`) clashes on the next
  saturation pass and the branch is abandoned (sound); the Hyp-rule still explores
  every disjunctive branch (complete), so the singleton collapse happens *per
  branch*.
- **root seeding.** `find_model` seeds one non-blockable root per nominal, carrying
  `__nom__a`. The named individuals therefore exist in *every* model, so an
  ABox-level inconsistency (`{a} ⊑ C`, `{a} ⊑ ¬C`) is caught by the consistency
  check and the ABox facts `C(a)` (lifted by the front-end to `__nom__a(x) → C(x)`)
  propagate. Seeded roots get low ids, so a blockable node that later acquires
  `__nom__a` merges *into* the root (lower id survives, stays non-blockable) — the
  msh09 "blockable→root, non-named→named" merge direction, for free.

Termination is unaffected for SHO/SHOQ (no inverse): nominals are finitely many
roots, the o-rule only *reduces* node count, and blockable subtrees stay bounded by
equality blocking (switched on whenever nominals are present, sound + a stricter
superset of subset blocking). The msh09 **NI-rule** (unbounded root chains) is
needed only when nominals, inverse, *and* number restrictions interact (SHOIQ);
the converter fences nominal + inverse (`nominal+inverse(SHOI/SHOIQ)`) so it never
arises. `cb_to_ht` emits the nominal proxy ids in `TInput.nominals` (was: fenced);
the tableau switches on the merge-capable path via `set_nominals`.

VALIDATED exact vs HermiT, 0 MISMATCH:
- 4 Rust unit tests: singleton-merge unsat (`∃s.{a} ⊓ ∃t.{a} ⊓ ∀s.C ⊓ ∀t.¬C`),
  singleton-merge consistent, ABox subsumption (`Q≡{a}`, `{a}⊑C` ⇒ `Q⊑C` but
  `C⋢Q`), ABox global inconsistency (`{a}⊑C ⊓ {a}⊑¬C` ⇒ all unsat).
- 6 committed `.ofn` fixtures (+ HermiT baselines in `oracle/results/`):
  `nom_singleton_unsat` (SHO singleton clash), `nom_disjunction` (singleton merge
  across a disjunctive branch), `nom_shoq` (`≤1 r` merges a nominal + B-successor),
  `nom_abox_sub`, `nom_test`, and `nom_inverse_fenced` (SHOI correctly fenced).
  All MATCH HermiT. The ORE tableau batch is unchanged (0 MISMATCH) — no real ORE
  nominal ontology un-fences (each is also gated by role-chains/datatypes), so the
  fixtures are the validation target, as planned.
The change is converter + tableau-internal; the Lean CB-calculus certificate is
untouched (the tableau is separately HermiT-validated, not yet Lean-certified).

### M3-lite status (2026-06-08): automatic engine routing (`engine/py/route.py`)

KM now has two validated-complete classifiers over overlapping fragments; `route.py`
picks one per ontology from a cheap single parse, so callers need not know which
engine fits. Two things had to be pinned down first:

1. **CB's actual completeness boundary** (empirically, vs HermiT). The CB engine
   (clauses-only, via `owl_classify`) is complete on EL/SH/SHQ + role hierarchy +
   transitivity + role chains, but moose's normalise does **not** fold
   domain/range into the clauses and the Rust engine has no domain/range trigger,
   so every `ObjectPropertyDomain/Range` axiom was silently lost (verified:
   `A ⊑ ∃r.B`, `domain(r)=D` did **not** yield `A ⊑ D`). FIXED in
   `preprocess.domain_range_clauses` (called from `frontend.ofn_to_clauses`): emit
   the backward Horn clauses `r(x,y)→D(x)` / `r(x,y)→C(y)`, which fire on the
   engine's Skolem edges and cover the super-role case via the existing `r⊑s`
   clause. Pure input-clause augmentation (like the nominal/transitivity augments)
   so the engine calculus and its Lean cert are unchanged. After the fix CB is
   complete on EL/SH/SHQ + hierarchy/transitivity/chains/**domain/range**, but
   still **not** on inverse roles (the engine never navigates inverse edges) or
   nominals (only the sound-but-incomplete ABox grounding).
2. **CB's blow-up is in *memory*, not time.** The `∀+⊔` excluded-middle pattern can
   drive CB to materialise every successor-type combination; an `EquivalentClasses`
   stress test pushed it past **47 GB in seconds**, OOM-thrashing the host so hard
   that a wall-clock `subprocess` timeout could not even fire. So a
   "try-CB-then-fall-back-on-timeout" race is unsafe — the router must decide up
   front and must cap CB's address space.

Routing (one parse; `live` = disjunctive clauses whose body concept is a
*successor concept* — asserted on a non-centre term, the `∀+⊔` pattern):
- **in-fragment + inverse or nominals → tableau** (CB incomplete; tableau is the
  validated-complete engine there).
- **in-fragment + `live > 0` → tableau** (CB could explode; never speculatively
  run). The tableau builds one model and terminates.
- **otherwise → CB**, under a hard address-space cap (default ~60 % of RAM, a
  host-safety backstop). If the static signal misjudges and CB overflows, CB fails
  cleanly (no host OOM) and the router falls back to the tableau when in-fragment,
  else reports `cb-failed` — never a wrong answer.

Calibration / validation:
- On all 40 ORE-sample ontologies `live = 0` — **every** real CB time-out is
  *size*-bound (e.g. 1012 at 1.8 M clauses, 10248 at 67 k concepts), not
  disjunction-bound, so the router keeps them on CB (the tableau is slower per step
  and times out *worse* — confirmed: 12 of them are TABLEAU-TIMEOUT). This corrects
  the earlier note that called 10248/10125/10161 "the tableau's job": they are
  size-bound and CB's scaling (semi-naive + parallel, the M1 work) is their fix,
  not the tableau.
- The `live` signal scores the doc's `∀r.(C⊔C')` stress at `live=20` while every
  CB-fast disjunctive ORE ontology (10006, 10019, 10123, 10140) scores `live≤1`.
- Router verdicts MATCH HermiT on all 18 committed fixtures (mixed CB/tableau
  routing; without the inverse/nominal routing, 3 would be wrong — CB-incomplete)
  and on 9 real ORE ontologies routed to CB (10056=1067 … 10146=8813 subs, exact).
  The synthetic live-disjunction stress routes to the tableau and finishes in 0.1 s
  matching HermiT. NB: the *current* CB engine (post semi-naive + audit fixes) is
  far more robust to disjunction than the old M1 measurements — it now handles most
  `∀+⊔` synthetic patterns in well under a second; the routing + memory cap are the
  safety net for the adversarial residue, while CB's genuine remaining wall is
  size, not disjunction.

### Perf status (2026-06-08): heap profile + trail-based backtracking

Heap-profiled the tableau (dhat, behind the `dhat-heap` Cargo feature; harness +
numbers in `engine/prof/`) on a live-disjunction stress with clash traps (forces
backtracking). Two hotspots:

1. **Peak memory** was 92% `Graph::clone` — the per-branch whole-graph copy in
   `expand`. **Fixed:** `expand` now mutates one graph in place and backtracks via
   a trail of reversible undo records (`Undo` / `MergeUndo`, `Graph::checkpoint` /
   `rollback_to` in `tableau.rs`); each branch alternative checkpoints, applies its
   edit, recurses, and rolls back on failure. `present_lits`/`present_roles` are
   left as a monotone over-approximation (not rolled back) — sound, since they only
   gate the cheap `matchable` pre-filter. The intricate case is undoing a `merge`
   (concept/exobl/edge moves + pred rewrites + union-find), recorded with a
   fresh-bit per moved item so undo removes exactly what the merge created.
   Result: **peak 268 MB -> 0.98 MB (274x)** on the K=12/P=8 stress, identical
   verdicts, 16/16 oracle fixtures still MATCH HermiT. The tableau is not
   Lean-certified (the Lean cert covers the CB ContextCalculus), so this was
   re-validated against HermiT, not re-proved.
2. **Allocation churn / runtime** is ~80% `Tableau::match_rec`: `Subst =
   HashMap<Var,Node>` for 1–3-variable maps + `match_body` materialising
   `Vec<Subst>` with a clone per solution. **Fixed:** `Subst` is now an inline
   `SmallVec<[(Var,Node);4]>` newtype (allocation-free `clone` for the 1–4-variable
   common case), and `match_rec` is an early-exit visitor so `find_disjunctive`
   stops at the first usable match. Result: **18.5 M -> 1.77 M allocations (10.5x),
   ~2.3x faster** (malloc/free *call count*, not byte volume, was the CPU cost),
   identical verdicts, 16/16 oracle fixtures MATCH. The residual churn is
   `horn_saturate` snapshotting each clause's solution set before it mutates the
   graph (a Role-body clause iterates `g.edges` while the head would mutate it, so
   it cannot apply during the match) — a deeper restructure for another day.

Combined, the two fixes take the tableau from the clone+HashMap baseline to
**peak memory 300x lower, allocations 10x fewer, ~2.3x faster**, verdicts
unchanged.

3. **Edge adjacency index (2026-06-08).** The matcher and the ∃-rules scanned all
   edges / all nodes (`match_rec`'s Role case, the `∃`-satisfied checks,
   `edge_label`). Added `Graph::out_edges` (a `Vec<Vec<(R,Node)>>` mirroring
   `edges`, maintained through `raw_edge_insert` / `raw_edge_remove` so it stays
   consistent under `merge` and rollback), turning those O(E)/O(N) scans into
   O(deg). The win grows with size: stress K=14/P=10 10.3 s -> 7.2 s (~30%), and
   K=16/P=12 (which timed out at 60 s on the clone baseline) now finishes in ~18 s.
   Verdicts identical, 16/16 oracle MATCH.

4. **Incremental (semi-naive) saturation (2026-06-08).** A KM_TAB_STATS counter
   showed the non-careful path was *saturation*-bound, not backtrack-bound: the
   ∀+⊔ stress did ~1170 `expand` calls with only ~90 backtracks, each call
   re-deriving the whole Horn closure from scratch even though it only adds one
   disjunct on top of an already-saturated parent. The non-careful path now drives
   saturation from a worklist of newly-derived facts (`expand_inc` / `saturate_inc`
   / `horn_inc`), firing only the clauses each fact can trigger (a body index
   `lit_index` / `role_index` / `node_triggered` built in `Tableau::new`) and
   binding the triggering variable so the matcher need not rescan all nodes. It
   reuses `match_rec` via a seeded substitution and collects head facts to apply
   after the match (the matcher holds `g` immutably). The ∃/blocking round stays
   batched. Result: stress K=14/P=10 7.2 s -> 0.93 s (~8x on top of the edge
   index, ~18x vs the original clone baseline); K=16/P=12 18.5 s -> 2.5 s. The
   careful path (merges/inverse/number/nominal) keeps the batch `saturate`.
   Verdicts identical, 22+16 tests pass, 16/16 oracle MATCH.

The `KM_TAB_STATS` env var prints per-`find_model` search stats (expands /
branch-tries / backtracks / nodes) to stderr; it also showed that *backjumping*
helps a different regime — a disjunction whose clash is decided far below the
relevant decision (a distant-clash instance did 33k tries / 99% backtracks).

5. **Dependency-directed backjumping (2026-06-08).** Each derived fact on the
   non-careful path now carries a `DepSet`: the set of disjunction decision
   *levels* it depends on (Horn heads inherit the union of their body's deps; a
   disjunct chosen at level `L` adds `{L}`; ∃ successors inherit the obligation's
   deps; a clash's conflict is the union of the two facts' deps). Stored in
   `Graph::cdep` / `edep` / `xdep`, rolled back with their facts. `expand_inc`
   returns `Outcome::Sat | Conflict(DepSet)`: when a disjunct's subtree clashes
   with a conflict that does not mention the current decision level, the choice is
   irrelevant — the whole disjunction is abandoned and the conflict propagates up,
   skipping untried siblings and any irrelevant intervening decisions. The
   distant-clash instance drops from **33,053 tries / 32,797 backtracks to 309 /
   53** (exponential → ~linear in k); the ∀+⊔ stress is unchanged (dep sets stay
   tiny — structural facts depend on nothing). Sound: 22+16 tests, 16/16 oracle,
   and 160/160 random disjunctive ontologies MATCH HermiT. The careful path keeps
   chronological backtracking.

6. **Told-subsumer classification pruning (2026-06-08).** A CB-style hybrid, but
   internal: `classify` builds one model `M_A` and reads each named subsumer `B`
   in its root. With dependency tracking, a root subsumer derived with an *empty*
   dependency set was derived deterministically (no disjunction choice), so it
   holds in every model of `A` and `A ⊑ B` is definite — recorded with no
   `{A, ¬B}` confirmation test (each test is a full model build). Only
   choice-dependent candidates are confirmed. On a 50-concept Horn chain with
   sprinkled disjunctions this classified all 1225 subsumptions with 0
   confirmation tests. Verdicts unchanged (16/16 oracle + 160/160 random MATCH).
   This realises CB's told-subsumer pruning from the tableau's own deterministic
   derivations, with no router plumbing and no CB-explosion risk; the careful path
   (no dependency tracking) confirms every candidate as before.

### Original M1 description

- **M1 (now): standalone ALC hypertableau consistency checker in Rust.**
  Fragment: `ALC` + role hierarchy + inverse + transitive (covers the stress test
  and 541; defer number restrictions >1 and nominals → no ≤/NI-rule, simpler
  blocking). Own completion-graph + Hyp + ≥(∃) + clash + pairwise blocking + DFS
  backtracking. Input: HT-clauses as JSON from a moose emit mode (reuse the OWL
  parser/NNF). Driver: consistency + classification (told-subsumer + per-pair
  `A⊓¬B` sat). GOAL: terminate fast on stress + 541 where CB times out; validate
  verdicts vs HermiT on a sample. NO Lean yet (standalone, HermiT-validated).
- **M1b: inverse roles + transitive + role hierarchy.** Needed for `ore_ont_541`
  (SRIF). Changes from M1:
  - *Edges bidirectional*: store `R(s,t)`; an inverse-role body/head atom `R⁻(s,t)`
    matches/asserts `R(t,s)`. The converter must preserve inverse roles (moose
    encodes them; M1 converter currently passes role atoms verbatim — extend with an
    `inv` flag on role atoms and `≥1 R⁻.B` exists atoms generating *predecessor*
    nodes is NOT needed, but ∀R⁻ and role atoms on inverses are).
  - *Pairwise (anywhere) blocking replaces subset blocking*: with inverse roles a
    blocked node's predecessor edge matters, so block `s` by `t` only when
    `L(s)=L(t)`, `L(pred(s))=L(pred(t))`, and both edge directions between node and
    predecessor match (msh09 Def 7). Subset blocking is unsound with inverses.
  - *Transitivity* is handled by the msh09 Ω-encoding already done in moose
    normalisation (∀R.C ⊑ ∀S.∀S.C axioms for transitive sub-roles S), so the tableau
    needs no transitive-edge rule — it is pure ∀-propagation via clauses. Verify the
    moose output carries these.
  - *Role hierarchy* `R ⊑ S`: clause `R(x,y) → S(x,y)`, already HT form.
  Validate on `ore_ont_541` (must finish where CB times out) + ORE SI/SH/SHI sample
  vs HermiT.
- **M2: number restrictions + nominals.** Add ≤-rule (eq-disjunction merging),
  NN/NI-rule, annotated equalities, full pairwise blocking. Re-validate vs HermiT
  on the full ORE DL+EL set.
- **M3: hybrid integration.** Wire the tableau as KM's per-context fallback with
  the liveness threshold and the SAT/UNSAT feedback clauses; per-context caching.
  Pay-as-you-go: Horn ontologies unchanged.
- **M4: certification.** Soundness per-run certificate for the tableau verdict
  (clash-core ⇒ unsat is checkable); Lean completeness scaffold for the tableau
  calculus, mirroring the existing CB completeness work.

Discipline (standing): never silently approximate (report unsupported); soundness
per-run certified; completeness validated via HermiT oracle + (later) Lean; never
commit sorries.
