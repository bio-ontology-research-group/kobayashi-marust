# Changelog

All notable changes to the kobayashi-marust reasoner. Newest first.

## [unreleased] — CB engine scaling (ORE 2015 coverage push)

### Parallel-speed work: dynamic query scheduler (landed) + the parallelism ceiling

Speed push aimed at the timeout tail, learning from Konclude (whose two main
speed sources are aggressive parallelism + lazy tableau-with-caching for
nondeterminism). Findings, with a thread-scaling probe (job 6227, node005,
KM_THREADS ∈ {1,8,16}, 480 s / 220 GB) partitioning the failures by family:

**Lever 1 — dynamic work-stealing query scheduler (LANDED, `7bc8611`).**
The old parallel path split the named concepts into `threads` static
contiguous chunks, one fixed engine each; when the hard query concepts cluster
in the named ordering they land in one chunk and serialise the whole run
(measured on ore_ont_12141). Replaced with `threads` long-lived engines
draining a shared atomic cursor in guided-size grabs (large early for low
contention + intra-engine cross-query context sharing, shrinking to 1 at the
tail), so a finished worker steals the next. Pure scheduling change — each
engine is independent and a query's subsumers don't depend on co-classified
queries (run_for contract), so the partition-independent union is confluent:
no Lean re-cert. `KM_STATIC_SCHED` restores the old path for A/B. Validated:
66+16 cargo tests; subsumptions byte-identical across KM_THREADS=1 / dynamic-8
/ static-8 on 8 onts (16461, 16076, 7270, 7482, 10019, 8169, 13018, 9635).
Also split `apply_pred` into `pred_payload` (reads only the immutable sender)
+ `apply_pred_payload` (mutates only the target) — output-neutral, isolates
the one sender/target aliasing read as a precondition for a future parallel
message-apply phase.

**Lever 2 — intra-saturation parallelism: scoped, then shelved as low-ROI.**
Konclude parallelises the saturation itself; KM only parallelises *across
queries*. The missing piece (concurrent context saturation) is the only lever
for "one giant saturation" onts that query-parallelism can't split. But two
facts make it a poor investment under the real benchmark limits (240 s, 20 GB):

- *Cost:* the saturation core touches the shared arena + intern tables
  directly across ~70 sites (only 6 are the `&[ContextClause]` slice
  signatures; the rest are `saturate`/`add_clause`/`hyper`/`intern_cc`/
  `cc_find` reaching `self.cc_arena` directly). True parallel saturation means
  parameterising that whole core over an arena+intern abstraction (each worker
  sees committed-global ++ its-own-new clauses) or a locked concurrent context
  graph — a multi-session, Lean-adjacent refactor needing iterative validation.
- *Payoff (probe 6227 + memory facts):* the speed-recoverable set is ~1 ont.
  - 12141 + the disjunction family: timeout at 1/8/16 threads, and 8/16
    threads **explode to ~204 GB** — parallelism-resistant *and*
    memory-explosive; needs the algorithmic lever (ordered resolution /
    tableau / BCP), not threads.
  - 16444 (59 GB) and 9724/GALEN (27 GB): both **over the 20 GB memcap**, so
    they are memouts regardless of speed.
  - 16303: th=1 and th=16 both timeout at an **identical 4.93 GB peak** — the
    textbook family-B signature (query-parallelism completely inert; one giant
    saturation). The lone genuine intra-saturation target: fits the memcap but
    needs ~8–10× scaling to clear 240 s.

  Conclusion: bank Lever 1; **shelve Lever 2** (multi-session core refactor,
  memory-neutral, reaches ~1 ont); the productive next lever is the
  disjunction family's algorithmic fix (the largest timeout group, provably
  out of parallelism's reach).

**Lever 2 — built anyway (`KM_PAR_SAT`, default OFF), confirmed inert.**
Branch `lever2-parsat`, commit `fb117df`. The core was parameterised over an
arena+intern abstraction (`ArenaView{Whole,Split}`, `Interner{Global,Local}`,
`Sat<'a>` bundling the saturation state, `with_sat` disjoint-borrow helper) —
an output-neutral refactor (8/8 onts byte-identical, 66+16 tests). On top of
it, `apply_batch_parallel` parallelises the inter-context message fixpoint:
when a batch carries >1 messages to distinct contexts and the ontology is
nominal-free (`nom_k==0`) and individual-free (`ground_ctx` is `None`), the
target contexts are moved out and saturated concurrently via rayon, each worker
writing into a thread-local clause overlay (a `Split` arena view = read-only
global base ++ local new clauses), followed by a serial merge that interns the
local clauses into the global arena and remaps their ids
(`Context::remap_local_ids`). Correct: 8/8 byte-identical to serial and it
converges (16076: `parallel_batches=2 parallel_ops=10 exit=0`).

But it delivers no speedup, for a structural reason: **the message fixpoint is
near-sequential.** Across probed onts the parallel batches are size 0–2 (≤10
ops total per ontology) — there is essentially no simultaneous message fan-out
to exploit. The eligible family-B onts are also unreachable by it: 16303 is
ABox-bearing (185 individuals → `ground_ctx` is `Some` → ineligible), and 6682
is query-bound rather than saturation-bound (110,717 queries — the lever for it
is Lever 1, which `KM_PAR_SAT` *disables*, since engine-level `par_iter` nested
under the reasoner-level query rayon scope deadlocks; hence the usage rule
`KM_PAR_SAT` ⟹ `KM_THREADS=1`). The build is kept gated-off for any future
ontology that exhibits wide message fan-out. This empirically confirms the
shelve call above.

### Sweep 6016: the first fully clean correctness table (datatypes included)

Full sweep with the datatype layer + chain-domain default + Phase-2 engine
(binaries `ofn-dt` / `kobayashi-marust-p2`): **545 ok / 45 timeout /
1 memout; vs Konclude gold 545 agree / 0 incomplete / 0 unsound /
0 both-disagree** — every completed ontology byte-equal to gold, with no
exclusions (ore_ont_6999's datatype gap closed). Zero status regressions vs
sweep 5976 and two recoveries (ore_ont_2397, ore_ont_8737 timeout → ok), so
the new clauses cost nothing net. The 3524 giant's stdout-runaway recurred
mid-sweep and is now fixed at the root (`KM_EMIT_CLAUSES` gating below).

### Nominal-mode r-Pred announcement guard (10594 livelock fix)

The Phase-2 per-source r-Pred path let body-empty ground clauses pass the
body-discharge check vacuously, spraying every ground fact to every context
with a root edge (ore_ont_10594, ~1900 individuals: 3.5M+ Pred messages,
ok → timeout under `KM_NOMINALS`). Restored the announcement guard (an edge
per mentioned individual) with additional nominals (id ≥ `nom_base`) exempt —
they are exactly what Nom conclusions carry and what no context can have
announced. 10594: timeout → 192 s, now faster than the Phase-1 engine on the
same host with identical published output.

### Datatypes: data-property axioms + a concrete-domain oracle

Closes the datatype gap (the last incomplete-vs-gold ontology): ore_ont_6999
is now byte-equal to gold — `Distortion_Type_Affine ⊑ =2 affc2` with
`Functional(affc2)` is correctly unsatisfiable. Two layers, both frontend
(no calculus change, no Lean re-cert needed):

1. **Axiom translation** (`parse.rs`; previously every `Data*` axiom was
   dropped): functionality → role functionality, sub/equivalent/disjoint
   data properties → the role counterparts, ranges → `∀p.__dt__D`,
   `DatatypeDefinition` → concept equivalence. Unqualified data cardinalities
   now count ALL successors (`⊤` filler — the old `__dt__val` filler made
   `≤ n` blind to `DataHasValue` successors). Complex ranges are keyed by
   canonical text (one shared `__dt__opaque` could invent subsumptions
   between different facet restrictions) and typed literals are re-glued
   with their `^^datatype` / `@lang` suffix (the tokeniser splits them off,
   which collapsed same-lexical different-type values).
2. **Pairwise oracle** (`frontend/datatypes.rs`): for the `__dt__` concepts
   occurring in the clause set, decide — per the OWL 2 datatype map — value
   membership, value (in)equality (exact rationals across the decimal tower
   and dyadic float/double, strings, booleans), range subsumption and
   disjointness (integer-tower bounds, string-family tower, partition
   disjointness, interval separation), and finite covers (boolean, DataOneOf,
   small integer intervals): `__dt__D(x) → ⋁ __dt__val__vᵢ(x)`, which with
   value disjointness gives finite-range counting through the engine's
   ordinary equality reasoning. Every relation is emitted as a plain concept
   clause; unknown decisions emit nothing (the old sound abstraction).
   `KM_NO_DATATYPES` disables the oracle pass for A/B.

82 cargo tests pass (5 new oracle tests). Full-corpus validation sweep
pending; built and validated on unimatrix while ws was unreachable.

### Nominals Phase 2+3: Join, r-Succ (*), the Nom rule, and Lean certification

Completes the ALCHOIQ calculus implementation behind `KM_NOMINALS` (Table 3 of
arXiv:1805.01396; design + status in `docs/NOMINALS-CB.md`):

- **Nom** (additional nominals): in the ground context, a hyper-match with
  `σ(x) = o` whose head a-equalities instantiate to `y ≈ y` / `y ≈ f(o')` no
  longer drops them as tautologies (the exact O+I+Q incompleteness) but
  replaces them with `⋁_{k} y ≈ o'_k` over fresh interned additional nominals.
  The disjunction width is `K + K''` (`K + 1` = max neighbour-variable index,
  `K''` = distinct pinned `f(o')` terms): the certified covering bound is the
  sum, and the paper's bare-`K` statement is too narrow whenever `K'' > K`.
  Budgeted (`KM_NOM_BUDGET`, default 4096) with an explicit incompleteness
  warning on exhaustion. Two enabling fixes: the ground context's Hyper now
  considers the side clause at non-side body positions (given-clause
  semantics — provably redundant elsewhere, the Nom trigger here), and the
  symmetric-group strict pruning admits the equal-`y` assignment there.
- **Join**: in-context resolution on ground atoms (cases 1+2 via new
  ground-body/bridge indexes and a `pred_local` refire on ground maximal
  heads; case 3 = provider over `x` + an `x ≈ o` bridge, fired from all three
  arrival orders).
- **r-Succ condition (*)**: pushes are blocked when a subsuming-modulo-merge
  clause shows the element may itself be a nominal (defer to equality
  reasoning).
- **r-Pred pipeline**: per-atom multi-edge discharge (different `A_i` over
  different individual-labelled edges of one source), verbatim `C_i` copies,
  and no edge requirement for head individuals — the old head filter made
  every Nom conclusion undeliverable.
- **Lean (Phase 3)**: `lean/ContextCalculus/Nominals.lean` (sorry-free)
  certifies soundness of all four rules and the grounded substitutions;
  `nom_cover`/`nom_sound` prove the covering bound and the
  conservative-extension soundness of Nom (the interpretation of the fresh
  constants is constructed).
- `owl_classify._run_engine`: the stdin writer thread raced
  `communicate()`'s flush on fast engine exits (`ValueError: I/O operation on
  closed file`); `communicate(input=…)` now owns the write.

Validation: 61 + 16 cargo tests (4 new engine-level tests incl. the paper's
Example 3 and a no-counting negative control); all six pipeline probes match
HermiT (`nom1`, `nom2`, `nom_dl8`, `nom_neg1`, `nom_unsat`,
`nom_oiq_funct` — the last is Example 3 as OWL, the first KM result that
*requires* additional nominals). Inert without individuals: every new code
path is gated on the ground context / ground atoms, and without `KM_NOMINALS`
the reasoner drops individual clauses, so SRIQ-fragment output is unchanged.
60-ontology corpus A/B with this binary pending.

### Chain-domain recognition validated corpus-wide; now DEFAULT ON

Full sweep 5976 (`KM_CHAIN_DOMAIN=1`, all 591 gold-comparable ontologies):
**543 ok / 46 timeout / 2 memout; vs Konclude gold 542 agree / 0 unsound /
1 incomplete / 0 both-disagree.** The single incomplete is `ore_ont_6999`,
whose one missing subsumption (`Distortion_Type_Affine`) is the known
*datatype* gap (identical in the old config) — within SROIQ-minus-datatypes
the corpus is now **0 unsound, 0 incomplete vs gold**, the first fully clean
correctness table. `ore_ont_11745` confirmed fixed at full scale (ok,
unsat=1592, gold-equal).

Landing: the pass is now default-on (`KM_NO_CHAIN_DOMAIN` opts out for A/B
debugging), per the completeness mandate and the disjunction-ordering
precedent. Cost vs the 5941 baseline: `ore_ont_2313` and `ore_ont_8737`
(chain-heavy; 8737 ran ~206 s before) go ok → timeout — honest resource
limits, not silent approximation.

### Frontend: role-chain recognition for pure-domain consumers (`KM_CHAIN_DOMAIN`)

Recovers `ore_ont_11745`, the last unsound-vs-gold ontology: with the flag,
full 11745 is byte-identical to Konclude gold (438277 subsumptions, 1592
unsatisfiable classes, `GO_0008046` correctly unsatisfiable). It was a genuine
unsat under-detection (HermiT-confirmed; an 18-axiom witness reduced from a
STAR module), not the parallel-pipeline artifact earlier assumed.

Root cause: `chain_clauses` / `transitivity_clauses` run inside `augment`
(frontend pass 1) and recognise a chain `R∘S⊑T` only when a TBox consumer
carries a concept on the chain target. A *pure-domain* consumer
`T(x,y) → D(x)` (from `ObjectPropertyDomain(T, D)`) has no such concept and is
added only in pass 2, so the chain feeding a domain restriction was never
recognised. In 11745, `GO_0008046` is a molecular_function (a `SubClassOf`
chain) and, via a transitive `part_of` chain plus `part_of∘ricdo⊑ridpo` with
`domain(ridpo) = biological_process`, also a biological_process; the two are
disjoint, so the class is unsatisfiable. KM reached the chain filler
(`__trans__part_of__GO_0048856`) but never composed it with the domain
restriction, so it missed the clash and emitted the class's ordinary
superclasses (scored as unsound, though KM never derived anything false).

Fix (gated by `KM_CHAIN_DOMAIN` while validated corpus-wide; reordering the
passes is blocked by the `reg.short` name-assignment byte-identity invariant):
`augment` now also returns the detected `ChainInfo`, and after
`domain_range_clauses` are built, `domain_consumer_chain_clauses` emits the
missing recognitions for pure-domain consumers of chain targets — the
`__chain__S__` recognition (any `S`-edge) plus the `R`-composition, and when
`R` is transitive the full `__trans__` up-propagation so the chain composes
across `part_of` hops. Additive and sound (only fresh recognition clauses;
standard chain unfolding, no calculus change, no Lean re-cert): off-flag output
is byte-identical. Reproducers:
`oracle/ontologies/{11745_unsat_core,chain_domain_propagation}.ofn`. Tests:
`domain_consumer_chain_recognition`, `domain_consumer_transitive_chain_recognition`.

### Nominals: grounded CB reasoning (`KM_NOMINALS`, default off) — Phases 0+1

KM's prior nominal handling replaced `{o}` with a fresh concept proxy
`__nom__o` and lifted unconditional ABox facts; sound but incomplete whenever
the singleton property matters. Minimal witness (HermiT-confirmed,
`oracle/ontologies/nom_merge_sub.ofn`): `A ⊑ ∃r.({o}⊓B)`, `A ⊑ ∃r.({o}⊓C)`,
`B⊓C ⊑ E`, `∃r.E ⊑ G` entails `A ⊑ G`, which the proxy misses (the two
successors stay distinct). 60 of the 592 benchmarked ORE ontologies use
`ObjectOneOf`/`ObjectHasValue`.

Implements the ALCHOIQ consequence-based calculus (Tena Cucala, Cuenca Grau,
Horrocks, IJCAI 2018; arXiv:1805.01396) behind `KM_NOMINALS`, mapped in
`docs/NOMINALS-CB.md`. Phase 0 (frontend): under the flag, `augment` emits the
DL7/DL8 defining clauses `⊤ → __nom__o(o)` and `__nom__o(x) → x ≈ o` plus the
ground ABox clauses, and fences ontologies with individuals off the elc path;
off-flag the output is byte-identical. Phase 1 (engine):

- Term space re-encoded to `z < y < x < o_k < f(x) < f(o)` (individuals below
  the Skolem terms, `f(o)` composites packed positionally), a pure id-space
  relabeling validated byte-identical vs the prior binary on `ore_ont_16461`
  and the cardinality probes. The order satisfies Def 3 of the calculus given
  the existing predecessor-trigger-bottom refinement.
- One ground (nominal root) context `v_r` is the only place Hyper grounds the
  central variable (`σ(x) ∈ Σo`); it is created eagerly when ground facts
  exist and holds all ground inference. Ground ontology facts seed `v_r`
  fully and every other context on demand (first clause mentioning the
  individual).
- The Su^r forms (`B(o)`, `S(x,o)`, `S(o,x)`) push their y-form to `v_r` over
  individual-labelled edges (r-Succ); `v_r`'s ground conclusions flow back
  through the existing Pred machinery (r-Pred), with an edge-coverage
  discipline that kept a naive version from livelocking. `x ≈ o` crosses an
  `f` edge as `f(x) ≈ o`, which the receiver's Eq rule rewrites into ground
  atoms. A `v_r` empty clause is global inconsistency.

All five witness probes pass (HermiT-checked): `nom_merge_sub` and the DL8
merge derive the expected subsumption, the two-distinct-nominals negative
stays underivable, and `{o}⊑B, {o}⊑C, B⊓C⊑⊥` is reported inconsistent.
Off-flag and SRIQ-path output are unchanged (every new branch is unreachable
without individuals in the clause set). Known cost on the flagged path:
ABox-heavy ontologies slow down (`ore_ont_10594` 0.6 s → 85 s) — perf and the
remaining rules (Join, the r-Succ side condition, Nom) plus Lean
re-certification are future phases before the flag can default on.

### Frontend: AtMost recognition (`≤n r.F` on the LHS could never fire)

The mirror of the AtLeast gap below, found by inspection: the AtMost
clausification emitted only the constraint direction, so nothing could ever
derive the reified Q and `≤n r.F ⊑ G` was silently incomplete (not
exercised by ORE gold so far). Fix: excluded-middle recognition — fresh NQ
with `⊤ → Q ∨ NQ`, `Q ⊓ NQ ⊑ ⊥`, and NQ ⊑ ≥(n+1) r.F (n+1 witnesses with
pairwise inequalities); a context that refutes the witnesses derives Q.
Polarity-gated (the `⊤ → Q ∨ NQ` split fires in every context): emitted for
negative or unseen occurrences, skipped only when the pre-pass proves the
occurrence positive-only. Probes: `∀r.⊥ ⊢ ≤1 r.J` (vacuous) and
functionality ⊢ `≤2 r.J` (merge-derived) both derive G; negative probes
stay sound. In-corpus clause changes are confined to current timeouts
(10702, 1194, 14817). Test:
`frontend::normalise::tests::atmost_recognition_polarity_gated`.

### Frontend: ≥n recognition clause for n ≥ 2 (the 16461 min-cardinality gap)

The clausifier (`normalise.rs`, `Concept::AtLeast`) emitted the recognition
direction of a reified `Q ≡ ≥n r.F` only for n == 1 (the plain ∃-recognition
clause). For n ≥ 2 no clause could ever derive Q, so a qualified
min-cardinality on the LHS of a subsumption never fired: ore_ont_16461's
single missing subsumption, reproduced in a 21-clause probe (`P ⊑ ∃r.J1,
P ⊑ ∃r.J2, J1⊑J, J2⊑J, Disjoint(J1,J2), ≥2 r.J ⊑ G ⊬ P⊑G`).

Fix: emit the standard contrapositive clausification `¬Q ⊑ ≤(n-1) r.F`, i.e.
`r(x,y0) ∧ F(y0) ∧ ... ∧ r(x,y_{n-1}) ∧ F(y_{n-1}) → Q(x) ∨ ⋁_{i<j} yi≈yj` —
the same clause shape the AtMost branch already produces and the engine's
Hyper + Eq/Factor machinery already reasons over (multi-neighbour-variable
bodies, equality heads). No calculus change, no Lean re-cert: only the input
clause set is completed; the emitted clause is the definitional-extension
direction of the reified Q and is logically equivalent to `≥n r.F ⊑ Q`.
(n == 0 falls out correctly as `→ Q(x)`, since `≥0 r.F ≡ ⊤`.)

The probe now derives P ⊑ G. Frontend output is byte-identical on
ontologies without min/exact-cardinality ≥ 2 (checked on 10); 27 corpus
ontologies are affected and were re-validated against gold. New tests:
`reasoner::tests::min_cardinality_recognition` (engine-level, the probe) and
`frontend::normalise::tests::atleast_two_recognition_clause`.

**Polarity gating**: the recognition clause is pure cost when the `≥n`
occurs only positively (RHS — intro direction suffices), and on
existential-rich ontologies it feeds the live-disjunction blow-up (a single
unqualified `≥5 setting-for` recognition clause on ore_ont_15672/DOLCE
doubles the pipeline wall time: the resolvent residues create new Hyper
providers, mutually incomparable under subsumption). The pre-pass
(`mark_polarity`) now records each AtLeast's polarities; recognition is
emitted unless the concept is PROVEN positive-only (negative or unseen ⇒
emit, so coverage gaps keep the complete behaviour). Even gated,
ore_ont_15672's genuinely-negative `≥5` (an EquivalentClasses conjunct)
keeps its recognition clause and the ontology joins the live-disjunction
timeout family — recovering it is the ordered-resolution workstream, not a
cardinality issue. Test:
`frontend::normalise::tests::atleast_recognition_polarity_gated`.

### Engine: symmetric-group pruning in the Hyper join

The recognition/at-most clause shape is fully symmetric in its neighbour
variables, so the backtracking join enumerated every permutation (and every
equal-term repeat) of each candidate combination — `k^n` assignments where
`C(k,n)` are distinct, ruinous for n ≥ 4. `OntologyClause` now precomputes
its exchange-invariant variable groups (pairwise swap-invariance,
union-find; transpositions of a connected component generate its full
symmetric group), flagging groups whose head carries an equality for every
pair. The join prunes assignments whose group terms are not sorted (strictly
sorted for flagged groups: an equal-term assignment makes some head equality
`t≈t`, a tautology `build_hyper_resolvent` drops). Side-clause variables are
exempt (the side clause is pinned to its body position and not
interchangeable with worked-off candidates). Output-preserving: every pruned
assignment is a permutation of a kept one and yields the identical canonical
resolvent (heads/bodies are sorted and deduped; `Lit::eq` normalises
orientation), so the derived set is unchanged — no Lean re-cert.

### Engine: central-strategy successor cores must hold facts only

With the recognition clause in place, n = 2 worked but n ≥ 3 still stalled
(probe: P with 3 pairwise-disjoint r-successors, `≥3 r.J ⊑ G` ⊬ P ⊑ G; the
real ore_ont_16461 needs n = 4). Trace: P's context correctly derives
`⊤ → A2(f1) | A3(f1) | Q` by paramodulation, but the central strategy had
pushed the disjunctively derived triggers A2(f1), A3(f1) into the successor
CORE alongside the fact A1(f1). The `[A1,A2,A3]`-core context derives ⊥, and
apply_pred conditions the push-back on the whole core — a clause
`A1(f1) ∧ A2(f1) ∧ A3(f1) → ⊥` that would have to cut TWO literals of the
same disjunction at once, which no resolution step can do. The per-disjunct
refutations (`A1 ∧ A2 → ⊥`, `A1 ∧ A3 → ⊥`) were unavailable because the
hypothesis clauses `p → p` added by apply_succ were subsumed by the
over-large core's `⊤ → p`. The legacy non-central strategy (empty cores,
pure hypotheses) does not have the bug — KM_NO_CENTRAL=1 derives G on every
probe, confirming the diagnosis.

Fix: a successor core now contains only the σ-image of FACT triggers (unit
clauses `⊤ → p(f)` in the predecessor); disjunctively or conditionally
derived triggers still travel as Succ messages (edge bookkeeping +
hypothesis `p → p` at the target) but stay out of the core, so their
consequences return conditioned on `p` alone and each disjunct is cut
individually. Context identity (`central_successor_for_core`) keys on the
fact core; hypothesis-only trigger growth keeps the same target and sends
just the new triggers. No calculus-rule change (Hyper/Pred/Succ/Eq schemata
untouched, no Lean re-cert, same category as the central-strategy landing):
cores shrink, so the context invariant (core ∧ body → head entailed) is
preserved, and every previously derived consequence is still derived — the
fact-trigger cores reproduce the old behaviour exactly on ontologies where
all succ triggers are facts (the common case: existential successors).
New test: `reasoner::tests::min_cardinality_recognition_three_witnesses`.
With both fixes the full ore_ont_16461 derives the gold-only subsumption
`Patient1 ⊑ Systemic_JIA_Patient` (≥4 hasAffectedJoint.Joint over 5
pairwise-disjoint joint successors).

### Engine: clause interning (Pred pipeline + global arena) — peak RSS −77%

KM_MEMSTATS accounting (new, diagnostics-only) on ore_ont_9944 at fixpoint
showed each derived clause stored 5+ times across the engine: per-context
`neighbor_pred` copies of back-substituted pred clauses (11.4M instances,
2.06 GB — only 388k distinct, 29x duplication), a full clause copy per
(edge, clause) in `pushed_pred`, full copies in `pred_pool`/`succ_pool` and
`clause_keys`, the `max_head` duplicate, and `Msg::Pred` carrying a cloned
neighbour core + clause per queued message (13.8M messages). On top of that,
the seeded shared closure was cloned into every context (8009 root contexts).

Two interning stages, both representation/sharing only (the derived clause
set is unchanged, so no Lean re-certification — skipping a duplicate Pred
arrival only skips re-deriving clauses `add_clause` would dedup anyway):

1. **Pred pipeline** (`228067f`): engine-level `pred_interned` table;
   contexts hold u32 ids and `neighbor_pred_seen` dedups duplicate arrivals
   (real, from a successor's pre-/post-growth contexts under the central
   strategy). `pushed_pred` keys by (edge → `pred_pool` index). `Msg::Pred`
   carries `{to, from, edge_label, pool_idx}` (24 B, no heap); the sender's
   pool entry and core are immutable, so apply-time resolution reads exactly
   the send-time snapshot. 9944: 8.50 → 4.99 GB, wall 2:58 → 2:26.

2. **Global clause arena**: `cc_arena: [Vec<ContextClause>; 2]`, content-
   interned, split by ordering domain (root / non-root — the same
   (body, head) caches a different `max_head` under the two orderings, so
   the domains are never crossed). `worked_off`/`todo`/pools become Vec of
   u32 arena ids; `clause_keys` becomes HashSet of the id (the id IS the
   content key); head indexes store ids; the shared closures seed ids
   instead of cloning clauses per context. 6.08M worked-off instances
   collapse to 193k distinct (31x). 9944: 8.50 → **1.99 GB peak (−77%)**,
   wall 2:58 → **1:56 (−35%)**, output identical (315,940 subsumptions,
   exact set match). 49+16 cargo tests pass.

This is the lever for the 9724 (GALEN) memout, which churns >82 GB
unconverged on the old representation.

### Engine: complete disjunctive case analysis (same-term literals incomparable)

The context literal ordering (`calc.rs pred_lteq`) imposed a total order on
same-term concept literals (iri id + internal-definer-low), applying the
mutually-incomparable refinement only in root contexts. That total order is
incomplete for disjunctive consequence finding: once a disjunct stops being
maximal it is never resolved, so a head disjunction never fully case-splits.
Minimal probe (CB engine): `A ⊑ ∃R.(C⊔D), C⊑E, D⊑E, ∃R.E⊑G ⊬ A⊑G` (the engine
derives `C(f)|Q_2(x)` and stalls). This is the root cause of the incomplete
disjunctive ORE ontologies (12698's `∃`-filler disjunction + transitive role).

Fix: concept literals on the same term are mutually incomparable in every
context, so Hyper fires on every disjunct and the case split completes. This
matches the Lean completeness proof, which models Hyper as resolution on an
arbitrary atom (`CompletenessProp.lean`) with no ordering assumption -- the total
order was never part of the certified calculus. Sound by construction (ordered
resolution is sound for any selection). Validated on probes + ORE 2313 / 12698
minimal cores; 65 tests green; Horn (single-head) reasoning is unaffected.

TRADEOFF (sweep 5814): genuinely-disjunctive ontologies now explore all branches,
which is heavy (12698 ~16-19 GB). About 10 ontologies regress ok→timeout/memout.
This is fundamental -- completeness on disjunctive inputs requires full case
analysis -- and is recoverable only by performance work (stronger redundancy on
disjunctive clauses, or decoupling Hyper-maximality from Succ-trigger selection),
not by weakening the ordering. `KM_DUMP_WO=1` dumps every context's worked-off
clauses (debug, env-gated). `KM_NO_PRUNE=1` disables inert inverse/role-bridge
pruning (diagnostic; pruning is sound -- disabling it does not recover the
remaining inverse-role / GALEN incompleteness, which is a separate engine gap).

### Frontend: handle EquivalentObjectProperties (was silently dropped)

`EquivalentObjectProperties(R1 … Rn)` had no parse arm in either the AST path
(`parse.rs`) or the streaming RBox builder (`rbox.rs` `rbox_node`), so role
equivalences were dropped. Every inference that bridges two equivalent roles was
lost. Minimal witness extracted from ORE `ore_ont_2313` (`ddmin`, oracle =
HermiT entails `C ⊑ D`), a 3-axiom core:

```
SubClassOf(TO_0000059, ObjectSomeValuesFrom(BFO_0000050, TO_0000056))
EquivalentObjectProperties(BFO_0000050, PPIO_0000091)
ObjectPropertyDomain(PPIO_0000091, PPIO_0000069)
⟹ TO_0000059 ⊑ PPIO_0000069
```

The existential uses `BFO_0000050`; the domain is stated on the equivalent
`PPIO_0000091`. Without the equivalence the two roles never connect, so the
domain never fires on the existential's Skolem edge. `2313` was missing 88 such
subsumptions.

Fix: expand `R1 ≡ … ≡ Rn` into pairwise both-direction inclusions. `parse.rs`
emits the AST `RoleInclusion`s (so `normalise` produces the subrole clauses that
reach the reasoner); `rbox_node` emits matching `Subrole` records (routing /
relevance / domain-range). Any inverse member fences the axiom to the CB engine.
`2313` now matches gold exactly (88 missing → 0, 0 extra). 57 ORE onts contain
the axiom; the change is sound (role equivalence = mutual inclusion) and can only
recover entailed subsumptions. Tests green.

### Correctness tail: sound datatype-ABox precheck + complex-domain clausification

Resolved the four "unsound vs gold" ontologies and recovered one incomplete one.
The headline result is that KM was never unsound on the four flagged ontologies:
they are all genuinely **inconsistent**, and the gold signatures were wrong.

**Proof the gold was wrong.** Delta-debugging (`ddmin` over the axioms, oracle =
HermiT-reports-inconsistent) reduced each of `8941` / `13912` / `15516` / `2669`
to a 2–8 axiom inconsistent core. Running those cores through HermiT *and*
Konclude directly, both reasoners report inconsistent (Konclude prints
`EquivalentClasses(Thing Nothing ...)`). The recorded gold said "consistent"
because of two benchmark-harness bugs, both fixed:
- `ore_canon.py` canonicalised Konclude's `Thing ≡ Nothing` (its encoding of an
  inconsistent ontology) into "consistent with N unsatisfiable classes". It now
  maps `owl:Thing` in the `owl:Nothing` SCC — and any `consistent=false` — to the
  uniform empty inconsistent signature.
- `ore_runone.py` recorded Konclude's exit-0-with-empty-output on a SWRL
  `DLSafeRule` parse failure (`15516` / `2669`) as a bogus "consistent". It now
  flags Konclude "All parsers failed" as `error` (excluded from comparison).
The gold was regenerated for every affected ontology.

**KM side (`frontend/data_abox.rs`).** The CB engine drops the ABox, so these
asserted-data clashes never reached saturation. A new sound precheck detects:
- range-vs-literal clash: a `DataPropertyAssertion` whose literal value-space is
  disjoint from a (possibly sub-property-inherited) `DataPropertyRange`
  (`8941`: `xsd:string` range carrying a language-tagged literal — an
  `rdf:PlainLiteral`, never in the string value space);
- functional-data clash: `FunctionalDataProperty` with two provably-distinct
  values on one individual;
- an at-most-1-driven ground individual merge (closing role assertions under
  symmetry / inverse / sub-roles and domain/range typing) feeding a
  `DataMax`/functional clash or a `DifferentIndividuals` violation (`13912`:
  symmetric `Owner` + domain `Photo` + `Photo ⊑ =1 Owner` merges two photos,
  then `Photo ⊑ ≤1 url` clashes their distinct urls);
plus an asserted-member-of-unsatisfiable-class rule (`asserted_classes` on the
ofn meta; `owl_classify` makes the ontology inconsistent when a class proved
unsatisfiable has a provable asserted member). Every clash is an OWL 2
entailment; caps degrade to "not detected" (incomplete, never unsound).

**Incompleteness.** `parse.rs` now clausifies a COMPLEX
`ObjectPropertyDomain`/`Range` on a named role as the equivalent class axiom
(`∃R.⊤ ⊑ C` / `⊤ ⊑ ∀R.C`) instead of dropping it as `complex-domain`. The
named-class case stays on the rbox path (byte-identical). Recovers `ore_ont_4827`
exactly (the olia `domain(hasCase) = Adjective ⊔ ...` chain via `∃hasCase.Self`).

**Validation.** 19 new `data_abox` unit tests; full suite green. Whole-corpus
frontend differential: clause + meta output byte-identical on every ontology
except those newly flagged inconsistent; all newly-inconsistent ontologies
confirmed inconsistent by HermiT/Konclude (zero false positives). Remaining
incomplete onts are deeper engine gaps: `16461` (1 nominal subsumption, CB drops
individuals); `2313` / `12698` / `9944` (existential-superclass `∃R.C`
propagation).

### EL completion: clone-free hot loop (recovers giant ore_ont_8737)

The `elcomplete` worklist saturation cloned a state collection on every
Sub/Edge item to satisfy the borrow checker. On the transitive ORE giants this
dominated: transitivity is encoded as NF4, so the existential rules fire on
huge predecessor and superclass sets, and each firing paid a full-set clone.
Three changes remove the per-item allocations:

- `in_edges` is `Vec<Vec<(parent,role)>>` instead of `Vec<HashSet<...>>` — a
  pair is appended only in the `edges[parent].insert` success branch, so
  duplicates were already impossible and the set bought nothing. The Sub-side
  NF4 rule and ⊥-edge back-propagation iterate it by index (new entries pushed
  during the loop are picked up by the growing bound), clone-free.
- The Edge-side NF4 rule collects conclusions into a reused `nf4_buf` during a
  read-only scan of `sub_super[d]`, then applies them (replaces a full-superset
  clone per edge).
- NF4/NF7 rule blocks are skipped outright when their indexes are empty.

Schedule-only change: the same conclusions are derived, possibly in a different
order; the fixpoint is unchanged (saturation is monotone + confluent), so no
Lean re-cert. Validated: 53 unit tests; gold-identical signatures on controls
16744 / 10016 / 1559 / 13482.

Effect: `ore_ont_8737` classify 252 → 221 s standalone; in the benchmark
pipeline it went **timeout → ok at 205.7 s** (9.5 GB peak), signature
byte-identical to the Konclude gold. `ore_ont_16744` pipeline 167 → 151 s.

**Full-sweep confirmation (job 5690): 564 ok / 26 timeout / 1 memout**, vs
gold 554 agree / 6 incomplete / 4 unsound / 0 both-disagree — agree +1 (the
recovered 8737), no regression anywhere. All three 3M-axiom giants (8737,
15059, 16744) now classify within budget via the EL path.

### EL fast path: optional canonical-model completeness certificate (`elc`)

`elcomplete::to_nf` no longer aborts on the first non-EL clause: it collects the
non-EL clauses into a *residual* and still saturates the EL subset. With
`KM_ELC_CERT=1`, `classify` then checks every residual clause against the
saturated **canonical model** (domain = satisfiable concept nodes; `x_C ∈ D^I`
iff `C ⊑ D` derived; `(x_C,x_D) ∈ R^I` iff edge `(C,R,D)` derived). If all hold,
`I ⊨ O` for the full ontology, so the EL classification is exact (sound AND
complete) for subsumption, unsatisfiability, and consistency; any failure (or a
work-budget overrun) returns `None` and the caller falls back to the CB engine.
Never an approximation. 7 unit tests; the certificate logic is a calculus-logic
addition and needs Lean certification of the canonical-model lemma (deferred).

**Default OFF.** On ORE 2015 every non-EL residual is a live covering
disjunction (`⊤ → A ⊔ B`), a non-inert inverse bridge, or multi-successor
functionality — none of which the canonical EL model satisfies — so the
certificate never passes there (verified: fails at residual clause 0 on
4205/6212/15803/7127/7246/11311), and attempting it would saturate the large EL
subset before failing, stealing time from the CB fallback. With the flag off,
routing is byte-identical to before (`to_nf` returns a non-empty residual ⇒
`classify` returns `None` ⇒ same exit-3 fallback). The capability is for
near-EL ontologies whose non-EL part IS model-satisfiable.

Also in `elc.rs`: read stdin as raw bytes + `serde_json::from_slice` (skips the
whole-buffer UTF-8 validation and a second allocation; lower peak memory), and
`KM_ELC_TIMING=1` per-stage timing. The timing showed the ORE giant
`ore_ont_8737` is **saturation-bound** (read 0.5 s, parse 8 s, classify 252 s,
serialise 2.8 s) — its 240 s timeout is the EL completion itself, not I/O, so it
needs a faster (parallel, ELK-style) completion, not an I/O fix. `ore_ont_16744`
classify is 83 s.

Goal: close the remaining ORE 2015 coverage gap to Konclude (was 551/590 ok;
40 failures = 21 timeout + 19 memout). Diagnosis, fixes, and benchmark deltas
tracked here.

### Frontend (`ofn`): inverse-role bridge clauses (8+ incomplete → agree)

`InverseObjectProperties(R, S)` was parsed into `hooks.role_inverses` — which no
code consumed — and `ObjectInverseOf(R)` in concepts became a fresh role
`__inv__R` with no clause linking it to `R`. The engine has no inverse machinery
of its own, so inverse-role semantics was silently dropped. Diagnosed on the
SWEET cluster (`14896`/`3795`/`4834`/`6060`/`7025`/`7320`, 24 byte-identical
missing subsumptions each): the gold derivation `Age ⊑ Set` needs
`temporalPartOf ⊑ subsetOf`, `inverse(subsetOf) = supersetOf ⊑ setRelation`,
`range(setRelation) = Set` — i.e. range of a superproperty of the inverse.

`normalise.rs` now emits the two bridge clauses `R(x,y) → S(y,x)` and
`S(x,y) → R(y,x)` per inverse pair (the same swapped-orientation shape as
symmetric roles, which the engine already propagates; verified on `14896` where
the engine derives exactly the 24 gold subsumptions once the bridges exist).

Two hardening fixes rode along: `elc`'s NF6/NF7 recognizers ignored variable
wiring (a bridge clause would parse as a FORWARD role inclusion — unsound; a
chain could bind in listed order, not chain order) and now check the wiring
explicitly, rejecting anything else to the CB engine (exit 3). `el_rbox_safe`
is also forced false whenever an inverse pair was registered, covering bare
`ObjectInverseOf` which produces no rbox record.

Clause output is byte-identical on ontologies without inverse constructs;
inverse-bearing ones gain only the bridge clauses. Harness-validated: the six
SWEET-cluster ontologies plus `3050` and `8999` flip incomplete → AGREE
(8 of the 17 incomplete; the rest have other causes). Sound by construction
(the bridges are the first-order semantics of the axiom; saturation only gains
derivations). No Lean re-cert (frontend/input clauses; calculus untouched).

### Frontend (`ofn`): sound ABox-inconsistency precheck (4 unsound → agree)

Re-diagnosed the 8 "unsound vs gold" ORE ontologies. The dominant cause is NOT
the nominal/number under-detection previously assumed: for `6720`, `15288`,
`443`, `7052` the **ABox** forces an individual into two disjoint named classes,
so the ontology is **inconsistent** (HermiT agrees; Konclude and ELK report all
classes unsatisfiable). KM missed it because the CB engine drops every
individual/ABox clause (`reasoner.rs` maps `Ind`/`Aux` terms to `None`), so the
clash never reaches saturation — KM emitted the full taxonomy of subsumptions,
which the aggregator scored as spurious "extra" subsumptions.

Witness (`6720`): `lemon_slice` is asserted both `fruit` (⊑ `non_alcoholic_-`
`ingredient`) and `sparqling_wine` (⊑ `alcoholic_ingredient`), and those two are
`DisjointClasses`.

New `frontend/abox_consistency.rs`: a sound, conservative precheck over the
parsed ontology. It closes ABox membership under the named subclass/equivalence
hierarchy, object-property domain/range, and `SameIndividual`, then reports
inconsistency iff some individual is provably in both ends of a named
`DisjointClasses`/`DisjointUnion` pair. Only NAMED classes participate (complex
operands and complex assertion concepts are skipped), so every fire is a genuine
OWL entailment — no false positives. The flag rides the `ofn` meta as
`abox_inconsistent`; `owl_classify` short-circuits to an inconsistent result
(empty subsumption set, matching the gold reasoners) without invoking the
engine. Cost is one TBox scan and an early-out (`None`) unless the ontology has
named-class disjointness, so the giants (no disjointness, no ABox) pay nothing.

Clause output is untouched (byte-identical); the only meta change is the added
`abox_inconsistent` field. Corpus-wide the flag fires only on the four family
ontologies plus two non-gold ontologies (`11305`, `11457`, both genuinely
inconsistent), and no ontology Konclude classifies consistently. Soundness vs
gold: **8 unsound → 4 unsound** (remaining: `7901` datatype empty data-range,
`8941` ALC `∀`-driven, `15516`/`2669` complex-boolean over-derivation); agree
530 → 534. No Lean re-cert (frontend, not calculus).

### Frontend (`ofn`): streaming parse + compact clause set (giant ontologies)

The three 3M-axiom giants (ore_ont_8737, 15059, 16744; 450–580 MB OFN) memouted
**in the frontend** at ~20 GB before the reasoner ever started. Three changes,
all output-preserving (byte-identical clause+meta JSON to the old frontend on the
full ORE corpus and on all three giants), cut the frontend peak ~5.5x:

- **Zero-copy tokeniser / parser** (`sexpr.rs`): tokens are now `&str` slices into
  the source produced by a lazy iterator, instead of a `Vec<String>` with a heap
  allocation per token. The parse tree (`Node`) borrows those slices. The
  whole-document token vector and its per-token strings are never materialised.
- **Streaming document walk** (`parse.rs` `for_each_ontology_child` /
  `parse_axioms`): each `Ontology(...)` child is parsed, turned into SROIQ
  axioms, and dropped, so the whole-document AST is never resident. The RBox /
  declared-class side scans re-stream the (cheap, zero-copy) parse instead of
  retaining and **deep-cloning** the AST across `normalise`/`augment` (the old
  `onto_nodes = args.clone()` was itself an O(document) copy). `reg.short` call
  order is preserved, so assigned internal names are identical.
- **Compact `DLClause`** (`clauses.rs`): `body`/`head` are sorted-deduped
  `Vec<Atom>` (canonicalised in the constructors) instead of `BTreeSet<Atom>`.
  A `BTreeSet` node over-allocates even for a 1–2 atom clause; on 3M clauses that
  dominated memory. `Ontology` also stores axioms behind `Rc` so the dedup set
  shares the allocation instead of cloning every axiom.

Measured on ore_ont_8737 (472 MB): frontend peak **19.2 GB → 3.6 GB**, wall
45 s → 20 s (per-stage `VmHWM` via `KM_OFN_TIMING`: normalise 9.4→2.6 GB,
augment 18.6→3.5 GB). Result: **ore_ont_15059 recovered** (was memout; now ok in
70 s / 5 GB, signature identical to the Konclude gold — consistent, empty
#UNSAT). 8737 and 16744 now reach the reasoner (frontend no longer the wall) but
are **not** EL-safe (inverse roles), so they route to the context engine and
remain time-bound there — the engine-scaling residual, not the frontend.

### Result (ORE 2015, 240 s / 20 GB, gold = Konclude 587 ok)

| build | ok | timeout | memout | vs baseline |
|---|---|---|---|---|
| baseline (16-thread, pre-fixes) | 551 | 21 | 19 | — |
| + Hyper join + adaptive retry | 553 | 33 | 5 | +2, 0 regressions |
| + message batching | 554 | 31 | 6 | +3, 0 regressions |
| **+ streaming frontend (final)** | **555** | 32 | 4 | **+4, 0 regressions** |

Recovered: 2397 (fully correct), 9944, 9724 (sound but CB-incomplete on
number/inverse), and 15059 (the giant — see the frontend section; agrees with the
Konclude gold). Soundness preserved: vs gold the correctness profile is unchanged
(530 agree, 17 incomplete, 8 unsound — the pre-existing CB nominal/number
under-detected-unsat cases — both-disagree = 0); the one newly-classified
ontology (15059) agrees with gold, and no previously-agreeing ontology regressed.
All landed changes (Hyper join, batching, streaming frontend) are
output-preserving, so they change *whether* an ontology finishes in budget, never
*what* it derives. km has the lowest median peak memory of the five reasoners
(45.9 MB; Konclude 65, Sequoia 536).

Residual is genuinely hard for the CB engine: live-`∀+⊔` disjunction
(message-traffic explosion — Sequoia, the same calculus, solves these via more
mature redundancy/ordering), the two remaining giants (8737, 16744 — frontend now
fits, but they are not EL-safe so they route to the context engine and time out
there), four CB-engine ~20 GB memouts (10781, 15491, 16444, 6682), and role-chain
propagation volume. The hypertableau (`tableau_cli`) is NOT a fallback: it errors
or hangs on real ORE ontologies (validated only on small synthetic + kinship).

### Hyper rule: backtracking join instead of full cartesian product
- `engine/src/engine.rs` `hyper()` / new `hyper_join()`: the Hyper rule used to
  build a candidate list per body position and iterate the **full cartesian
  product**, attempting unification per combination and discarding the ones that
  fail cross-position variable consistency. On number restrictions
  (`R(x,y1) ∧ C(y1) ∧ R(x,y2) ∧ C(y2) → …`) that is `(#successors)^k`
  combinations, almost all immediately discarded.
  Measured on ore_ont_13912: **738171 enumerated, only 2462 unifiable (99.7 %
  waste)**.
  Replaced with a backtracking join that extends the central substitution one
  body position at a time and only descends into candidates consistent with the
  bindings already made (shared neighbour variables bound earliest). Yields the
  **identical resolvent set** — the skipped combinations were exactly the ones
  that fail `unify` — at a fraction of the enumeration. Same ont: 738171 → 59410
  combinations (12×). All `cargo test` pass (incl. `factor_number_restriction_clash`,
  `existential_subsumption`). No change to soundness/completeness; pure
  enumeration optimisation.
- Added env-gated `KM_PROF` diagnostics (per-query seeding + message-loop
  progress, per-rule saturate counters). Off by default, no hot-path cost.

### Message loop: batched propagation
- `engine.rs` `run_for`: the inter-context message fixpoint used to `saturate`
  *and* `propagate` the target after **every** message. On disjunction/role-chain
  ontologies that re-scans each context's predecessor-edge and Succ/Pred pools
  thousands of times (ore_ont_5303: ~86 k propagate calls). Applying a message
  never enqueues new messages (only `propagate` does), so the loop now **drains
  the whole pending batch**, saturates each target, records the touched contexts,
  and propagates each **once** per round. `apply_succ`/`apply_pred` return the
  touched context instead of propagating inline. Fixpoint unchanged (saturation
  is monotone and confluent — the schedule does not affect the derived set);
  ~1.5× faster message throughput. Recovers ore_ont_9724; all `cargo test` pass;
  vs gold no new unsound/incomplete.

### Threading: adaptive parallel-then-single-threaded-retry (memory-aware)
- Root cause: `reasoner.rs` `saturate()` splits the named queries into
  `available_parallelism` chunks, each a full `Engine` that **re-derives the
  shared successor contexts**. On existential-heavy ontologies this multiplies
  the dominant cost by the thread count. Measured on ore_ont_2397 (ALCH): 1
  thread = 9 GB / 138 s **SUCCESS**, 8 = 40 GB, 16 = 84 GB, 64 = 20 GB **MEMOUT
  @ 9 s**.
- A *blanket* `KM_THREADS=1` is **net-negative**: it recovers the memory-bound
  onts but regresses the speed-bound ones (measured: −12 onts that needed
  parallelism for speed now time out, vs +1..4 memout recoveries). Parallelism
  is genuinely valuable for throughput; it is only harmful (memory) on the
  existential-blow-up onts.
- Fix (`owl_classify.py` `_run_engine_adaptive`): run the **default parallel**
  attempt under an RSS watchdog (`KM_PAR_MEM_GB`, default 18 GiB, just under the
  20 GiB benchmark memcap) that kills *only the engine child*; on overflow,
  **retry single-threaded** (one engine, successor contexts shared, far lower
  memory). Keeps parallel speed for the speed-bound onts (no regression) and
  recovers the memory-bound onts via the fallback. RSS (not virtual address
  space) is monitored so legitimate large parallel runs are not falsely tripped.
  An explicit `KM_THREADS` bypasses the adaptive logic.
