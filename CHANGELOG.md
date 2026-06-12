# Changelog

All notable changes to the kobayashi-marust reasoner. Newest first.

## [unreleased] — CB engine scaling (ORE 2015 coverage push)

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
