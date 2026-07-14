# Solved ontologies: the playbook

How each once-failing ORE 2015 ontology was diagnosed and solved, in enough
detail to reproduce the reasoning and to apply the same mechanism to the next
ontology of its family. Newest first within each section. Gold = Konclude,
except where HermiT/ELK consensus shows Konclude is wrong (see
`CONTESTED-GOLD.md`); an ontology KM solves correctly counts as solved even if
Konclude fails on it.

Companion docs: `../CHANGELOG.md` (result tables per change),
`../engine/src/konclude_ht/STATUS.md` (port state), `PERF-LEDGER.md`.

---

## Solved via the konclude_ht bridge (Konclude's algorithm in Rust)

### ore_ont_9724: constant-time intrusive free-list representation (2026-07-14)

- **Symptom**: KM returned a sound partial taxonomy with 3,325 missing pairs
  after the production saturation budget. A 1,200-second exact-input run
  recovered only one pair and grew beyond 24 GB. The worker never reached the
  planned completion-side ATMOST merge path; it remained in the saturation
  outer queue.
- **Konclude diagnosis**: instrumented Konclude completed with one worker in
  10.46 seconds and built 33,422 saturation items, close to KM's 33,678 seeds.
  Four live KM samples at 30, 90, 160, and 220 seconds all stopped in
  `memcpy -> release_role_saturation_process_linker ->
  process_successor_functional_concepts_extensions`. Konclude releases and
  reacquires these objects through the intrusive
  `mRemRoleSatProcessLinker` head in O(1). KM's collapsed `Vec` represented
  the head at index zero, so every `insert(0)`/`remove(0)` shifted the growing
  free list.
- **Mechanism**:
  1. Store collapsed allocation-free-list heads at the Vec tail, translating
     Konclude's prepend/head-pop to constant-time `push`/`pop` while preserving
     its exact LIFO order. Reverse diagnostic getters to retain the C++
     head-to-tail view. Apply the same invariant to adjacent `mRemaining*`
     allocator lists with the same constructor pattern.
  2. Represent implication reapply state as a non-owning operand cursor rather
     than a cloned suffix, including Konclude's stack-local initial application.
  3. Use pointer-like integer hashing for role arena ids, consolidate backward
     role-bucket mutation, and keep temporary status worklists as O(1) LIFO
     stacks. These faithful supporting ports reduced overhead but did not close
     9724 until the measured role-linker free list was fixed.
- **Result**: production IBEX job 48798145 finished `km classify` in 24.72
  seconds at 8,091,788 KB and emitted all 457,090 canonical pairs, with zero
  extra and zero missing. Exact-normalized-input job 48798075 independently
  matched in 32.15 seconds.
- **Validation**: 1,475 release tests pass, 7 are ignored, and none fail. Full
  592-ontology IBEX job 48799766 raises exact matches from 511 to 514, with
  unchanged timeout and disagreement counts and no prior exact-match
  regression. The same general fix also changes 1016 from 2,510 missing to
  exact and 11623 from 3,423 missing to exact. Detailed traces, C++ source
  correspondence, and reproduction artifacts are in
  `SOLVE-7914-9663-9724.md` and
  `../results/benchmarks/2026-07-14-9724-closure/`.

### ore_ont_9663: native RBox links + role-specific saturation successors (2026-07-14)

- **Symptom**: production KM terminated soundly but returned 685,932 of
  Konclude's 725,040 non-self pairs, leaving 39,108 missing. Of these, 39,087
  were 13,029 subjects each missing the same BFO domain class and its two
  superclasses.
- **Konclude diagnosis**: Konclude stores property domains/ranges directly on
  `CRole`. When a restriction role has ranges, its precomputation constructs a
  separate saturation item keyed by `(role, filler, polarity)`, wires it into
  the restriction's existential-successor reference, and initializes the node
  with that role. KM had neither the source RBox links nor these role-specific
  items. Reusing the ordinary filler node lost domain consequences reached only
  after `BFO_0000050 ∘ RO_0002202 ⊑ RO_0002202`.
- **Mechanism**:
  1. Preserve exact source RBox provenance as `TInput::role_domains` and
     `TInput::role_ranges`, then install only those pairs on the native role and
     its inverse. Clause shape is deliberately not used as provenance.
  2. Port `hasRoleRanges` over signed indirect super roles.
  3. Intern `(role, concept, polarity)` successor items, use them in dependency
     ordering, wire each restriction's existential-specific reference, and
     initialize both ontology/process items with the role.
  4. Port the intermediate substitute-chain subsumer extraction exactly. It is
     retained and tested, although its isolated candidate did not alter 9663.
- **Result**: full production job 48795569 returned all 725,040 pairs with zero
  extra and zero missing in 1:56.81 at 3,369,420 KB. Promoted gate job
  48797088 task 0 matched again in 52.75 seconds at 3,189,032 KB. Its 422
  completion residue subjects closely match Konclude's 423 insufficient
  saturation nodes, and all 422 finish without defer.
- **Validation**: the release suite passes 1,474 tests with 0 failed and 7
  ignored. Permanent tests cover RBox provenance, rejection of a same-shaped
  non-RBox guarded rule, direct domain application, inverse range-automaton
  construction, and the complex role-chain-domain witness. Full 592-ontology
  IBEX job 48797094 raises exact matches from 508 to 511 and regresses no
  previously exact ontology. The detailed trace and source correspondence are
  in `SOLVE-7914-9663-9724.md`; reproducible artifacts are in
  `../results/benchmarks/2026-07-14-9663-closure/`.

### ore_ont_3215: Konclude's global KPSet phase barrier (2026-07-13)

- **Symptom**: the source-terminology bridge covered every axiom and eventually
  derived the correct positive taxonomy, but production classification still
  timed out over 54,974 active classes and 3,923,171 gold pairs.
- **First Konclude divergence**: KM attached 18,323 reverse implications to the
  common condition `C047449`, producing an approximately 18,000-concept label;
  Konclude's corresponding label had 3 concepts. The bridge now ports
  Konclude's active-class filtering, trigger over-use penalty, pair reuse,
  decreasing trigger order, left-deep binary chain, rounded-average OR
  complexity, and source-TBox/definer separation.
- **Decisive classifier diagnosis**: instrumented Konclude processed 54,974
  items, derived 36,651 satisfiability results directly, ran 18,323 completion
  satisfiability jobs, and ran zero pairwise subsumption tests. KM interleaved
  each model with pair tests and never executed the global phase in
  `createNextSubsumtionTest` that connects the propagation graph and compares
  all completed child/parent possible maps.
- **Fix**: run all 18,323 prepare models first, then cross one synchronous KPSet
  barrier, build the `owl:Thing`-rooted propagation graph, prune absent parent
  candidates, and only then verify survivors. The barrier propagates 202,002
  false candidates and leaves zero pair jobs. Supporting integer hashing,
  duplicate-descriptor precheck, and LIFO free-list changes preserve the same
  saturation fixpoint while making it finish.
- **Production scheduling**: the serial bridge finished in 137 seconds with one
  CB competitor but timed out when the speculative CB fallback occupied 15
  cores. For faithful bridges with at least 50,000 active classes, the race now
  limits only that fallback to one thread. Smaller bridge races are unchanged.
- **Result**: final production smoke job 48790271 matches Konclude in 129
  seconds at 5,351,252 KB. Full-sweep job 48790295 matches again in 120 seconds
  at 5,357,524 KB. Both have 3,923,171 / 3,923,171 pairs, zero extra, zero
  missing, and identical consistency/unsatisfiable-class results.
- **Validation**: 1,468 release tests pass, 7 are ignored, and none fail. The
  592-ontology sweep has 508 exact matches and zero gold-match regressions,
  improving from 499. The complete C++ comparison and evidence are in
  `SOLVE-3215.md` and
  `../results/benchmarks/2026-07-13-3215-closure/`.

### ore_ont_5303: equivalent non-candidate classification hand-off (2026-07-13)

- **Regression symptom**: the first feature-enabled IBEX sweep completed 5303
  but missed only `CarbonHydrogenSubstructure ⊑ Hydrocarbon`. Controlled A/B
  with identical flags showed the previous binary matched gold and the 7914
  candidate was incomplete by one pair.
- **Localization**: the direct completion probe proved the pair, while the
  nondeterministic root-model read-off omitted `Hydrocarbon`. Disabling the
  associated cache, all saturation caching, or saturation itself did not
  change the miss. The completion rules and cache were therefore not the
  cause; the missing step was post-satisfiability candidate initialization.
- **Konclude mechanism**: `Hydrocarbon` is one of three source equivalent
  definitions that remain `CCEQ` (`eq=0/3`) because their positive universal
  restrictions prevent full trigger absorption. Konclude records such
  definitions in `CTBox::mEquivConNonCandidateSet` when it does not use the
  optional partial-candidate optimization. Its classification analyser filters
  the live set, emits an initialize-possible-subsumption message, and the KPSet
  classifier schedules every surviving pair.
- **Root cause**: KM retained the `CCEQ` definitions but never populated the
  ontology set. It then called the old analyser wrapper with an empty
  `HashMap`, despite already having ports for the live ontology set, the
  filtering test, the message payload, and the KPSet receiver.
- **Fix**: take Konclude's exact equivalent-non-candidate branch for retained
  source definitions, call the live-set analyser, deliver its messages, and
  refresh the synchronous candidate list from the resulting KPSet map before
  verification. No ontology or class-name special case was added.
- **Result**: the production trace now schedules
  `CarbonHydrogenSubstructure v Hydrocarbon` and proves it true. The raw
  nondeterministic read-off remains false, confirming that the repair acts at
  the intended classification boundary. Final IBEX job 48737778 matches 5303
  exactly and raises the feature-enabled corpus total from 498 to 499 gold
  matches. The 18-ontology same-flags panel has zero old-versus-final changes.

### ore_ont_7914: descriptor-chain-safe associated expansion cache (2026-07-13)

- **Symptom**: KM originally timed out after completion-side OR fan-out. After
  the OR planning and satisfiable-cache ports made it terminate, KM produced
  141,546 subsumptions against Konclude's 141,517. The 29 extras were 24
  members of the `UBERON_0003657` family and 5 members of the
  `UBERON_0010961` family.
- **Konclude diagnosis**: disabling KM's associated saturation expansion cache
  removed the first false family but made the second time out, so the cache was
  necessary but partitioned incorrectly. KM classified branch-derived CCAND
  concept 45405 as nondeterministic, then replayed the same concept as a
  deterministic associated expansion. Instrumented Konclude cached only its
  two branch-tag-1 CCSUB descriptors as nondeterministic and wrote no
  deterministic suffix.
- **Root cause**: Konclude's
  `CReapplyConceptLabelSet::insertConceptGetClash` prepends with
  `mConceptDesLinker = conceptDescriptor->append(mConceptDesLinker)`. KM moved
  the label head but never set the new descriptor's `next` pointer. The broken
  newest-first chain made `CSaturationNodeExpansionCacheHandler` wrap from a
  null nondeterministic boundary back to the label head and duplicate the
  branch-derived descriptor into the deterministic suffix.
- **Mechanism**:
  1. Port Konclude's OR delay/replacement/planning pipeline, restriction
     specification, single-survivor `CORONLYOPTIONDependencyNode`, and exact
     branch dependencies.
  2. Port satisfiable-cached OR/existential parking, reapplication, saturation
     cache establishment, and extension resolution.
  3. Restore the load-bearing insertion invariant by setting every successfully
     inserted descriptor's `next` to the previous label head before insertion.
     No cache exception or ontology-specific rule is used.
  4. Align the associated-cache constructor default with Konclude by allowing
     one nondeterministic expansion rather than zero. This is an exact adjacent
     port, but the descriptor link is the change that removes the 7914 extras.
- **Result**: full Slurm job 7936 completed all 93 residue subjects in round 0,
  with no deferred subjects, in 2:30.56 at 18,882,684 KB. KM and Konclude both
  produced 141,517 subsumptions; comparison found 0 extra, 0 missing, no
  unsatisfiable-class difference, and no consistency mismatch. Targeted jobs
  7934 and 7935 independently closed both residual families.
- **Validation**: final release suite 1,460 passed, 0 failed, 7 ignored. Permanent
  regressions cover the production descriptor chain, nondeterministic-prefix
  cache split, OR-only dependency, and nondeterministic model read-off. The
  full causal trace and source references are in
  `SOLVE-7914-9663-9724.md`. Final 592-ontology IBEX job 48737778 matched 7914
  exactly; the same-flags 18-ontology panel found no old-versus-final
  regression.

### ore_ont_541 and ore_ont_12653: source terminology + isolated OR tasks (2026-07-10)

- **Symptom**: both timed out in the production CB portfolio. Earlier bridge
  variants either thrashed, deferred, or solved only a test harness.
- **Konclude diagnosis**: instrumentation plus source inspection showed two
  decisive boundaries. `CConcreteOntologyUpdateBuilder` stores named-left
  inclusions directly as `CCSUB`/`CCEQ` terminology; the binary absorber sees
  only 23 residual GCIs on 541 and 10 on 12653. Its OR rule forks independent
  satisfiability tasks. KM instead fed 647/501 generated HT clauses into the
  absorber and explored siblings in one mutable context.
- **Mechanism**:
  1. Carry normalized source axioms through the frontend under
     `KM_TRIGGER_ABSORB`, leaving default JSON byte-identical.
  2. Build native `CCSUB`/`CCEQ`, restrictions, role domains/ranges, and only
     then run the ported full/partial binary absorber. Counters match Konclude:
     541 eq 1/2 and GCI 22/23; 12653 eq 1/1 and GCI 9/10.
  3. Use complete branch-epoch COW for every OR sibling. The load-bearing
     oracle is PathOfLength4 in 12653: the old shared state falsely exhausted
     19 backtracks and returned UNSAT; isolated state finds the SAT model.
  4. Keep saturation and completion in separate calculation tasks. Seed
     classification with the deterministic named `CCSUB` closure and verify
     only residual possible subsumers, matching Konclude's KPSet workflow.
  5. Let `KM_TRIGGER_ABSORB=1` activate the certified bridge route and accept
     its answer immediately; a bridge defer still falls back without a verdict.
- **Result on ws, release `km classify`**: 541 = **0.86 s**, 12653 =
  **0.08 s**. Gold projection is exact: 164/164 and 10/10 respectively, with
  zero missing and zero spurious pairs. 541 has 166 full-IRI pairs because two
  distinct classes share the local name `ProcessQuality`.
- **Validation**: 1433 passed, 0 failed, 7 ignored; default frontend output for
  both ontologies is byte-identical with the flag off.

### ore_ont_12653 — path/universe QCR ontology (2026-07-06, `d64e78b`)

- **Symptom**: production km times out (240 s). Family: disjunction +
  qualified cardinality.
- **Diagnosis path**: `bridge_scale_probe` showed the bridge terminates each
  subject in ~8 ms (33 nodes, 4 backtracks) but full classify derived 0/10
  gold pairs with `unsupported=103` clauses dropped. `KM_BRIDGE_DUMP_UNSUP`
  categorised the drops: inverse-role axioms (`R(x,y) → S(y,x)`),
  domain/range axioms (`R(x,y) → C(x)` / `→ C(y)`), and qualified-cardinality
  pigeonhole clauses (`C(0) ∧ D(1) ∧ D(2) ∧ R(0,1) ∧ R(0,2) → eq(1,2)`).
- **Mechanisms** (all faithful Konclude ports, in `konclude_ht/bridge.rs` +
  `completion/u08.rs`):
  1. Domain/range: fill `Role::{domain,range}_linker` from the clausal forms;
     apply at EVERY link install (base role, each super-role, mirror-inverse)
     in `ht_apply_role_domain_range` — the exact
     `createNewIndividualsLink*` placement (Konclude cpp 22303–22334,
     22382–22395).
  2. Inverse-role hierarchy: `R(x,y) → S(y,x)` is `R ⊑ S⁻`; encode as a PLAIN
     super-role entry pointing at the concrete inverse-role object, closure
     over both polarities (`R ⊑ S` also yields `R⁻ ⊑ S⁻`). Never encode
     polarity in the linker's negated flag: `has_indirect_super_role`
     (the ∀-matcher) ignores it.
  3. Qualified number restrictions: `cb_to_ht::convert(card_enabled=true)`
     replaces the pigeonhole clauses with structured `card_defs`
     (`marker ⊑ ≥n/≤n R.filler`); the bridge builds CCATLEAST / qualified
     CCATMOST concepts and absorbs them onto the marker (CCSUB → AND rule).
  4. Pairwise fallback: a subject whose saturation made nondeterministic
     choices is not read-off-authoritative; each candidate subsumer is
     verified by `bridged_unsat(s ⊓ ¬sup)`, which is exact under any branch
     discipline.
- **Result**: missing=0 spurious=0 in 1.0 s (subjects=14). konclude_ht suite
  1208/1208; ore_ont_1016 read-off regression byte-identical.
- **Status**: historical first harness close. Superseded by the 2026-07-10
  source-terminology production route above.

### Read-off soundness gate (2026-07-06, follow-up to `d64e78b`)

Found while validating ore_ont_3215: the model read-off trusted
`or_backtrack_count == 0` as a determinism witness. Wrong — a drive can OPEN
OR branch points and commit to each first disjunct without ever clashing;
concepts added under those choices are branch-dependent, not consequences.
Measured: 86 spurious subsumptions on 3215. Fix: count branch-point openings
(`or_branch_open_count`); read-off is authoritative only if the drive opened
none and backtracked never. Konclude gates the same extraction on the
dependency track point's branching tag (cpp 4121); the open-count stands in
because the in-process OR adds disjuncts under the OR concept's own track
point. Nondeterministic subjects degrade to candidate extraction + pairwise
verification instead of being trusted.

**Rule for all future model read-offs: backtrack-free is NOT deterministic;
branch-open-free is.**

---

## Solved in production km (this branch, pre-bridge)

### ore_ont_10702 — wine/nominals (2026-07-05)

- **Symptom**: 23 missing FrenchWine subsumptions (incomplete).
- **Diagnosis**: `nominal_clauses` carried only the ClassAssertion half of the
  ABox; RoleAssertions between named individuals were dropped.
- **Mechanism**: add `{a} ⊑ ∃R.{b}` nomlink clauses (sound, additive).
- **Result**: 587/587 MATCH.

### ore_ont_12698 — colon-localname classes (2026-07-05, `03cdb8b`)

- **Symptom**: classes with `:` in the localname missing from output.
- **Diagnosis**: the HT arms passed an EMPTY named set to `cb_to_ht`, so
  colon-named classes were treated as internal and dropped.
- **Mechanism**: thread the real named set through. Residual 18 differences
  are gold localname collisions, not KM errors.

### ore_ont_2669, 15516, 10906 — SWRL DL-safe rules (2026-07-05, `0d20dd1`)

- **Symptom**: timeouts; gold says satisfiable.
- **Diagnosis**: the ontologies are inconsistent BECAUSE of their SWRL rules,
  which km (and Konclude's ORE config) ignored. HermiT agrees: inconsistent.
- **Mechanism**: `KM_HT_RULES` (default-on, rule-gated): ABox individuals as
  nominal nodes + rules as HtClauses in the HT arm. Inert on rule-free onts
  (14817 frontend output byte-identical).
- **Result**: correctly inconsistent in < 120 s. Counts as solved under the
  consensus-gold rule.

### ore_ont_1603, 9540, 7499 — cardinality + recognition (2026-07-05)

- **Symptom**: timeout family with `≥n/≤n` folding blowups.
- **Diagnosis**: clausal pigeonhole expansion of number restrictions explodes;
  unguarded `⊤ → Q ∨ NQ` recognition branches on every node.
- **Mechanism**: frontend CardMeta → first-class `card_defs` (`KM_HT_CARD`,
  default-on) + guarded/lazy recognition (`CARD_RECOG`). 7499's "missing
  3297" was a gold localname collision, not incompleteness.
- **Validation**: panel 48067625 clean, no regressions.

### ore_ont_541 — functional-role variant (2026-07-05)

- **Historical mechanism**: `KM_HT_CARD_FN` makes functional data/object properties
  become
  first-class `≤1 R`. Validated 21 s MATCH standalone; the confirming panel
  was still pending as of 2026-07-05, and the ORE-config production route
  still listed 541 as a timeout. This route remains gated because its corpus
  panel regressed other ontologies. The source-terminology bridge above now
  solves 541 cleanly in production; this entry is retained as history.

### ore_ont_5303 — deep-decision ALC+⊔ (2026-06)

- **Symptom**: timeout; decision depth 15k+.
- **Diagnosis path** (documented in `5303-ATTEMPTS.md`): conflict learning
  inert; EAGER refuted; the winning discipline was EAGER + NEGTRIED + ORD=1,
  then per-step cost elimination.
- **Mechanism**: `KM_HT_INCRBLOCK2` (incremental blocking) +
  `KM_HT_INCROBLIG` (incremental obligations), both result-identical.
- **Result**: 207 s → 5 s. Gotcha that cost 3 debug cycles: build fail-loud;
  a stale binary faked a null result.

### ore_ont_7581 — QoSat + router (2026-06, `16e6749`)

- **Mechanism**: INVCHAIN + GFCERT + short-QO-budget in the router sweep.
- **Result**: gold-exact, 0 regressions. ht-RACE mode measured UNSAFE
  (7216/7901) — keep fallback, never race.

### ore_ont_16461 — cardinality recognition (2026-06, `fd94c7e`)

- **Mechanism**: `≥n` recognition + fact-only successor cores.

### The three giants — 8737, 15059, 16744 (2026-06)

- **8737** (450–580 MB class): clone-free EL completion hot loop (`cd60ce3`):
  `in_edges` as flat `Vec<Vec<(parent,role)>>`, index-loop NF4, reused
  conclusion buffer. 252 → 221 s standalone; pipeline timeout → ok.
- **15059**: streaming frontend parse + compact DLClause (`ac153ef`):
  frontend peak 19.2 → 3.6 GB, byte-identical output.
- **16744**: Skolem-exclusion in EL-routing relevance (`72acb3a`) — the ont
  is EL-safe once Skolem-only symbols are excluded from the relevance check.

### Correctness family — the 4 "unsound" + contested gold (2026-06)

- All 4 apparent unsoundnesses were GOLD bugs; fixed data_abox precheck +
  complex-domain handling. 8941/13912/15516/2669 are genuinely inconsistent
  (HermiT agrees); proof in `CONTESTED-GOLD.md`.

---

## Diagnosed, not yet solved (the current frontier)

| Ont | Route | Signature | The path |
|---|---|---|---|
| 14817 | production | 71 missing = transitive `part_of` propagation | Role-automaton ∀-propagation is ported and live in konclude_ht tests (`6a7a67e`) but not production-wired: needs OntologyArenas-from-clauses + consistency classify. |
| 10621 | — | contested gold | Konclude-vs-HermiT disagreement; resolve gold first. |

## Reusable diagnostics

- `KM_BRIDGE_PROGRESS=1` — per-drive counters (`drives/backtracks/nodes/
  inserts/bp_depth` every 4096 drives; `PROGRESS-SAT` every 1M in-drive
  iterations). Distinguishes backtrack thrashing (nodes flat, backtracks
  climbing) from model explosion (nodes climbing) in one 120 s run.
- `KM_BRIDGE_DUMP_UNSUP=N` — shape of the first N clauses the bridge cannot
  encode; scopes the next coverage wave.
- `KM_BRIDGE_MAX_SUBJECTS=N` — bounded-sample classification against a
  (sampled) gold for correctness checks on deep taxonomies.
- `bridge_scale_probe` / `bridge_classify_full` (both `#[ignore]`d tests in
  `konclude_ht/bridge.rs`) — per-subject termination probe / full classify
  vs gold with MISSING/SPURIOUS attribution.
