# Solved ontologies: the playbook

How each once-failing ORE 2015 ontology was diagnosed and solved, in enough
detail to reproduce the reasoning and to apply the same mechanism to the next
ontology of its family. Newest first within each section. Gold = Konclude,
except where HermiT/ELK consensus shows Konclude is wrong (see
`CONTESTED-GOLD.md`); an ontology KM solves correctly counts as solved even if
Konclude fails on it.

Companion docs: `../CHANGELOG.md` (result tables per change),
`../engine/src/konclude_ht/STATUS.md` (port state), `PERF-LEDGER.md`.

The authoritative per-ontology acceptance ledger is
[`../results/benchmarks/2026-07-21-route-confirmation/reproduced-route-ledger.tsv`](../results/benchmarks/2026-07-21-route-confirmation/reproduced-route-ledger.tsv).
Its source-bound replays reproduce 587 exact full-IRI results and two additional
adjudicated correct results. It records 4669, 10860 and 1194 as explicit
nonclaims. The executable
[`REPRODUCIBILITY-PROOF.md`](../results/benchmarks/2026-07-21-route-confirmation/REPRODUCIBILITY-PROOF.md)
checks the ledger and external IBEX receipt. The older
[`ontology-solve-routes.tsv`](../results/benchmarks/2026-07-18-ore-solve-routes/ontology-solve-routes.tsv)
remains historical provenance. See the accompanying
[`TAIL-EIGHT.md`](../results/benchmarks/2026-07-18-ore-solve-routes/TAIL-EIGHT.md)
before treating process completion as a solved ontology.

The current single default route is the source-bound v16 `km classify` sweep:
588 of 592 ontologies complete operationally, 586 match the retained full-IRI
gold exactly, and 2669 plus 15516 are the two adjudicated consistency
mismatches. IBEX array `49689798` and audit `49692538` are the authoritative
current-binary evidence.

The uniform 2026-07-22 panel is retained as authority for its frozen historical
binary and is superseded for current-default behavior by v16 above.
It validates 562 automatic-route answers, 575 preselected-route answers, and a
post hoc current-route union of 579. The 589 total above is a cross-revision
source-bound ledger. In particular, the frozen current revision does not
reproduce the source-bound 10621 capsule.

---

## Solved via exact positive-EL ABox materialization

### ore_ont_6934 via typed-ABox SHOIQ certification (2026-07-31)

- **Symptom**: source profiling selected the conservative nominal path, while
  retained fast HT measurements had not proved a generally safe admission
  boundary for the ontology's data assertions and cardinalities.
- **Certificate**: after normalization, KM proves that positive data assertions
  can be omitted without changing consistency. The proof obligation accounts
  for inherited data properties, conditional maximum/exact cardinality one,
  duplicate values, datatype-top semantics, and unsupported constructs on each
  property. All uncertain shapes defer to exact CB.
- **Mechanism**: `nominal_ni_abox` runs the no-blocking SHOIQ
  complete-answer-or-defer worker while retaining the exact nominal CB
  fallback. Empty-suffix individual proxies, trusted ABox-only classes, and
  inverse-functional constraints are handled exactly.
- **Evidence**: production array `49689798` selected `nominal_ni_abox` and
  matched the full-IRI gold in 199.3235 seconds at 1,434.64 MiB. Signature
  SHA-256 is
  `5e60a794400802833a9d5785abb6320b7b13d702e48a4c810462bad6c1fc931e`;
  audit `49692538` validates the complete 592-row sweep.

### ore_ont_1579 and ore_ont_3377 (2026-07-30)

- **Symptom**: automatic routing treated every explicit individual as a
  general nominal. Ontology 1579 exhausted about 18 GiB and 3377 failed after
  about 201 seconds, although a nominal-free production run produced the gold
  taxonomy quickly.
- **Why dropping the ABox was not enough**: both TBoxes contain bottom
  constraints. An asserted individual could therefore make the ontology
  inconsistent, in which case the nominal-free taxonomy would be incomplete.
- **Certificate**: the source gate accepts only positive EL++ class and role
  assertions plus exact `SameIndividual`/`DifferentIndividuals` constraints.
  Union-find forms equality classes and rejects an equality/inequality clash.
  EL completion then materializes every asserted type and role edge and checks
  whether any individual node derives bottom. Any unsupported ABox item or
  non-EL normalized clause makes the route decline.
- **Route**: ordinary `km classify` selects `production_all` from ontology
  features and runs the consistency certificate before publishing. There is
  no ontology-ID dispatch.
- **Result**: source-bound IBEX job 49637883 matches Konclude exactly. Ontology
  1579 returns 56,782 pairs in 12.33 seconds at 852,504 KiB. Ontology 3377
  returns 4,490,309 pairs in 37.03 seconds at 1,971,828 KiB. Both have zero
  missing or extra pairs and matching consistency/UNSAT sets.

---

## Solved via typed source-symbol encoding

### ore_ont_3524, 15703, and 13503: OWL builtin spellings in legal source IRIs (2026-07-18)

- **Symptom**: 3524 and 15703 completed quickly but omitted 123,310 strict
  told subsumptions to a legal generated class whose IRI ends in `#Thing`.
  Ontology 13503 omitted the declared class `daml+oil#Nothing` from its UNSAT
  set. A local-name-only comparison had hidden the 13503 error.
- **Precise cause**: the frontend first reduced a source IRI to its last
  fragment and then interpreted bare `Thing` and `Nothing` as OWL top and
  bottom. It decided builtin semantics from a non-injective local name instead
  of the complete OWL IRI.
- **Fix**: recognize only `owl:Thing`, `owl:Nothing`, and their full W3C IRIs as
  semantic constants. Escape every registry-owned source symbol with a
  reserved spelling to a collision-safe `km_src_*` internal name and restore
  its complete IRI at output. The Python reference frontend and output filter
  use the same identity and ownership rule.
- **Route**: run the fixed binary with `KM_ROUTE=production_all`, 16 threads,
  the 240 second timeout and 20 GiB memory limit. The exact binary SHA-256 and
  copyable per-ontology invocations are in the route registry.
- **Result**: 3524 completes in 35.8973 seconds at 4591.72 MB and 15703 in
  24.4077 seconds at 4347.40 MB. Each returns 1,604,386 full-IRI pairs, preserves
  all 123,310 strict told edges, and matches the shared Konclude/ELK taxonomy
  hash `090129a7f...`. Ontology 13503 completes in 0.0627 seconds at 6.47 MB,
  returns 113 pairs plus the one named UNSAT class, and matches Konclude hash
  `1b8fdf730b...`; a targeted HermiT query independently confirms that class is
  unsatisfiable.
- **Regression**: fixed ontology 7581 completes in 19.2328 seconds at 4654.28
  MB and retains its exact 1,246,911-pair full-IRI taxonomy hash
  `27a29aab96...`. IBEX job 49086702 passes 1,524 Rust library tests, the new
  end-to-end regression, and six Python parity tests. This is frontend symbol
  encoding, not a CB-calculus rule change, so it needs no Lean re-certification.

### ore_ont_8864, 12009, and 6817: source names that look generated (2026-07-16)

- **Symptom**: the first corrected matrix canonicalizer removed four false
  disagreements but left three real incomplete classifications. Every missing
  row had a declared source class beginning with `__`, such as
  `__adipocyte_glucose_uptake`, `__SyndromeDeBuckley`, or
  `__hydroxy_proline_MI_0149`.
- **Precise cause**: KM encoded generated concepts through reserved string
  prefixes. `Signature::is_internal_concept` therefore treated these legal OWL
  source names as generated auxiliaries and did not create query contexts for
  them. Sequoia instead carries source and generated symbols as different
  types, so the collision cannot occur.
- **Fix**: the IRI registry assigns reserved-looking source names a
  collision-safe `km_src_` internal spelling. Generated symbols never pass
  through that registry. The inverse map restores the exact source IRI in
  public output, including a collision with a real `km_src_*` source name.
- **Result**: production `cb_plain16` returns exact frozen Konclude signatures:
  6,094 pairs for 8864, 10,509 for 12009, and 2,431 for 6817, with zero extra,
  missing, unsatisfiability, or consistency differences.
- **Validation**: 1,515 release tests pass, none fail, and 7 are ignored. IBEX
  Gold-6248 job 48946056 repeats all three exact comparisons and also preserves
  the 148/178/11016 nominal signatures. Corrected full matrix job 48946164 is
  the remaining corpus-wide regression gate.

---

## Solved via the certified cardinality arm

### ore_ont_7499: clause-retained fences on the number-role certificate (2026-07-30)

- **Symptom**: no current-main route returned the ontology. The 2026-07-27 full
  sweep records `auto` as an error at 190 s, `manual` and the documented
  `card_race`/`htforce_race` environments as 240 s timeouts, and
  `production_all` as SOUND but INCOMPLETE: 32,847 of the 36,145 gold
  subsumptions in 68.8 s.
- **Precise cause**: the 3,298 missing pairs all need `X ⊑ ≥2
  VO_0001243.OBI_0100026`, the definition of `VO_0000641`, which only the
  first-class `≥n` rules derive. The cardinality arm was gated off by three
  certificate rules that are each stricter than their own justification: an
  RBox `fenced` row for `IrreflexiveObjectProperty(RO_0002351)` and for the
  `ObjectUnionOf` range of `VO_0001480`, although `parse.rs`/`normalise.rs`
  clausify both exactly; the tautological
  `SubObjectPropertyOf(RO_0001000, owl:topObjectProperty)`, which the frontend
  compiles into a write-only bridge clause; and the native-ABox conditions,
  which are bundled into the same flag as the number-role separation proof even
  though the 74 asserted `BFO_0000062` edges say nothing about whether a number
  restriction touches an inverse role.
- **Mechanism**: admit clause-retained fence rows and a write-only universal
  super-role in both the source and the normalized certificate; split
  `card_number_role_separable` (number-role separation) from
  `inverse_cardinality_role_separable` (that plus exact ABox materialization);
  and add the `certified_card_proxy_abox` route, which reproduces the validated
  `card_race` environment and keeps an uncertified native ABox out of the card
  input.
- **Result**: `km classify --route certified_card_proxy_abox` returns 36,145
  subsumptions and 0 unsatisfiable classes in 114 s of HT worker time (1 m 54 s
  wall) at 1.04 GiB on the shared workstation. The full-IRI taxonomy fingerprint
  is `a87bedcb6f6af4e3471686a5a6627a98e4ecd3a8fd102bd610ed38e352d22038`,
  identical to Konclude and HermiT in the frozen sweep. The historical
  `card_race` binary (`0d20dd1`) produced the same answer in 92.8 s at 18.5 GiB
  while running the arm inverse-blind; the restored route keeps the
  inverse-aware configuration and uses 15x less memory.
- **Claim boundary**: this is a solved ontology for an EXPLICITLY selected
  route, not for the automatic policy. The route drops an ABox it cannot
  materialize, which is an under-approximation: sound, but complete for the
  whole ontology only if the ABox cannot change a named-class subsumption and
  the KB is consistent. The frontend's asserted-inconsistency precheck decides
  neither, so `auto` keeps 7499 on `nominals` until a general ABox-irrelevance
  certificate and a complete consistency decision exist.
- **Correction**: the 2026-07-05 entry below reads 7499's missing pairs as a
  gold local-name collision. The full-IRI fingerprint refutes that: the pairs
  are genuinely absent from the CB answer and present in both baselines.

---

## Solved via the exact CB nominal calculus

### ore_ont_148: nominal-label isolation and incremental Pred (2026-07-16)

- **Symptom**: the exact nominal route hit its resource backstop after about
  190 seconds. A proxy-only CB run was fast and happened to match gold, but that
  transformation is incomplete for OWL nominals and cannot satisfy the routing
  contract.
- **Precise cause**: `Cryosphere` adds `Ice` to the `Water` nominal reached
  through `Hydrosphere ⊑ hasSubstance value Water`. One eight-premise r-Pred
  clause then had six exact providers per premise, causing repeated
  `6^8 = 1,679,616` Cartesian products. Dynamic workers also accumulated
  independently conditioned nominal labels in one ground context.
- **Konclude/Sequoia correspondence**: Konclude copies each nominal's completed
  consistency-graph label into an isolated influenced task. Sequoia enumerates
  Pred products and retains their strengthening antichain through exact context
  indexes. KM now uses exact maximal-head indexes, an exact rarest-posting
  active redundancy index, a provably equivalent incremental Pred antichain,
  and fixed per-engine nominal query partitions.
- **Result**: normal `km classify --route nominals`, without an external static
  flag, finishes on `ws` in 54.69 seconds at 3,029,400 KB. It returns all 21,037
  canonical pairs, zero extra, zero missing, no unsatisfiable-class difference,
  and the same consistency result and signature SHA-256 as Konclude.
- **Validation**: 1,515 release tests pass, none fail, and 7 are ignored after
  the independent source-symbol typing tests. Exact
  regression checks keep ore_ont_11016 at 265/265 and ore_ont_178 at 56/56.
  IBEX jobs 48943813 and 48946056 independently confirm all three signatures;
  the current binary classifies 148 in 53.3149 seconds at 2,956.60 MB on the
  required Xeon 6248. Full current-binary matrix job 48946164 is the remaining
  corpus-regression and paired-performance gate. Full diagnosis and proof
  obligations are in `SOLVE-148.md`.

---

## Solved via the konclude_ht bridge (Konclude's algorithm in Rust)

### ore_ont_14817: saturation-aware cardinality successors (2026-07-15)

- **Symptom**: production KM saturated 48,642 of 58,364 active subjects but
  timed out on the 9,722-subject completion residue. Exact cache-lifecycle and
  task-slicing ports reduced its cost without closing it. Isolated subject
  85031 (`UBERON_0014672`) still deferred after 51 seconds and 72,670
  disjunction replacement events.
- **Konclude diagnosis**: a trusted native-object Konclude trace handled the
  same target in 125 ms. It saturation-expanded the first six root successors
  as three cardinality-created pairs. KM created corresponding successors 1001
  through 1006 without expansion and began its nine expansion events at 1007.
  Queue and label tracing ruled out duplicate insertion and accidental
  requeueing; the explosion was real branch search below those under-expanded
  nodes.
- **Root cause**: Konclude's `applyATLEASTRule` creates an `ATLEAST` dependency
  and delegates to `createDistinctSuccessorIndividuals`, which allocates and
  distinguishes all successors, replays the relevant saturation successor,
  installs signed indirect-super-role links, adds qualifiers, and establishes
  saturation caching. Production Rust bypassed its existing full port and
  called the reduced `ht_create_distinct_successors`, which omitted saturation
  replay and cache establishment.
- **Fix**: route production `apply_atleast_rule` through the full constructor
  with Konclude's dependency, role list, pending-clash propagation, low-level
  nominal handling, and queue order. Retain the supporting exact ports for the
  ontology-wide satisfiable-expander cache, per-node cache state, pointer-like
  label signatures, 80-rule scheduler boundary, cache-pool release, and KPSet
  touched-candidate order.
- **Result**: the isolated subject finishes in 14.66 seconds and now expands
  successors 1001 through 1006. Production-sweep job 48853569 task 518 solves
  the full ontology in 56 seconds at 3,365,116 KB, returning all 1,184,692
  subsumptions with zero extra and zero missing.
- **Validation**: a focused production-path regression proves that every
  `≥2 R.C` successor receives saturation-only consequences. The release suite
  passes 1,480 tests, with 7 ignored and none failed. Full 592-ontology IBEX
  job 48853569 improves from 574 to 575 completed and from 514 to 515 exact
  matches. Only 14817 changes, and no previously exact ontology regresses.
  Full traces and reproduction artifacts are in `SOLVE-14817.md` and
  `../results/benchmarks/2026-07-14-14817-closure/`.

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
- **Restored 2026-07-30**: the 2026-07-27 sweep reported 3215 as a timeout on
  every KM arm, and so did the source-bound rerun of this closure binary, so
  the cause was lost headroom rather than a regression against the design above.
  On today's benchmark hardware both the closure build and current main need
  about 400 seconds, and both still produce the exact 3,923,171-pair signature.
  Phase timers put the whole cost in the satisfiability phase, and stack
  sampling put over a third of that phase in `getenv`: the completion rule
  bodies read their CLI-only diagnostics inline, once per concept addition. The
  cached gates in `konclude_ht::completion` remove that cost the same way the
  2026-07-13 change removed it from saturation. IBEX job 49624875 now finishes
  `ht_bridge` in 162.2 s at 5,560,592 KB and the production `auto` route in
  161.9 s at 5,500,480 KB, both exactly equal to gold. See `SOLVE-3215.md` and
  `../results/benchmarks/2026-07-30-3215-restoration/`.

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

- **Current automatic route for 12653 (2026-07-31)**: the exact bridge
  certificate represents its bounded atomic numeric fragment, including
  `positiveInteger ⊑ nonNegativeInteger ⊑ integer ⊑ decimal`, cardinalities
  zero through two, and the fixed integer values 2, 3, and 4. Unsupported
  datatype shapes still defer. Source-bound IBEX job 49665588 selected
  `production_all` and matched all 10 Konclude pairs with zero missing or
  extra entries, matching consistency, and no unsatisfiable named classes in
  0.1012 seconds at 39.81 MiB. The tested binary SHA-256 is
  `1c904f79ed1058e4dd3395c1028eb14f6fb41e420940c88d66f67a1dd78e1bed`.
- **Current automatic-route restoration (2026-07-30)**: 541's only logical
  uses of `owl:topObjectProperty` are three tautological
  `R SubPropertyOf owl:topObjectProperty` axioms. The frontend now elides these
  from the normalized ontology and RBox only when neither builtin top property
  occurs anywhere else. This leaves all OWL entailments unchanged and removes
  the artificial universal-role fence that prevented the source-terminology
  bridge from running. Source-bound IBEX build 49633775 and exact test
  49633776 produced 164/164 reference pairs, zero missing, zero extra, matching
  consistency and no unsatisfiable-class difference in 0.15 seconds at
  29,760 KiB. The tested binary SHA-256 is
  `0e9e612a3c51b03f0709ce1ae3c10a67bdd70653bdc83480bc0f3cd8c64cd460`.
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
- **2026-07-15 routing audit**: later exact source-RBox provenance caused
  `cb_to_ht` to fence 541's complex domain and range for the legacy tableau.
  The orchestrator mistakenly reused that legacy fence for the source-TBox
  bridge, so the documented bridge kernel remained exact but was never
  spawned. The gate now accepts complex domain/range fences only when
  `KM_TRIGGER_ABSORB` supplied a complete source TBox; the reconstructed-clause
  path remains fenced. Production `km classify` again closes 541 in 0.25 s at
  53 MB and 12653 in 0.15 s at 18 MB on `ws`.

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

## Solved in production km

### ore_ont_10702 — wine/nominals (2026-07-31)

- **Symptom**: the exact nominal CB route exceeds the benchmark limit; the
  unrestricted fast hypertableau lacks the SHOIQ nominal-introduction rule.
- **Diagnosis**: 10702's finite completed models have only direct
  number-role successors of roots. The NI rule applies only to a blockable
  number-role neighbour that is not the root's direct successor.
- **Mechanism**: automatic source-feature route `nominal_ni_tbox`; preserve
  the validated clausal TBox, use inverse-safe pairwise blocking, and inspect
  every completed model for the NI premise. Any occurrence makes the worker
  defer. The one positive data assertion is omitted only after its integer
  range and explicit named domain are certified.
- **Result**: 587/587 MATCH; IBEX job 49675463, 2.6099 seconds, 19.84 MiB,
  signature
  `eee761d0c89347a42ce9a221e7d98295f4a9d7527c755cb3eafa9978cc06d55b`.
- **Full-sweep status**: automatic-route regression job 49676527 is running;
  completed production totals are unchanged until its audit finishes.

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

### Correctness family — contested gold

- All 4 apparent unsoundnesses were GOLD bugs; fixed data_abox precheck +
  complex-domain handling. 8941/13912/15516/2669 are genuinely inconsistent
  (HermiT agrees); proof in `CONTESTED-GOLD.md`.
- **13503** is a separate named-unsatisfiable-class gold omission. It declares
  `daml+oil#Nothing ≡ ¬owl:Thing`, so that declared class is necessarily
  unsatisfiable although the ontology is consistent. Exact builtin recognition
  exposes the missing `#UNSAT` member in the stored Konclude signature. The
  two-axiom witness is committed under `results/contested-cores/`.

---

## Current frontier and recently closed target

| Ont | Route | Signature | The path |
|---|---|---|---|
| 6934 | automatic `nominal_ni_abox` | full-IRI exact | Typed normalized-ABox certificate plus complete-answer-or-defer SHOIQ worker; v16 production 199.3235 s / 1,434.64 MiB. |
| 4669 | retained production and HT executions terminate, but both outputs are unsound; logical completeness unknown | no authoritative full taxonomy | HermiT proves eight sampled production-UNSAT classes and all 56 additional HT-UNSAT classes satisfiable. No completed existing KM output is valid. |
| 10621 | source-bound Capsule-10 `ht_bridge`; frozen current revision returns unsupported | full-IRI exact against fresh source-built Konclude for Capsule-10 | Capsule-10 completes in 118.2149 s at 1096.54 MiB. One runtime trace selects `ht_bridge`; KM and Konclude both produce 70,827 subsumptions and 33,433 unsatisfiable named classes, taxonomy SHA-256 `066b41b5f3e845110eceb3607b050627da744968ccef1ceafed50e3c3ea4468e`. Restore and revalidate this mechanism before claiming it for current main. |
| 1194 | — | no authoritative gold | 75 MB SRIQ ontology; no confirmed previous KM closure. Establish gold by decomposition and independent checks. |
| 10860 | — | no authoritative gold | DL-safe-rule ontology; inspect ABox/rules and adjudicate directly because neither raw Konclude nor raw HermiT supplies valid gold. |

The hard-residual audit, including the previously lost closures of 10702,
15672, and 6934 and the later source-bound closure of 10621, is maintained in
[`HARD-RESIDUAL-AUDIT.md`](HARD-RESIDUAL-AUDIT.md). Do not describe all six as
unsolved. The historical source-bound ledger reproduces every one of the 589
cross-revision solve claims. The uniform current-revision panel reports 575
validated preselected-route answers and a post hoc current-route union of 579;
only the three rows listed above remain source-bound-ledger nonclaims.

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
