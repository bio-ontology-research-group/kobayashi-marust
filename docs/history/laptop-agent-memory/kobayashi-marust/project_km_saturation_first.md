---
name: project-km-saturation-first
description: Task
metadata: 
  node_type: memory
  type: project
  originSessionId: 35856588-304b-4786-a05c-4b601119991f
---

# Saturation-first probe answering (tasks #23/#24) — state as of 2026-07-10

## Task #24 wave 3 (2026-07-10, commit c116a9c) — ext wrong clashes FIXED + 12653 "regression" resolved
- **ROOT CAUSE of the ext-ON wrong-UNSAT family**: the watch-side implication
  trigger check `insert_concept_reapplication_return_triggered` faithfully
  ported the C++ `present && !isNegated()` (positive presence only) — safe in
  Konclude because absorption only builds positive-presence triggers (linkers
  store INVERTED polarity, `¬sub` convention) — but the bridge's `implication()`
  encoding also emits NEGATIVE-presence triggers (non-negated linkers). A label
  carrying +C then satisfied a want-¬C trigger. On the 13-axiom reproducer:
  +EntityAtSomeTime satisfied the ¬E trigger of (¬E ∧ Q_6 → Q_12) while
  preprocessing a resolved extension node → Q_12 → (Q_12 → ¬E) fired → ¬E
  insert clashed with +E → indirect propagation (non-inv-connected edges) into
  MaterialObject's seed = wrong verdict. Insert-side reapply was already
  polarity-aware (`negated != con_neg`); FIX = thread wanted polarity
  (= !linker.negated) into the watch-side triggered test (identical behavior
  for Konclude-shaped triggers).
- **Validation (ws)**: reproducer 0/20 wrong (was 8/8 deterministic);
  541 ext-ON 3 runs 0 wrong + 6-9/59 family subjects answered SAT-certain =
  FIRST sound nonzero family coverage; 12653 ext ON/OFF unchanged (0/21);
  suite 1424/1424. KM_HT_SAT_EXT stays OPT-IN: 541 saturation 0.4s → ~40s
  with extensions + run-to-run coverage variance (HashMap succ-ext maps) +
  W6-DEFER ext bodies partial. One selftest corrected (stored positive
  triggers as non-negated linkers — insert-side never fired those either).
- **Debug aids landed** (env-gated, OnceLock-cached): KM_SAT_CLASH_TRACE=1
  (all 7 CLASHED-set sites + indirect clash propagation edges + SAT-IMPL-EXEC
  implication executions), KM_SAT_ADD_TRACE=<concept idx> (backtrace on adds),
  KM_SAT_DEBUG now also dumps SAT-SUBJ (subject→node map), SAT-NAME
  (named index→concept→IRI), SAT-CONCEPT (full concept arena: op/tag/role/
  param/operands). Debug build on ws gives readable backtraces (release has
  no debuginfo).
- **12653 plain-bridge "regression" = NOT A REGRESSION (bisect closed)**:
  tested 1c931e7 / 18c9a46 / 8481c9b / HEAD — ALL permanent-poison-defer
  (subject 1 or 14; which subject trips first varies by commit, both
  by-design). The "plain closes 12653 in 10-20s" memories date from the
  pre-7a01372 era (84e38bf cont-13/14, 067aaa4 task #14); 7a01372 (2026-07-08)
  RESTORED complete-or-defer (unrestored advances poison SAT verdicts) and
  cont-17 already recorded the bridge arm closing NOTHING and staying OFF in
  production. The cont-19 "17s" figures were COW+DDB probe-harness
  measurements, not plain km-level classify (km-level COW+DDB @ budget 1s
  does not finish 12653 in 120s). Production baseline (bridge OFF) never
  regressed.
- **Family lever ordering after wave 3**: extensions are now SOUND but slow —
  next levers are (a) making the ext fixpoint cheap/deterministic (BTreeMap
  the succ-ext maps like CPROCESSMAP, bound re-resolution), (b) the
  ext-resolve refinement into the satcache coupling (its establish failures
  under ∀-content are exactly what getSaturationResolvedIndividualNodeExtension
  fixes), then re-evaluate KM_HT_SATCACHE.

## Task #24 wave 2+2b (2026-07-10, commits 1b57b9d + bf282e8) — saturation-node coupling
- **LANDED, opt-in KM_HT_SATCACHE=1** (on top of KM_HT_SATURATION=1): Konclude's
  production expand-from-saturation + caching-blocking profile in the probes.
  u22 getCreationSuccessorSaturationNode (existential ref-linking + operand
  fallback) / validateSaturationCachingPossible / tryEstablishSaturationCaching
  (+ isGeneratingConceptSatisfiableCachedAbsorpable LIVE), u17
  tryExpansionFromSaturatedData (clash replay ⇒ raise_clash), u08 applySOMERule
  wiring (cpp 14224 lookup + expansion + establish + the cpp 14340 absorption
  gate: SATURATIONSUCCESSORCREATIONBLOCKINGCACHED nodes absorb their ∃s).
  Env: saturation runs ON the probe env; reset_probe_env carries the saturation
  arenas (ProcessContext::adopt_saturation_state_from — probes only read them).
  bridged_classify_opts(tin, use_saturation, use_satcache) for tests.
  Counters saturation_cache_establish_count / saturation_expansion_concept_count.
  Suite 1424/1424; 4 new bridge tests.
- **WHY OPT-IN (measured, 12653)**: coupled probes poison-defer at subject 1 vs
  subject 14 plain — without the extension-resolving refinement
  (getSaturationResolvedIndividualNodeExtension, needs the ext machinery =
  currently unsound/off) the replayed labels under-approximate ∀-restricted
  successors, establish FAILS there, and the enlarged replayed labels only feed
  branching → earlier unrestored advances. KM_HT_SATURATION alone now reproduces
  plain-probe behavior EXACTLY (verified). The coupling becomes profitable only
  after the ext-machinery wrong-clash fix + the resolve refinement port.
- **PRE-EXISTING FINDING**: plain bridge on 12653 permanent-defers at subject 14
  (completeness poison) at HEAD even WITHOUT any saturation — 12653 no longer
  closes via the bridge arm (memories claim 17-20s closes on 2026-07-08/09 builds).
  Not caused by wave 1/2 (saturation-only code). Needs its own bisect.
- **ddmin DONE: 13-axiom ext-ON wrong-clash reproducer** at
  ws:~/km-frontend/ddmin541/minimal.owl (353→13): biotoplite fragment with
  inheresIn ⊑ isIncludedIn, isBearerOf = inheresIn⁻ ⊑ includes,
  EntityAtSomeTime ∀-closure over includes/isIncludedIn, disjunctive ∀-fillers,
  ⊓-body GCIs. Inverse-role successor-EXTENSION propagation is the suspect.
  Next: trace which CLASHED-set site fires on it (s03:512, s03:638, s02:1227,
  s05:113, s05:345, s11:1846, s04:151, s08:1262) + shared-node pollution audit.

## Task #24 wave 1 (2026-07-10, commits 8481c9b + 76cc6e0)
- **Precise ATMOST criticality test LANDED** (8481c9b): s09
  is_critical_atmost_concept_descriptor_insufficient full port over the
  already-existing s08 machinery (collect + simple/detailed mergeability);
  completed the deferred concept-absent arm of
  is_individual_node_label_merging_problematic (needed for soundness of the
  discounts); live ports of markATMOST/markNominalATMOST
  RestrictedAncestorsAsInsufficient (ancestors get INSUFFICIENT, node keeps
  its verdict + CARDINALITYPROPLEMATIC — replaces node-poisoning substitute);
  succ_node_data_map HashMap→BTreeMap. 5 new bridge tests (within-bound SAT,
  qualified counting, merging discount, disjoint-veto, ≥over≤). 1420/1420.
- **CRITICAL-QUEUE MISROUTING BUG FIXED** (76cc6e0): s03's file-local
  CCT_DISJUNCTION/EQCANDIDATE were 4/5 but Konclude's enum is 2/3 (VALUE=4,
  NOMINAL=5) ⇒ every OR critical went to the always-defer VALUE stub queue;
  the precise OR test never ran. Found via new per-type SAT-STATS counters
  (541 showed 240 "VALUE" criticals with zero hasValue) + enqueue trace
  (all opcode CCOR=-3). Sound before/after (same defer direction).
- **Family verdict after both fixes (sound ext-OFF)**: STILL 0/21 (12653) and
  0/59 (541) — or=1843/1234 criticals are now decided by the PRECISE OR test
  and are genuinely critical (no disjunct entailed in saturated labels). The
  criticality-test path is exhausted; matches [[project-km-family-diagnosis]]
  (shortcuts closed). NEXT LEVER = Konclude's saturation-node expansion cache
  feeding the completion probes (cache/satnode.rs is ported but not wired):
  probes that expand into saturation-cached SAT nodes stop immediately.
- **Ext-ON wrong clashes STILL OPEN post-BTreeMap**: 541 3 runs = 12/13/10
  wrong unsats, still nondeterministic ⇒ succ_node_data_map wasn't the (only)
  unordered map; the wrong clashes are in the extension merge machinery
  itself. ddmin running on ws (~/km-frontend/ddmin541.py → ddmin541/minimal.owl,
  ws PID 3940386, log ~/km-frontend/ddmin541.log); property = any
  SAT-UNSAT-VERDICT on an axiom subset (monotonicity: any unsat on any subset
  of 541 is wrong since gold #UNSAT is empty).
- **ws HYGIENE INCIDENT**: first ddmin used subprocess.run(timeout) which
  kills only the direct km child — worker subprocesses orphaned, load hit 730.
  Cleaned by PID. Driver v2 uses start_new_session + os.killpg(SIGKILL).
  Rule: ANY harness that timeouts km classify MUST kill the process group.

# Saturation-first probe answering (task #23) — state as of 2026-07-09

**Landed** (commit `18c9a46` on payg-strategy + follow-up ext-off default): the ported
approximation-saturation units wired in front of the bridge's completion probes,
opt-in `KM_HT_SATURATION=1` inside the `KM_HT_BRIDGE` arm. `bridged_saturate` =
production config + propagation-into-creation preprocess + per-(concept,polarity)
seeds + `run_saturation_on` + `CPrecomputedSaturationSubsumerExtractor`-style
extraction (CLASHED ⇒ unsat-certain; completed+¬INSUFFICIENT+¬UNPROCESSED+¬EQCAND ⇒
sat-certain with exact subsumer row). Consumption in `bridged_classify` before the
probe loop; residue unchanged. Suite 1415/1415.

## Five port bugs found by the synthetic tests (all fixed)
1. Label-set resolve create=true default (s11 filtered-add wrappers).
2. Rule linkers allocated but never init+attached (`add_concept_to_individual`).
3. Linker-pool cycle: `initLinker` must reset `next`, release* must clearNext
   (gdb-proven infinite chain walk).
4. `checkNextCriticalConcepts` was a stub that never dequeued ⇒ infinite driver
   loop with no budget check (the 3 hanging tests). Full port of
   checkNextCriticalConcepts + checkCriticalConceptsForNode (6 typed queues)
   + precise OR/EQCAND tests + precise ALL successor-walk; ATMOST/NOMINAL/VALUE
   deferred verdicts flipped to conservative INSUFFICIENT (stubs returned
   sufficient = unsound direction).
5. **[[project-km-bridge-disjunction-probe]] [identity] strikes again**: ALL
   saturation-side super-role walks (s06/s07/s08/s10) used the bridge's STRICT
   lists ⇒ linked-successor registration was EMPTY ⇒ `isCriticalALL` saw no
   successors ⇒ ∃r.B ⊓ ∀r.¬B completed SAT-certain. Fixed with
   `saturation_indirect_super_roles` (self-inclusive) everywhere saturation-side.

## Root-⊤ completion fix (default path, in 18c9a46)
Bridge probe ROOTS were created bare; `apply_bottom_rule`'s faithful ¬⊤ insert met
no ⊤ ⇒ derived ⊥ on a root was silently satisfiable (under-detected unsat; found
by the saturation oracle test A⊑B, A⊓B⊑⊥ classified SAT by the PROBE path).
Both root-creation sites now seed ⊤. `KM_HT_NO_ROOT_TOP=1` = A/B escape hatch.
Konclude_ht suite green; candidate relevance to the 8941 under-detected-unsat tail.

## Budget soundness
`KM_HT_SATURATION_BUDGET_S` (120s default). A tripped valve can leave CRITICALS
untested ⇒ `run_saturation_on` returns false BEFORE completing nodes and
`bridged_saturate` returns None (whole pass discarded). Never read flags after
an aborted drain.

## Measurement (ws, KM_HT_BRIDGE=1 KM_HT_SATURATION=1)
- **12653**: saturation 0.06s, answered 0/21 (every subject critical-deferred).
  Family residue unchanged ⇒ still times out. Saturation cost ≈ zero.
- **541 with extensions ON**: 13-59s (NONDETERMINISTIC — HashMap succ maps vs
  Konclude's sorted CPROCESSMAP), answered 11-13 unsat + 7-8 sat of 59 —
  **UNSOUND: gold #UNSAT for 541 is EMPTY**; wrong-unsat subjects = Cell,
  Organism, Atom, MaterialObject... (core satisfiable classes).
- **Bisect**: `KM_HT_SAT_NO_EXT=1` (extensions off) ⇒ 0 wrong verdicts, 0
  answered, 0.34s ⇒ wrong clashes come from the successor-EXTENSION machinery
  (newly armed by the identity fix; W6-DEFER bodies + suspected shared-node /
  resolve-copy pollution). **Default is now extensions OFF**
  (`KM_HT_SAT_EXT=1` re-enables, currently unsound).

## Why family coverage is 0 (and what would give Konclude's ~95%)
Every family subject carries critical ⊔/≤ that the conservative tests mark
INSUFFICIENT. Konclude rescues most via (a) the precise ATMOST cardinality test
(collectATMOSTConceptRelevantSuccessors + simple/detailed mergeability, cpp
3625-3770) + delayed ATMOST merging (the merging-queue enqueue has NO live
producer in the port), and (b) sound successor extensions. Next levers, in order:
1. Port the precise ATMOST test + the merging enqueue plumbing.
2. Fix the extension machinery: complete W6-DEFER bodies, switch succ maps
   HashMap→BTreeMap (CPROCESSMAP is sorted — also fixes nondeterminism), audit
   extension writes for shared-node pollution (extensions must write to
   RESOLVED copies only).
3. Re-run the 541/12653 coverage A/B; only then decide default-on.

Debug aids: `KM_SAT_DEBUG=1` = per-node label/flag dump after saturation +
unsat-verdict subject names; `KM_BRIDGE_PROGRESS=1` prints
`BRIDGE-SATURATION: <t>s, answered N unsat + M sat of T subjects`.
Worker stderr is NULLED unless `KM_HT_STATS=1` or `KM_HT_TRACE=1` — always set
one when reading progress lines through `km classify`.
